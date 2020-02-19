use crate::built_info;
use crypto::identity::MixIdentityKeyPair;
use healthcheck::HealthChecker;
use log::{error, info, trace, warn};
use std::marker::PhantomData;
use std::sync::Arc;
use std::time;
use tokio::sync::RwLock as FRwLock;
use topology::NymTopology;

const NODE_HEALTH_THRESHOLD: f64 = 0.0;

// auxiliary type for ease of use
pub type TopologyInnerRef<T> = Arc<FRwLock<Inner<T>>>;

pub(crate) struct TopologyControl<T: NymTopology> {
    directory_server: String,
    inner: Arc<FRwLock<Inner<T>>>,
    health_checker: HealthChecker,
    refresh_rate: time::Duration,
}

#[derive(Debug)]
enum TopologyError {
    HealthCheckError,
    NoValidPathsError,
}

pub(crate) struct TopologyControlConfig<T: NymTopology> {
    directory_server: String,
    refresh_rate: time::Duration,
    identity_keypair: MixIdentityKeyPair,
    resolution_timeout: time::Duration,
    number_test_packets: usize,

    // the only reason I put phantom data here is so that we would we able to infer type
    // of TopologyControl directly from the provided config rather than having to
    // specify it during TopologyControl::<type>::new() call
    _topology_type_phantom: PhantomData<*const T>,
}

impl<T: NymTopology> TopologyControlConfig<T> {
    pub(crate) fn new(
        directory_server: String,
        refresh_rate: time::Duration,
        identity_keypair: MixIdentityKeyPair,
        resolution_timeout: time::Duration,
        number_test_packets: usize,
    ) -> Self {
        TopologyControlConfig {
            directory_server,
            refresh_rate,
            identity_keypair,
            resolution_timeout,
            number_test_packets,
            _topology_type_phantom: PhantomData,
        }
    }
}

impl<T: NymTopology> TopologyControl<T> {
    pub(crate) async fn new(cfg: TopologyControlConfig<T>) -> Self {
        // this is a temporary solution as the healthcheck will eventually be moved to validators
        let health_checker = healthcheck::HealthChecker::new(
            cfg.resolution_timeout,
            cfg.number_test_packets,
            cfg.identity_keypair,
        );

        let mut topology_control = TopologyControl {
            directory_server: cfg.directory_server,
            refresh_rate: cfg.refresh_rate,
            inner: Arc::new(FRwLock::new(Inner::new(None))),
            health_checker,
        };

        // best effort approach to try to get a valid topology after call to 'new'
        let initial_topology = match topology_control.get_current_compatible_topology().await {
            Ok(topology) => Some(topology),
            Err(err) => {
                error!("Initial topology is invalid - {:?}. Right now it will be impossible to send any packets through the mixnet!", err);
                None
            }
        };
        topology_control
            .update_global_topology(initial_topology)
            .await;

        topology_control
    }

    async fn get_current_compatible_topology(&self) -> Result<T, TopologyError> {
        let full_topology = T::new(self.directory_server.clone());
        let version_filtered_topology = full_topology.filter_node_versions(
            built_info::PKG_VERSION,
            built_info::PKG_VERSION,
            built_info::PKG_VERSION,
        );

        let healthcheck_result = self
            .health_checker
            .do_check(&version_filtered_topology)
            .await;
        let healthcheck_scores = match healthcheck_result {
            Err(err) => {
                error!("Error while performing the healthcheck: {:?}", err);
                return Err(TopologyError::HealthCheckError);
            }
            Ok(scores) => scores,
        };

        let healthy_topology = healthcheck_scores
            .filter_topology_by_score(&version_filtered_topology, NODE_HEALTH_THRESHOLD);

        // make sure you can still send a packet through the network:
        if !healthy_topology.can_construct_path_through() {
            return Err(TopologyError::NoValidPathsError);
        }

        Ok(healthy_topology)
    }

    pub(crate) fn get_inner_ref(&self) -> Arc<FRwLock<Inner<T>>> {
        self.inner.clone()
    }

    async fn update_global_topology(&mut self, new_topology: Option<T>) {
        // acquire write lock
        let mut write_lock = self.inner.write().await;
        write_lock.topology = new_topology;
    }

    pub(crate) async fn run_refresher(mut self) {
        info!("Starting topology refresher");
        loop {
            trace!("Refreshing the topology");
            let new_topology_res = self.get_current_compatible_topology().await;

            let new_topology = match new_topology_res {
                Ok(topology) => Some(topology),
                Err(err) => {
                    warn!("the obtained topology seems to be invalid - {:?}, it will be impossible to send packets through", err);
                    None
                }
            };

            self.update_global_topology(new_topology).await;
            tokio::time::delay_for(self.refresh_rate).await;
        }
    }
}

pub struct Inner<T: NymTopology> {
    pub topology: Option<T>,
}

impl<T: NymTopology> Inner<T> {
    fn new(topology: Option<T>) -> Self {
        Inner { topology }
    }
}