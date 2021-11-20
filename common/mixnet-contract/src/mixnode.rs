// due to code generated by JsonSchema
#![allow(clippy::field_reassign_with_default)]

use crate::{IdentityKey, SphinxKey};
use az::CheckedCast;
use cosmwasm_std::{coin, Addr, Coin, Uint128};
use log::error;
use network_defaults::{DEFAULT_OPERATOR_EPOCH_COST, DEFAULT_PROFIT_MARGIN};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use serde_repr::{Deserialize_repr, Serialize_repr};
use std::cmp::Ordering;
use std::fmt::Display;

type U128 = fixed::types::U75F53; // u128 with 18 significant digits

#[cfg_attr(feature = "ts-rs", derive(ts_rs::TS))]
#[derive(Clone, Debug, Deserialize, PartialEq, PartialOrd, Serialize, JsonSchema)]
pub struct MixNode {
    pub host: String,
    pub mix_port: u16,
    pub verloc_port: u16,
    pub http_api_port: u16,
    pub sphinx_key: SphinxKey,
    /// Base58 encoded ed25519 EdDSA public key.
    pub identity_key: IdentityKey,
    pub version: String,
}

#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize_repr,
    Deserialize_repr,
    JsonSchema,
)]
#[repr(u8)]
pub enum Layer {
    Gateway = 0,
    One = 1,
    Two = 2,
    Three = 3,
}

#[derive(Debug, Clone, JsonSchema, PartialEq, Serialize, Deserialize, Copy)]
pub struct NodeRewardParams {
    period_reward_pool: Uint128,
    k: Uint128,
    reward_blockstamp: u64,
    circulating_supply: Uint128,
    uptime: Uint128,
    sybil_resistance_percent: u8,
}

impl NodeRewardParams {
    pub fn new(
        period_reward_pool: u128,
        k: u128,
        reward_blockstamp: u64,
        circulating_supply: u128,
        uptime: u128,
        sybil_resistance_percent: u8,
    ) -> NodeRewardParams {
        NodeRewardParams {
            period_reward_pool: Uint128(period_reward_pool),
            k: Uint128(k),
            reward_blockstamp,
            circulating_supply: Uint128(circulating_supply),
            uptime: Uint128(uptime),
            sybil_resistance_percent,
        }
    }

    pub fn performance(&self) -> U128 {
        U128::from_num(self.uptime.u128()) / U128::from_num(100)
    }

    pub fn operator_cost(&self) -> U128 {
        U128::from_num(self.uptime.u128() / 100u128 * DEFAULT_OPERATOR_EPOCH_COST as u128)
    }

    pub fn set_reward_blockstamp(&mut self, blockstamp: u64) {
        self.reward_blockstamp = blockstamp;
    }

    pub fn period_reward_pool(&self) -> u128 {
        self.period_reward_pool.u128()
    }

    pub fn k(&self) -> u128 {
        self.k.u128()
    }

    pub fn circulating_supply(&self) -> u128 {
        self.circulating_supply.u128()
    }

    pub fn reward_blockstamp(&self) -> u64 {
        self.reward_blockstamp
    }

    pub fn uptime(&self) -> u128 {
        self.uptime.u128()
    }

    pub fn one_over_k(&self) -> U128 {
        U128::from_num(1) / U128::from_num(self.k.u128())
    }

    pub fn alpha(&self) -> U128 {
        U128::from_num(self.sybil_resistance_percent) / U128::from_num(100)
    }
}

#[derive(Debug)]
pub struct NodeRewardResult {
    reward: U128,
    lambda: U128,
    sigma: U128,
}

impl NodeRewardResult {
    pub fn reward(&self) -> U128 {
        self.reward
    }

    pub fn lambda(&self) -> U128 {
        self.lambda
    }

    pub fn sigma(&self) -> U128 {
        self.sigma
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, JsonSchema)]
pub struct MixNodeBond {
    pub bond_amount: Coin,
    pub total_delegation: Coin,
    pub owner: Addr,
    pub layer: Layer,
    pub block_height: u64,
    pub mix_node: MixNode,
    pub profit_margin_percent: Option<u8>,
    pub proxy: Option<Addr>
}

impl MixNodeBond {
    pub fn new(
        bond_amount: Coin,
        owner: Addr,
        layer: Layer,
        block_height: u64,
        mix_node: MixNode,
        profit_margin_percent: Option<u8>,
        proxy: Option<Addr>,
    ) -> Self {
        MixNodeBond {
            total_delegation: coin(0, &bond_amount.denom),
            bond_amount,
            owner,
            layer,
            block_height,
            mix_node,
            profit_margin_percent,
            proxy
        }
    }

    pub fn profit_margin(&self) -> U128 {
        U128::from_num(self.profit_margin_percent.unwrap_or(DEFAULT_PROFIT_MARGIN))
            / U128::from_num(100)
    }

    pub fn identity(&self) -> &String {
        &self.mix_node.identity_key
    }

    pub fn bond_amount(&self) -> Coin {
        self.bond_amount.clone()
    }

    pub fn owner(&self) -> &Addr {
        &self.owner
    }

    pub fn mix_node(&self) -> &MixNode {
        &self.mix_node
    }

    pub fn total_stake(&self) -> Option<u128> {
        if self.bond_amount.denom != self.total_delegation.denom {
            None
        } else {
            Some(self.bond_amount.amount.u128() + self.total_delegation.amount.u128())
        }
    }

    pub fn total_delegation(&self) -> Coin {
        self.total_delegation.clone()
    }

    pub fn bond_to_circulating_supply(&self, circulating_supply: u128) -> U128 {
        U128::from_num(self.bond_amount().amount.u128()) / U128::from_num(circulating_supply)
    }

    pub fn total_stake_to_circulating_supply(&self, circulating_supply: u128) -> U128 {
        U128::from_num(self.bond_amount().amount.u128() + self.total_delegation().amount.u128())
            / U128::from_num(circulating_supply)
    }

    pub fn lambda(&self, params: &NodeRewardParams) -> U128 {
        // Ratio of a bond to the token circulating supply
        let bond_to_circulating_supply_ratio =
            self.bond_to_circulating_supply(params.circulating_supply());
        bond_to_circulating_supply_ratio.min(params.one_over_k())
    }

    pub fn sigma(&self, params: &NodeRewardParams) -> U128 {
        // Ratio of a delegation to the the token circulating supply
        let total_stake_to_circulating_supply_ratio =
            self.total_stake_to_circulating_supply(params.circulating_supply());
        total_stake_to_circulating_supply_ratio.min(params.one_over_k())
    }

    pub fn reward(&self, params: &NodeRewardParams) -> NodeRewardResult {
        // Assuming uniform work distribution across the network this is one_over_k * k
        let omega_k = U128::from_num(1u128);
        let lambda = self.lambda(params);
        let sigma = self.sigma(params);

        let reward = params.performance()
            * params.period_reward_pool()
            * (sigma * omega_k + params.alpha() * lambda * sigma * params.k())
            / (U128::from_num(1) + params.alpha());

        NodeRewardResult {
            reward,
            lambda,
            sigma,
        }
    }

    pub fn node_profit(&self, params: &NodeRewardParams) -> U128 {
        if self.reward(params).reward() < params.operator_cost() {
            U128::from_num(0)
        } else {
            self.reward(params).reward() - params.operator_cost()
        }
    }

    pub fn operator_reward(&self, params: &NodeRewardParams) -> u128 {
        let reward = self.reward(params);
        let profit = if reward.reward < params.operator_cost() {
            U128::from_num(0)
        } else {
            reward.reward - params.operator_cost()
        };
        let operator_base_reward = reward.reward.min(params.operator_cost());
        let operator_reward = (self.profit_margin()
            + (U128::from_num(1) - self.profit_margin()) * reward.lambda / reward.sigma)
            * profit;

        let reward = (operator_reward + operator_base_reward).max(U128::from_num(0));

        if let Some(int_reward) = reward.checked_cast() {
            int_reward
        } else {
            error!(
                "Could not cast reward ({}) to u128, returning 0 - mixnode {}",
                reward,
                self.identity()
            );
            0u128
        }
    }

    pub fn sigma_ratio(&self, params: &NodeRewardParams) -> U128 {
        if self.total_stake_to_circulating_supply(params.circulating_supply()) < params.one_over_k()
        {
            self.total_stake_to_circulating_supply(params.circulating_supply())
        } else {
            params.one_over_k()
        }
    }

    pub fn reward_delegation(&self, delegation_amount: Uint128, params: &NodeRewardParams) -> u128 {
        let scaled_delegation_amount =
            U128::from_num(delegation_amount.u128()) / U128::from_num(params.circulating_supply());

        let delegator_reward = (U128::from_num(1) - self.profit_margin())
            * scaled_delegation_amount
            / self.sigma(params)
            * self.node_profit(params);

        let reward = delegator_reward.max(U128::from_num(0));
        if let Some(int_reward) = reward.checked_cast() {
            int_reward
        } else {
            error!(
                "Could not cast delegator reward ({}) to u128, returning 0 - mixnode {}",
                reward,
                self.identity()
            );
            0u128
        }
    }
}

impl PartialOrd for MixNodeBond {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // first remove invalid cases
        if self.bond_amount.denom != self.total_delegation.denom {
            return None;
        }

        if other.bond_amount.denom != other.total_delegation.denom {
            return None;
        }

        if self.bond_amount.denom != other.bond_amount.denom {
            return None;
        }

        // try to order by total bond + delegation
        let total_cmp = (self.bond_amount.amount + self.total_delegation.amount)
            .partial_cmp(&(self.bond_amount.amount + self.total_delegation.amount))?;

        if total_cmp != Ordering::Equal {
            return Some(total_cmp);
        }

        // then if those are equal, prefer higher bond over delegation
        let bond_cmp = self
            .bond_amount
            .amount
            .partial_cmp(&other.bond_amount.amount)?;
        if bond_cmp != Ordering::Equal {
            return Some(bond_cmp);
        }

        // then look at delegation (I'm not sure we can get here, but better safe than sorry)
        let delegation_cmp = self
            .total_delegation
            .amount
            .partial_cmp(&other.total_delegation.amount)?;
        if delegation_cmp != Ordering::Equal {
            return Some(delegation_cmp);
        }

        // then check block height
        let height_cmp = self.block_height.partial_cmp(&other.block_height)?;
        if height_cmp != Ordering::Equal {
            return Some(height_cmp);
        }

        // finally go by the rest of the fields in order. It doesn't really matter at this point
        // but we should be deterministic.
        let owner_cmp = self.owner.partial_cmp(&other.owner)?;
        if owner_cmp != Ordering::Equal {
            return Some(owner_cmp);
        }

        let layer_cmp = self.layer.partial_cmp(&other.layer)?;
        if layer_cmp != Ordering::Equal {
            return Some(layer_cmp);
        }

        self.mix_node.partial_cmp(&other.mix_node)
    }
}

impl Display for MixNodeBond {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "amount: {} {}, owner: {}, identity: {}",
            self.bond_amount.amount, self.bond_amount.denom, self.owner, self.mix_node.identity_key
        )
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, JsonSchema)]
pub struct PagedMixnodeResponse {
    pub nodes: Vec<MixNodeBond>,
    pub per_page: usize,
    pub start_next_after: Option<IdentityKey>,
}

impl PagedMixnodeResponse {
    pub fn new(
        nodes: Vec<MixNodeBond>,
        per_page: usize,
        start_next_after: Option<IdentityKey>,
    ) -> Self {
        PagedMixnodeResponse {
            nodes,
            per_page,
            start_next_after,
        }
    }
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, JsonSchema)]
pub struct MixOwnershipResponse {
    pub address: Addr,
    pub has_node: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mixnode_fixture() -> MixNode {
        MixNode {
            host: "1.1.1.1".to_string(),
            mix_port: 123,
            verloc_port: 456,
            http_api_port: 789,
            sphinx_key: "sphinxkey".to_string(),
            identity_key: "identitykey".to_string(),
            version: "0.11.0".to_string(),
        }
    }

    #[test]
    fn mixnode_bond_partial_ord() {
        let _150foos = Coin::new(150, "foo");
        let _50foos = Coin::new(50, "foo");
        let _0foos = Coin::new(0, "foo");

        let mix1 = MixNodeBond {
            bond_amount: _150foos.clone(),
            total_delegation: _50foos.clone(),
            owner: Addr::unchecked("foo1"),
            layer: Layer::One,
            block_height: 100,
            mix_node: mixnode_fixture(),
            profit_margin_percent: Some(10),
            proxy: None
        };

        let mix2 = MixNodeBond {
            bond_amount: _150foos.clone(),
            total_delegation: _50foos.clone(),
            owner: Addr::unchecked("foo2"),
            layer: Layer::One,
            block_height: 120,
            mix_node: mixnode_fixture(),
            profit_margin_percent: Some(10),
            proxy: None
        };

        let mix3 = MixNodeBond {
            bond_amount: _50foos,
            total_delegation: _150foos.clone(),
            owner: Addr::unchecked("foo3"),
            layer: Layer::One,
            block_height: 120,
            mix_node: mixnode_fixture(),
            profit_margin_percent: Some(10),
            proxy: None
        };

        let mix4 = MixNodeBond {
            bond_amount: _150foos.clone(),
            total_delegation: _0foos.clone(),
            owner: Addr::unchecked("foo4"),
            layer: Layer::One,
            block_height: 120,
            mix_node: mixnode_fixture(),
            profit_margin_percent: Some(10),
            proxy: None
        };

        let mix5 = MixNodeBond {
            bond_amount: _0foos,
            total_delegation: _150foos,
            owner: Addr::unchecked("foo5"),
            layer: Layer::One,
            block_height: 120,
            mix_node: mixnode_fixture(),
            profit_margin_percent: Some(10),
            proxy: None
        };

        // summary:
        // mix1: 150bond + 50delegation, foo1, 100
        // mix2: 150bond + 50delegation, foo2, 120
        // mix3: 50bond + 150delegation, foo3, 120
        // mix4: 150bond + 0delegation, foo4, 120
        // mix5: 0bond + 150delegation, foo5, 120

        // highest total bond+delegation is used
        // then bond followed by delegation
        // finally just the rest of the fields

        // mix1 has higher total than mix4 or mix5
        assert!(mix1 > mix4);
        assert!(mix1 > mix5);

        // mix1 has the same total as mix3, however, mix1 has more tokens in bond
        assert!(mix1 > mix3);
        // same case for mix4 and mix5
        assert!(mix4 > mix5);

        // same bond and delegation, so it's just ordered by height
        assert!(mix1 < mix2);
    }
}
