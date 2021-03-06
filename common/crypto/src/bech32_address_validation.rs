use config::defaults;
use subtle_encoding::bech32;

#[derive(Debug, Clone, PartialEq)]
pub enum Bech32Error {
    DecodeFailed(String),
    WrongPrefix(String),
}

/// Try to decode the address (to make sure it's a valid bech32 encoding)
pub fn try_bech32_decode(address: &str) -> Result<String, Bech32Error> {
    match bech32::decode(address) {
        Err(e) => Err(Bech32Error::DecodeFailed(e.to_string())),
        Ok((prefix, _)) => Ok(prefix),
    }
}

pub fn validate_bech32_prefix(address: &str) -> Result<(), Bech32Error> {
    let prefix = try_bech32_decode(address)?;

    if prefix == defaults::BECH32_PREFIX {
        Ok(())
    } else {
        Err(Bech32Error::WrongPrefix(format!(
            "your bech32 address prefix should be {}, not {}",
            defaults::BECH32_PREFIX,
            prefix
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod decoding_bech32_addresses {
        use super::*;

        #[test]
        fn total_crap_fails() {
            let res = try_bech32_decode("crap");
            assert_eq!(
                Err(Bech32Error::DecodeFailed("bad encoding".to_string())),
                res
            );
        }

        #[test]
        fn bad_checksum_fails() {
            let chopped_address = "punk1h3w4nj7kny5dfyjw2le4vm74z03v9vd4dstpu"; // this has the final "0" chopped off
            let res = try_bech32_decode(chopped_address);
            assert_eq!(
                Err(Bech32Error::DecodeFailed("checksum mismatch".to_string())),
                res
            );
        }

        #[test]
        fn good_address_returns_prefix() {
            let prefix = try_bech32_decode("punk1h3w4nj7kny5dfyjw2le4vm74z03v9vd4dstpu0");
            assert_eq!(Ok("punk".to_string()), prefix);
        }
    }

    #[cfg(test)]
    mod ensuring_correct_bech32_prefix {
        use super::*;

        #[test]
        fn wrong_prefix_fails() {
            assert_eq!(
                Err(Bech32Error::WrongPrefix(
                    "your bech32 address prefix should be nymt, not punk".to_string()
                )),
                validate_bech32_prefix("punk1h3w4nj7kny5dfyjw2le4vm74z03v9vd4dstpu0")
            )
        }

        #[test]
        fn correct_prefix_works() {
            assert_eq!(
                Ok(()),
                validate_bech32_prefix("nymt1z9egw0knv47nmur0p8vk4rcx59h9gg4zuxrrr9")
            )
        }
    }
}
