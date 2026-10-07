//! Versioned JSON command boundary. Payload objects remain in the executor.
use serde::{Deserialize, Serialize};

/// Parse and serialize an integer as a decimal string, avoiding JS precision loss.
pub(crate) mod decimal {
    use serde::{Deserialize, Deserializer, Serializer};
    use std::{fmt::Display, str::FromStr};
    pub fn serialize<T: Display, S: Serializer>(
        value: &T,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&value.to_string())
    }
    pub fn deserialize<'de, T: FromStr, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<T, D::Error>
    where
        T::Err: Display,
    {
        let value = String::deserialize(deserializer)?;
        if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
            return Err(serde::de::Error::custom(
                "identity must be a decimal string",
            ));
        }
        value.parse().map_err(serde::de::Error::custom)
    }
}
pub(crate) mod optional_decimal {
    use serde::{Deserialize, Deserializer};
    use std::{fmt::Display, str::FromStr};
    pub fn deserialize<'de, T: FromStr, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<T>, D::Error>
    where
        T::Err: Display,
    {
        Option::<String>::deserialize(deserializer)?
            .map(|value| {
                if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(serde::de::Error::custom(
                        "identity must be a decimal string",
                    ));
                }
                value.parse().map_err(serde::de::Error::custom)
            })
            .transpose()
    }
}

/// Identity of a service in a particular isolation realm.
#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ServicePort {
    #[serde(with = "decimal")]
    pub key: u64,
    #[serde(with = "decimal")]
    pub realm: u64,
}
impl From<ServicePort> for cordis_kernel::Port {
    fn from(value: ServicePort) -> Self {
        Self {
            key: value.key,
            realm: value.realm,
        }
    }
}
impl From<cordis_kernel::Port> for ServicePort {
    fn from(value: cordis_kernel::Port) -> Self {
        Self {
            key: value.key,
            realm: value.realm,
        }
    }
}

/// An action acknowledged once, even when cancellation happened in flight.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ActionTicket {
    #[serde(with = "decimal")]
    pub domain: u64,
    #[serde(with = "decimal")]
    pub id: usize,
    #[serde(with = "decimal")]
    pub generation: u64,
    #[serde(with = "decimal")]
    pub action: u64,
    pub kind: ActionKind,
}

#[derive(Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ActionKind {
    Setup,
    Cleanup,
}

/// Instructions to the executor. Removed is an observation, not a callback.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HostAction {
    Setup {
        #[serde(with = "decimal")]
        id: usize,
        ticket: ActionTicket,
    },
    Cleanup {
        #[serde(with = "decimal")]
        id: usize,
        ticket: ActionTicket,
    },
    Removed {
        #[serde(with = "decimal")]
        id: usize,
    },
}

/// Public command protocol. Unknown fields and lossy numeric identities fail.
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
pub enum Command {
    Configure {
        profile: Profile,
    },
    Mount {
        #[serde(default = "default_sealed")]
        sealed: bool,
        #[serde(default, deserialize_with = "optional_decimal::deserialize")]
        parent: Option<usize>,
        #[serde(default)]
        dependencies: Vec<ServicePort>,
        #[serde(default)]
        provisions: Vec<ServicePort>,
    },
    Prepare {
        #[serde(with = "decimal")]
        id: usize,
    },
    Seal {
        #[serde(with = "decimal")]
        id: usize,
        dependencies: Vec<ServicePort>,
    },
    Reclaim {
        #[serde(with = "decimal")]
        id: usize,
        #[serde(with = "decimal")]
        generation: u64,
        #[serde(with = "decimal")]
        publication: usize,
    },
    CommittedReaches {
        #[serde(with = "decimal")]
        from: usize,
        #[serde(with = "decimal")]
        generation: u64,
        #[serde(with = "decimal")]
        target: usize,
    },
    Drive,
    Complete {
        ticket: ActionTicket,
        success: bool,
        #[serde(default)]
        error: Option<String>,
    },
    #[serde(alias = "dispose")]
    Retire {
        #[serde(with = "decimal")]
        id: usize,
    },
    Restart {
        #[serde(with = "decimal")]
        id: usize,
    },
    RetryCleanup {
        #[serde(with = "decimal")]
        id: usize,
    },
    Validate {
        #[serde(with = "decimal")]
        id: usize,
        #[serde(with = "decimal")]
        generation: u64,
    },
    Publish {
        #[serde(default)]
        check: bool,
        #[serde(with = "decimal")]
        id: usize,
        #[serde(with = "decimal")]
        generation: u64,
        #[serde(with = "decimal")]
        key: u64,
        #[serde(with = "decimal")]
        realm: u64,
        #[serde(with = "decimal")]
        value: u64,
    },
    Set {
        #[serde(with = "decimal")]
        id: usize,
        #[serde(with = "decimal")]
        generation: u64,
        #[serde(with = "decimal")]
        publication: usize,
        #[serde(with = "decimal")]
        value: u64,
    },
    Revoke {
        #[serde(with = "decimal")]
        id: usize,
        #[serde(with = "decimal")]
        generation: u64,
        #[serde(with = "decimal")]
        publication: usize,
    },
    #[serde(alias = "lookup")]
    Resolve {
        #[serde(with = "decimal")]
        key: u64,
        #[serde(with = "decimal")]
        realm: u64,
        #[serde(default, deserialize_with = "optional_decimal::deserialize")]
        consumer: Option<usize>,
        #[serde(default, deserialize_with = "optional_decimal::deserialize")]
        generation: Option<u64>,
    },
    Checks,
    Notify {
        ports: Vec<ServicePort>,
    },
    ValidateCheck {
        ticket: crate::availability::CheckTicket,
    },
    CompleteCheck {
        ticket: crate::availability::CheckTicket,
        available: bool,
        #[serde(default)]
        error: Option<String>,
    },
    Snapshot,
    /// Internal lifecycle observation without graph diagnostics or storage scans.
    SnapshotState,
}

fn default_sealed() -> bool {
    true
}

/// Policy is frozen before the first logical fiber is allocated.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Profile {
    #[default]
    Cordis,
    Harness,
}
