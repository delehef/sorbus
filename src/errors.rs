use thiserror::Error;

use crate::NodeHandle;

#[derive(Error, Debug)]
pub enum Error {
    #[error("node {0} not found")]
    NodeNotFound(NodeHandle),
}
