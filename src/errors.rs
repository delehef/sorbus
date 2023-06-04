use thiserror::Error;

use crate::NodeID;

#[derive(Error, Debug)]
pub enum Error {
    #[error("node {0} not found")]
    NodeNotFound(NodeID),
}
