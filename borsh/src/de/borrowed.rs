use crate::{
    maybestd::io::{Error, ErrorKind, Result},
    BorshDeserialize,
};

use super::{ERROR_NOT_ALL_BYTES_READ, ERROR_UNEXPECTED_LENGTH_OF_INPUT};

/// A borrowed data-structure that can be de-serialized from binary format by NBOR.
pub trait BorshBorrowedDeserialize<'de>: Sized {
    /// Deserializes this instance from a given slice of bytes.
    /// Updates the buffer to point at the remaining bytes.
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self>;

    /// Deserialize this instance from a slice of bytes.
    fn try_from_slice(v: &'de [u8]) -> Result<Self> {
        let mut v_mut = v;
        let result = Self::deserialize(&mut v_mut)?;
        if !v_mut.is_empty() {
            return Err(Error::new(ErrorKind::InvalidData, ERROR_NOT_ALL_BYTES_READ));
        }
        Ok(result)
    }
}

impl<'de, T: BorshDeserialize> BorshBorrowedDeserialize<'de> for T {
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        T::deserialize(buf)
    }
}

impl<'de> BorshBorrowedDeserialize<'de> for &'de str {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = <u32 as BorshDeserialize>::deserialize(buf)? as usize;
        if len > buf.len() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }

        let (bytes, new_buf) = buf.split_at(len);
        *buf = new_buf;

        std::str::from_utf8(bytes).map_err(|err| {
            let msg = err.to_string();
            Error::new(ErrorKind::InvalidData, msg)
        })
    }
}

impl<'de> BorshBorrowedDeserialize<'de> for &'de [u8] {
    #[inline]
    fn deserialize(buf: &mut &'de [u8]) -> Result<Self> {
        let len = <u32 as BorshDeserialize>::deserialize(buf)? as usize;
        if len > buf.len() {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                ERROR_UNEXPECTED_LENGTH_OF_INPUT,
            ));
        }

        let (bytes, new_buf) = buf.split_at(len);
        *buf = new_buf;
        Ok(bytes)
    }
}
