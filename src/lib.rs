use std::{
    cell::RefCell,
    fs::File,
    io::{Read, Seek, SeekFrom, Write},
    marker::PhantomData,
};

use serde::{Deserialize, Serialize};

struct ColdVecInner<const CHUNK_SIZE: usize> {
    file: File,
    len: u64,
    cursor: u64,
}

const CHUNK_HEADER_SIZE: i64 = 16;

#[derive(Debug)]
struct ChunkHeader {
    index: u64,
    offset: u32,
    len: u32,
}

impl<const CHUNK_SIZE: usize> ColdVecInner<CHUNK_SIZE> {
    fn new(file: File) -> Result<Self, std::io::Error> {
        let mut r = Self {
            file,
            len: 0,
            cursor: 0,
        };

        if r.file.metadata()?.len() > 0 {
            r.file.seek(SeekFrom::End(-Self::total_chunk_size_i64()))?;
            let h = r.read_chunk_header()?;
            r.len = h.index + 1;
            r.cursor = h.index + 1;
        }
        Ok(r)
    }

    const fn total_chunk_size_i64() -> i64 {
        CHUNK_HEADER_SIZE as i64 + CHUNK_SIZE as i64
    }

    const fn total_chunk_size_u64() -> u64 {
        CHUNK_HEADER_SIZE as u64 + CHUNK_SIZE as u64
    }

    fn write_chunk_header(&mut self, header: ChunkHeader) -> Result<(), std::io::Error> {
        assert_eq!(
            self.file.stream_position().unwrap() % Self::total_chunk_size_u64(),
            0
        );

        self.file.write_all(&header.index.to_le_bytes())?;
        self.file.write_all(&header.offset.to_le_bytes())?;
        self.file.write_all(&header.len.to_le_bytes())?;
        Ok(())
    }

    fn read_chunk_header(&mut self) -> Result<ChunkHeader, std::io::Error> {
        let mut index = [0u8; 8];
        let mut offset = [0u8; 4];
        let mut len = [0u8; 4];

        self.file.read_exact(&mut index)?;
        self.file.read_exact(&mut offset)?;
        self.file.read_exact(&mut len)?;

        Ok(ChunkHeader {
            index: u64::from_le_bytes(index),
            offset: u32::from_le_bytes(offset),
            len: u32::from_le_bytes(len),
        })
    }

    pub fn get(&mut self, index: u64) -> Result<Option<Vec<u8>>, std::io::Error> {
        let total_chunk_size = CHUNK_HEADER_SIZE as u64 + CHUNK_SIZE as u64;

        if index >= self.len {
            return Ok(None);
        }
        if self.cursor == index {
            return self.read_value().map(Some);
        }

        let mut ok = 0;
        let ng0 = self.file.metadata()?.len() / total_chunk_size;
        let mut ng = ng0;

        while ng - ok > 1 {
            let mid = ok + (ng - ok) / 2;
            self.file.seek(SeekFrom::Start(mid * total_chunk_size))?;

            let header = self.read_chunk_header()?;

            if (header.index, header.offset) <= (index, 0) {
                ok = mid;
            } else {
                ng = mid;
            }
        }

        if ok == ng0 {
            return Ok(None);
        }
        self.file.seek(SeekFrom::Start(ok * total_chunk_size))?;
        let result = self.read_value().map(Some);

        result
    }

    fn read_value(&mut self) -> Result<Vec<u8>, std::io::Error> {
        let mut result = Vec::new();
        loop {
            let header = self.read_chunk_header()?;
            let mut buf = [0u8; CHUNK_SIZE];
            self.file.read_exact(&mut buf)?;
            if header.len - header.offset <= CHUNK_SIZE as u32 {
                result.extend_from_slice(&buf[0..(header.len - header.offset) as usize]);
                self.cursor = header.index + 1;
                break;
            } else {
                result.extend_from_slice(&buf);
            };
        }
        Ok(result)
    }

    pub fn push(&mut self, value: &[u8]) -> Result<(), std::io::Error> {
        self.file.seek(SeekFrom::End(0))?;
        let len = value.len() as u32;
        for (i, chunk) in value.chunks(CHUNK_SIZE).enumerate() {
            self.write_chunk_header(ChunkHeader {
                index: self.len,
                offset: (i * CHUNK_SIZE) as u32,
                len,
            })?;
            self.file.write_all(chunk)?;

            if chunk.len() != CHUNK_SIZE {
                let pad = [0u8; CHUNK_SIZE];
                self.file.write_all(&pad[chunk.len()..])?;
            }
        }
        self.len += 1;
        self.cursor = self.len;
        Ok(())
    }

    pub fn clear(&mut self) -> Result<(), std::io::Error> {
        self.file.seek(SeekFrom::Start(0))?;
        self.file.set_len(0)?;
        self.len = 0;
        self.cursor = 0;
        Ok(())
    }
}

pub struct ColdVec<T, const CHUNK_SIZE: usize = 112>
where
    for<'any> T: Serialize + Deserialize<'any>,
{
    inner: RefCell<ColdVecInner<CHUNK_SIZE>>,
    phantom: PhantomData<T>,
}

impl<T, const CHUNK_SIZE: usize> ColdVec<T, CHUNK_SIZE>
where
    for<'any> T: Serialize + Deserialize<'any>,
{
    pub fn new(path: impl AsRef<std::path::Path>) -> Result<Self, std::io::Error> {
        let file = File::options()
            .read(true)
            .write(true)
            .create(true)
            .open(path)?;
        Ok(Self {
            inner: RefCell::new(ColdVecInner::new(file).expect("io error")),
            phantom: PhantomData,
        })
    }

    pub fn get(&self, index: usize) -> Option<T> {
        let mut inner = self.inner.borrow_mut();
        let data = inner.get(index as u64).expect("io error")?;
        rmp_serde::from_slice(&data).expect("deserialize error")
    }

    pub fn push(&mut self, value: &T) {
        let value = rmp_serde::to_vec(value).expect("failed to parse");
        let mut inner = self.inner.borrow_mut();
        inner.push(&value).expect("io error");
    }

    pub fn clear(&mut self) {
        self.inner.borrow_mut().clear().expect("io error");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut target = ColdVec::<String>::new(format!("test-ws/{l}", l = line!())).unwrap();
        target.clear();

        let n = 1000;
        for i in 0..n {
            let s = "a".repeat(i);
            target.push(&s);
        }

        for i in 0..n {
            let s = "a".repeat(i);
            assert_eq!(target.get(i), Some(s));
        }

        for i in (0..n).rev() {
            let s = "a".repeat(i);
            assert_eq!(target.get(i), Some(s));
        }
    }

    #[test]
    fn test_clear() {
        let mut target = ColdVec::<String>::new(format!("test-ws/{l}", l = line!())).unwrap();
        target.clear();

        let n = 1000;
        for i in 0..n {
            let s = "a".repeat(i);
            target.push(&s);
        }

        target.clear();

        assert_eq!(target.get(0), None);
    }

    #[test]
    fn test_reopen() {
        let name = format!("test-ws/{l}", l = line!());
        let mut target = ColdVec::<String>::new(&name).unwrap();
        target.clear();

        let n = 1000;
        for i in 0..n {
            let s = "a".repeat(i);
            target.push(&s);
        }
        drop(target);

        let target = ColdVec::<String>::new(&name).unwrap();
        for i in 0..n {
            let s = "a".repeat(i);
            assert_eq!(target.get(i), Some(s));
        }
    }
}
