use std::{
    cell::RefCell,
    fs::File,
    io::{BufReader, BufWriter, Read, Seek, SeekFrom, Write},
    marker::PhantomData,
};

use serde::{Deserialize, Serialize};

struct ColdVecInner<const CHUNK_SIZE: usize> {
    file: Option<File>,
    reader: Option<BufReader<File>>,
    writer: Option<BufWriter<File>>,
    elements_len: u64,
    chunks_len: u64,
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
            file: Some(file),
            reader: None,
            writer: None,
            elements_len: 0,
            chunks_len: 0,
            cursor: 0,
        };

        let file_len = r.file.as_ref().unwrap().metadata()?.len();
        if file_len > 0 {
            r.seek(SeekFrom::End(-Self::total_chunk_size_i64()))?;
            let h = r.read_chunk_header()?;
            r.elements_len = h.index + 1;
            r.chunks_len = file_len / Self::total_chunk_size_u64();
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

    fn stream_position(&mut self) -> Result<u64, std::io::Error> {
        if let Some(r) = self.reader.as_mut() {
            r.stream_position()
        } else if let Some(w) = self.writer.as_mut() {
            w.stream_position()
        } else if let Some(f) = self.file.as_mut() {
            f.stream_position()
        } else {
            unreachable!()
        }
    }

    fn seek(&mut self, pos: SeekFrom) -> Result<u64, std::io::Error> {
        if let Some(r) = self.reader.as_mut() {
            r.seek(pos)
        } else if let Some(w) = self.writer.as_mut() {
            w.seek(pos)
        } else if let Some(f) = self.file.as_mut() {
            f.seek(pos)
        } else {
            unreachable!()
        }
    }

    fn take_file(&mut self) -> Result<File, std::io::Error> {
        match (self.reader.take(), self.writer.take(), self.file.take()) {
            (Some(r), None, None) => Ok(r.into_inner()),
            (None, Some(w), None) => w.into_inner().map_err(|e| e.into_error()),
            (None, None, Some(f)) => Ok(f),
            _ => unreachable!(),
        }
    }

    fn start_reading(&mut self) -> Result<(), std::io::Error> {
        if self.reader.is_some() {
            return Ok(());
        }
        self.reader = Some(BufReader::new(self.take_file()?));
        Ok(())
    }

    fn start_writing(&mut self) -> Result<(), std::io::Error> {
        if self.writer.is_some() {
            return Ok(());
        }
        self.writer = Some(BufWriter::new(self.take_file()?));
        Ok(())
    }

    fn write_chunk_header(&mut self, header: ChunkHeader) -> Result<(), std::io::Error> {
        assert_eq!(
            self.stream_position().unwrap() % Self::total_chunk_size_u64(),
            0
        );

        self.start_writing()?;
        let w = self.writer.as_mut().unwrap();
        w.write_all(&header.index.to_le_bytes())?;
        w.write_all(&header.offset.to_le_bytes())?;
        w.write_all(&header.len.to_le_bytes())?;
        Ok(())
    }

    fn read_chunk_header(&mut self) -> Result<ChunkHeader, std::io::Error> {
        let mut index = [0u8; 8];
        let mut offset = [0u8; 4];
        let mut len = [0u8; 4];

        self.start_reading()?;
        let r = self.reader.as_mut().unwrap();
        r.read_exact(&mut index)?;
        r.read_exact(&mut offset)?;
        r.read_exact(&mut len)?;

        Ok(ChunkHeader {
            index: u64::from_le_bytes(index),
            offset: u32::from_le_bytes(offset),
            len: u32::from_le_bytes(len),
        })
    }

    pub fn get(&mut self, index: u64) -> Result<Option<Vec<u8>>, std::io::Error> {
        if index >= self.elements_len {
            return Ok(None);
        }
        if self.reader.is_some() && self.cursor == index {
            return self.read_value().map(Some);
        }

        let mut ok = 0;
        let mut ng = self.chunks_len;
        self.start_reading()?;

        while ng - ok > 1 {
            let mid = ok + (ng - ok) / 2;
            self.seek(SeekFrom::Start(mid * Self::total_chunk_size_u64()))?;

            let header = self.read_chunk_header()?;

            if (header.index, header.offset) <= (index, 0) {
                ok = mid;
            } else {
                ng = mid;
            }
        }

        if ok == self.chunks_len {
            return Ok(None);
        }
        self.seek(SeekFrom::Start(ok * Self::total_chunk_size_u64()))?;
        let result = self.read_value().map(Some);

        result
    }

    fn read_value(&mut self) -> Result<Vec<u8>, std::io::Error> {
        let mut result = Vec::new();
        loop {
            let header = self.read_chunk_header()?;
            let mut buf = [0u8; CHUNK_SIZE];
            self.reader.as_mut().unwrap().read_exact(&mut buf)?;
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
        self.seek(SeekFrom::End(0))?;
        let len = value.len() as u32;
        for (i, chunk) in value.chunks(CHUNK_SIZE).enumerate() {
            self.write_chunk_header(ChunkHeader {
                index: self.elements_len,
                offset: (i * CHUNK_SIZE) as u32,
                len,
            })?;

            let w = self.writer.as_mut().unwrap();
            w.write_all(chunk)?;

            if chunk.len() != CHUNK_SIZE {
                let pad = [0u8; CHUNK_SIZE];
                w.write_all(&pad[chunk.len()..])?;
            }

            self.chunks_len += 1;
        }
        self.elements_len += 1;
        self.cursor = self.elements_len;
        Ok(())
    }

    pub fn clear(&mut self) -> Result<(), std::io::Error> {
        self.file = Some(self.take_file()?);

        let f = self.file.as_mut().unwrap();
        f.seek(SeekFrom::Start(0))?;
        f.set_len(0)?;

        self.elements_len = 0;
        self.chunks_len = 0;
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

    pub fn len(&self) -> usize {
        let inner = self.inner.borrow();
        inner.elements_len as usize
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
            assert_eq!(target.len(), i);
            let s = "a".repeat(i);
            target.push(&s);
        }
        assert_eq!(target.len(), n);

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
        assert_eq!(target.len(), n);
        for i in 0..n {
            let s = "a".repeat(i);
            assert_eq!(target.get(i), Some(s));
        }
    }
}
