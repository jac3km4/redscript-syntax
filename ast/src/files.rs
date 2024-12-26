use std::{
    fmt, fs, io,
    path::{Path, PathBuf},
};

use crate::span::FileId;

#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<File>,
}

impl SourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_files(it: impl IntoIterator<Item = impl Into<PathBuf>>) -> io::Result<Self> {
        let mut files = Self::new();
        for path in it {
            let path = path.into();
            let source = fs::read_to_string(&path)?;
            files.add(path, source);
        }
        Ok(files)
    }

    pub fn add(&mut self, path: PathBuf, source: String) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(File::new(path, source));
        id
    }

    #[inline]
    pub fn get(&self, id: FileId) -> Option<&File> {
        self.files.get(id.0 as usize)
    }

    pub fn files(&self) -> impl Iterator<Item = (FileId, &File)> {
        self.files
            .iter()
            .enumerate()
            .map(|(i, f)| (FileId(i as u32), f))
    }
}

#[derive(Debug)]
pub struct File {
    path: PathBuf,
    source: String,
    lines: Vec<u32>,
}

impl File {
    pub fn new(path: PathBuf, source: String) -> Self {
        let mut lines = vec![];
        for (offset, _) in source.match_indices('\n') {
            lines.push(offset as u32 + 1);
        }
        Self {
            path,
            source,
            lines,
        }
    }

    #[inline]
    pub fn source(&self) -> &str {
        &self.source
    }

    #[inline]
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn lookup(&self, offset: u32) -> SourceLoc {
        let (line, line_offset) = if self.lines.first().is_some_and(|&p| p > offset) {
            (0, 0)
        } else {
            let line = self
                .lines
                .binary_search(&offset)
                .map(|i| i + 1)
                .unwrap_or_else(|i| i);
            (line, self.lines[line - 1])
        };
        SourceLoc {
            line,
            col: self.source[line_offset as usize..offset as usize]
                .chars()
                .count(),
        }
    }

    pub fn line(&self, idx: usize) -> Option<&str> {
        let start = if idx == 0 {
            0
        } else {
            self.lines.get(idx - 1).copied()?
        };
        let end = self
            .lines
            .get(idx)
            .copied()
            .unwrap_or(self.source.len() as u32);
        Some(&self.source[start as usize..end as usize - 1])
    }
}

#[derive(Debug, Clone)]
pub struct SourceLoc {
    pub line: usize,
    pub col: usize,
}

impl fmt::Display for SourceLoc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line + 1, self.col + 1)
    }
}
