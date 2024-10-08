use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
    pub file: FileId,
}

impl Span {
    #[inline]
    pub fn contains(&self, pos: u32) -> bool {
        self.start <= pos && pos < self.end
    }

    pub fn compare_pos(&self, pos: u32) -> std::cmp::Ordering {
        if pos < self.start {
            std::cmp::Ordering::Less
        } else if pos >= self.end {
            std::cmp::Ordering::Greater
        } else {
            std::cmp::Ordering::Equal
        }
    }

    pub fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.file, other.file);
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            file: self.file,
        }
    }
}

#[cfg(feature = "chumsky")]
impl From<(FileId, chumsky::span::SimpleSpan)> for Span {
    #[inline]
    fn from((file, sp): (FileId, chumsky::span::SimpleSpan)) -> Self {
        Span {
            start: sp.start as u32,
            end: sp.end as u32,
            file,
        }
    }
}

impl From<(FileId, std::ops::Range<u32>)> for Span {
    #[inline]
    fn from((file, range): (FileId, std::ops::Range<u32>)) -> Self {
        Span {
            start: range.start,
            end: range.end,
            file,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

#[cfg(feature = "chumsky")]
impl chumsky::span::Span for Span {
    type Context = FileId;

    type Offset = u32;

    #[inline]
    fn new(context: Self::Context, range: std::ops::Range<Self::Offset>) -> Self {
        Span {
            start: range.start,
            end: range.end,
            file: context,
        }
    }

    #[inline]
    fn context(&self) -> Self::Context {
        self.file
    }

    #[inline]
    fn start(&self) -> Self::Offset {
        self.start
    }

    #[inline]
    fn end(&self) -> Self::Offset {
        self.end
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FileId(pub(super) u32);

impl FileId {
    #[cfg(feature = "testing")]
    pub fn from_u32(id: u32) -> Self {
        Self(id)
    }
}
