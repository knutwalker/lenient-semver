use std::{
    cmp::Ordering,
    iter::FromIterator,
    ops::{Deref, DerefMut, Index, IndexMut},
};

/// Additional numeric identifiers, not part of the semver spec.
#[derive(Debug, Clone, Default, Eq, Hash)]
pub struct Additional {
    numbers: Vec<u64>,
}

impl Additional {
    /// Constructs an empty list of additional numbers
    pub const fn empty() -> Self {
        Self {
            numbers: Vec::new(),
        }
    }

    /// Returns an iterator over the additional numbers
    pub fn iter(&self) -> impl Iterator<Item = &u64> + '_ {
        self.numbers.iter()
    }

    /// Returns a mutable iterator over the additional numbers
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut u64> + '_ {
        self.numbers.iter_mut()
    }

    pub(super) fn push(&mut self, num: u64) {
        self.numbers.push(num);
    }

    pub(super) fn set_to_zero(&mut self) {
        self.numbers.iter_mut().for_each(|n| *n = 0);
    }

    pub(super) fn clone_with_zeroes(&self) -> Self {
        Self {
            numbers: vec![0; self.numbers.len()],
        }
    }

    pub(super) fn bump(&mut self, index: usize) {
        let mut add = self.numbers.iter_mut().skip(index);
        if let Some(add) = add.next() {
            *add += 1;
        }
        add.for_each(|n| *n = 0);
    }
}

impl Deref for Additional {
    type Target = [u64];

    fn deref(&self) -> &Self::Target {
        &self.numbers[..]
    }
}

impl DerefMut for Additional {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.numbers[..]
    }
}

impl AsRef<[u64]> for Additional {
    fn as_ref(&self) -> &[u64] {
        &self.numbers[..]
    }
}

impl AsMut<[u64]> for Additional {
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.numbers[..]
    }
}

impl Index<usize> for Additional {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        &self.numbers[index]
    }
}

impl IndexMut<usize> for Additional {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.numbers[index]
    }
}

impl FromIterator<u64> for Additional {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        Self {
            numbers: iter.into_iter().collect(),
        }
    }
}

impl From<Vec<u64>> for Additional {
    fn from(numbers: Vec<u64>) -> Self {
        Self { numbers }
    }
}

impl From<&[u64]> for Additional {
    fn from(numbers: &[u64]) -> Self {
        Self {
            numbers: numbers.to_vec(),
        }
    }
}

impl PartialEq for Additional {
    fn eq(&self, other: &Self) -> bool {
        AdditionalCmp {
            lhs: self.numbers.iter(),
            rhs: other.numbers.iter(),
        }
        .all(|c| c == Ordering::Equal)
    }
}

impl PartialOrd for Additional {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Additional {
    fn cmp(&self, other: &Self) -> Ordering {
        AdditionalCmp {
            lhs: self.numbers.iter(),
            rhs: other.numbers.iter(),
        }
        .find(|c| *c != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
    }
}

struct AdditionalCmp<I, J> {
    lhs: I,
    rhs: J,
}

impl<'a, I, J> Iterator for AdditionalCmp<I, J>
where
    I: Iterator<Item = &'a u64>,
    J: Iterator<Item = &'a u64>,
{
    type Item = Ordering;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.lhs.next(), self.rhs.next()) {
            (None, None) => None,
            (Some(a), None) => Some(a.cmp(&0)),
            (None, Some(b)) => Some(0.cmp(b)),
            (Some(a), Some(b)) => Some(a.cmp(b)),
        }
    }
}

/// The pre-release segment of a semantic Version.
#[derive(Debug, Clone, Eq, Hash)]
pub struct PreRelease<'input> {
    identifier: Option<&'input str>,
}

impl<'input> PreRelease<'input> {
    /// Constructs an empty pre-release segment
    pub const fn empty() -> Self {
        Self { identifier: None }
    }

    /// Returns true if the pre-release segment is missing
    pub const fn is_empty(&self) -> bool {
        self.identifier.is_none()
    }

    /// Returns true if the pre-release is defined
    pub const fn is_defined(&self) -> bool {
        self.identifier.is_some()
    }

    pub(super) fn set(&mut self, identifier: &'input str) {
        self.identifier = Some(identifier);
    }

    pub(super) fn clear(&mut self) {
        self.identifier = None;
    }
}

impl<'input> Deref for PreRelease<'input> {
    type Target = Option<&'input str>;

    fn deref(&self) -> &Self::Target {
        &self.identifier
    }
}

impl<'input> DerefMut for PreRelease<'input> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.identifier
    }
}

impl<'input> AsRef<str> for PreRelease<'input> {
    fn as_ref(&self) -> &str {
        self.identifier.unwrap_or_default()
    }
}

impl<'input> From<&'input str> for PreRelease<'input> {
    fn from(identifier: &'input str) -> Self {
        Self {
            identifier: Some(identifier),
        }
    }
}

impl<'input> PartialEq for PreRelease<'input> {
    fn eq(&self, other: &Self) -> bool {
        match (self.identifier, other.identifier) {
            (None, None) => true,
            (None, Some(_)) => false,
            (Some(_), None) => false,
            (Some(lhs), Some(rhs)) => lhs
                .split(['-', '.'].as_ref())
                .eq(rhs.split(['-', '.'].as_ref())),
        }
    }
}

impl<'input> PartialOrd for PreRelease<'input> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'input> Ord for PreRelease<'input> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.identifier, other.identifier) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (Some(lhs), Some(rhs)) => PreReleaseCmp {
                lhs: lhs.split(['-', '.'].as_ref()),
                rhs: rhs.split(['-', '.'].as_ref()),
            }
            .find(|c| *c != Ordering::Equal)
            .unwrap_or(Ordering::Equal),
        }
    }
}

struct PreReleaseCmp<I, J> {
    lhs: I,
    rhs: J,
}

impl<'input, I, J> Iterator for PreReleaseCmp<I, J>
where
    I: Iterator<Item = &'input str>,
    J: Iterator<Item = &'input str>,
{
    type Item = Ordering;

    /// Identifiers consisting of only digits are compared numerically.
    /// Identifiers with letters or hyphens are compared lexically in ASCII sort order.
    /// Numeric identifiers always have lower precedence than non-numeric identifiers.
    /// A larger set of pre-release fields has a higher precedence than a smaller set, if all of the preceding identifiers are equal.
    /// Example: 1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11 < 1.0.0-rc.1 < 1.0.0.
    fn next(&mut self) -> Option<Self::Item> {
        match (self.lhs.next(), self.rhs.next()) {
            (None, None) => None,
            (Some(_), None) => Some(Ordering::Greater),
            (None, Some(_)) => Some(Ordering::Less),
            (Some(a), Some(b)) => Some(match (a.parse::<u64>(), b.parse::<u64>()) {
                (Ok(a), Ok(ref b)) => a.cmp(b),
                (Ok(_), Err(_)) => Ordering::Less,
                (Err(_), Ok(_)) => Ordering::Greater,
                (Err(_), Err(_)) => a.cmp(&b),
            }),
        }
    }
}

/// The build segment of a semantic Version.
#[derive(Debug, Clone)]
pub struct Build<'input> {
    identifier: Option<&'input str>,
}

impl<'input> Build<'input> {
    /// Constructs an empty build segment
    pub const fn empty() -> Self {
        Self { identifier: None }
    }

    /// Returns true if the build segment is missing
    pub const fn is_empty(&self) -> bool {
        self.identifier.is_none()
    }

    /// Returns true if the build is defined
    pub const fn is_defined(&self) -> bool {
        self.identifier.is_some()
    }

    pub(super) fn set(&mut self, identifier: &'input str) {
        self.identifier = Some(identifier);
    }

    pub(super) fn clear(&mut self) {
        self.identifier = None;
    }
}

impl<'input> Deref for Build<'input> {
    type Target = Option<&'input str>;

    fn deref(&self) -> &Self::Target {
        &self.identifier
    }
}

impl<'input> DerefMut for Build<'input> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.identifier
    }
}

impl<'input> AsRef<str> for Build<'input> {
    fn as_ref(&self) -> &str {
        self.identifier.unwrap_or_default()
    }
}

impl<'input> From<&'input str> for Build<'input> {
    fn from(identifier: &'input str) -> Self {
        Self {
            identifier: Some(identifier),
        }
    }
}

#[cfg(feature = "semver")]
impl std::convert::TryInto<semver::Prerelease> for PreRelease<'_> {
    type Error = semver::Error;

    fn try_into(self) -> Result<semver::Prerelease, Self::Error> {
        semver::Prerelease::new(self.identifier.unwrap_or_default())
    }
}

#[cfg(feature = "semver")]
impl std::convert::TryInto<semver::BuildMetadata> for Build<'_> {
    type Error = semver::Error;

    fn try_into(self) -> Result<semver::BuildMetadata, Self::Error> {
        semver::BuildMetadata::new(self.identifier.unwrap_or_default())
    }
}

#[cfg(feature = "semver011")]
impl Into<Vec<semver011::Identifier>> for Additional {
    fn into(self) -> Vec<semver011::Identifier> {
        self.numbers
            .into_iter()
            .map(semver011::Identifier::Numeric)
            .collect()
    }
}

#[cfg(feature = "semver011")]
impl Into<Vec<semver011::Identifier>> for PreRelease<'_> {
    fn into(self) -> Vec<semver011::Identifier> {
        self.identifier
            .into_iter()
            .flat_map(|s| s.split(['-', '.'].as_ref()))
            .map(parse_11)
            .collect()
    }
}

#[cfg(feature = "semver011")]
impl Into<Vec<semver011::Identifier>> for Build<'_> {
    fn into(self) -> Vec<semver011::Identifier> {
        self.identifier
            .into_iter()
            .flat_map(|s| s.split(['-', '.', '+'].as_ref()))
            .map(parse_11)
            .collect()
    }
}

#[cfg(feature = "semver010")]
impl Into<Vec<semver010::Identifier>> for Additional {
    fn into(self) -> Vec<semver010::Identifier> {
        self.numbers
            .into_iter()
            .map(semver010::Identifier::Numeric)
            .collect()
    }
}

#[cfg(feature = "semver010")]
impl Into<Vec<semver010::Identifier>> for PreRelease<'_> {
    fn into(self) -> Vec<semver010::Identifier> {
        self.identifier
            .into_iter()
            .flat_map(|s| s.split(['-', '.'].as_ref()))
            .map(parse_10)
            .collect()
    }
}

#[cfg(feature = "semver010")]
impl Into<Vec<semver010::Identifier>> for Build<'_> {
    fn into(self) -> Vec<semver010::Identifier> {
        self.identifier
            .into_iter()
            .flat_map(|s| s.split(['-', '.', '+'].as_ref()))
            .map(parse_10)
            .collect()
    }
}

#[cfg(feature = "semver011")]
fn parse_11(s: &str) -> semver011::Identifier {
    s.parse::<u64>().map_or_else(
        |_| semver011::Identifier::AlphaNumeric(String::from(s)),
        semver011::Identifier::Numeric,
    )
}

#[cfg(feature = "semver010")]
fn parse_10(s: &str) -> semver010::Identifier {
    s.parse::<u64>().map_or_else(
        |_| semver010::Identifier::AlphaNumeric(String::from(s)),
        semver010::Identifier::Numeric,
    )
}

#[cfg(test)]
mod tests {
    use super::{Additional, Build, PreRelease};
    use std::{cmp::Ordering, convert::TryInto};

    #[test]
    fn test_additional_eq_cmp() {
        let mut add = Additional::empty();

        add.push(42);
        add.push(1337);
        assert_eq!(&[42, 1337][..], &add.numbers);

        let add2 = Additional {
            numbers: vec![42, 1337],
        };

        assert_eq!(add, add2);
        assert_eq!(add.cmp(&add2), Ordering::Equal);

        add.set_to_zero();
        assert_eq!(&[0, 0][..], &add.numbers);

        assert_ne!(add, add2);
        assert_eq!(add.cmp(&add2), Ordering::Less);
        assert_eq!(Additional::empty().cmp(&add2), Ordering::Less);

        add.push(0);
        assert_eq!(add.cmp(&add2), Ordering::Less);

        let add3 = add2.clone_with_zeroes();
        assert_eq!(add, add3);
        assert_eq!(add.cmp(&add3), Ordering::Equal);
    }

    #[test]
    fn test_bump_additional() {
        let mut add = Additional::empty();

        add.bump(0);
        assert!(add.numbers.is_empty());

        add.push(1);
        add.push(2);
        add.push(3);

        assert_eq!(&[1, 2, 3][..], &add.numbers);

        add.bump(2);
        assert_eq!(&[1, 2, 4][..], &add.numbers);

        add.bump(1);
        assert_eq!(&[1, 3, 0][..], &add.numbers);

        add.bump(0);
        assert_eq!(&[2, 0, 0][..], &add.numbers);
    }

    #[test]
    fn test_pre_eq_cmp() {
        let mut pre1 = PreRelease::empty();
        let mut pre2 = PreRelease::empty();

        assert_eq!(pre1, pre2);
        assert_eq!(pre1.cmp(&pre2), Ordering::Equal);

        pre1.set("13.37");
        pre2.set("13-37");

        assert_eq!(pre1, pre2);
        assert_eq!(pre1.cmp(&pre2), Ordering::Equal);

        pre1.clear();

        assert_ne!(pre1, pre2);
        assert_eq!(pre1.cmp(&pre2), Ordering::Greater);

        pre1.set("4");
        assert_eq!(pre1.cmp(&pre2), Ordering::Less);

        pre1.set("42");
        assert_eq!(pre1.cmp(&pre2), Ordering::Greater);

        pre1.set("alpha");
        assert_eq!(pre1.cmp(&pre2), Ordering::Greater);

        pre2.set("alpha.beta");
        assert_eq!(pre1.cmp(&pre2), Ordering::Less);
    }

    #[cfg(feature = "semver")]
    #[cfg_attr(feature = "semver", test)]
    fn test_into_semver() {
        // let add = Additional {
        //     numbers: vec![42, 37],
        // };
        // let identifiers: Vec<semver::Identifier> = add.into();

        // assert_eq!(
        //     vec![
        //         semver::Identifier::Numeric(42),
        //         semver::Identifier::Numeric(37),
        //     ],
        //     identifiers
        // );

        let pre = PreRelease {
            identifier: Some("13.alpha-42beta"),
        };
        let identifiers: semver::Prerelease = pre.try_into().unwrap();

        assert_eq!(
            semver::Prerelease::new("13.alpha-42beta").unwrap(),
            identifiers
        );

        let build = Build {
            identifier: Some("13.alpha-42beta+37"),
        };
        let identifiers: semver::BuildMetadata = build.try_into().unwrap();

        assert_eq!(
            semver::BuildMetadata::new("13.alpha-42beta+37").unwrap(),
            identifiers
        );
    }

    #[cfg(feature = "semver011")]
    #[cfg_attr(feature = "semver011", test)]
    fn test_into_semver011() {
        let add = Additional {
            numbers: vec![42, 37],
        };
        let identifiers: Vec<semver011::Identifier> = add.into();

        assert_eq!(
            vec![
                semver011::Identifier::Numeric(42),
                semver011::Identifier::Numeric(37),
            ],
            identifiers
        );

        let pre = PreRelease {
            identifier: Some("13.alpha-42beta"),
        };
        let identifiers: Vec<semver011::Identifier> = pre.into();

        assert_eq!(
            vec![
                semver011::Identifier::Numeric(13),
                semver011::Identifier::AlphaNumeric(String::from("alpha")),
                semver011::Identifier::AlphaNumeric(String::from("42beta")),
            ],
            identifiers
        );

        let build = Build {
            identifier: Some("13.alpha-42beta+37"),
        };
        let identifiers: Vec<semver011::Identifier> = build.into();

        assert_eq!(
            vec![
                semver011::Identifier::Numeric(13),
                semver011::Identifier::AlphaNumeric(String::from("alpha")),
                semver011::Identifier::AlphaNumeric(String::from("42beta")),
                semver011::Identifier::Numeric(37),
            ],
            identifiers
        );
    }

    #[cfg(feature = "semver010")]
    #[cfg_attr(feature = "semver010", test)]
    fn test_into_semver010() {
        let add = Additional {
            numbers: vec![42, 37],
        };
        let identifiers: Vec<semver010::Identifier> = add.into();

        assert_eq!(
            vec![
                semver010::Identifier::Numeric(42),
                semver010::Identifier::Numeric(37),
            ],
            identifiers
        );

        let pre = PreRelease {
            identifier: Some("13.alpha-42beta"),
        };
        let identifiers: Vec<semver010::Identifier> = pre.into();

        assert_eq!(
            vec![
                semver010::Identifier::Numeric(13),
                semver010::Identifier::AlphaNumeric(String::from("alpha")),
                semver010::Identifier::AlphaNumeric(String::from("42beta")),
            ],
            identifiers
        );

        let build = Build {
            identifier: Some("13.alpha-42beta+37"),
        };
        let identifiers: Vec<semver010::Identifier> = build.into();

        assert_eq!(
            vec![
                semver010::Identifier::Numeric(13),
                semver010::Identifier::AlphaNumeric(String::from("alpha")),
                semver010::Identifier::AlphaNumeric(String::from("42beta")),
                semver010::Identifier::Numeric(37),
            ],
            identifiers
        );
    }
}
