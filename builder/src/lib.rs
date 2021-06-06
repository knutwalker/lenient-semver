//! Lenient parser for Semantic Version numbers.
#![deny(
    bad_style,
    const_err,
    dead_code,
    improper_ctypes,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    no_mangle_generic_items,
    non_shorthand_field_patterns,
    overflowing_literals,
    path_statements,
    patterns_in_fns_without_body,
    private_in_public,
    rust_2018_idioms,
    trivial_casts,
    trivial_numeric_casts,
    unconditional_recursion,
    unsafe_code,
    unused_allocation,
    unused_comparisons,
    unused_extern_crates,
    unused_import_braces,
    unused_parens,
    unused_qualifications,
    unused_results,
    unused,
    while_true
)]

/// Trait to abstract over version building.
///
/// The methods to implement in this trait represent the components of [`semver::Version`],
/// but allow for parsing into a custom type.
///
/// The trait is generic over the lifetime of the input string, so that one could
/// parse into a version without having to allocate.
///
/// Most methods have a default implementation that does nothing and ignores the input.
/// This can be used to implement some form of validation without needing to keep the result.
pub trait VersionBuilder<'input> {
    /// The return type of the final version.
    type Out;

    /// Construct a new version builder.
    ///
    /// The function must not fail and the version (if returned from [`VersionBuilder::build`] at this point)
    /// should represent something akin to "0.0.0"
    fn new() -> Self;

    /// Set the major version component.
    ///
    /// This method is the only required component and will be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_major(&mut self, major: u64) {}

    /// Set the minor version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_minor(&mut self, minor: u64) {}

    /// Set the patch version component.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn set_patch(&mut self, patch: u64) {}

    /// Add additional numeric components following patch and preceding pre-release.
    ///
    /// For a version like `1.2.3.4.5`, this would call add_additional with `4` and `5`.
    ///
    /// For strict semver versions, those values are invalid.
    /// For lenient semver, those values are better represented as build than pre-release,
    /// although they might be "in the same block" as pre-release.
    /// In terms of comparing versions, the values added here should still have an impact.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    #[allow(unused)]
    fn add_additional(&mut self, num: u64) {}

    /// The pre-release metadata.
    ///
    /// The string might represent any alpha-numeric identifier,
    /// including numbers with or without leading zeroes.
    /// It is up to the implementor to parse those into more specific
    /// identifiers, if required.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times,
    /// although the default implementation produces only one identifier.
    #[allow(unused)]
    fn add_pre_release(&mut self, pre_release: &'input str) {}

    /// The build identifier.
    ///
    /// The string might represent any alpha-numeric identifier,
    /// including numbers with or without leading zeroes.
    /// It is up to the implementor to parse those into more specific
    /// identifiers, if required.
    ///
    /// This component is optional and might not be called
    /// before [`VersionBuilder::build`].
    ///
    /// This method might be called multiple times,
    /// although the default implementation produces only one identifier.
    #[allow(unused)]
    fn add_build(&mut self, build: &'input str) {}

    /// Construct the final version.
    fn build(self) -> Self::Out;
}

#[cfg(feature = "semver")]
impl<'input> VersionBuilder<'input> for semver::Version {
    type Out = Self;

    fn new() -> Self {
        semver::Version::new(0, 0, 0)
    }

    fn set_major(&mut self, major: u64) {
        self.major = major;
    }

    fn set_minor(&mut self, minor: u64) {
        self.minor = minor;
    }

    fn set_patch(&mut self, patch: u64) {
        self.patch = patch;
    }

    fn add_additional(&mut self, num: u64) {
        if self.build.is_empty() {
            self.build = semver::BuildMetadata::new(&format!("{}", num)).unwrap();
        } else {
            let build = self.build.as_str();
            let build = format!("{}.{}", build, num);
            self.build = semver::BuildMetadata::new(&build).unwrap();
        }
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre = semver::Prerelease::new(&sanitize_pre_release(pre_release)).unwrap();
    }

    fn add_build(&mut self, build: &'input str) {
        let build = if self.build.is_empty() {
            semver::BuildMetadata::new(&sanitize_build(build))
        } else {
            let build = format!("{}.{}", self.build, build);
            semver::BuildMetadata::new(&sanitize_build(build))
        };
        self.build = build.unwrap();
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(any(test, feature = "semver011"))]
impl<'input> VersionBuilder<'input> for semver011::Version {
    type Out = Self;

    fn new() -> Self {
        semver011::Version::new(0, 0, 0)
    }

    fn set_major(&mut self, major: u64) {
        self.major = major;
    }

    fn set_minor(&mut self, minor: u64) {
        self.minor = minor;
    }

    fn set_patch(&mut self, patch: u64) {
        self.patch = patch;
    }

    fn add_additional(&mut self, num: u64) {
        self.build.push(semver011::Identifier::Numeric(num))
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.extend(split_pre_release_011(pre_release));
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.extend(split_build_011(build));
    }

    fn build(self) -> Self::Out {
        self
    }
}

#[cfg(feature = "semver010")]
impl<'input> VersionBuilder<'input> for semver010::Version {
    type Out = Self;

    fn new() -> Self {
        semver010::Version::new(0, 0, 0)
    }

    fn set_major(&mut self, major: u64) {
        self.major = major;
    }

    fn set_minor(&mut self, minor: u64) {
        self.minor = minor;
    }

    fn set_patch(&mut self, patch: u64) {
        self.patch = patch;
    }

    fn add_additional(&mut self, num: u64) {
        self.build.push(semver010::Identifier::Numeric(num))
    }

    fn add_pre_release(&mut self, pre_release: &'input str) {
        self.pre.extend(split_pre_release_010(pre_release));
    }

    fn add_build(&mut self, build: &'input str) {
        self.build.extend(split_build_010(build));
    }

    fn build(self) -> Self::Out {
        self
    }
}

/// Sanitizes an input to be a valid pre-release identifier for [`semver::Version`].
///
/// This includes:
///   - Replacing every non-supported character with `-`
///   - Removing trailing zeroes from all-numeric identifier segments
///   - Collapsing empty segments
#[cfg(feature = "semver")]
pub fn sanitize_pre_release<'s>(
    s: impl Into<std::borrow::Cow<'s, str>>,
) -> std::borrow::Cow<'s, str> {
    remove_empty_segments(remove_leading_zeroes(remove_illegal_characters(s)))
}

/// Sanitizes an input to be a valid build identifier for [`semver::Version`].
///
/// This includes:
///   - Replacing every non-supported character with `-`
///   - Collapsing empty segments
#[cfg(feature = "semver")]
pub fn sanitize_build<'s>(s: impl Into<std::borrow::Cow<'s, str>>) -> std::borrow::Cow<'s, str> {
    remove_empty_segments(remove_illegal_characters(s))
}

/// Splits a single input into valid pre-release identifiers for [`semver011::Version`].
#[cfg(feature = "semver011")]
#[inline]
pub fn split_pre_release_011(s: &str) -> impl Iterator<Item = semver011::Identifier> + '_ {
    s.split(['.', '-'].as_ref()).map(try_num_semver011)
}

/// Splits a single input into valid pre-release identifiers for [`semver010::Version`].
#[cfg(feature = "semver010")]
#[inline]
pub fn split_pre_release_010(s: &str) -> impl Iterator<Item = semver010::Identifier> + '_ {
    s.split(['.', '-'].as_ref()).map(try_num_semver010)
}

/// Splits a single input into valid build identifiers for [`semver011::Version`].
#[cfg(feature = "semver011")]
#[inline]
pub fn split_build_011(s: &str) -> impl Iterator<Item = semver011::Identifier> + '_ {
    s.split(['.', '-', '+'].as_ref()).map(try_num_semver011)
}

/// Splits a single input into valid build identifiers for [`semver010::Version`].
#[cfg(feature = "semver010")]
#[inline]
pub fn split_build_010(s: &str) -> impl Iterator<Item = semver010::Identifier> + '_ {
    s.split(['.', '-', '+'].as_ref()).map(try_num_semver010)
}

#[cfg(feature = "semver")]
fn remove_illegal_characters<'s>(
    s: impl Into<std::borrow::Cow<'s, str>>,
) -> std::borrow::Cow<'s, str> {
    fn illegal_char(c: char) -> bool {
        !matches!(c, 'A'..='Z' | 'a'..='z' | '0'..='9' | '-' | '.')
    }
    let s = s.into();
    if s.contains(illegal_char) {
        s.replace(illegal_char, "-").into()
    } else {
        s
    }
}

#[cfg(feature = "semver")]
fn remove_leading_zeroes<'s>(s: impl Into<std::borrow::Cow<'s, str>>) -> std::borrow::Cow<'s, str> {
    fn illegal_zero(s: &str) -> bool {
        s.len() > 1 && s.starts_with('0') && s.bytes().all(|b| b.is_ascii_digit())
    }
    let mut s = s.into();
    if s.split('.').any(illegal_zero) {
        let st: &mut String = s.to_mut();
        let mut start = 0;
        while start < st.len() {
            let mut end = match st[start..].find('.') {
                Some(end) => end + start,
                None => st.len(),
            };

            if illegal_zero(&st[start..end]) {
                match st[start..end].find(|c| c > '0') {
                    Some(leading_zeroes) => {
                        let _ = st.drain(start..start + leading_zeroes);
                        end -= leading_zeroes;
                    }
                    None => {
                        st.replace_range(start..end, "0");
                        end = start + 1;
                    }
                }
            }
            start = end + 1;
        }
    }

    s
}

#[cfg(feature = "semver")]
fn remove_empty_segments<'s>(s: impl Into<std::borrow::Cow<'s, str>>) -> std::borrow::Cow<'s, str> {
    let mut s = s.into();

    if !s.is_empty() && s.split('.').any(str::is_empty) {
        let start = match s.find(|c| c != '.') {
            Some(start) => start,
            None => {
                s.to_mut().clear();
                return s;
            }
        };
        let mut end = match s.rfind(|c| c != '.') {
            Some(end) => end + 1,
            None => {
                s.to_mut().clear();
                return s;
            }
        };

        let st: &mut String = s.to_mut();
        if start > 0 {
            let _ = st.drain(..start);
            end -= start;
        }
        if end < st.len() {
            let _ = st.drain(end..);
        }

        let mut pos = 0;
        while pos < st.len() {
            let next = match st[pos..].find('.') {
                Some(next) => next + pos,
                None => st.len(),
            };

            if next == pos {
                let _ = st.remove(pos);
            } else {
                pos = next + 1;
            }
        }
    }

    s
}

#[cfg(any(test, feature = "semver011"))]
fn try_num_semver011(s: &str) -> semver011::Identifier {
    try_num(s).map_err(String::from).map_or_else(
        semver011::Identifier::AlphaNumeric,
        semver011::Identifier::Numeric,
    )
}

#[cfg(feature = "semver010")]
fn try_num_semver010(s: &str) -> semver010::Identifier {
    try_num(s).map_err(String::from).map_or_else(
        semver010::Identifier::AlphaNumeric,
        semver010::Identifier::Numeric,
    )
}

#[cfg(any(test, feature = "semver011", feature = "semver010"))]
fn try_num(s: &str) -> Result<u64, &str> {
    match s.parse::<u64>() {
        Ok(num) if !s.starts_with('0') || s == "0" => Ok(num),
        _ => Err(s),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sanitize_pre_release() {
        assert_eq!(
            "a-b.0.1010.-001",
            &sanitize_pre_release("a+b.000..01010...?001..")
        );
    }

    #[test]
    fn test_sanitize_build() {
        assert_eq!(
            "a-b.000.01010.-001",
            &sanitize_build("a+b.000..01010...?001..")
        );
    }

    #[test]
    fn test_remove_illegal_characters() {
        assert_eq!("a-b", &remove_illegal_characters("a+b"));
        assert_eq!("a-b", &remove_illegal_characters("a?b"));
        assert_eq!("a-b", &remove_illegal_characters("a*b"));
        assert_eq!("a-b", &remove_illegal_characters("a!b"));
        assert_eq!("a-b", &remove_illegal_characters("a🙈b"));
    }

    #[test]
    fn test_remove_leading_zeroes() {
        assert_eq!("0", &remove_leading_zeroes("0"));
        assert_eq!("0", &remove_leading_zeroes("000000000"));
        assert_eq!("1", &remove_leading_zeroes("1"));
        assert_eq!("1", &remove_leading_zeroes("01"));
        assert_eq!("1", &remove_leading_zeroes("0001"));
        assert_eq!("101", &remove_leading_zeroes("101"));
        assert_eq!("101", &remove_leading_zeroes("0101"));
        assert_eq!("101", &remove_leading_zeroes("000101"));
        assert_eq!("0a", &remove_leading_zeroes("0a"));
        assert_eq!("00a", &remove_leading_zeroes("00a"));
        assert_eq!("0.0.0", &remove_leading_zeroes("0.0.0"));
        assert_eq!("0.0.0", &remove_leading_zeroes("0.0000.0"));
        assert_eq!("0.11.0", &remove_leading_zeroes("0.0011.0"));
        assert_eq!("0.11.101", &remove_leading_zeroes("0.0011.0101"));
    }

    #[test]
    fn test_remove_empty_segments() {
        assert_eq!("123", &remove_empty_segments("123"));
        assert_eq!("123", &remove_empty_segments(".123"));
        assert_eq!("123", &remove_empty_segments("..123"));
        assert_eq!("123", &remove_empty_segments("....123"));
        assert_eq!("abc.123", &remove_empty_segments("abc.123"));
        assert_eq!("abc.123", &remove_empty_segments("abc..123"));
        assert_eq!("abc.123", &remove_empty_segments("abc...123"));
        assert_eq!("abc.123", &remove_empty_segments("abc.....123"));
        assert_eq!("123", &remove_empty_segments("123."));
        assert_eq!("123", &remove_empty_segments("123.."));
        assert_eq!("123", &remove_empty_segments("123...."));
        assert_eq!("abc.123", &remove_empty_segments("abc.123."));
        assert_eq!("abc.123", &remove_empty_segments("abc.123.."));
        assert_eq!("abc.123", &remove_empty_segments("abc.123...."));
        assert_eq!("", &remove_empty_segments("."));
        assert_eq!("", &remove_empty_segments(".."));
        assert_eq!("", &remove_empty_segments("...."));
    }
}
