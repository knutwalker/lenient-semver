//! These tests are replicated in the crate documentation as a doc test
//! Please try to keep them in sync

mod custom_test {
    use crate::VersionBuilder;

    /// Simpler version struct that lives only on the stack
    #[derive(Debug, Default)]
    struct MyVersion {
        numbers: [u64; 3],
        is_pre_release: bool,
    }

    /// The VersionBuilder trait is generic over the lifetime of the input string.
    /// We don't store references to those strings, so we don't care about the specific lifetime.
    impl VersionBuilder<'_> for MyVersion {
        /// We will modify the target struct directly
        type Out = Self;

        /// Construct a new builder instance.
        /// One can only expect `set_major` to be called before `build`, all other methods are optional.
        fn new() -> Self {
            Self::default()
        }

        /// Construct the final result. In this case, we can just return ourselves.
        fn build(self) -> Self::Out {
            self
        }

        /// Called when the major component was found.
        fn set_major(&mut self, major: u64) {
            self.numbers[0] = major;
        }

        /// Called when the minor component was found.
        fn set_minor(&mut self, minor: u64) {
            self.numbers[1] = minor;
        }

        /// Called when the patch component was found.
        fn set_patch(&mut self, patch: u64) {
            self.numbers[2] = patch;
        }

        /// Called when any pre-relase metadata identifier was found.
        /// This identifier can just numeric, no attempts at parsing it into a number have been made.
        /// For this implementation, we don't care about the value, just it's presence.
        fn add_pre_release(&mut self, _pre_release: &str) {
            self.is_pre_release = true
        }
    }

    #[test]
    fn test_custom_version_builder() {
        let input = "1.3.3.7-alpha21+build.42";

        let my_version = crate::parse_into::<MyVersion>(input).unwrap();

        assert_eq!([1, 3, 3], my_version.numbers);
        assert!(my_version.is_pre_release);
    }
}

mod builder_as_validation_test {

    //! This test is replicated in the crate documentation as a doc test
    //! Please try to keep them in sync

    use crate::VersionBuilder;

    /// newtype around bool, so we can implement the VersionBuilder trait for it
    #[derive(Debug, Default)]
    struct IsPreRelease(bool);

    impl VersionBuilder<'_> for IsPreRelease {
        /// Here we parse into a different value than Self
        type Out = bool;

        fn new() -> Self {
            Self::default()
        }

        /// Return the wrapped bool
        fn build(self) -> Self::Out {
            self.0
        }

        /// We only care about this method and can ignore all the other ones
        fn add_pre_release(&mut self, _pre_release: &str) {
            self.0 = true;
        }
    }

    /// This method also return false for invalid version strings,
    /// which is technically true, as those are not pre-release versions.
    /// Usually you would want to have a better error handling.
    fn is_pre_release(v: &str) -> bool {
        crate::parse_into::<IsPreRelease>(v).unwrap_or_default()
    }

    #[test]
    fn test_custom_version_validation() {
        assert!(is_pre_release("1.2.3-pre") == true);
        assert!(is_pre_release("1.2.3") == false);
        assert!(is_pre_release("1.2.3+build") == false);
    }
}

#[cfg(feature = "version_lite")]
mod version_test {

    use crate::{Version, VersionBuilder};

    #[test]
    fn test_version() {
        let input = "1.3.3.7-beta.21+build.42";
        // make an owned copy, so we don't cheat by using the 'static lifetime.
        let input = String::from(input);

        // This version references slices from the `input` String
        let version = crate::parse_into::<Version>(input.as_ref()).unwrap();

        // Which prevents us from dropping the input
        // drop(input);

        // We can disassociate the metadata, which allows the new version to reference something else
        let (mut version, pre, build) = version.disassociate_metadata();

        // We still get the referenced input slices, so we create owned copies
        let pre: Vec<String> = pre.into_iter().map(ToOwned::to_owned).collect();
        let build: Vec<String> = build.into_iter().map(ToOwned::to_owned).collect();

        // now we can safely drop the input
        drop(input);

        // We can also re-add the cloned identifiers.
        // The version would now be bound to the lifetime of this method.
        // Just for fun, we swap pre-release and build
        for pre in &pre {
            version.add_build(pre.as_ref());
        }
        for build in &build {
            version.add_pre_release(build.as_ref());
        }

        assert_eq!("1.3.3.7-build.42+beta.21".to_string(), version.to_string());
    }
}

#[cfg(all(feature = "version_lite", feature = "version_serde"))]
mod serde_test {

    use crate::{Version, VersionBuilder};
    use serde::Deserialize;
    #[derive(Debug, Deserialize)]
    struct DependencySpec<'input> {
        /// Refer to name as owned value
        name: String,
        /// Borrows from the input string
        #[serde(borrow)]
        version: Version<'input>,
    }

    #[test]
    fn test_serde_feature() {
        let input = "
            {
                \"name\": \"lenient_semver\",
                \"version\": \"1.3.3.7+build.42\"
            }";
        // make an owned copy, so we don't cheat by using the 'static lifetime.
        let input = String::from(input);

        // use serde as one would normally do
        let dep = serde_json::from_str::<DependencySpec>(input.as_ref()).unwrap();
        println!("{:?}", dep);

        // cannot move out of `input` because it is borrowed
        // drop(input);

        let mut expected = Version::new(1, 3, 3);
        expected.add_additional(7);
        expected.add_build("build");
        expected.add_build("42");

        assert_eq!(dep.version, expected);

        // now we can drop the input
        drop(input);
    }
}
