extern crate rustc_version;

use rustc_version::{version_meta, Version};

fn main() {
    let version = version_meta().unwrap();

    if version.semver >= Version::new(1, 10, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_10_0\""); // extended_compare_and_swap
    }

    if version.semver >= Version::new(1, 15, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_15_0\""); // atomic_access
    }

    if version.semver >= Version::new(1, 27, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_27_0\""); // atomic_nand
    }

    if version.semver >= Version::new(1, 34, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_34_0\""); // integer_atomics
    }

    if version.semver >= Version::new(1, 45, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_45_0\""); // update, min, max
    }

    if version.semver >= Version::new(1, 50, 0) {
        println!("cargo:rustc-cfg=feature=\"since_1_50_0\""); // extended_compare_and_swap deprecated
    }
}
