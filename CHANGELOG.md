# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- Linux native Python wheels are now built with a `manylinux_2_35` baseline for `binar`, `paulimer`, and `deq-runtime`, improving compatibility with glibc 2.35 systems. This is achieved by building on glibc-2.35 agents (Ubuntu 22.04 on both x86_64 and aarch64) rather than adding a build-time toolchain dependency.

## [0.1.0] - 2026-01-23

### Added
- Initial (beta) release of binar, paulimer and pauliverse crates and python bindings.

[0.1.0]: https://github.com/microsoft/qdk-ec/releases/tag/v0.1.0
