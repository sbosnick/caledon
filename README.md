# Caledon

**Caledon is a Rust implementation of the Wayland protocol.**

[![CI](https://github.com/sbosnick/caledon/workflows/CI/badge.svg)](https://github.com/sbosnick/caledon/actions?query=workflow%3ACI)
---

Caledon implements the [Wayland] display server protocol directly in Rust without any
dependancies on C code. It provides an implementation of the [Wayland] wire protocol
and abstractions to expose the various [Wayland] protocol messages as types.

Caledon will (eventually) also proivde abstractions for building [Wayland] clients
and servers.

[Wayland]: https://wayland.freedesktop.org/

## License

Caledon is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE-2.0](LICENSE-APACHE-2.0) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.

## Contribution

If you would like to contribute to this project I ask that you start by filing
an issue. Currently the project is not well set up to co-ordinate contribution
from multiple people (it is a personal proof-of-concept right now). I am
interested in contribution from other people. If others are interested in
contributing I would make it a priority to transition the project to a state
where it can co-ordinate multiple contributors.

Please note that this project is released with a [Contributor Code of
Conduct][code-of-conduct].  By participating in this project you agree to abide
by its terms.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Calandon by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[code-of-conduct]: CODE_OF_CONDUCT.md
