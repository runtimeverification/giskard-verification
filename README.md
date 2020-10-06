# Giskard Verification

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/runtimeverification/giskard-verification/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/runtimeverification/giskard-verification/actions?query=workflow%3ACI

The Giskard consensus protocol is used to validate transactions and computations
in the PlatON network. This project provides a model of Giskard in Coq, and formally
proves several key safety properties of the protocol.

## Meta

- License: [University of Illinois/NCSA Open Source License](LICENSE.md)
- Compatible Coq versions: 8.12
- Coq namespace: `Giskard`

## Building instructions

We recommend installing Coq 8.12 via [OPAM](http://opam.ocaml.org/doc/Install.html):
```shell
opam install coq.8.12.0
```
When Coq is installed, use the following commands to obtain and build the project:
```shell
git clone https://github.com/runtimeverification/giskard-verification.git
cd giskard-verification
make   # or make -j <number-of-cores-on-your-machine>
```
This will build all model definitions and check all the proofs.

## Protocol

An overview of the Giskard protocol is provided as part of the
[PlatON Consensus Solution documentation](https://devdocs.platon.network/docs/en/PlatON_Solution/).
The Coq formalization is based on a more abstract [specification](https://arxiv.org/abs/2010.02124)
of the protocol.

## Coq model and proofs

The Coq protocol model aims to capture safety properties of Giskard, and thus omits
many implementation-level details such as on verifiable random functions.
For details on the model and the safety proofs, see the report:

<img src="resources/pdf-icon.png" alt="PDF" width="20" /> *[Verifying Safety of the Giskard Consensus Protocol in Coq](https://github.com/runtimeverification/giskard-verification/blob/master/report/report.pdf)*

## File organization

All Coq code is in the `theories` directory and is organized as follows:

- `lib.v`: supplementary general tactics and results
- `structures.v`: definitions of Giskard datatypes and axioms
- `local.v`: local state operations, properties, and transitions
- `global.v`: global state operations, transitions, and properties
- `prepare.v`: safety property one, prepare stage height injectivity
- `precommit.v`: safety property two, precommit stage height injectivity
- `commit.v`: safety property three, commit stage height injectivity

## Generating documentation

HTML documentation can be generated using `coqdoc` by running the following
command in the repository root:
```
make coqdoc
```
Then, a good entry point for your browser is `docs/coqdoc/toc.html`.
