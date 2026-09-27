# Reading and checking the Lean proofs

Start with the [publication proof map](proof-map.md). It links a numbered
paper result to the original manuscript, a `Standalone` statement, and a
`Novel` proof. The [complete lab index](lab-results.md) also includes results
that were not selected for either edited paper.

## Build

Install Lean's `elan` toolchain manager, then:

```sh
cd lean
lake exe cache get
lake build
cd ..
python scripts/proof_map.py --check --lean
```

`lean-toolchain` pins Lean to `v4.35.0-rc2`. `lakefile.toml` pins Mathlib to
`6ebcdee77a1b7bf10f211d4c993d85fbb19644bc`, and `lake-manifest.json` pins
transitive dependencies. The first run downloads the toolchain and dependencies;
Mathlib's cache avoids rebuilding the entire library. No lab commands are used.

The Lake package retains its original internal name, `lab`, to preserve the
dependency manifest. It has no scheduler or background-agent functionality.

| Directory or target | Meaning |
|---|---|
| `Standalone/` | Result statements and definitions; inspect these hypotheses first |
| `Novel/` | Proofs, supporting lemmas, and assembly theorems |
| `Upstream/` | Explicit interfaces for cited stochastic-calculus and consistency inputs |
| `Audit.lean` | Checks that declarations use only Lean's standard allowed axioms |

`lake build` includes all four targets. `Audit` rejects project-level global
axioms and dependence on nonstandard axioms (including an unfinished proof).
The allowed set is `propext`, `Classical.choice`, and `Quot.sound`.
The map checker additionally elaborates all declaration names in the map.

## What a successful check establishes

A proof establishes its encoded proposition under the hypotheses in its type.
It does not establish that all those hypotheses have a nontrivial stochastic
model. A field in an `Upstream` structure is a supplied mathematical premise,
even though no global Lean `axiom` is declared.

Several interfaces have only degenerate or vacuous consistency instances, with
separate convention checks. Those instances do not construct a Brownian
probability space satisfying every hypothesis used by a publication theorem.
The archived [axiom ledger](archive/AXIOMS.md) records each interface and its
literature basis. References to historical local source-text paths in that
ledger describe the original review record; those third-party texts are not
bundled here.

The most consequential boundaries are:

- **Gaussian diffusion pricing:** `GaussLaw` and `ShapeGaussLaw` supply joint
  Gaussian integral laws, regularity and independence. A nonzero-diffusion
  instance is not constructed. Calendar/rank algebra is proved independently
  of those stochastic hypotheses.
- **Recurrent approximation:** the source bounds are formalized; sharper
  constants and pointwise bounds in the first paper are proved only in prose.
- **Correlated splice:** the formal theorem matches coefficients under the
  integrated drift condition, given an existing block. It does not construct
  all processes and their joint progressive measurability.
- **Three-exponent stochastic variance:** the construction derives its state
  and martingale conclusions using compatible calculus, SDE and exponential-
  martingale interfaces; a nontrivial instance of the full interface is not built.
- **Varying decays:** the splice reduction is proved. The classical exponent
  restrictions are an explicit cited input in `Upstream.ExpPolyConsistency`.
- **American exercise:** the source development proves the state-rule direction,
  residual independence and product representation. The general reverse
  stopping-time inequality is supplied in the edited paper, not in Lean.
- **Factor support:** SDE solutions, moments and integrand admissibility remain
  explicit hypotheses. A small support dimension does not show that a specific
  numerical loading matrix has independent columns.

Numerical fits, data extraction, plotting, calibration LPs and trade diagnostics
are Python calculations, not formal proofs. The repository does not claim a
fully verified implementation of a listed-American option pricer.

## Updating the map

After editing statement numbers or mapped declarations, update
`docs/proof-map.json`, compile the papers, and run `python scripts/proof_map.py`.
Commit the regenerated Markdown and JSON together. `--check` fails if any
numbered publication result is unmapped or a mapped declaration is missing.
