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
- **Recurrent approximation:** the exact publication constants, including the
  pointwise price bounds, are formalized in `ApproximationConstants`. Price
  estimates require the supplied calculus and a Brownian driver with no Lean
  witness constructed. These are suprema of expectations, not pathwise suprema.
- **Correlated splice:** `FrontEndConstruction` constructs the front-end
  processes for an existing block and deterministic initial values, under the
  supplied calculus. Observability is required for necessity. Coefficients are
  progressive for each fixed maturity and jointly Borel measurable; joint
  maturity-indexed progressivity is not proved. No true-martingale conclusion
  follows from the local bounds alone.
- **Three-exponent stochastic variance:** the construction derives its state
  and martingale conclusions using compatible calculus, SDE and exponential-
  martingale interfaces; a nontrivial instance of the full interface is not built.
- **Varying decays:** the splice reduction is proved. The classical exponent
  restrictions are an explicit cited input in `Upstream.ExpPolyConsistency`.
- **American exercise:** pure-jump aggregation already includes the full
  sectioning and equality proofs. `ContinuousAggregation` extends these to
  continuous pre-cutoff risk under `GaussLaw`, including zero total variance.
  Exercise uses the usual augmentation of the natural filtration of the
  integrated diffusion and revealed meeting surprises, a Borel state-payoff
  rule and an integrable state envelope. An arbitrary larger filtration is
  outside the claim. European aggregation is formalized for nonnegative Borel
  payoffs; the paper obtains signed integrable payoffs by decomposition.
- **Common maturity exceptional set:** `MaturityNull` assumes local maturity
  integrability and differentiates only at interior maturities T>t. It does
  not derive local integrability from the global joint-integrability assumption.
- **Two strikes with an initial curve:** `TwoStrikeInitialCurve` proves the
  rescaling and identification, including zero variance. Its stochastic parts
  depend on the same Gaussian-law interface as the pricing model.
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
