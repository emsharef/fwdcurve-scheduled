import Standalone.ZeroMeanReversionVarianceSupport
import Standalone.StochasticMeetingVariance
import Standalone.ZeroMeanReversionUpstreamBridge
import Mathlib.Probability.Distributions.Gamma

/-! # Claim 023: exact support with nonnegative mean reversion and piecewise-constant volatility
of volatility

Formalization of the revised claim, conditional on its SDE, moment and original
integral-domain hypotheses. The paired components are listed below. `riccatiStatement`: the single-piece backward Riccati flow (23.2), `Q_{θ,α}(λ; h)` and
`R_{θ,α}(λ; h)` with `κ = α²/(2θ)`, taken as functions of the actual time `u = t − h`, satisfies
`dq/du = θq + α²q²/2` and `dr/du = −θq` on the piece with `q = λ` and `r = 0` at its right end,
for `λ ≥ 0`, in the three cases `θ > 0`, `θ = 0` and `α = 0`, and the deterministic flow
`ℓ` of `dℓ/du = θ(1 − ℓ)` from `0` and from a starting value `v` has the displayed values, with
`ℓ_j(s,t) > 0` for `θ > 0`. `translatedConeStatement`: the support algebra of (23.6) and
(23.7): for a product law whose coordinates have supports `[ℓ_j, ∞)` on an active set `J` and
the points `{ℓ_j}` off it, and a nonnegative matrix `A`, the image under `x ↦ C + A x` has
support the closed translated cone `C + A ℓ + A_J [0, ∞)^J`, whose affine hull is the translate of
the range of `A_J`, of dimension at most `|J|`, precisely the vectors in the kernel of `A_J^T`
give the almost-sure affine equalities about the vertex, and the mass at the vertex is the
product over the active factors with nonzero columns of the coordinate masses at `ℓ_j`.
`chiSquareParameterStatement`: for `θ > 0`, `α > 0` and `h > 0`, the flow (23.2) is the
Laplace transform of the scaled noncentral chi-square law of AX-08a, `exp(−(π v + ρ)) =
(1 + 2aλ)^{−ν/2} exp(−aηvλ/(1 + 2aλ))` with `a = κ(1 − e^{−θh})/2`, `ν = 4θ/α²` and
`η = 4θe^{−θh}/(α²(1 − e^{−θh}))`, the identification in (b). `sourceColumnStatement`: the
deterministic half of (e): with the printed decays `(0.1, 0, 11.0)` and strictly positive last
pieces every factor is active on its last piece, and for a product law with every coordinate
supported on `[0, ∞)` the image support is `C + A[0, ∞)³` with affine hull `C + range A` of
dimension at most three, the form (23.7). `compositionStatement`: the composition of the flow
over pieces, the deterministic content of (a) and of the conditional mean in (d): the composed
`π_j(λ; s, t)` and `ρ_j(λ; s, t)` are nonnegative for `λ ≥ 0`, compose over concatenated pieces as
the transforms do, vanish at `λ = 0` with derivatives `e^{−θ(t−s)}` and `1 − e^{−θ(t−s)}` whatever
the `α_k`, so the exponent of (23.3) has derivative `1 + (v − 1)e^{−θ(t−s)}` at `λ = 0`, the
conditional mean `E[v_j(t) | F_s]` of (d). `atomStatement`: the transform at large `λ`, the
deterministic content of (b): on a piece without noise the exponent is `λ` times the
deterministic flow (the point law); for `θ = 0` the transform tends to `exp(−2v/(α²h))`, the atom
at zero of (23.4); for `θ > 0` it tends to `0`, no atom, whatever the starting value, also after
composition with any earlier pieces. `varianceStatement`: the conditional variance of (d) read
off the second derivative of the exponent at `λ = 0`: `2eκ(1 − e) v + κ(1 − e)²` for `θ > 0`,
positive for every starting value including zero, and `α²h v` for `θ = 0`, positive exactly when
the starting value is. `generatorStatement`: the generator identity behind (a), the
deterministic core of the Itô step: the backward exponential `exp(−(q(u) x + r(u)))` of one piece
is annihilated by `∂_u + θ(1 − x)∂_x + (α² x/2)∂_xx`, the generator of (23.1).
`extensionStatement`: the joint backward exponential of (23.3) over the factors agrees on
`(−∞, t]` with a globally `C²` function, the input of the Itô formula. `itoStatement`: the Itô
representation of (a) on one piece from the field AX-05, the joint backward exponential of the
variance states up to the horizon being its initial value plus the driver integrals of (U4)
integrands, the finite-variation term cancelling by the generator identity.
`localizationStatement`: along Claim 015's localizers the stopped joint backward exponential is
a martingale, the stopped-martingale premise `H023` of one piece. `conditionalTransformStatement`:
from `H023`, the conditional transform (23.3) on one piece, `E[exp(−Σ_j λ_j v_j(t)) | F_s] =
exp(−Σ_j (q_j(t − s) v_j(s) + r_j(t − s)))`, and the unconditional transform from the initial
value. `pieceCompositionStatement`: the composition over the pieces of `(s, t]` by the tower
property, giving (23.3) in full with the composed flows when the one-piece transform holds on
each piece. `itoIncrementStatement`: the Itô representation of the increment of a piece's joint
exponential over the piece `[a, b]`, for states driven by a piecewise coefficient, the first step
of the time shift of the one-piece result. `onePieceStatement`: the one-piece transform on the
piece `[a, b]` from the fields, by the localization of that increment and its bounded limit,
so that with `pieceCompositionStatement` (23.3) holds in full for the piecewise coefficient.
`independenceStatement`: a nonnegative random vector whose joint transform has the
composed-flow form of (23.3) has independent coordinates with the one-factor transforms, by
the Laplace uniqueness on the orthant. `atomMassStatement`: the transform of a nonnegative
random variable tends to its mass at zero, so with the composed-flow transform the law has no
atom at zero when the last piece is stochastic with `θ > 0`, and the atom `exp(−2x/(α²h))` on
one stochastic piece with `θ = 0`. `meanStatement`: an integrable nonnegative random variable
with the composed-flow transform has mean `1 + (x − 1)e^{−θ(t−s)}`, the conditional mean of (d)
at a deterministic start. `secondMomentStatement`: a square-integrable nonnegative random
variable with the one-piece transform has the variance of `varianceStatement`, by the
second-order slopes of the transform and of the exponential. `conditionalLawStatement`: the
conditional joint transform gives a measurable regular conditional probability kernel with
independent coordinates and the composed-flow coordinate transforms. `conditionalMeanStatement`
gives the actual conditional mean over every finite list of pieces, and
`conditionalVarianceStatement` gives the actual conditional variance on one piece, including zero noise and zero length.
`piecewiseVarianceStatement` and `conditionalPiecewiseVarianceStatement` extend the actual
variance to every finite list of pieces, with positivity exactly on the active set.
`piecewiseCovarianceStatement` and `conditionalPiecewiseCovarianceStatement` give the
covariance of every affine image, its kernel and its rank, unconditionally and under a
regular conditional law. `sourceCovarianceStatement` specializes the covariance kernel and
rank to the printed three-factor column with positive last pieces, giving rank equal to
`rank A` without asserting that rank is three. `coordinateLawStatement` identifies the composed
coordinate laws, their exact supports and lower-endpoint atoms. `piecewiseJointLawStatement`
and `conditionalPiecewiseLawStatement` identify the joint and regular conditional laws with
their products. `piecewiseImageLawStatement` and `sourcePiecewiseSupportStatement` give
the exact translated-cone support, affine hull, equalities and vertex mass, including the
printed three-factor specialization. `fieldsTransformStatement` and `fieldsLawStatement`
derive the composed transform and laws from the SDE fields over the listed pieces, with
locally bounded coefficients. `fieldsMeetingVarianceStatement` and its conditional version
identify the law and exact support of the actual conditional-variance vector under these
SDE hypotheses and Claim 013's explicit moment premises. `fieldsStateMeanStatement` derives
the state mean and its bound by one. `fieldsCoefficientStatement`, `fieldsIncrementStatement`
and `fieldsKernelIsometryStatement` then derive square integrability, conditional isometry
and cross-factor orthogonality for the actual two-driver increments with time-dependent
coefficients. `backwardWeightRegularityStatement` and `kernelIdentificationStatement` supply
the regularity of Claim 013's backward weight and identify its full-kernel integral.
`fieldsConditionalMeanStatement` permits any earlier conditioning time, and
`fieldsWeightedIntegralStatement` derives conditional first-moment integration.
`fieldsMomentAssemblyStatement` combines these with the increment results into `H0239`,
retaining only its centered meeting-jump representation as a moment premise.
`productTerminalStatement` and `fieldsCenteredStatement` now derive that representation
for the constructed jumps. `fieldsConstructedMomentsStatement` derives all of `H0239`, and
`fieldsConstructedVarianceStatement` and its conditional version give the actual variance
vector its law and exact support with no moment-identity premise.
`fieldsShortRateJumpStatement` now connects the constructed jumps to the actual short-rate
jumps. `fieldsSourceVarianceStatement` and its conditional version transfer their laws and
exact supports, and `fieldsSourceColumnStatement` gives the full translated cone and affine
hull for the printed three-factor speeds with positive last pieces.
`fieldsFiniteTransformStatement` and `fieldsFiniteLawStatement` assemble the transform and
product laws for the original almost-surely continuous state. The six
`fieldsFiniteSource*Statement` components assemble its actual meeting-variance law, support,
means, covariance and printed-column conclusions. Finite breakpoint data supply coefficient
regularity and the common partitions. The original noise and loading integrands belong to
(U4) by the revised Statement's explicit hypotheses; no conclusion about values of the
integral operator outside that domain is used. No stochastic solution is constructed, and
no rank-three assertion is made. Red's review of the revised prose is separate from the
paired Lean proof.
-/
open MeasureTheory Set Matrix
open Standalone.ZeroMeanReversionVarianceSupport (cone0154)

namespace Standalone.PositiveMeanReversionSupport

/-! ### The backward Riccati flow (23.2) -/

/-- `Q_{θ,α}(λ; h)`, the value at the left end of a piece of length `h` traversed backward from
the value `λ` at its right end: `λ e^{−θh}/[1 + λ κ (1 − e^{−θh})]` for `θ > 0` with
`κ = α²/(2θ)`, and `λ/(1 + α²hλ/2)` for `θ = 0`. -/
noncomputable def Qflow (θ α l h : ℝ) : ℝ :=
  if θ = 0 then l / (1 + α^2 * h * l / 2)
  else l * Real.exp (-θ * h) / (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))

/-- `R_{θ,α}(λ; h)`: `(2θ/α²) log[1 + λ κ (1 − e^{−θh})]` for `θ > 0` and `α > 0`,
`λ(1 − e^{−θh})` for `α = 0`, and `0` for `θ = 0`. -/
noncomputable def Rflow (θ α l h : ℝ) : ℝ :=
  if θ = 0 then 0
  else if α = 0 then l * (1 - Real.exp (-θ * h))
  else (2 * θ / α^2) * Real.log (1 + l * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)))

/-- The deterministic flow of `dℓ/du = θ(1 − ℓ)` over a length `h` from the value `v`. -/
noncomputable def lflow (θ v h : ℝ) : ℝ := 1 + (v - 1) * Real.exp (-θ * h)

/-- (23.2) as backward equations in the actual time: for `λ ≥ 0`, `θ ≥ 0` and `α ≥ 0`, the
functions `u ↦ Q_{θ,α}(λ; t − u)` and `u ↦ R_{θ,α}(λ; t − u)` satisfy `dq/du = θq + α²q²/2` and
`dr/du = −θq` at every `u ≤ t`, with `q(t) = λ` and `r(t) = 0`; and the flow `ℓ` from `v` at `s`
satisfies `dℓ/du = θ(1 − ℓ)`, equals `v` at `s`, and from `v = 0` is positive after `s` when
`θ > 0`. -/
def riccatiStatement : Prop :=
  ∀ (θ α l t : ℝ), 0 ≤ θ → 0 ≤ α → 0 ≤ l →
    (∀ u, u ≤ t → HasDerivAt (fun u => Qflow θ α l (t - u))
      (θ * Qflow θ α l (t - u) + α^2 * (Qflow θ α l (t - u))^2 / 2) u) ∧
    (∀ u, u ≤ t → HasDerivAt (fun u => Rflow θ α l (t - u)) (-(θ * Qflow θ α l (t - u))) u) ∧
    Qflow θ α l 0 = l ∧ Rflow θ α l 0 = 0 ∧
    (∀ v s : ℝ, (∀ u, HasDerivAt (fun u => lflow θ v (u - s)) (θ * (1 - lflow θ v (u - s))) u) ∧
      lflow θ v 0 = v) ∧
    (0 < θ → ∀ h, 0 < h → 0 < lflow θ 0 h)

/-! ### The translated cone (23.6) -/

/-- The columns of `A` on the active set `J`, zero elsewhere. -/
def activeCols {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (J : Finset (Fin d)) :
    Matrix (Fin m) (Fin d) ℝ :=
  fun i j => if j ∈ J then A i j else 0

/-- (23.6)–(23.7), the support algebra: for a product law with coordinate supports `[ℓ_j, ∞)`
on `J` and `{ℓ_j}` off `J`, the image under `x ↦ C + A x` has support the closed translated cone
`C + A ℓ + A_J [0, ∞)^J`, affine hull the translate of `range A_J` of dimension at most `|J|`,
affine equalities exactly `ker A_J^T`, and vertex mass the product of the active nonzero-column
coordinate masses at `ℓ_j`. -/
def translatedConeStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ) (ℓ : Fin d → ℝ)
    (J : Finset (Fin d)),
    (∀ i j, 0 ≤ A i j) →
    ∀ (μ : Fin d → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j ∈ J, (μ j).support = Ici (ℓ j)) → (∀ j ∉ J, (μ j).support = {ℓ j}) →
      let B := activeCols A J
      let b' := C + A.mulVec ℓ
      ((Measure.pi μ).map (fun x => C + A.mulVec x)).support = cone0154 B b' ∧
      IsClosed (cone0154 B b') ∧
      (affineSpan ℝ (cone0154 B b') : Set (Fin m → ℝ)) =
        (fun y => b' + y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
      B.rank ≤ J.card ∧
      (∀ w, (∀ᵐ y ∂(Measure.pi μ).map (fun x => C + A.mulVec x), dotProduct w (y - b') = 0) ↔
        B.transpose.mulVec w = 0) ∧
      ((Measure.pi μ).map (fun x => C + A.mulVec x)) {b'} =
        ∏ j, if (∃ i, B i j ≠ 0) then μ j {ℓ j} else 1

/-! ### The noncentral chi-square parametrization of the flow (23.2) -/

/-- The scale `a`, the degrees of freedom `ν` and the noncentrality rate `η` of AX-08a for a
piece of length `h`. -/
noncomputable def chiScale (θ α h : ℝ) : ℝ := (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) / 2
noncomputable def chiDof (θ α : ℝ) : ℝ := 4 * θ / α^2
noncomputable def chiRate (θ α h : ℝ) : ℝ :=
  4 * θ * Real.exp (-θ * h) / (α^2 * (1 - Real.exp (-θ * h)))

/-- (b), the identification of the flow with the noncentral chi-square transform: for `θ > 0`,
`α > 0`, `h > 0` and `λ ≥ 0`, `ρ = (ν/2) log(1 + 2aλ)`, `π = aηλ/(1 + 2aλ)`, so that
`exp(−(π v + ρ)) = (1 + 2aλ)^{−ν/2} exp(−aηvλ/(1 + 2aλ))`, the Laplace transform of
`a · χ²_ν(η v)` at `λ`. -/
def chiSquareParameterStatement : Prop :=
  ∀ θ α h l v : ℝ, 0 < θ → 0 < α → 0 < h → 0 ≤ l →
    0 < chiScale θ α h ∧ 0 < chiDof θ α ∧ 0 < chiRate θ α h ∧
    chiScale θ α h * chiRate θ α h = Real.exp (-θ * h) ∧
    Rflow θ α l h = (chiDof θ α / 2) * Real.log (1 + 2 * chiScale θ α h * l) ∧
    Qflow θ α l h = chiScale θ α h * chiRate θ α h * l / (1 + 2 * chiScale θ α h * l) ∧
    Real.exp (-(Qflow θ α l h * v + Rflow θ α l h)) =
      (1 + 2 * chiScale θ α h * l) ^ (-(chiDof θ α / 2)) *
        Real.exp (-(chiScale θ α h * chiRate θ α h * v * l / (1 + 2 * chiScale θ α h * l)))

/-! ### The deterministic half of (e) -/

/-- The printed decays of the time-dependent column. -/
noncomputable def θ0235 : Fin 3 → ℝ := ![1/10, 0, 11]

/-- The factors whose last piece before `t` carries a positive volatility of volatility. -/
noncomputable def activeLast (αLast : Fin 3 → ℝ) : Finset (Fin 3) :=
  Finset.univ.filter fun j => 0 < αLast j

/-- (e), deterministic half: with strictly positive last pieces every factor is in `J_+`, the
decays are `(0.1, 0, 11.0)` with the second zero and the others positive, and for a product law
with every coordinate supported on `[0, ∞)` the image support is `C + A[0, ∞)³` with affine hull
`C + range A`, of dimension at most three. -/
def sourceColumnStatement : Prop :=
  (∀ αLast : Fin 3 → ℝ, (∀ j, 0 < αLast j) → activeLast αLast = Finset.univ) ∧
  (0 < θ0235 0 ∧ θ0235 1 = 0 ∧ 0 < θ0235 2) ∧
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 3) ℝ) (C : Fin m → ℝ), (∀ i j, 0 ≤ A i j) →
    ∀ (μ : Fin 3 → Measure ℝ), (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j, (μ j).support = Set.Ici 0) →
      ((Measure.pi μ).map (fun x => C + A.mulVec x)).support = cone0154 A C ∧
      IsClosed (cone0154 A C) ∧
      (affineSpan ℝ (cone0154 A C) : Set (Fin m → ℝ)) =
        (fun y => C + y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
      A.rank ≤ 3

/-! ### The composition of the flow over pieces and the conditional mean -/

/-- The composed backward flow over the pieces `(α_K, h_K), …, (α_1, h_1)`, listed from the right
end `t` of `(s, t]`: `q_K = λ`, `q_{k−1} = Q_{θ,α_k}(q_k; h_k)`, and `π_j(λ; s, t) = q_0`. -/
noncomputable def piFlow (θ : ℝ) : List (ℝ × ℝ) → ℝ → ℝ
  | [], l => l
  | p :: ps, l => piFlow θ ps (Qflow θ p.1 l p.2)

/-- The accumulated `ρ_j(λ; s, t) = Σ_k R_{θ,α_k}(q_k; h_k)` over the same pieces. -/
noncomputable def rhoFlow (θ : ℝ) : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | p :: ps, l => Rflow θ p.1 l p.2 + rhoFlow θ ps (Qflow θ p.1 l p.2)

/-- The total length `t − s` of the pieces. -/
def totalLength (ps : List (ℝ × ℝ)) : ℝ := (ps.map Prod.snd).sum

/-- The composition of the flow over pieces, the deterministic content of (a) and of the
conditional mean in (d): for `θ ≥ 0` and pieces with `α_k ≥ 0`, `h_k ≥ 0`, the composed
`π_j(λ; s, t)` and `ρ_j(λ; s, t)` are nonnegative for `λ ≥ 0`; they compose over concatenated
pieces as the transforms do, `π(λ; s, t) = π(π(λ; r, t); s, r)` and
`ρ(λ; s, t) = ρ(λ; r, t) + ρ(π(λ; r, t); s, r)`; they vanish at `λ = 0`, where their derivatives
are `e^{−θ(t−s)}` and `1 − e^{−θ(t−s)}`, whatever the `α_k`; so the exponent
`π(λ) v + ρ(λ)` of (23.3) has derivative `1 + (v − 1)e^{−θ(t−s)}` at `λ = 0`, the conditional mean
`E[v_j(t) | F_s]` of (d) from the starting value `v = v_j(s)`, and the transform
`exp(−(π(λ) v + ρ(λ)))` has derivative minus that mean. -/
def compositionStatement : Prop :=
  ∀ (θ : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ θ → (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
    (∀ l, 0 ≤ l → 0 ≤ piFlow θ ps l ∧ 0 ≤ rhoFlow θ ps l) ∧
    (∀ (qs : List (ℝ × ℝ)) (l : ℝ), piFlow θ (qs ++ ps) l = piFlow θ ps (piFlow θ qs l) ∧
      rhoFlow θ (qs ++ ps) l = rhoFlow θ qs l + rhoFlow θ ps (piFlow θ qs l)) ∧
    piFlow θ ps 0 = 0 ∧ rhoFlow θ ps 0 = 0 ∧
    HasDerivAt (piFlow θ ps) (Real.exp (-θ * totalLength ps)) 0 ∧
    HasDerivAt (rhoFlow θ ps) (1 - Real.exp (-θ * totalLength ps)) 0 ∧
    ∀ v : ℝ,
      HasDerivAt (fun l => piFlow θ ps l * v + rhoFlow θ ps l) (lflow θ v (totalLength ps)) 0 ∧
      HasDerivAt (fun l => Real.exp (-(piFlow θ ps l * v + rhoFlow θ ps l)))
        (-(lflow θ v (totalLength ps))) 0

/-! ### The transform at large `λ`: the point law, the atom at zero, and its absence -/

/-- The deterministic content of (b) in the transform: on a piece without noise (`α = 0`) the
exponent `π(λ) v + ρ(λ)` is `λ ℓ_θ(v; h)`, the transform of the point law at the deterministic
flow; for `θ = 0` and `α > 0` the transform `exp(−(π(λ) v + ρ(λ)))` tends, as `λ → ∞`, to
`exp(−2v/(α²h))`, the atom at zero of (23.4) and Claim 015 (15.16); for `θ > 0` and `α > 0` it
tends to `0`, so there is no atom, whatever `v ≥ 0`, including `v = 0`; and the same holds for the
composed transform over any earlier pieces when the last piece (the first listed) has `θ > 0` and
`α > 0`. -/
def atomStatement : Prop :=
  ∀ (θ α h v : ℝ), 0 ≤ θ → 0 < h → 0 ≤ v →
    (∀ l, Qflow θ 0 l h * v + Rflow θ 0 l h = l * lflow θ v h) ∧
    (θ = 0 → 0 < α →
      Filter.Tendsto (fun l => Real.exp (-(Qflow 0 α l h * v + Rflow 0 α l h))) Filter.atTop
        (nhds (Real.exp (-(2 * v / (α^2 * h)))))) ∧
    (0 < θ → 0 < α →
      Filter.Tendsto (fun l => Real.exp (-(Qflow θ α l h * v + Rflow θ α l h))) Filter.atTop
        (nhds 0)) ∧
    (0 < θ → 0 < α → ∀ ps : List (ℝ × ℝ), (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      Filter.Tendsto
        (fun l => Real.exp (-(piFlow θ ((α, h) :: ps) l * v + rhoFlow θ ((α, h) :: ps) l)))
        Filter.atTop (nhds 0))

/-! ### The conditional variance from the second derivative of the exponent -/

/-- The deterministic content of the conditional variance in (d): the exponent
`π(λ) v + ρ(λ)` of the transform (23.3) on one piece has, in `λ`, the first derivatives
`e/(1 + λκ(1 − e))²` and `(1 − e)/(1 + λκ(1 − e))` (with `e = e^{−θh}`, `κ = α²/(2θ)`) for
`θ > 0`, and `1/(1 + cλ)²` and `0` (with `c = α²h/2`) for `θ = 0`; their derivatives at `λ = 0`
are `−2eκ(1 − e)`, `−κ(1 − e)²` and `−2c`, `0`; so minus the second derivative of the exponent at
`λ = 0`, the conditional variance `Var(v_j(t) | F_s)` from the starting value `v`, is
`2eκ(1 − e) v + κ(1 − e)²`, positive for every `v ≥ 0` including `v = 0` when `θ > 0` and `α > 0`,
and `α²h v`, positive exactly when `v > 0`, when `θ = 0`: with positive mean reversion the
coordinate is active whatever its state, with zero mean reversion only when its state is
positive. -/
def varianceStatement : Prop :=
  ∀ (θ α h v : ℝ), 0 < α → 0 < h → 0 ≤ v →
    (0 < θ →
      let e := Real.exp (-θ * h)
      let κ := α^2 / (2 * θ)
      (∀ l, 0 ≤ l →
        HasDerivAt (fun l => Qflow θ α l h) (e / (1 + l * κ * (1 - e))^2) l ∧
        HasDerivAt (fun l => Rflow θ α l h) ((1 - e) / (1 + l * κ * (1 - e))) l) ∧
      HasDerivAt (fun l => e / (1 + l * κ * (1 - e))^2) (-(2 * e * κ * (1 - e))) 0 ∧
      HasDerivAt (fun l => (1 - e) / (1 + l * κ * (1 - e))) (-(κ * (1 - e)^2)) 0 ∧
      0 < 2 * e * κ * (1 - e) * v + κ * (1 - e)^2) ∧
    (θ = 0 →
      let c := α^2 * h / 2
      (∀ l, 0 ≤ l → HasDerivAt (fun l => Qflow 0 α l h) (1 / (1 + c * l)^2) l) ∧
      (∀ l, Rflow 0 α l h = 0) ∧
      HasDerivAt (fun l => 1 / (1 + c * l)^2) (-(2 * c)) 0 ∧
      (0 < 2 * c * v ↔ 0 < v))

/-! ### The generator identity behind (a) -/

/-- The backward exponential of one piece, `f(u, x) = exp(−(q(u) x + r(u)))` with `q`, `r` the
flow (23.2) in the actual time `u ≤ t`. -/
noncomputable def backwardExp (θ α l t u x : ℝ) : ℝ :=
  Real.exp (-(Qflow θ α l (t - u) * x + Rflow θ α l (t - u)))

/-- The generator identity behind (a), the deterministic core of the Itô step: for `θ ≥ 0`,
`α ≥ 0`, `λ ≥ 0` and `u ≤ t`, the backward exponential `f(u, x) = exp(−(q(u) x + r(u)))` has the
time derivative `−(q'(u) x + r'(u)) f` with `q' = θq + α²q²/2`, `r' = −θq`, the state
derivatives `−q f` and `q² f`, and `∂_u f + θ(1 − x) ∂_x f + (α² x/2) ∂_xx f = 0`, the generator
of (23.1) applied to `f`, so that `f(u, v_j(u))` is a local martingale by the Itô formula, which
is (23.3) on one piece once the local martingale is shown to be a martingale, as in Claim 015. -/
def generatorStatement : Prop :=
  ∀ (θ α l t : ℝ), 0 ≤ θ → 0 ≤ α → 0 ≤ l → ∀ (u x : ℝ), u ≤ t →
    let q := Qflow θ α l (t - u)
    HasDerivAt (fun u => backwardExp θ α l t u x)
      (-((θ * q + α^2 * q^2 / 2) * x - θ * q) * backwardExp θ α l t u x) u ∧
    HasDerivAt (fun x => backwardExp θ α l t u x) (-q * backwardExp θ α l t u x) x ∧
    HasDerivAt (fun x => -q * backwardExp θ α l t u x) (q^2 * backwardExp θ α l t u x) x ∧
    -((θ * q + α^2 * q^2 / 2) * x - θ * q) * backwardExp θ α l t u x +
      θ * (1 - x) * (-q * backwardExp θ α l t u x) +
      α^2 * x / 2 * (q^2 * backwardExp θ α l t u x) = 0

/-! ### The globally `C²` extension of the joint backward exponential -/

/-- The saturation width: at most `1/(1 + α_j² l_j)` for a factor with `θ_j = 0` and at most
`(1/θ_j) log(1 + 1/(1 + 2 l_j κ_j))` for `θ_j > 0`, so that every denominator of the flow stays
positive on `[−δ, ∞)`. -/
noncomputable def δ0235 {d : ℕ} (θ α l : Fin d → ℝ) : ℝ :=
  1 / (1 + ∑ j, if θ j = 0 then 1 + (α j)^2 * l j
    else θ j / Real.log (1 + 1 / (1 + 2 * l j * ((α j)^2 / (2 * θ j)))))

/-- The flow (23.2) with the length `t − u` replaced by the saturating
`g0155 t δ u` of Claim 015's bridge, equal to `t − u` for `u ≤ t`. -/
noncomputable def QExt (θ α l t δ u : ℝ) : ℝ := Qflow θ α l (Standalone.ZeroMeanReversionUpstreamBridge.g0155 t δ u)
noncomputable def RExt (θ α l t δ u : ℝ) : ℝ := Rflow θ α l (Standalone.ZeroMeanReversionUpstreamBridge.g0155 t δ u)

/-- The joint backward exponential of (23.3) over the factors, extended past the horizon. -/
noncomputable def EExt023 {d : ℕ} (θ α l : Fin d → ℝ) (t δ : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  Real.exp (-(∑ j, (QExt (θ j) (α j) (l j) t δ p.1 * p.2 j + RExt (θ j) (α j) (l j) t δ p.1)))

/-- The joint backward exponential `exp(−Σ_j (q_j(u) x_j + r_j(u)))` of (23.3) on one piece
agrees on `(−∞, t]` with a globally `C²` function, the input of the Itô formula (AX-05) for the
Itô step of (a). -/
def extensionStatement : Prop :=
  ∀ (d : ℕ) (θ α l : Fin d → ℝ) (t : ℝ), (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) → (∀ j, 0 ≤ l j) →
    ∃ f : ℝ × (Fin d → ℝ) → ℝ, ContDiff ℝ 2 f ∧ ∀ u x, u ≤ t →
      f (u, x) = Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) (t - u) * x j +
        Rflow (θ j) (α j) (l j) (t - u))))

/-! ### The Itô representation of (a) on one piece -/

section ItoStep
open scoped NNReal
open Standalone.ZeroMeanReversionUpstreamBridge (ItoCalculus U4 U5 twoDriverIncrement LocallyIntegrableDrift driverForm
  dX Hdrv)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The joint backward exponential `exp(−Σ_j (q_j(u) x_j + r_j(u)))` of (23.3) on one piece. -/
noncomputable def E023 {d : ℕ} (θ α l : Fin d → ℝ) (t u : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) (t - u) * x j + Rflow (θ j) (α j) (l j) (t - u))))

/-- The drift `θ_j (1 − v_j)` of (23.1). -/
noncomputable def Kdrv {d : ℕ} (θ : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => θ i * (1 - X s ω i)

/-- The Itô-formula integrand of the extended joint exponential along the driver `k i`. -/
noncomputable def Gint023 {d : ℕ} (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (θ α l : Fin d → ℝ)
    (t : ℝ) (x0 : Fin d → NNReal) (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) :
    ℝ≥0 → Ω → ℝ :=
  fun s ω => dX (EExt023 θ α l t (δ0235 θ α l))
    ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hdrv k α X) (Kdrv θ X) s ω) i *
    Hdrv k α X i (k i) s ω

/-- The Itô representation of (a) on one piece from the field AX-05: for variance states
solving (23.1) with the drift `θ_j(1 − v_j)` and one driver per coordinate carrying the identity
covariation, the joint backward exponential up to the horizon `t` is its initial value plus the
driver integrals of `Gint023`, each a (U4) integrand; the finite-variation term cancels by the
generator identity. -/
def itoStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) →
    (X 0 =ᵐ[S.μ] fun _ => x0) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    ∀ (t : ℝ) (l : Fin d → ℝ), (∀ j, 0 ≤ l j) →
      (∀ i, U4 S.ℱ S.μ (Gint023 S k θ α l t x0 X i)) ∧
      ∀ᵐ ω ∂S.μ, ∀ u : ℝ≥0, (u : ℝ) ≤ t →
        E023 θ α l t u (fun i => (X u ω i : ℝ)) =
          E023 θ α l t 0 (fun i => (x0 i : ℝ)) + ∑ i, S.I (k i) (Gint023 S k θ α l t x0 X i) u ω

/-! ### The localization of (a) on one piece -/

open Standalone.ZeroMeanReversionVarianceSupport (filt0152)
open Standalone.ZeroMeanReversionUpstreamBridge (filtR stateR)

/-- The joint backward exponential along the states, in real time. -/
noncomputable def M023 {d : ℕ} {Ω : Type} (θ α l : Fin d → ℝ) (t : ℝ)
    (X : ℝ → Ω → Fin d → NNReal) (s : ℝ) (ω : Ω) : ℝ :=
  E023 θ α l t s (fun j => (X s ω j : ℝ))

/-- The stopped-martingale premise of (a) on one piece, the analogue of Claim 015's `H0152`:
localizers in `[0, t]`, eventually equal to `t`, along which the stopped joint backward
exponential is a martingale. -/
def H023 {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (F : MeasureTheory.Filtration ℝ mΩ) (θ α l : Fin d → ℝ)
    (t : NNReal) (X : ℝ → Ω → Fin d → NNReal) : Prop :=
  ∃ σ : ℕ → Ω → Set.Icc (0 : ℝ) t,
    (∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, σ n ω = ⟨t, t.coe_nonneg, le_rfl⟩) ∧
    ∀ n, MeasureTheory.Martingale
      (fun (s : Set.Icc (0 : ℝ) t) ω => M023 θ α l t X (min (s : ℝ) (σ n ω : ℝ)) ω)
      (filt0152 F t) μ

/-- `H023` for the variance states under the fields: with one driver per coordinate carrying
the identity covariation, continuous adapted paths, an initial value at most one, the drift
locally integrable and the noise coefficient a (U4) integrand, and the integral equation (23.1)
written with `I`, the stopped joint backward exponential along Claim 015's localizers is a
martingale, from the Itô representation and the fields AX-03c and AX-04b. -/
def localizationStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ α : Fin d → ℝ) (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => α j * Real.sqrt (X s ω j))) →
    (∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => α j * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    ∀ (t : NNReal) (l : Fin d → ℝ), (∀ j, 0 ≤ l j) →
      H023 S.μ (filtR S.ℱ) θ α l t (stateR X)

/-- (23.3) on one piece from the stopped-martingale premise: for a probability measure, a
filtration in which the states are adapted on `[0, t]`, and `H023`, the conditional transform
of `v(t)` given `F_s` is `exp(−Σ_j (q_j(t − s) v_j(s) + r_j(t − s)))` for every `s ∈ [0, t]`, and
the unconditional transform from the initial value `x` is
`exp(−Σ_j (q_j(t) x_j + r_j(t)))`: the stopped exponentials converge boundedly to the exponential
along the localizers, so it is a martingale on `[0, t]`, and its terminal value is
`exp(−Σ_j λ_j v_j(t))` since `q_j(0) = λ_j` and `r_j(0) = 0`. -/
def conditionalTransformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ (F : MeasureTheory.Filtration ℝ mΩ) (θ α l : Fin d → ℝ) (t : NNReal)
      (X : ℝ → Ω → Fin d → NNReal),
      (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ l j) →
      (∀ s ∈ Set.Icc (0 : ℝ) t, Measurable[F s] (X s)) → H023 μ F θ α l t X →
      (∀ s ∈ Set.Icc (0 : ℝ) t,
        μ[fun ω => Real.exp (-(∑ j, l j * X t ω j)) | F s] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) ((t : ℝ) - s) * X s ω j +
            Rflow (θ j) (α j) (l j) ((t : ℝ) - s))))) ∧
      ∀ x : Fin d → NNReal, (X 0 =ᵐ[μ] fun _ => x) →
        (∫ ω, Real.exp (-(∑ j, l j * X t ω j)) ∂μ) =
          Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) t * x j + Rflow (θ j) (α j) (l j) t)))

/-! ### The composition over pieces by the tower property -/

/-- The one-piece transform property on `[a, b]` with the constant volatility of volatility
`α`: (23.3) with the flow of that piece, for every `λ ≥ 0` and `s ∈ [a, b]`. -/
def OnePiece {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : MeasureTheory.Filtration ℝ mΩ) (θ α : Fin d → ℝ) (a b : ℝ)
    (X : ℝ → Ω → Fin d → NNReal) : Prop :=
  ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) → ∀ s ∈ Set.Icc a b,
    μ[fun ω => Real.exp (-(∑ j, l j * X b ω j)) | F s] =ᵐ[μ]
      fun ω => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) (b - s) * X s ω j +
        Rflow (θ j) (α j) (l j) (b - s))))

/-- The pieces of `(s, t]` listed from the right end `b`, each with its constant `α` and its
length, and the one-piece property on each of them. -/
def PiecesOK {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (F : MeasureTheory.Filtration ℝ mΩ) (θ : Fin d → ℝ) (X : ℝ → Ω → Fin d → NNReal) :
    ℝ → List ((Fin d → ℝ) × ℝ) → Prop
  | _, [] => True
  | b, p :: ps => OnePiece μ F θ p.1 (b - p.2) b X ∧ PiecesOK μ F θ X (b - p.2) ps

/-- The left end `s` of the pieces of `(s, t]`. -/
def leftEnd {d : ℕ} (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)) : ℝ := b - (ps.map Prod.snd).sum

/-- The composition of (23.3) over the pieces by the tower property: if the one-piece transform
holds on each piece of `(s, t]`, then the transform of `v(t)` given `F_s` is the exponential of
`Σ_j (π_j(λ_j; s, t) v_j(s) + ρ_j(λ_j; s, t))` with the composed flows of `compositionStatement`,
which is (23.3) in full for the piecewise-constant `α`. -/
def pieceCompositionStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ (F : MeasureTheory.Filtration ℝ mΩ) (θ : Fin d → ℝ) (X : ℝ → Ω → Fin d → NNReal),
      (∀ j, 0 ≤ θ j) → (∀ s, Measurable[F s] (X s)) →
      ∀ (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)), (∀ p ∈ ps, 0 ≤ p.2) →
        PiecesOK μ F θ X b ps →
        ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
          μ[fun ω => Real.exp (-(∑ j, l j * X b ω j)) | F (leftEnd b ps)] =ᵐ[μ]
            fun ω => Real.exp (-(∑ j,
              (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * X (leftEnd b ps) ω j +
                rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j))))

/-! ### The Itô representation of the increment over a piece, for a piecewise coefficient -/

/-- The noise integrand with a time-dependent volatility of volatility `α_j(s)`: `α_i(s) √X_i` on
the driver `k i`, zero on the others. -/
noncomputable def Hpw {d m : ℕ} (k : Fin d → Fin m) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) (k' : Fin m) : ℝ≥0 → Ω → ℝ :=
  if k' = k i then fun s ω => αf i s * Real.sqrt (X s ω i) else fun _ _ => 0

/-- The Itô-formula integrand of the piece's extended joint exponential along the driver `k i`,
for the states driven by the piecewise coefficient. -/
noncomputable def GintPw {d : ℕ} (S : ItoCalculus Ω) (k : Fin d → Fin S.m) (θ : Fin d → ℝ)
    (αf : Fin d → ℝ≥0 → ℝ) (α l : Fin d → ℝ) (b : ℝ) (x0 : Fin d → NNReal)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (i : Fin d) : ℝ≥0 → Ω → ℝ :=
  fun s ω => dX (EExt023 θ α l b (δ0235 θ α l))
    ((s : ℝ), driverForm S.I (fun j => (x0 j : ℝ)) (Hpw k αf X) (Kdrv θ X) s ω) i *
    Hpw k αf X i (k i) s ω

/-- The Itô representation of the increment over the piece `[a, b]`: for states solving (23.1)
with a measurable locally bounded piecewise coefficient `α_j(s)` equal to the constant `α_j` on `(a, b)`,
continuous paths, and the drift and noise data of `itoStatement`, the joint backward exponential
of the piece with horizon `b` satisfies, almost surely for every `u ∈ [a, b]`,
`E(u, v(u)) − E(a, v(a)) = Σ_j (∫_0^u G_j dU_j − ∫_0^a G_j dU_j)` with the (U4) integrands
`G_j`: the finite-variation term of the Itô formula is interval integrable (its continuous part
and its bounded measurable quadratic part) and vanishes on `(a, b)` by the generator identity. -/
def itoIncrementStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ j, Measurable (αf j)) → (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    ∀ (a b : ℝ≥0) (l : Fin d → ℝ), a ≤ b → (∀ j, 0 ≤ l j) →
      (∀ j (s : ℝ≥0), a < s → s < b → αf j s = α j) →
      (∀ i, U4 S.ℱ S.μ (GintPw S k θ αf α l b x0 X i)) ∧
      ∀ᵐ ω ∂S.μ, ∀ u : ℝ≥0, a ≤ u → u ≤ b →
        E023 θ α l b u (fun i => (X u ω i : ℝ)) - E023 θ α l b a (fun i => (X a ω i : ℝ)) =
          ∑ i, (S.I (k i) (GintPw S k θ αf α l b x0 X i) u ω -
            S.I (k i) (GintPw S k θ αf α l b x0 X i) a ω)

/-- The real-time filtration restricted to the piece `[a, b]`. -/
def filtI {Ω : Type} [mΩ : MeasurableSpace Ω] (F : MeasureTheory.Filtration ℝ mΩ) (a b : ℝ) :
    MeasureTheory.Filtration (Set.Icc a b) mΩ where
  seq s := F s.val
  mono' := fun _ _ h => F.mono h
  le' := fun s => F.le s.val

/-- The one-piece transform on `[a, b]` from the fields: under the hypotheses of the increment
representation, with adapted states and an initial value at most one, `OnePiece` holds on the
piece `[a, b]` of the piecewise coefficient: along Claim 015's localizers the stopped increment
of the piece's joint exponential is a martingale on `[a, b]` by AX-03c and AX-04b, its bounded
limit is a martingale, and its terminal value is `exp(−Σ_j λ_j v_j(b))`. With
`pieceCompositionStatement` this gives (23.3) in full from the fields. -/
def onePieceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ) (α : Fin d → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) → (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    ∀ (a b : ℝ≥0), a ≤ b → (∀ j (s : ℝ≥0), a < s → s < b → αf j s = α j) →
      OnePiece S.μ (filtR S.ℱ) θ α (a : ℝ) (b : ℝ) (stateR X)

/-- The independence of the coordinates in (a): a nonnegative random vector whose joint Laplace
transform has the composed-flow form `exp(−Σ_j (π_j(λ_j) x_j + ρ_j(λ_j)))` of (23.3), as `v(t)`
has under a deterministic start `x` by `pieceCompositionStatement`, has independent coordinates,
each with the transform `exp(−(π_j(λ) x_j + ρ_j(λ)))`: the joint transform factorizes into the
marginal ones since `π_j(0) = ρ_j(0) = 0`, and a law on the orthant is determined by its
Laplace transform. -/
def independenceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ (Y : Ω → Fin d → ℝ), Measurable Y → (∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j) →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Fin d → ℝ),
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
          Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x j + rhoFlow (θ j) (ps j) (l j))))) →
      ProbabilityTheory.iIndepFun (fun j ω => Y ω j) μ ∧
      ∀ (j : Fin d) (l : ℝ), 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω j)) ∂μ) =
        Real.exp (-(piFlow (θ j) (ps j) l * x j + rhoFlow (θ j) (ps j) l))

/-- The atom at zero from the transform, the stochastic half of the atom clauses of (b): for a
nonnegative random variable the Laplace transform tends, as `λ → ∞`, to the mass at zero; so
when the transform has the composed-flow form of (23.3) with a stochastic last piece and
`θ > 0` the law has no atom at zero, whatever the start, and with `θ = 0` on a single stochastic
piece from the start `x` the atom at zero has mass `exp(−2x/(α²h))`, (23.4)'s atom and Claim
015 (15.16). -/
def atomMassStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ Y : Ω → ℝ, Measurable Y → (∀ᵐ ω ∂μ, 0 ≤ Y ω) →
      Filter.Tendsto (fun l : ℝ => ∫ ω, Real.exp (-(l * Y ω)) ∂μ) Filter.atTop
        (nhds (μ.real {ω | Y ω = 0})) ∧
      ∀ (θ x : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ x → (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
        (∀ l : ℝ, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) =
          Real.exp (-(piFlow θ ps l * x + rhoFlow θ ps l))) →
        (∀ (α h : ℝ) (ps' : List (ℝ × ℝ)), 0 < θ → 0 < α → 0 < h → ps = (α, h) :: ps' →
          μ.real {ω | Y ω = 0} = 0) ∧
        (∀ α h : ℝ, θ = 0 → 0 < α → 0 < h → ps = [(α, h)] →
          μ.real {ω | Y ω = 0} = Real.exp (-(2 * x / (α^2 * h))))

/-- The mean from the transform, the stochastic half of the conditional mean in (d) at a
deterministic start: an integrable nonnegative random variable whose Laplace transform has the
composed-flow form of (23.3) from the start `x` has mean `ℓ_θ(x; t − s) = 1 + (x − 1)e^{−θ(t−s)}`,
whatever the pieces: the slope of the transform at zero tends to minus the mean by dominated
convergence, and the slope of the composed-flow exponential is the derivative of
`compositionStatement`. -/
def meanStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ Y : Ω → ℝ, Measurable Y → (∀ᵐ ω ∂μ, 0 ≤ Y ω) → MeasureTheory.Integrable Y μ →
    ∀ (θ x : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ θ → (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : ℝ, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) =
        Real.exp (-(piFlow θ ps l * x + rhoFlow θ ps l))) →
      (∫ ω, Y ω ∂μ) = lflow θ x (totalLength ps)

/-- The variance from the transform, the stochastic half of the conditional variance in (d) at
a deterministic start on one piece: a square-integrable nonnegative random variable whose
Laplace transform is the one-piece exponential `exp(−(q(λ) x + r(λ)))` of (23.3) has the
variance of `varianceStatement`, `2eκ(1 − e)x + κ(1 − e)²` for `θ > 0` and `α²h x` for `θ = 0`:
the second-order slope `(φ(λ) − 1 + λ m)/λ²` of the transform tends to half the second moment
by dominated convergence, and that of the exponential to half its second derivative by
L'Hôpital's rule. -/
def secondMomentStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    ∀ Y : Ω → ℝ, Measurable Y → (∀ᵐ ω ∂μ, 0 ≤ Y ω) → MeasureTheory.MemLp Y 2 μ →
    ∀ (θ α h x : ℝ), 0 ≤ θ → 0 < α → 0 < h → 0 ≤ x →
      (∀ l : ℝ, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) =
        Real.exp (-(Qflow θ α l h * x + Rflow θ α l h))) →
      (0 < θ → ProbabilityTheory.variance Y μ =
        2 * Real.exp (-θ * h) * (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h)) * x +
          (α^2 / (2 * θ)) * (1 - Real.exp (-θ * h))^2) ∧
      (θ = 0 → ProbabilityTheory.variance Y μ = α^2 * h * x)

open ProbabilityTheory in
/-- The regular conditional distribution in (a) and (d): the conditional joint transform
(23.3) determines a measurable probability kernel with independent coordinates. Each
coordinate has the composed-flow transform from the corresponding earlier state, outside
one null set for all nonnegative transform arguments. The named coordinate laws,
exact supports and conditional moment identities are not part of this statement. -/
def conditionalLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ),
      (∀ j, 0 ≤ θ j) → (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
            rhoFlow (θ j) (ps j) (l j))))) →
      ∃ κ : ProbabilityTheory.Kernel Ω (Fin d → ℝ≥0), ProbabilityTheory.IsMarkovKernel κ ∧
        (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
        (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
        (∀ ω, ProbabilityTheory.iIndepFun (fun j (y : Fin d → ℝ≥0) => y j) (κ ω)) ∧
        ∀ᵐ ω ∂μ, ∀ (j : Fin d) (l : ℝ), 0 ≤ l →
          (∫ y, Real.exp (-(l * y j)) ∂κ ω) =
            Real.exp (-(piFlow (θ j) (ps j) l * x ω j + rhoFlow (θ j) (ps j) l))

/-- The conditional mean in (d) for every finite list of pieces: the joint conditional
transform (23.3) and integrability give the conditional expectation of each terminal
coordinate as the deterministic mean-reversion flow of its earlier state. -/
def conditionalMeanStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    (∀ j, MeasureTheory.Integrable (fun ω => (Y ω j : ℝ)) μ) →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ),
      Measurable[G] x → (∀ j, 0 ≤ θ j) → (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
            rhoFlow (θ j) (ps j) (l j))))) →
      ∀ j, μ[fun ω => (Y ω j : ℝ) | G] =ᵐ[μ]
        fun ω => lflow (θ j) (x ω j) (totalLength (ps j))

/-- The conditional variance in (d) on one piece: square-integrable terminal
coordinates with (23.3) have the actual conditional variance given by the one-piece formula,
with the earlier state allowed to be random and zero. Noiseless coordinates and zero-length
pieces have zero variance. The variance over several pieces is not asserted here. -/
def conditionalVarianceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : MeasureTheory.Measure Ω), MeasureTheory.IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    (∀ j, MeasureTheory.MemLp (fun ω => (Y ω j : ℝ)) 2 μ) →
    ∀ (θ α : Fin d → ℝ) (h : ℝ) (x : Ω → Fin d → ℝ),
      Measurable[G] x → (∀ ω j, 0 ≤ x ω j) →
      (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ α j) → 0 ≤ h →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (Qflow (θ j) (α j) (l j) h * x ω j +
            Rflow (θ j) (α j) (l j) h)))) →
      ∀ j, ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ =ᵐ[μ]
        fun ω => if θ j = 0 then (α j)^2 * h * x ω j else
          2 * Real.exp (-θ j * h) * ((α j)^2 / (2 * θ j)) *
            (1 - Real.exp (-θ j * h)) * x ω j +
              ((α j)^2 / (2 * θ j)) * (1 - Real.exp (-θ j * h))^2

/-- The coefficient of the transform denominator on one piece. -/
noncomputable def varianceScale (θ α h : ℝ) : ℝ :=
  if θ = 0 then α^2 * h / 2 else α^2 / (2 * θ) * (1 - Real.exp (-θ * h))
/-- The one-piece conditional variance, including zero noise and zero length. -/
noncomputable def pieceVariance (θ α x h : ℝ) : ℝ :=
  2 * Real.exp (-θ * h) * varianceScale θ α h * x +
    (1 - Real.exp (-θ * h)) * varianceScale θ α h
/-- Variance across a finite list of pieces, with the latest piece first as in `piFlow`.
Earlier variance is multiplied by the squared mean-reversion factor; the last piece
adds its variance evaluated at the earlier mean. -/
noncomputable def varianceFlow (θ x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p :: ps => Real.exp (-θ * p.2)^2 * varianceFlow θ x ps +
      pieceVariance θ p.1 (lflow θ x (totalLength ps)) p.2

/-- The variance in (c) and (d) from the composed transform, with its exact positivity criterion. -/
def piecewiseVarianceStatement : Prop :=
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (Y : Ω → ℝ), Measurable Y → (∀ᵐ ω ∂μ, 0 ≤ Y ω) → MemLp Y 2 μ →
    ∀ (θ x : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ θ → 0 ≤ x →
      (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l, 0 ≤ l → (∫ ω, Real.exp (-(l * Y ω)) ∂μ) =
        Real.exp (-(piFlow θ ps l * x + rhoFlow θ ps l))) →
      ProbabilityTheory.variance Y μ = varianceFlow θ x ps ∧
      (0 < ProbabilityTheory.variance Y μ ↔
        (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x))

/-- Actual conditional variances for all the pieces of (23.3). Positive variance is equivalent
to membership in the state-dependent active set of (d). -/
def conditionalPiecewiseVarianceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    (∀ j, MemLp (fun ω => (Y ω j : ℝ)) 2 μ) →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ),
      Measurable[G] x → (∀ ω j, 0 ≤ x ω j) → (∀ j, 0 ≤ θ j) →
      (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
            rhoFlow (θ j) (ps j) (l j))))) →
      ∀ j, (ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ =ᵐ[μ]
        fun ω => varianceFlow (θ j) (x ω j) (ps j)) ∧
        ∀ᵐ ω ∂μ, (0 < ProbabilityTheory.condVar G (fun ω => (Y ω j : ℝ)) μ ω ↔
          (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x ω j))

/-- Covariance of an affine image under the joint transform, including its exact kernel
and rank. Independence and coordinate variances are consequences of the transform. -/
def piecewiseCovarianceStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ (Y : Ω → Fin d → ℝ), Measurable Y →
    (∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j) → (∀ j, MemLp (fun ω => Y ω j) 2 μ) →
    ∀ (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)), (∀ j, 0 ≤ θ j) →
      (∀ j, 0 ≤ x j) → (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
          Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x j + rhoFlow (θ j) (ps j) (l j))))) →
      ∀ (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ),
        let q := fun j => varianceFlow (θ j) (x j) (ps j)
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
        (∀ i k, ProbabilityTheory.covariance (fun ω => C i + A.mulVec (Y ω) i)
          (fun ω => C k + A.mulVec (Y ω) k) μ =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- The same covariance formula, kernel and rank under a regular conditional law given
`G`, outside one null set for all deterministic affine images. -/
def conditionalPiecewiseCovarianceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    (∀ j, MemLp (fun ω => (Y ω j : ℝ)) 2 μ) →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ),
      (∀ ω j, 0 ≤ x ω j) → (∀ j, 0 ≤ θ j) →
      (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
            rhoFlow (θ j) (ps j) (l j))))) →
    ∃ κ : ProbabilityTheory.Kernel Ω (Fin d → ℝ≥0), ProbabilityTheory.IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
      ∀ᵐ ω ∂μ, ∀ (m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ),
        let q := fun j => varianceFlow (θ j) (x ω j) (ps j)
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x ω j)
        (∀ i k, ProbabilityTheory.covariance
          (fun y : Fin d → ℝ≥0 => C i + A.mulVec (fun j => (y j : ℝ)) i)
          (fun y : Fin d → ℝ≥0 => C k + A.mulVec (fun j => (y j : ℝ)) k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

/-- The covariance-rank consequence of (e), for the printed mean-reversion speeds and
a stochastic last piece in every factor. Starting at one makes all three variances
strictly positive. This imposes no rank assertion on the unspecified loading matrix. -/
def sourceCovarianceStatement : Prop :=
  ∀ (m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (Y : Ω → Fin 3 → ℝ), Measurable Y → (∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j) →
    (∀ j, MemLp (fun ω => Y ω j) 2 μ) →
    ∀ (ps : Fin 3 → List (ℝ × ℝ)), (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ j, ∃ α h qs, ps j = (α, h) :: qs ∧ 0 < α ∧ 0 < h) →
      (∀ l : Fin 3 → ℝ, (∀ j, 0 ≤ l j) →
        (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
          Real.exp (-(∑ j, (piFlow (θ0235 j) (ps j) (l j) + rhoFlow (θ0235 j) (ps j) (l j))))) →
      ∀ (A : Matrix (Fin m) (Fin 3) ℝ) (C : Fin m → ℝ),
        let q := fun j => varianceFlow (θ0235 j) 1 (ps j)
        (∀ j, 0 < q j) ∧
        (∀ i k, ProbabilityTheory.covariance (fun ω => C i + A.mulVec (Y ω) i)
          (fun ω => C k + A.mulVec (Y ω) k) μ =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker A.transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
        m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin)

section CoordinateLaws
open ProbabilityTheory
open scoped ENNReal

/-- Gamma components of the series in [malham2008square] Proposition 1, as used in (23.4). -/
noncomputable def G023 (a r : ℝ) : Kernel ℕ ℝ :=
  Kernel.ofFunOfCountable (fun n => gammaMeasure (a+n) r)

/-- The Poisson mixture of those components, with shape offset `a`, rate `r` and Poisson mean `z`. -/
noncomputable def P023 (a r : ℝ) (z : ℝ≥0) : Measure ℝ := G023 a r ∘ₘ poissonMeasure z

/-- The scaled noncentral chi-square law in (23.4), written as its Poisson mixture; the Gamma rate is the inverse of the scale `2a`. -/
noncomputable def T023 (θ α h x : ℝ) : Measure ℝ :=
  P023 (chiDof θ α / 2) (2 * chiScale θ α h)⁻¹ (chiRate θ α h * x / 2).toNNReal

/-- The coordinate law on one piece: absorbed at zero for zero mean reversion, deterministic for zero noise or length, and the scaled noncentral chi-square law otherwise. -/
noncomputable def T023Piece (θ α h : ℝ) : ℝ → Measure ℝ :=
  if θ = 0 then fun x => Standalone.ZeroMeanReversionVarianceSupport.T01513 (α^2*h/2) x.toNNReal
  else if α = 0 ∨ h = 0 then fun x => Measure.dirac (lflow θ x h)
  else T023 θ α h

/-- Coordinate law across pieces, latest piece first; each new transition is integrated against the law after the earlier pieces. -/
noncomputable def L023 (θ : ℝ) : List (ℝ × ℝ) → ℝ → Measure ℝ
  | [], x => Measure.dirac x
  | p::ps, x => (L023 θ ps x).bind (T023Piece θ p.1 p.2)

/-- The lower endpoint in (23.4)–(23.5): a stochastic piece resets it to zero and a deterministic piece carries it forward by the mean-reversion flow. -/
noncomputable def ell023 (θ x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => x
  | p::ps => if p.1 = 0 ∨ p.2 = 0 then lflow θ (ell023 θ x ps) p.2 else 0

/-- The accumulated parameter of Claim 015 for zero mean reversion: the sum of `α²h/2` over the pieces. -/
noncomputable def c023 : List (ℝ × ℝ) → ℝ
  | [] => 0
  | p::ps => p.1^2*p.2/2 + c023 ps

/-- The coordinate laws, exact supports and lower-endpoint masses in (b), for every finite list of pieces. The transform uniquely identifies this law. -/
def coordinateLawStatement : Prop :=
  ∀ (θ : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ θ →
    (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) → Measurable (L023 θ ps) ∧
    ∀ x : ℝ, 0 ≤ x →
      IsProbabilityMeasure (L023 θ ps x) ∧
      (∀ l, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂L023 θ ps x) =
        Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l))) ∧
      (L023 θ ps x).support =
        (if (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x)
          then Ici (ell023 θ x ps) else {ell023 θ x ps}) ∧
      L023 θ ps x {ell023 θ x ps} =
        (if (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x) then
          if θ = 0 then ENNReal.ofReal (Real.exp (-x/c023 ps)) else 0 else 1) ∧
      (0 < θ → (∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) → ∀ y, L023 θ ps x {y} = 0) ∧
      ((¬ ((∃ p ∈ ps, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ ∨ 0 < x))) →
        L023 θ ps x = Measure.dirac (ell023 θ x ps)) ∧
      (θ = 0 → L023 θ ps x = Standalone.ZeroMeanReversionVarianceSupport.T01513 (c023 ps) x.toNNReal) ∧
      (∀ (μ : Measure ℝ), IsProbabilityMeasure μ → (∀ᵐ y ∂μ, 0 ≤ y) →
        (∀ l, 0 ≤ l → (∫ y, Real.exp (-(l*y)) ∂μ) =
          Real.exp (-(piFlow θ ps l*x + rhoFlow θ ps l))) → μ = L023 θ ps x)

/-- The lower endpoint is nonnegative, is zero after a stochastic last piece, and is
strictly positive after a positive-length deterministic last piece with positive mean
reversion. With no stochastic piece it is the deterministic flow of the initial state. -/
def lowerEndpointStatement : Prop :=
  ∀ (θ x : ℝ) (ps : List (ℝ × ℝ)), 0 ≤ θ → 0 ≤ x →
    (∀ p ∈ ps, 0 ≤ p.1 ∧ 0 ≤ p.2) →
    0 ≤ ell023 θ x ps ∧
    (∀ α h qs, ps = (α,h)::qs → 0 < α → 0 < h → ell023 θ x ps = 0) ∧
    (∀ h qs, ps = (0,h)::qs → 0 < θ → 0 < h → 0 < ell023 θ x ps) ∧
    ((∀ p ∈ ps, p.1 = 0 ∨ p.2 = 0) → ell023 θ x ps = lflow θ x (totalLength ps))

/-- The joint transform in (23.3) identifies the product of the composed coordinate laws. -/
def piecewiseJointLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ (Y : Ω → Fin d → ℝ), Measurable Y → (∀ᵐ ω ∂μ, ∀ j, 0 ≤ Y ω j) →
    ∀ (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)), (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ x j) →
      (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        (∫ ω, Real.exp (-(∑ j, l j * Y ω j)) ∂μ) =
          Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x j + rhoFlow (θ j) (ps j) (l j))))) →
      μ.map Y = Measure.pi (fun j => L023 (θ j) (ps j) (x j))

/-- Exact image support, affine hull, affine equalities and vertex mass in (c) and (d),
for the identified coordinate laws. No coordinate-support premise is assumed. -/
def piecewiseImageLawStatement : Prop :=
  ∀ (m d : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ), (∀ i j, 0 ≤ A i j) →
    ∀ (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)), (∀ j, 0 ≤ θ j) → (∀ j, 0 ≤ x j) →
      (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
    let J := Finset.univ.filter fun j => (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
    let ell := fun j => ell023 (θ j) (x j) (ps j)
    let B := activeCols A J
    let b := C + A.mulVec ell
    let ν := (Measure.pi (fun j => L023 (θ j) (ps j) (x j))).map (fun y => C + A.mulVec y)
    ν.support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b) ∧
    (affineSpan ℝ ν.support : Set (Fin m → ℝ)) =
      (fun y => b+y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
    B.rank ≤ J.card ∧
    (∀ w, (∀ᵐ y ∂ν, dotProduct w (y-b) = 0) ↔ B.transpose.mulVec w = 0) ∧
    ν {b} = ∏ j, if (∃ i, B i j ≠ 0) then L023 (θ j) (ps j) (x j) {ell j} else 1

/-- The regular conditional law in (a) and (d) has exactly the identified product law
almost surely. `piecewiseImageLawStatement` gives its deterministic affine images. -/
def conditionalPiecewiseLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (G : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω)
    (μ : Measure Ω), IsProbabilityMeasure μ → G ≤ mΩ →
    ∀ (Y : Ω → Fin d → ℝ≥0), Measurable Y →
    ∀ (θ : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (x : Ω → Fin d → ℝ),
      (∀ ω j, 0 ≤ x ω j) → (∀ j, 0 ≤ θ j) →
      (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        μ[fun ω => Real.exp (-(∑ j, l j * Y ω j)) | G] =ᵐ[μ]
          fun ω => Real.exp (-(∑ j, (piFlow (θ j) (ps j) (l j) * x ω j +
            rhoFlow (θ j) (ps j) (l j))))) →
    ∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[G] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[G] D → (μ.restrict D).map Y = κ ∘ₘ μ.restrict D) ∧
      ∀ᵐ ω ∂μ, (κ ω).map (fun y j => (y j : ℝ)) = Measure.pi (fun j => L023 (θ j) (ps j) (x ω j))

/-- The exact support and affine hull in (23.7) for the printed three-factor speeds,
with positive last pieces. A nonzero column on a positive-mean-reversion factor removes
the atom at the vertex. No rank-three conclusion is asserted. -/
def sourcePiecewiseSupportStatement : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 3) ℝ) (C : Fin m → ℝ), (∀ i j, 0 ≤ A i j) →
    ∀ (ps : Fin 3 → List (ℝ × ℝ)), (∀ j p, p ∈ ps j → 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ j, ∃ α h qs, ps j = (α,h)::qs ∧ 0 < α ∧ 0 < h) →
    let ν := (Measure.pi (fun j => L023 (θ0235 j) (ps j) 1)).map (fun y => C + A.mulVec y)
    ν.support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ ν.support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → ν {C} = 0)

end CoordinateLaws

/-! ### Composition from the SDE hypotheses -/

/-- The SDE hypotheses already used by `onePieceStatement`, grouped for the finite-piece
assembly. The coefficient is bounded on every finite horizon and the continuous version is fixed everywhere. -/
def H0237 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal) : Prop :=
  (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) ∧
  (∀ j, 0 ≤ θ j) ∧
  (∀ ω j, Continuous fun t => (X t ω j : ℝ)) ∧
  (∀ t, Measurable[S.ℱ t] (X t)) ∧
  (∀ j, Measurable (αf j)) ∧ (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) ∧
  (X 0 =ᵐ[S.μ] fun _ => x0) ∧ (∀ j, x0 j ≤ 1) ∧
  (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) ∧
  (∀ j, LocallyIntegrableDrift S.ℱ S.μ (Kdrv θ X j)) ∧
  (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
    X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
      ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω)

/-- The deterministic coefficient equals the listed value in the interior of each successive piece,
listed from the right endpoint backward. No transform or independence is assumed. -/
def H0238 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ) :
    ℝ → List ((Fin d → ℝ) × ℝ) → Prop
  | _, [] => True
  | b, p::ps =>
      (∀ j (s : ℝ≥0), b-p.2 < s → (s : ℝ) < b → αf j s = p.1 j) ∧
      H0238 αf (b-p.2) ps

/-- The composed conditional transform from the SDE hypotheses and deterministic pieces.
The one-piece transform is proved from the audited fields, then composed by the tower property. -/
def fieldsTransformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    ∀ (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      0 ≤ leftEnd b ps → H0238 αf b ps →
      ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X b ω j)) | filtR S.ℱ (leftEnd b ps)] =ᵐ[S.μ]
          fun ω => Real.exp (-(∑ j,
            (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * stateR X (leftEnd b ps) ω j +
              rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j))))

open ProbabilityTheory in
/-- The regular conditional law and the deterministic-start joint law from the SDE fields.
Both identify the finite-piece laws `L023`; no transform premise remains. -/
def fieldsLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    ∀ (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      0 ≤ leftEnd b ps → H0238 αf b ps →
    (∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd b ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd b ps)] D →
        (S.μ.restrict D).map (stateR X b) = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ, (κ ω).map (fun y j => (y j : ℝ)) =
        Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (stateR X (leftEnd b ps) ω j))) ∧
    (leftEnd b ps = 0 → S.μ.map (fun ω j => (stateR X b ω j : ℝ)) =
      Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j)))

/-- Claim 013's centered representation, conditional isometry, orthogonality and
conditional first-moment integration, with the deterministic integrability required for
its affine assembly. These are premises of the variance-law statements;
`fieldsMomentAssemblyStatement` derives them under the explicit centered representation. -/
def H0239 {m d : ℕ} {Ω : Type} (G : MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
    (v : Ω → Fin d → ℝ≥0) (K : Fin m → Fin d → ℝ → ℝ)
    (θ : Fin d → ℝ) (T : Fin m → ℝ) (t : ℝ) : Prop :=
  (∀ n i j, Integrable (fun ω => Z n i ω * Z n j ω) μ) ∧
  (∀ n, Y n - μ[Y n | G] =ᵐ[μ] fun ω => ∑ j, Z n j ω) ∧
  (∀ n j, μ[fun ω => Z n j ω ^ 2 | G] =ᵐ[μ] μ[I01314 n j | G]) ∧
  (∀ n i j, i ≠ j → μ[fun ω => Z n i ω * Z n j ω | G] =ᵐ[μ] 0) ∧
  (∀ n j, μ[I01314 n j | G] =ᵐ[μ] fun ω =>
    ∫ u in t..T n, K n j u *
      (1 + ((v ω j : ℝ) - 1) * Standalone.StochasticMeetingVariance.E (fun _ => θ j) t u)) ∧
  (∀ n j, IntervalIntegrable (K n j) volume t (T n)) ∧
  (∀ n j, IntervalIntegrable
    (fun u => K n j u * Standalone.StochasticMeetingVariance.E (fun _ => θ j) t u) volume t (T n))

/-- The exact support, affine hull, equalities and vertex mass for an affine-image law,
with the state-dependent active columns and lower endpoint of (c)–(d). -/
def C02310 {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (C : Fin m → ℝ)
    (θ x : Fin d → ℝ) (ps : Fin d → List (ℝ × ℝ)) (ν : Measure (Fin m → ℝ)) : Prop :=
  let J := Finset.univ.filter fun j => (∃ p ∈ ps j, 0 < p.1 ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < x j)
  let ell := fun j => ell023 (θ j) (x j) (ps j)
  let B := activeCols A J
  let b := C + A.mulVec ell
  ν.support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b ∧
  IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 B b) ∧
  (affineSpan ℝ ν.support : Set (Fin m → ℝ)) =
    (fun y => b+y) '' (LinearMap.range B.mulVecLin : Set (Fin m → ℝ)) ∧
  B.rank ≤ J.card ∧
  (∀ w, (∀ᵐ y ∂ν, dotProduct w (y-b) = 0) ↔ B.transpose.mulVec w = 0) ∧
  ν {b} = ∏ j, if (∃ i, B i j ≠ 0) then L023 (θ j) (ps j) (x j) {ell j} else 1

/-- The actual conditional-variance vector of the meeting jumps has the identified law
and exact support under the SDE fields and Claim 013's explicit moment premises. The matrix
and offset are Claim 013's integrals, not arbitrary assumed affine coefficients. -/
def fieldsMeetingVarianceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    ∀ (t : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      leftEnd t ps = 0 → H0238 αf t ps →
    ∀ (m : ℕ) (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
      (K : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ),
      (∀ n, t ≤ T n) → (∀ n j u, 0 ≤ K n j u) →
      H0239 (filtR S.ℱ t) S.μ Y Z I01314 (stateR X t) K θ T t →
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) T t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) T t
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (filtR S.ℱ t) S.μ Y
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (stateR X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- Conditional version of the actual meeting-variance law and exact support, given the
left endpoint of the listed pieces, under the same explicit Claim 013 moment premises. -/
def fieldsConditionalMeetingVarianceStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    ∀ (t : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      0 ≤ leftEnd t ps → H0238 αf t ps →
    ∀ (m : ℕ) (Y : Fin m → Ω → ℝ) (Z I01314 : Fin m → Fin d → Ω → ℝ)
      (K : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ),
      (∀ n, t ≤ T n) → (∀ n j u, 0 ≤ K n j u) →
      H0239 (filtR S.ℱ t) S.μ Y Z I01314 (stateR X t) K θ T t →
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) T t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) T t
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (filtR S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)

/-! ### Square integrability and moments of the stochastic increments -/

/-- Finite piece representations on every horizon, with nonnegative lengths and values. -/
def H02311 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ) : Prop :=
  ∀ t : ℝ≥0, ∃ ps : List ((Fin d → ℝ) × ℝ),
    (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧ leftEnd t ps = 0 ∧ H0238 αf t ps

/-- The state mean from the SDE fields is the mean-reversion flow of the initial state,
so it is at most one when the initial state is at most one. -/
def fieldsStateMeanStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    ∀ (t : ℝ≥0) (j : Fin d),
      (∫ ω, (X t ω j : ℝ) ∂S.μ) = lflow (θ j) (x0 j) t ∧
      (∫ ω, (X t ω j : ℝ) ∂S.μ) ≤ 1

/-- Every locally bounded deterministic coefficient times the square root of the state
is square integrable on each finite horizon, from the derived state mean bound. -/
def fieldsCoefficientStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (j : Fin d) (K : ℝ≥0 → ℝ), Measurable K →
      (∀ T : ℝ≥0, ∃ C, ∀ s, s ≤ T → |K s| ≤ C) →
      ∀ T : ℝ≥0, U5 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j)) T

/-- Conditional isometry and cross-factor orthogonality for two-driver increments with
locally bounded deterministic coefficients and the mean-reverting variance states.
Square integrability is derived from the SDE state mean, not assumed for the integrands. -/
def fieldsIncrementStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (kw : Fin d → Fin S.m) (K₁ K₂ : Fin d → ℝ≥0 → ℝ),
    (∀ j, Measurable (K₁ j)) → (∀ j, Measurable (K₂ j)) →
    (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |K₁ j s| ≤ C) →
    (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |K₂ j s| ≤ C) →
    ∀ (T t : ℝ≥0), t ≤ T →
    (∀ j : Fin d,
      MemLp (twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
        (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t) 2 S.μ ∧
      S.μ[fun ω => twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω ^ 2 | S.ℱ t] =ᵐ[S.μ]
        S.μ[fun ω =>
          (∫ s in (t : ℝ)..T, K₁ j (Real.toNNReal s) ^ 2 * S.c (kw j) (kw j) (Real.toNNReal s) *
            (X (Real.toNNReal s) ω j : ℝ)) +
          2 * (∫ s in (t : ℝ)..T, K₁ j (Real.toNNReal s) * K₂ j (Real.toNNReal s) *
            S.c (kw j) (k j) (Real.toNNReal s) * (X (Real.toNNReal s) ω j : ℝ)) +
          (∫ s in (t : ℝ)..T, K₂ j (Real.toNNReal s) ^ 2 * S.c (k j) (k j) (Real.toNNReal s) *
            (X (Real.toNNReal s) ω j : ℝ)) | S.ℱ t]) ∧
    (∀ i j : Fin d,
      (∀ s, S.c (kw i) (kw j) s = 0) → (∀ s, S.c (kw i) (k j) s = 0) →
      (∀ s, S.c (k i) (kw j) s = 0) → (∀ s, S.c (k i) (k j) s = 0) →
      Integrable (fun ω =>
        twoDriverIncrement S (kw i) (k i) (fun s ω => K₁ i s * Real.sqrt (X s ω i))
          (fun s ω => K₂ i s * Real.sqrt (X s ω i)) T t ω *
        twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω) S.μ ∧
      S.μ[fun ω =>
        twoDriverIncrement S (kw i) (k i) (fun s ω => K₁ i s * Real.sqrt (X s ω i))
          (fun s ω => K₂ i s * Real.sqrt (X s ω i)) T t ω *
        twoDriverIncrement S (kw j) (k j) (fun s ω => K₁ j s * Real.sqrt (X s ω j))
          (fun s ω => K₂ j s * Real.sqrt (X s ω j)) T t ω | S.ℱ t] =ᵐ[S.μ] 0)

/-- The two-driver increment in Claim 013, with the time-dependent coefficient `α R`. -/
noncomputable def Z02312 {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (g R : Fin d → ℝ≥0 → ℝ) (T t : ℝ≥0) (j : Fin d) : Ω → ℝ :=
  twoDriverIncrement S (kw j) (k j) (fun s ω => g j s * Real.sqrt (X s ω j))
    (fun s ω => (αf j s * R j s) * Real.sqrt (X s ω j)) T t

/-- The integral of Claim 013's full kernel against the variance state. -/
noncomputable def I02312 {d : ℕ} {Ω : Type} (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (g R ρ : Fin d → ℝ≥0 → ℝ)
    (T t : ℝ≥0) (j : Fin d) : Ω → ℝ :=
  fun ω => ∫ s in (t : ℝ)..T,
    Standalone.StochasticMeetingVariance.F (g j (Real.toNNReal s)) (ρ j (Real.toNNReal s))
      (αf j (Real.toNNReal s)) (R j (Real.toNNReal s)) * (X (Real.toNNReal s) ω j : ℝ)

/-- Integrable products, conditional isometry with the full kernel, and cross-factor
orthogonality for the increments `Z02312`. The backward weights are supplied as measurable
locally bounded deterministic functions; the centered representation of the meeting jumps
is not part of this statement. -/
def fieldsKernelIsometryStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (kw : Fin d → Fin S.m) (g R ρ : Fin d → ℝ≥0 → ℝ),
      (∀ j, Measurable (g j)) → (∀ j, Measurable (R j)) →
      (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |g j s| ≤ C) →
      (∀ j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |R j s| ≤ C) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (T t : ℝ≥0), t ≤ T →
      (∀ j, MemLp (Z02312 S k kw αf X g R T t j) 2 S.μ) ∧
      (∀ i j, Integrable (fun ω => Z02312 S k kw αf X g R T t i ω *
        Z02312 S k kw αf X g R T t j ω) S.μ) ∧
      (∀ j, S.μ[fun ω => Z02312 S k kw αf X g R T t j ω ^ 2 | S.ℱ t] =ᵐ[S.μ]
        S.μ[I02312 αf X g R ρ T t j | S.ℱ t]) ∧
      (∀ i j, i ≠ j → S.μ[fun ω => Z02312 S k kw αf X g R T t i ω *
        Z02312 S k kw αf X g R T t j ω | S.ℱ t] =ᵐ[S.μ] 0)

/-- Claim 013's backward weight is continuous, hence measurable and bounded on finite
horizons, for constant mean reversion and locally integrable drift coefficients. -/
def backwardWeightRegularityStatement : Prop :=
  ∀ (θ : ℝ) (b : ℝ → ℝ) (T : ℝ),
    (∀ a c, IntervalIntegrable b volume a c) →
    Continuous (Standalone.StochasticMeetingVariance.R (fun _ => θ) b T) ∧
    Measurable (fun s : ℝ≥0 => Standalone.StochasticMeetingVariance.R (fun _ => θ) b T s) ∧
    ∀ U : ℝ≥0, ∃ C, ∀ s : ℝ≥0, s ≤ U →
      |Standalone.StochasticMeetingVariance.R (fun _ => θ) b T s| ≤ C

/-- With the backward weight of Claim 013, `I02312` is exactly its full-kernel integral,
including the time-dependent volatility of volatility. -/
def kernelIdentificationStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ≥0) (g b : Fin m → Fin d → ℝ → ℝ)
    (ρ : Fin d → ℝ → ℝ) (T : Fin m → ℝ≥0) (n : Fin m) (j : Fin d) (t : ℝ≥0), t ≤ T n →
    I02312 αf X (fun j s => g n j s)
      (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
      (fun j s => ρ j s) (T n) t j =
    fun ω => ∫ u in (t : ℝ)..T n,
      Standalone.StochasticMeetingVariance.kernel0136 g b ρ (fun j s => αf j (Real.toNNReal s))
        (fun j _ => θ j) (fun n => (T n : ℝ)) n j u * (X (Real.toNNReal u) ω j : ℝ)


/-- The state conditional mean between arbitrary nonnegative times. The finite pieces
may be cut at the earlier conditioning time. -/
def fieldsConditionalMeanStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    ∀ (a b : ℝ≥0), a ≤ b → ∀ j,
      S.μ[fun ω => (X b ω j : ℝ) | S.ℱ a] =ᵐ[S.μ]
        fun ω => lflow (θ j) (X a ω j) ((b : ℝ)-a)

/-- Conditional first-moment integration for any interval-integrable deterministic weight,
including the full kernel. No conditional integration premise is assumed. -/
def fieldsWeightedIntegralStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    ∀ (a b : ℝ≥0), a ≤ b → ∀ (j : Fin d) (K : ℝ → ℝ),
      IntervalIntegrable K volume (a : ℝ) b →
      Integrable (fun ω => ∫ u in (a : ℝ)..b, K u * (stateR X u ω j : ℝ)) S.μ ∧
      (S.μ[fun ω => ∫ u in (a : ℝ)..b, K u * (stateR X u ω j : ℝ) | S.ℱ a] =ᵐ[S.μ]
        fun ω => ∫ u in (a : ℝ)..b, K u * lflow (θ j) (X a ω j) (u-a))

/-- All of Claim 013's moment premises are derived for the actual two-driver increments,
except the centered representation, which is explicit. The deterministic kernels here use
supplied measurable locally bounded weights; `kernelIdentificationStatement` specializes
them to Claim 013's backward weights. -/
def fieldsMomentAssemblyStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (kw : Fin d → Fin S.m) (g R : Fin m → Fin d → ℝ≥0 → ℝ) (ρ : Fin d → ℝ≥0 → ℝ),
      (∀ n j, Measurable (g n j)) → (∀ n j, Measurable (R n j)) →
      (∀ n j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |g n j s| ≤ C) →
      (∀ n j (T : ℝ≥0), ∃ C, ∀ s, s ≤ T → |R n j s| ≤ C) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (T : Fin m → ℝ≥0) (t : ℝ≥0), (∀ n, t ≤ T n) → ∀ (Y : Fin m → Ω → ℝ),
      (∀ n, Y n - S.μ[Y n | S.ℱ t] =ᵐ[S.μ]
        fun ω => ∑ j, Z02312 S k kw αf X (g n) (R n) (T n) t j ω) →
      H0239 (S.ℱ t) S.μ Y
        (fun n j => Z02312 S k kw αf X (g n) (R n) (T n) t j)
        (fun n j => I02312 αf X (g n) (R n) ρ (T n) t j) (X t)
        (fun n j u => Standalone.StochasticMeetingVariance.F
          (g n j (Real.toNNReal u)) (ρ j (Real.toNNReal u))
          (αf j (Real.toNNReal u)) (R n j (Real.toNNReal u))) θ (fun n => (T n : ℝ)) t


/-- Deterministic coefficients and driver covariations for the constructed meeting jumps.
No centered representation, conditional moment, transform or support is assumed. -/
def H02314 {m d : ℕ} {Ω : Type} [MeasurableSpace Ω] (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ) : Prop :=
  (∀ n j, Measurable (g n j)) ∧
  (∀ n j (U : ℝ≥0), ∃ C, ∀ s : ℝ≥0, s ≤ U → |g n j s| ≤ C) ∧
  (∀ n j, Measurable (b n j)) ∧ (∀ n j a c, IntervalIntegrable (b n j) volume a c) ∧
  (∀ j s, S.c (kw j) (kw j) s = 1) ∧ (∀ j s, S.c (kw j) (k j) s = ρ j s) ∧
  (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) ∧
  (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) ∧
  (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1)

/-- The product-rule identity at the meeting horizon. Its deterministic mean-reversion contribution
is retained; centering subsequently removes it. The drift coefficient needs only local
integrability, so no smoothness restriction is added to the piecewise coefficients. -/
def productTerminalStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (j : Fin d) (b : ℝ → ℝ), Measurable b →
      (∀ a c, IntervalIntegrable b volume a c) → ∀ T : ℝ≥0,
      ∀ᵐ ω ∂S.μ, (∫ u in (0 : ℝ)..T, b u * (X (Real.toNNReal u) ω j : ℝ)) =
        Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T 0 * (x0 j : ℝ) +
        (∫ u in (0 : ℝ)..T, θ j * Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T u) +
        S.I (k j) (fun s ω => (αf j s * Standalone.StochasticMeetingVariance.R (fun _ => θ j) b T s) *
          Real.sqrt (X s ω j)) T ω

/-- Integrability and the centered representation of the constructed meeting jump,
derived from the audited fields with time-dependent volatility of volatility. -/
def fieldsCenteredStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (T : Fin m → ℝ≥0) (n : Fin m),
      (∀ j, Measurable (g n j)) →
      (∀ j (U : ℝ≥0), ∃ C, ∀ s : ℝ≥0, s ≤ U → |g n j s| ≤ C) →
      (∀ j, Measurable (b n j)) → (∀ j a c, IntervalIntegrable (b n j) volume a c) →
    ∀ t : ℝ≥0, t ≤ T n →
      Integrable (Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n) S.μ ∧
      Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n -
        S.μ[Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n | S.ℱ t] =ᵐ[S.μ]
        fun ω => ∑ j, Z02312 S k kw αf X (fun j s => g n j s)
          (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
          (T n) t j ω

/-- All moment premises for the constructed jumps and Claim 013's actual full kernel,
with none of those moment identities assumed. -/
def fieldsConstructedMomentsStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ), H02314 S k kw g b ρ →
    ∀ (T : Fin m → ℝ≥0) (t : ℝ≥0), (∀ n, t ≤ T n) →
      H0239 (S.ℱ t) S.μ
        (fun n => Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n)
        (fun n j => Z02312 S k kw αf X (fun j s => g n j s)
          (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s) (T n) t j)
        (fun n j => I02312 αf X (fun j s => g n j s)
          (fun j s => Standalone.StochasticMeetingVariance.R (fun _ => θ j) (b n j) (T n) s)
          (fun j s => ρ j s) (T n) t j) (X t)
        (Standalone.StochasticMeetingVariance.kernel0136 g b ρ (fun j s => αf j (Real.toNNReal s))
          (fun j _ => θ j) (fun n => (T n : ℝ))) θ (fun n => (T n : ℝ)) t

/-- The law and exact support of the conditional-variance vector of the constructed jumps,
with all Claim 013 moment premises derived. The remaining bridge assumptions are explicit. -/
def fieldsConstructedVarianceStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ), H02314 S k kw g b ρ →
    ∀ (T : Fin m → ℝ≥0) (t : ℝ≥0), (∀ n, t ≤ T n) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) (fun n => (T n : ℝ))
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) (fun n => (T n : ℝ)) t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) (fun n => (T n : ℝ)) t
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ
      (fun n => Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n)
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- The regular conditional law and support of the same constructed variance vector,
given the earlier endpoint of the coefficient pieces, with all moment identities derived. -/
def fieldsConstructedConditionalVarianceStatement : Prop :=
  ∀ (m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (g b : Fin m → Fin d → ℝ → ℝ) (ρ : Fin d → ℝ → ℝ), H02314 S k kw g b ρ →
    ∀ (T : Fin m → ℝ≥0) (t : ℝ≥0), (∀ n, t ≤ T n) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → 0 ≤ leftEnd t ps → H0238 αf t ps →
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) (fun n => (T n : ℝ))
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) (fun n => (T n : ℝ)) t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) (fun n => (T n : ℝ)) t
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ
      (fun n => Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b (fun n => (T n : ℝ)) n)
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)


/-- The source meeting dates, deterministic scales and decays of Claim 013.
Finite loadings need no separate bound. -/
def H02315 {N d : ℕ} (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) : Prop :=
  StrictMono T ∧ (∀ n, 0 < T n) ∧ (∀ j, Measurable (a j)) ∧
  (∀ j, Measurable (lam j)) ∧ (∀ j u, 0 ≤ lam j u) ∧
  (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |lam j u| ≤ B) ∧
  (∀ j l r, ∃ B : ℝ, ∀ u ∈ Set.Icc l r, |a j u| ≤ B)

open scoped Topology in
/-- The forward-rate version identity and the short-rate left limits and jumps, with the
positive-mean-reversion coefficient bounds used to establish the loading integrands in (U4). -/
def fieldsShortRateJumpStatement : Prop :=
  ∀ (N d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ), H02315 T a lam →
    (∀ (t : ℝ≥0) (u : ℝ), ∀ᵐ ω ∂S.μ,
      Standalone.ZeroMeanReversionUpstreamBridge.forwardSrc S kw (fun n => (T n : ℝ)) a lam γ X c t u ω =
        c + (∫ s in (0 : ℝ)..t,
          Standalone.ZeroMeanReversionUpstreamBridge.driftSrc (fun n => (T n : ℝ)) a lam γ X s u ω) +
        ∑ j, S.I (kw j) (fun s ω => Standalone.ZeroMeanReversionUpstreamBridge.hSrc
          (fun n => (T n : ℝ)) a lam γ j s u * Real.sqrt (X s ω j)) t ω) ∧
    ∀ n : Fin N, ∀ᵐ ω ∂S.μ, ∃ L : ℝ,
      Filter.Tendsto (fun t : ℝ => Standalone.ZeroMeanReversionUpstreamBridge.shortSrc S kw
        (fun n => (T n : ℝ)) a lam γ X c (Real.toNNReal t) ω) (𝓝[<] (T n : ℝ)) (𝓝 L) ∧
      Standalone.ZeroMeanReversionUpstreamBridge.shortSrc S kw (fun n => (T n : ℝ)) a lam γ X c (T n) ω - L =
        Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X
          (Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ)
          (Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ)
          (fun n => (T n : ℝ)) n ω

/-- The variance law of the actual short-rate jumps at any retained meetings, with the
source coefficients and every conditional-moment premise derived from the field hypotheses. -/
def fieldsSourceVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (∀ n, Y n =ᵐ[S.μ] Standalone.ZeroMeanReversionUpstreamBridge.Yactual S kw X g b Tr n) ∧
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- Regular conditional law and exact support of the actual short-rate variance vector. -/
def fieldsSourceConditionalVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → 0 ≤ leftEnd t ps → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)

/-- The published three-factor speeds and positive last coefficient pieces give the full
translated cone for the actual short-rate variance vector. No rank-three conclusion is assumed. -/
def fieldsSourceColumnStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal), H0237 S k θ0235 αf X (fun _ => 1) →
    H02311 αf → (∀ s j, Integrable (fun ω => (X s ω j : ℝ)) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin 3 → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
      (∃ a h qs, ps = (a,h)::qs ∧ (∀ j, 0 < a j) ∧ 0 < h) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (S.μ.map V).support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ (S.μ.map V).support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → (S.μ.map V) {C} = 0)

/-- The stated integrable supremum of squared states implies the endpoint first and
second moments. Almost-sure continuous paths suffice for this implication. -/
def stateMomentsStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω),
    IsProbabilityMeasure μ → ∀ X : ℝ≥0 → Ω → Fin d → ℝ≥0,
      (∀ t, Measurable (X t)) →
      (∀ j, ∀ᵐ ω ∂μ, Continuous (fun s => (X s ω j : ℝ))) →
      (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) μ) →
      ∀ t j, MemLp (fun ω => (X t ω j : ℝ)) 2 μ ∧ Integrable (fun ω => (X t ω j : ℝ)) μ

/-- Covariance, active columns, kernel and rank of the actual source variance vector.
The first and second moments follow from the integrable supremum of squared states;
no transform or affine premise is assumed. -/
def fieldsSourceCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ j) (x0 j) (ps.map fun p => (p.1 j,p.2))
    let J := Finset.univ.filter fun j =>
      (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < (x0 j : ℝ))
    (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- The covariance formula holds in a regular conditional law of the source variance
vector given the earlier time, with precisely the state-dependent active columns. -/
def fieldsSourceConditionalCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → 0 ≤ leftEnd t ps → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D →
        (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        let q := fun j => varianceFlow (θ j) (stateR X (leftEnd t ps) ω j)
          (ps.map fun p => (p.1 j,p.2))
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
            (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))
        (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
        (∀ i k, ProbabilityTheory.covariance (fun v => v i) (fun v => v k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

/-- All three coordinate variances are positive in the printed column. The covariance
rank of the actual source variance vector is exactly the loading rank, which is at most three. -/
def fieldsSourceColumnCovarianceStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal), H0237 S k θ0235 αf X (fun _ => 1) →
    H02311 αf →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin 3 → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
      (∃ a h qs, ps = (a,h)::qs ∧ (∀ j, 0 < a j) ∧ 0 < h) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ0235 j) 1 (ps.map fun p => (p.1 j,p.2))
    (∀ j, 0 < q j) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker A.transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
    m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin)

/-- Integrability and both mean formulas for the actual source variance vector.
State moments, its affine representation and conditional state means are derived. -/
def fieldsSourceMeanStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal), H0237 S k θ αf X x0 →
    H02311 αf →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (∀ n, Integrable (fun ω => V ω n) S.μ) ∧
    (∀ s : ℝ≥0, s ≤ t → ∀ n,
      S.μ[fun ω => V ω n | S.ℱ s] =ᵐ[S.μ] fun ω =>
        C n + A.mulVec (fun j => lflow (θ j) (X s ω j) ((t : ℝ)-s)) n) ∧
    (∀ n, (∫ ω, V ω n ∂S.μ) = C n + A.mulVec (fun j => lflow (θ j) (x0 j) t) n)

/-- The local Itô-integrability premises in `H0237` follow from the deterministic
coefficient bounds and continuous adapted state paths. Predictability of the square
root and the everywhere-continuous version are still explicit hypotheses. -/
def fieldsPremisesStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    H0237 S k θ αf X x0

/-- AX-09, restated verbatim from `Upstream.Predictability` for standalone statements. -/
structure Predictability {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) : Prop where
  continuous_predictable : ∀ (X : ℝ≥0 → Ω → ℝ),
    (∀ t, Measurable[ℱ t] (X t)) → (∀ ω, Continuous fun t => X t ω) →
    IsStronglyPredictable ℱ X

/-- Almost-sure continuous adapted states have an indistinguishable nonnegative version
with continuous paths everywhere and predictable square roots, using AX-09. -/
def continuousVersionStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    ∃ X' : ℝ≥0 → Ω → Fin d → NNReal,
      (∀ᵐ ω ∂S.μ, ∀ t, X' t ω = X t ω) ∧
      (∀ ω j, Continuous fun t => (X' t ω j : ℝ)) ∧
      (∀ t, Measurable[S.ℱ t] (X' t)) ∧
      (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X' s ω j)))

/-- The original SDE is transferred to the continuous version. Its original noise
integrands must be in the domain (U4) of the integral operator; square-root
predictability and every `H0237` premise for the new version are derived. -/
def fieldsVersionStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    ∃ X' : ℝ≥0 → Ω → Fin d → NNReal,
      (∀ᵐ ω ∂S.μ, ∀ t, X' t ω = X t ω) ∧ H0237 S k θ αf X' x0 ∧
      (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X' s ω j))) ∧
      (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X' s ω j : ℝ)^2) S.μ)

open ProbabilityTheory in
/-- The conditional and unconditional finite-piece laws for the original almost-surely
continuous state, obtained through its indistinguishable continuous version. -/
def fieldsAeLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    ∀ (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      0 ≤ leftEnd b ps → H0238 αf b ps →
    (∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd b ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd b ps)] D →
        (S.μ.restrict D).map (stateR X b) = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ, (κ ω).map (fun y j => (y j : ℝ)) =
        Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (stateR X (leftEnd b ps) ω j))) ∧
    (leftEnd b ps = 0 → S.μ.map (fun ω j => (stateR X b ω j : ℝ)) =
      Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j)))

/-- Indistinguishable state processes give the same source forward curves, meeting
jumps and variance vectors, when both loading integrands belong to the integral domain. -/
def sourceVersionStatement : Prop :=
  ∀ (N d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
    (kw : Fin d → Fin S.m) (T : Fin N → ℝ) (a lam : Fin d → ℝ → ℝ)
    (γ : Fin d → ℕ → ℝ) (c : ℝ) (X X' : ℝ≥0 → Ω → Fin d → NNReal),
    (∀ᵐ ω ∂S.μ, ∀ t, X t ω = X' t ω) →
    (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt T a lam γ X j q)) →
    (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt T a lam γ X' j q)) →
    (∀ᵐ ω ∂S.μ, ∀ t u,
      Standalone.ZeroMeanReversionUpstreamBridge.forwardSrc S kw T a lam γ X c t u ω =
      Standalone.ZeroMeanReversionUpstreamBridge.forwardSrc S kw T a lam γ X' c t u ω) ∧
    (∀ᵐ ω ∂S.μ, ∀ n,
      Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw T a lam γ X c n ω =
      Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw T a lam γ X' c n ω) ∧
    ∀ (m : ℕ) (rows : Fin m → Fin N) (t : ℝ≥0),
      Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ
        (fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw T a lam γ X c (rows n)) =ᵐ[S.μ]
      Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ
        (fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw T a lam γ X' c (rows n))

open ProbabilityTheory in
/-- Source variance conclusions for the original almost-surely continuous state;
noise and loading integral-domain premises remain explicit. -/
def fieldsSourceAeVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- Source variance conclusions for the original almost-surely continuous state;
noise and loading integral-domain premises remain explicit. -/
def fieldsSourceAeConditionalVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → 0 ≤ leftEnd t ps → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)

open ProbabilityTheory in
/-- Source covariance conclusions transferred to the original almost-surely continuous state,
with the original noise and loading integral-domain conditions explicit. -/
def fieldsSourceAeCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ j) (x0 j) (ps.map fun p => (p.1 j,p.2))
    let J := Finset.univ.filter fun j =>
      (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < (x0 j : ℝ))
    (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- Conditional source covariance conclusions transferred to the original almost-surely continuous state,
with the original noise and loading integral-domain conditions explicit. -/
def fieldsSourceAeConditionalCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → 0 ≤ leftEnd t ps → H0238 αf t ps →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D →
        (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        let q := fun j => varianceFlow (θ j) (stateR X (leftEnd t ps) ω j)
          (ps.map fun p => (p.1 j,p.2))
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
            (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))
        (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
        (∀ i k, ProbabilityTheory.covariance (fun v => v i) (fun v => v k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- Source mean conclusions transferred to the original almost-surely continuous state,
with the original noise and loading integral-domain conditions explicit. -/
def fieldsSourceAeMeanStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (∀ n, Integrable (fun ω => V ω n) S.μ) ∧
    (∀ s : ℝ≥0, s ≤ t → ∀ n,
      S.μ[fun ω => V ω n | S.ℱ s] =ᵐ[S.μ] fun ω =>
        C n + A.mulVec (fun j => lflow (θ j) (X s ω j) ((t : ℝ)-s)) n) ∧
    (∀ n, (∫ ω, V ω n ∂S.μ) = C n + A.mulVec (fun j => lflow (θ j) (x0 j) t) n)

open ProbabilityTheory in
/-- Published three-factor support conclusions transferred to the original almost-surely continuous state,
with the original noise and loading integral-domain conditions explicit. -/
def fieldsSourceAeColumnStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => (fun _ => 1)) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ0235 X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin 3 → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
      (∃ a h qs, ps = (a,h)::qs ∧ (∀ j, 0 < a j) ∧ 0 < h) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (S.μ.map V).support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ (S.μ.map V).support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → (S.μ.map V) {C} = 0)

open ProbabilityTheory in
/-- Published three-factor covariance conclusions transferred to the original almost-surely continuous state,
with the original noise and loading integral-domain conditions explicit. -/
def fieldsSourceAeColumnCovarianceStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => (fun _ => 1)) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ0235 X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02311 αf →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ ps : List ((Fin 3 → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) → leftEnd t ps = 0 → H0238 αf t ps →
      (∃ a h qs, ps = (a,h)::qs ∧ (∀ j, 0 < a j) ∧ 0 < h) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ0235 j) 1 (ps.map fun p => (p.1 j,p.2))
    (∀ j, 0 < q j) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker A.transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
    m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin)

/-- Joint conditional transform of the original almost-surely continuous state. -/
def fieldsAeTransformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, Measurable (αf j)) →
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    ∀ (b : ℝ) (ps : List ((Fin d → ℝ) × ℝ)),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) →
      0 ≤ leftEnd b ps → H0238 αf b ps →
      ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X b ω j)) | filtR S.ℱ (leftEnd b ps)] =ᵐ[S.μ]
          fun ω => Real.exp (-(∑ j,
            (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * stateR X (leftEnd b ps) ω j +
              rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j))))

/-- Each factor has finitely many breakpoints on every bounded interval and is
constant on every open subinterval containing none of its breakpoints. Endpoint
values are unrestricted; the stochastic time integrals ignore finitely many points. -/
def H02316 {d : ℕ} (αf : Fin d → ℝ≥0 → ℝ) : Prop :=
  ∀ j (T : ℝ≥0), ∃ S : Finset ℝ,
    ∀ l r : ℝ, 0 ≤ l → r ≤ T → l < r →
      (∀ u ∈ S, u ∉ Set.Ioo l r) →
      ∃ c : ℝ, ∀ s : ℝ≥0, l < s → (s : ℝ) < r → αf j s = c

/-- Finite factor breakpoint sets supply the common interval partition. -/
def commonPartitionStatement : Prop :=
  ∀ (d : ℕ) (αf : Fin d → ℝ≥0 → ℝ),
    (∀ j t, 0 ≤ αf j t) → H02316 αf →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 < p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps

/-- Finite factor breakpoint sets supply the horizon partitions used by the stochastic proofs. -/
def finitePiecesStatement : Prop :=
  ∀ (d : ℕ) (αf : Fin d → ℝ≥0 → ℝ),
    (∀ j t, 0 ≤ αf j t) → H02316 αf → H02311 αf

/-- Finite factor breakpoint sets supply a common final piece with positive factor coefficients. -/
def finiteLastPieceStatement : Prop :=
  ∀ (d : ℕ) (αf : Fin d → ℝ≥0 → ℝ),
    (∀ j t, 0 ≤ αf j t) → H02316 αf → ∀ t : ℝ≥0, 0 < t →
    (∀ j, ∃ a : ℝ, a < t ∧
      ∀ s : ℝ≥0, a < s → (s : ℝ) < t → 0 < αf j s) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
      ∃ c h qs, ps = (c,h)::qs ∧ (∀ j, 0 < c j) ∧ 0 < h

open ProbabilityTheory in
/-- Source variance conclusions with the common partition constructed
from the separate finite factor breakpoint sets. -/
def fieldsFiniteSourceVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- Source conditionalvariance conclusions with the common partition constructed
from the separate finite factor breakpoint sets. -/
def fieldsFiniteSourceConditionalVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ a0 : ℝ, 0 ≤ a0 → a0 ≤ t →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = a0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)

/-- Exact support and covariance rank for the published three-factor column,
with a common positive last piece constructed from the individual factor hypotheses. -/
def fieldsFiniteSourceColumnStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => (fun _ => 1)) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ0235 X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    0 < t → (∀ j, ∃ a0 : ℝ, a0 < t ∧
      ∀ s : ℝ≥0, a0 < s → (s : ℝ) < t → 0 < αf j s) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ((S.μ.map V).support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ (S.μ.map V).support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → (S.μ.map V) {C} = 0)) ∧
    ∃ q : Fin 3 → ℝ, (∀ j, 0 < q j) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker A.transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
    m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin)

open ProbabilityTheory in
/-- Source mean with finite factor partitions assembled internally. -/
def fieldsFiniteSourceMeanStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (∀ n, Integrable (fun ω => V ω n) S.μ) ∧
    (∀ s : ℝ≥0, s ≤ t → ∀ n,
      S.μ[fun ω => V ω n | S.ℱ s] =ᵐ[S.μ] fun ω =>
        C n + A.mulVec (fun j => lflow (θ j) (X s ω j) ((t : ℝ)-s)) n) ∧
    (∀ n, (∫ ω, V ω n ∂S.μ) = C n + A.mulVec (fun j => lflow (θ j) (x0 j) t) n)

open ProbabilityTheory in
/-- Source covariance with finite factor partitions assembled internally. -/
def fieldsFiniteSourceCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ j) (x0 j) (ps.map fun p => (p.1 j,p.2))
    let J := Finset.univ.filter fun j =>
      (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < (x0 j : ℝ))
    (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- Source conditionalcovariance with finite factor partitions assembled internally. -/
def fieldsFiniteSourceConditionalCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      (∀ j q, U4 S.ℱ S.μ (Standalone.ZeroMeanReversionUpstreamBridge.loadInt
        (fun n => (T n : ℝ)) a lam γ X j q)) → ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ a0 : ℝ, 0 ≤ a0 → a0 ≤ t →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = a0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D →
        (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        let q := fun j => varianceFlow (θ j) (stateR X (leftEnd t ps) ω j)
          (ps.map fun p => (p.1 j,p.2))
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
            (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))
        (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
        (∀ i k, ProbabilityTheory.covariance (fun v => v i) (fun v => v k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

/-- For an everywhere-continuous adapted state, AX-09 and compact path bounds
put every measurable locally bounded coefficient times its square root in (U4),
including the SDE noise and the source forward-rate loading integrands. -/
def continuousDomainsStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ X : ℝ≥0 → Ω → Fin d → NNReal,
      (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
      (∀ t, Measurable[S.ℱ t] (X t)) →
    (∀ j, IsStronglyPredictable S.ℱ (fun s ω => Real.sqrt (X s ω j))) ∧
    (∀ j (K : ℝ≥0 → ℝ), Measurable K →
      (∀ T : ℝ≥0, ∃ C : ℝ, ∀ s, s ≤ T → |K s| ≤ C) →
      U4 S.ℱ S.μ (fun s ω => K s * Real.sqrt (X s ω j))) ∧
    ∀ (N : ℕ) (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ),
      H02315 T a lam → ∀ j q, U4 S.ℱ S.μ
        (Standalone.ZeroMeanReversionUpstreamBridge.loadInt (fun n => (T n : ℝ)) a lam γ X j q)

open ProbabilityTheory in
/-- The source variance conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (V =ᵐ[S.μ] fun ω => C + A.mulVec (fun j => (X t ω j : ℝ))) ∧
    S.μ.map V = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j))).map
      (fun y => C + A.mulVec y) ∧
    C02310 A C θ (fun j => (x0 j : ℝ)) (fun j => ps.map fun p => (p.1 j,p.2)) (S.μ.map V)

open ProbabilityTheory in
/-- The source conditional variance conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceConditionalVarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ a0 : ℝ, 0 ≤ a0 → a0 ≤ t →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = a0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D → (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        κ ω = (Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2))
          (stateR X (leftEnd t ps) ω j))).map (fun y => C + A.mulVec y) ∧
        C02310 A C θ (fun j => (stateR X (leftEnd t ps) ω j : ℝ))
          (fun j => ps.map fun p => (p.1 j,p.2)) (κ ω)

open ProbabilityTheory in
/-- The source column conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceColumnStatement : Prop :=
  ∀ (N m : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin 3 → Fin S.m) (αf : Fin 3 → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin 3 → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => (fun _ => 1)) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ0235 X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin 3 → ℝ → ℝ) (γ : Fin 3 → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin 3 → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    0 < t → (∀ j, ∃ a0 : ℝ, a0 < t ∧
      ∀ s : ℝ≥0, a0 < s → (s : ℝ) < t → 0 < αf j s) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ0235 j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ0235 j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ0235 j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ((S.μ.map V).support = Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C ∧
    IsClosed (Standalone.ZeroMeanReversionVarianceSupport.cone0154 A C) ∧
    (affineSpan ℝ (S.μ.map V).support : Set (Fin m → ℝ)) =
      (fun y => C+y) '' (LinearMap.range A.mulVecLin : Set (Fin m → ℝ)) ∧
    A.rank ≤ 3 ∧
    ((∃ j : Fin 3, 0 < θ0235 j ∧ ∃ i, A i j ≠ 0) → (S.μ.map V) {C} = 0)) ∧
    ∃ q : Fin 3 → ℝ, (∀ j, 0 < q j) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker A.transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = A.rank ∧ A.rank ≤ 3 ∧
    m - 3 ≤ Module.finrank ℝ (LinearMap.ker A.transpose.mulVecLin)

open ProbabilityTheory in
/-- The source mean conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceMeanStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    (∀ n, Integrable (fun ω => V ω n) S.μ) ∧
    (∀ s : ℝ≥0, s ≤ t → ∀ n,
      S.μ[fun ω => V ω n | S.ℱ s] =ᵐ[S.μ] fun ω =>
        C n + A.mulVec (fun j => lflow (θ j) (X s ω j) ((t : ℝ)-s)) n) ∧
    (∀ n, (∫ ω, V ω n ∂S.μ) = C n + A.mulVec (fun j => lflow (θ j) (x0 j) t) n)

open ProbabilityTheory in
/-- The source covariance conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = 0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    let q := fun j => varianceFlow (θ j) (x0 j) (ps.map fun p => (p.1 j,p.2))
    let J := Finset.univ.filter fun j =>
      (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧ (0 < θ j ∨ 0 < (x0 j : ℝ))
    (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
    (∀ i k, ProbabilityTheory.covariance (fun ω => V ω i) (fun ω => V ω k) S.μ =
      Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
    LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
      LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
    (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

open ProbabilityTheory in
/-- The source conditional covariance conclusions for a selected continuous adapted version.
Noise and loading integral-domain conditions and the common partitions are derived. -/
def fieldsContinuousSourceConditionalCovarianceStatement : Prop :=
  ∀ (N m d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k kw : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ (T : Fin N → ℝ≥0) (a lam : Fin d → ℝ → ℝ) (γ : Fin d → ℕ → ℝ) (c : ℝ),
      H02315 T a lam →
      ∀ ρ : Fin d → ℝ → ℝ,
      (∀ j u, -1 ≤ ρ j u ∧ ρ j u ≤ 1) →
      (∀ j s, S.c (kw j) (kw j) s = 1) → (∀ j s, S.c (kw j) (k j) s = ρ j s) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (kw j) s = 0) →
      (∀ i j, i ≠ j → ∀ s, S.c (kw i) (k j) s = 0) →
    ∀ (rows : Fin m → Fin N) (t : ℝ≥0), (∀ n, t ≤ T (rows n)) →
    ∀ a0 : ℝ, 0 ≤ a0 → a0 ≤ t →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd t ps = a0 ∧ H0238 αf t ps ∧
    let g := fun n => Standalone.ZeroMeanReversionUpstreamBridge.gJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let b := fun n => Standalone.ZeroMeanReversionUpstreamBridge.bJump (fun n => (T n : ℝ)) a lam γ (rows n)
    let Tr := fun n => (T (rows n) : ℝ)
    let K := Standalone.StochasticMeetingVariance.kernel0136 g b ρ
      (fun j s => αf j (Real.toNNReal s)) (fun j _ => θ j) Tr
    let A := Standalone.StochasticMeetingVariance.A K (fun j _ => θ j) Tr t
    let C := Standalone.StochasticMeetingVariance.C K (fun j _ => θ j) Tr t
    let Y := fun n => Standalone.ZeroMeanReversionUpstreamBridge.jumpSrc S kw (fun n => (T n : ℝ)) a lam γ X c (rows n)
    let V := Standalone.ZeroMeanReversionVarianceSupport.V0150 (S.ℱ t) S.μ Y
    ∃ κ : Kernel Ω (Fin m → ℝ), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd t ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd t ps)] D →
        (S.μ.restrict D).map V = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ,
        let q := fun j => varianceFlow (θ j) (stateR X (leftEnd t ps) ω j)
          (ps.map fun p => (p.1 j,p.2))
        let J := Finset.univ.filter fun j =>
          (∃ p ∈ ps, 0 < p.1 j ∧ 0 < p.2) ∧
            (0 < θ j ∨ 0 < (stateR X (leftEnd t ps) ω j : ℝ))
        (∀ j, 0 ≤ q j ∧ (0 < q j ↔ j ∈ J)) ∧
        (∀ i k, ProbabilityTheory.covariance (fun v => v i) (fun v => v k) (κ ω) =
          Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q i k) ∧
        LinearMap.ker (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).mulVecLin =
          LinearMap.ker (activeCols A J).transpose.mulVecLin ∧
        (Standalone.ZeroMeanReversionVarianceSupport.cov0157 A q).rank = (activeCols A J).rank

/-- Finite piecewise-constant coefficients are measurable and bounded on each
bounded horizon, including their arbitrary values at the finitely many breakpoints. -/
def coefficientRegularityStatement : Prop :=
  ∀ (d : ℕ) (αf : Fin d → ℝ≥0 → ℝ), (∀ j t, 0 ≤ αf j t) → H02316 αf →
    (∀ j, Measurable (αf j)) ∧
    (∀ j (T : ℝ≥0), ∃ C : ℝ, ∀ s, s ≤ T → |αf j s| ≤ C)

open ProbabilityTheory in
/-- The joint transform for a selected continuous state version, with
coefficient regularity, integral-domain membership and common partitions derived. -/
def fieldsContinuousTransformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps ∧
      ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X b ω j)) | filtR S.ℱ (leftEnd b ps)] =ᵐ[S.μ]
          fun ω => Real.exp (-(∑ j,
            (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * stateR X (leftEnd b ps) ω j +
              rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j))))

open ProbabilityTheory in
/-- The joint law for a selected continuous state version, with
coefficient regularity, integral-domain membership and common partitions derived. -/
def fieldsContinuousLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ ω j, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps ∧
    (∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd b ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd b ps)] D →
        (S.μ.restrict D).map (stateR X b) = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ, (κ ω).map (fun y j => (y j : ℝ)) =
        Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (stateR X (leftEnd b ps) ω j))) ∧
    (leftEnd b ps = 0 → S.μ.map (fun ω j => (stateR X b ω j : ℝ)) =
      Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j)))

open ProbabilityTheory in
/-- The joint transform for the original almost-surely continuous state, with
coefficient regularity and common partitions derived. The original noise integrand
remains in (U4), as required by the revised Claim 023 Statement. -/
def fieldsFiniteTransformStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps ∧
      ∀ l : Fin d → ℝ, (∀ j, 0 ≤ l j) →
        S.μ[fun ω => Real.exp (-(∑ j, l j * stateR X b ω j)) | filtR S.ℱ (leftEnd b ps)] =ᵐ[S.μ]
          fun ω => Real.exp (-(∑ j,
            (piFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j) * stateR X (leftEnd b ps) ω j +
              rhoFlow (θ j) (ps.map fun p => (p.1 j, p.2)) (l j))))

open ProbabilityTheory in
/-- The joint law for the original almost-surely continuous state, with
coefficient regularity and common partitions derived. The original noise integrand
remains in (U4), as required by the revised Claim 023 Statement. -/
def fieldsFiniteLawStatement : Prop :=
  ∀ (d : ℕ) (Ω : Type) (mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω), Predictability S.ℱ →
    ∀ (k : Fin d → Fin S.m) (θ : Fin d → ℝ) (αf : Fin d → ℝ≥0 → ℝ)
    (X : ℝ≥0 → Ω → Fin d → NNReal) (x0 : Fin d → NNReal),
    (∀ j j' s, S.c (k j) (k j') s = if j = j' then 1 else 0) →
    (∀ j, 0 ≤ θ j) →
    (∀ j, ∀ᵐ ω ∂S.μ, Continuous fun t => (X t ω j : ℝ)) →
    (∀ t, Measurable[S.ℱ t] (X t)) →
    (X 0 =ᵐ[S.μ] fun _ => x0) → (∀ j, x0 j ≤ 1) →
    (∀ j, U4 S.ℱ S.μ (fun s ω => αf j s * Real.sqrt (X s ω j))) →
    (∀ j, ∀ᵐ ω ∂S.μ, ∀ t, (X t ω j : ℝ) =
      X 0 ω j + S.I (k j) (fun s ω => αf j s * Real.sqrt (X s ω j)) t ω +
        ∫ s in (0 : ℝ)..t, Kdrv θ X j (Real.toNNReal s) ω) →
    (∀ t j, Integrable (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, (X s ω j : ℝ)^2) S.μ) →
    H02316 αf → (∀ j t, 0 ≤ αf j t) →
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    ∃ ps : List ((Fin d → ℝ) × ℝ),
      (∀ p ∈ ps, (∀ j, 0 ≤ p.1 j) ∧ 0 ≤ p.2) ∧
      leftEnd b ps = a ∧ H0238 αf b ps ∧
    (∃ κ : Kernel Ω (Fin d → ℝ≥0), IsMarkovKernel κ ∧
      (∀ B, MeasurableSet B → Measurable[filtR S.ℱ (leftEnd b ps)] (fun ω => κ ω B)) ∧
      (∀ D, MeasurableSet[filtR S.ℱ (leftEnd b ps)] D →
        (S.μ.restrict D).map (stateR X b) = κ ∘ₘ S.μ.restrict D) ∧
      ∀ᵐ ω ∂S.μ, (κ ω).map (fun y j => (y j : ℝ)) =
        Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (stateR X (leftEnd b ps) ω j))) ∧
    (leftEnd b ps = 0 → S.μ.map (fun ω j => (stateR X b ω j : ℝ)) =
      Measure.pi (fun j => L023 (θ j) (ps.map fun p => (p.1 j,p.2)) (x0 j)))

end ItoStep

def statement : Prop := riccatiStatement ∧ translatedConeStatement ∧
  chiSquareParameterStatement ∧ sourceColumnStatement ∧ compositionStatement ∧ atomStatement ∧
  varianceStatement ∧ generatorStatement ∧ extensionStatement ∧ itoStatement ∧
  localizationStatement ∧ conditionalTransformStatement ∧ pieceCompositionStatement ∧
  itoIncrementStatement ∧ onePieceStatement ∧ independenceStatement ∧ atomMassStatement ∧
  meanStatement ∧ secondMomentStatement ∧ conditionalLawStatement ∧
  conditionalMeanStatement ∧ conditionalVarianceStatement ∧ piecewiseVarianceStatement ∧
  conditionalPiecewiseVarianceStatement ∧ piecewiseCovarianceStatement ∧
  conditionalPiecewiseCovarianceStatement ∧ sourceCovarianceStatement ∧ coordinateLawStatement ∧
  piecewiseJointLawStatement ∧ piecewiseImageLawStatement ∧ conditionalPiecewiseLawStatement ∧
  sourcePiecewiseSupportStatement ∧ lowerEndpointStatement ∧ fieldsTransformStatement ∧ fieldsLawStatement ∧ fieldsMeetingVarianceStatement ∧ fieldsConditionalMeetingVarianceStatement ∧ fieldsStateMeanStatement ∧ fieldsCoefficientStatement ∧ fieldsIncrementStatement ∧ fieldsKernelIsometryStatement ∧ backwardWeightRegularityStatement ∧ kernelIdentificationStatement ∧ fieldsConditionalMeanStatement ∧
  fieldsWeightedIntegralStatement ∧ fieldsMomentAssemblyStatement ∧ productTerminalStatement ∧
  fieldsCenteredStatement ∧ fieldsConstructedMomentsStatement ∧ fieldsConstructedVarianceStatement ∧
  fieldsConstructedConditionalVarianceStatement ∧ fieldsShortRateJumpStatement ∧
  fieldsSourceVarianceStatement ∧ fieldsSourceConditionalVarianceStatement ∧ fieldsSourceColumnStatement ∧
  stateMomentsStatement ∧ fieldsSourceCovarianceStatement ∧ fieldsSourceConditionalCovarianceStatement ∧
  fieldsSourceColumnCovarianceStatement ∧ fieldsSourceMeanStatement ∧ fieldsPremisesStatement ∧
  continuousVersionStatement ∧ fieldsVersionStatement ∧ fieldsAeLawStatement ∧
  sourceVersionStatement ∧ fieldsSourceAeVarianceStatement ∧ fieldsSourceAeConditionalVarianceStatement ∧
  fieldsSourceAeCovarianceStatement ∧ fieldsSourceAeConditionalCovarianceStatement ∧ fieldsSourceAeMeanStatement ∧ fieldsSourceAeColumnStatement ∧ fieldsSourceAeColumnCovarianceStatement ∧ fieldsAeTransformStatement ∧
  commonPartitionStatement ∧ finitePiecesStatement ∧ finiteLastPieceStatement ∧
  fieldsFiniteSourceVarianceStatement ∧ fieldsFiniteSourceConditionalVarianceStatement ∧ fieldsFiniteSourceColumnStatement ∧
  fieldsFiniteSourceMeanStatement ∧ fieldsFiniteSourceCovarianceStatement ∧ fieldsFiniteSourceConditionalCovarianceStatement ∧
  continuousDomainsStatement ∧ fieldsContinuousSourceVarianceStatement ∧ fieldsContinuousSourceConditionalVarianceStatement ∧ fieldsContinuousSourceColumnStatement ∧ fieldsContinuousSourceMeanStatement ∧ fieldsContinuousSourceCovarianceStatement ∧ fieldsContinuousSourceConditionalCovarianceStatement ∧
  coefficientRegularityStatement ∧ fieldsContinuousTransformStatement ∧ fieldsContinuousLawStatement ∧
  fieldsFiniteTransformStatement ∧ fieldsFiniteLawStatement

end Standalone.PositiveMeanReversionSupport
