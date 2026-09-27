import Standalone.SharefFilipovicResidual
import Standalone.ZeroMeanReversionUpstreamBridge

/-! # Claim 034 (a): the block's drift and volatility by Itô's formula

The block's parameter is an Itô process `Z^i_t = z0_i + ∑_k I_k(H_{ik})(t) + ∫_0^t K_i`, with (U4)
integrands `H_{ik}` on the drivers and locally integrable drifts `K_i` (in (34.2) the block
drivers are `W^B`, with `H_{ik} = σ_Z^{ik}` and `K_i = b_i`). The block part of the curve at a
maturity `T` is `F(T − t, Z_t) = ∑_i Z^i_t φ_i(T − t)`, linear in `Z`.

`blockItoStatement` is Itô's formula (AX-05) for it, coordinate by coordinate: the integrands
`φ_i(T − ·) H_{ik}` are in (U4), and almost surely, for every `t`,
`F(T − t, Z_t) = F(T, z0) + ∑_i ∫_0^t (−Z^i_s φ_i'(T − s) + K_i(s) φ_i(T − s)) ds
  + ∑_i ∑_k I_k(φ_i(T − ·) H_{ik})(t)`.
The drift integrands sum to `D^B(s, T) = −∂_x F(T − s, Z_s) + ∑_i b_i φ_i(T − s)` and the
volatility integrands to `σ^B(s, T) = ∑_i φ_i(T − s) σ_Z^{i,·}`, which are the forms used in
`SharefFilipovicSplit`. Since `F` is linear in `z`, the second-order term vanishes.
-/

open MeasureTheory
open scoped NNReal
namespace Standalone.SharefFilipovicIto
open Standalone.ZeroMeanReversionUpstreamBridge Standalone.SharefFilipovicResidual

def blockItoStatement : Prop := ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (S : ItoCalculus Ω)
  (β : ℝ) (n₁ n₂ : ℕ) (T : ℝ) (Z : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ≥0 → Ω → ℝ)
  (z0 : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ)
  (H : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → Fin S.m → ℝ≥0 → Ω → ℝ)
  (K : Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → ℝ≥0 → Ω → ℝ),
  (∀ i k, U4 S.ℱ S.μ (H i k)) → (∀ i, LocallyIntegrableDrift S.ℱ S.μ (K i)) →
  (∀ i, ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0, Z i t ω =
    z0 i + ∑ k, S.I k (H i k) t ω + ∫ s in (0:ℝ)..t, K i (Real.toNNReal s) ω) →
  (∀ i k, U4 S.ℱ S.μ (fun s ω => phi034 β n₁ n₂ i (T - s) * H i k s ω)) ∧
  ∀ᵐ ω ∂S.μ, ∀ t : ℝ≥0,
    F034 β n₁ n₂ (fun i => Z i t ω) (T - t) = F034 β n₁ n₂ z0 T +
      ∑ i, (∫ s in (0:ℝ)..t, (-(Z i (Real.toNNReal s) ω * deriv (phi034 β n₁ n₂ i) (T - s)) +
        K i (Real.toNNReal s) ω * phi034 β n₁ n₂ i (T - s))) +
      ∑ i, ∑ k, S.I k (fun s ω => phi034 β n₁ n₂ i (T - s) * H i k s ω) t ω

def statement : Prop := blockItoStatement

end Standalone.SharefFilipovicIto
