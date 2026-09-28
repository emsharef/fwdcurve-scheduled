import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-! # Claim 054 (54-S): sectioning on a product with a right-continuous filtration

Unconditional. `(E₁, μ₁)` and `(E₂, μ₂)` are probability spaces, and `G` is a filtration on `E₂`,
indexed by `ℝ`. The conventions are those of Claims 018 and 020:
* `aug μ G` is the usual augmentation of `G` under `μ`, on the completed space
  `NullMeasurableSpace E μ`: `G⁺_t = ⋂_{s > t} (G_s ∨ 𝒩_μ)`, where `G_s ∨ 𝒩_μ`
  (`eventuallyMeasurableSpace (G s) (ae μ)`) consists of the sets almost everywhere equal to a
  `G_s`-measurable set;
* `prodFilt G` is the product filtration `σ(E₁) ⊗ G_t` on `E₁ × E₂`, and `F⁺ = aug (μ₁ ⊗ μ₂)
  (prodFilt G)`;
* `times μ G A S` are the stopping times of `aug μ G` with values in `[A, S]`;
* `value₂` is `sup_{ρ G⁺-stopping} ∫ Π(ρ(e₂), e₂) dμ₂`, and `valueProd` is
  `sup_{τ F⁺-stopping} ∫ Π(τ(e₁, e₂), e₂) d(μ₁ ⊗ μ₂)`, each under the completed measure.

`sectioningStatement`, (54-S): let `Pay : ℝ × E₂ → ℝ` be Borel with `|Pay(t, e)| ≤ D(e)` for `t ∈ [A, S]`
and `D` integrable. Then both suprema are of sets bounded above, and they are equal. The claim also
asks that `Pay(t, ·)` be `G_t`-measurable. The argument does not use this, so it is not assumed.
-/

open MeasureTheory Set

namespace Standalone.ContinuousAggregationSectioning

/-- The usual augmentation `G⁺_t = ⋂_{s > t} (G_s ∨ 𝒩_μ)` on the completed space. -/
noncomputable def aug {E : Type*} [m : MeasurableSpace E] (μ : Measure E) (G : Filtration ℝ m) :
    Filtration ℝ (inferInstance : MeasurableSpace (NullMeasurableSpace E μ)) where
  seq t := ⨅ s ∈ Ioi t, eventuallyMeasurableSpace (G s) (ae μ)
  mono' := fun _ _ htt' => le_iInf₂ fun s hs => iInf₂_le s (lt_of_le_of_lt htt' hs)
  le' := fun t => (iInf₂_le (t + 1) (show t < t + 1 by linarith)).trans
    fun _ ⟨B, hB, hAB⟩ => ⟨B, G.le _ B hB, hAB⟩

/-- The product filtration `σ(E₁) ⊗ G_t` on `E₁ × E₂`. -/
def prodFilt {E₁ E₂ : Type*} [m₁ : MeasurableSpace E₁] [m₂ : MeasurableSpace E₂]
    (G : Filtration ℝ m₂) : Filtration ℝ (inferInstance : MeasurableSpace (E₁ × E₂)) where
  seq t := MeasurableSpace.comap Prod.fst m₁ ⊔ MeasurableSpace.comap Prod.snd (G t)
  mono' := fun _ _ hst => sup_le_sup le_rfl (MeasurableSpace.comap_mono (G.mono hst))
  le' := fun t => sup_le_sup le_rfl (MeasurableSpace.comap_mono (G.le t))

/-- The stopping times of `aug μ G` with values in `[A, S]`. -/
def times {E : Type*} [m : MeasurableSpace E] (μ : Measure E) (G : Filtration ℝ m) (A S : ℝ) :
    Set (NullMeasurableSpace E μ → ℝ) :=
  {τ | (∀ e, τ e ∈ Icc A S) ∧ IsStoppingTime (aug μ G) (fun e => (τ e : WithTop ℝ))}

/-- `sup_{ρ G⁺-stopping} ∫ Π(ρ(e₂), e₂) dμ₂`. -/
noncomputable def value₂ {E₂ : Type*} [m₂ : MeasurableSpace E₂] (μ₂ : Measure E₂)
    (G : Filtration ℝ m₂) (A S : ℝ) (Pay : ℝ × E₂ → ℝ) : ℝ :=
  sSup ((fun ρ => ∫ e, Pay (ρ e, e) ∂μ₂.completion) '' times μ₂ G A S)

/-- `sup_{τ F⁺-stopping} ∫ Π(τ(e₁, e₂), e₂) d(μ₁ ⊗ μ₂)`. -/
noncomputable def valueProd {E₁ E₂ : Type*} [MeasurableSpace E₁] [m₂ : MeasurableSpace E₂]
    (μ₁ : Measure E₁) (μ₂ : Measure E₂) (G : Filtration ℝ m₂) (A S : ℝ) (Pay : ℝ × E₂ → ℝ) : ℝ :=
  sSup ((fun τ => ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion) ''
    times (μ₁.prod μ₂) (prodFilt G) A S)

def sectioningStatement : Prop := ∀ (E₁ E₂ : Type) [MeasurableSpace E₁] [m₂ : MeasurableSpace E₂]
  (μ₁ : Measure E₁) (μ₂ : Measure E₂) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  (G : Filtration ℝ m₂) (A S : ℝ), A ≤ S →
  ∀ (Pay : ℝ × E₂ → ℝ) (D : E₂ → ℝ), Measurable Pay → Measurable D → Integrable D μ₂ →
    (∀ t ∈ Icc A S, ∀ e, |Pay (t, e)| ≤ D e) →
    BddAbove ((fun ρ => ∫ e, Pay (ρ e, e) ∂μ₂.completion) '' times μ₂ G A S) ∧
    BddAbove ((fun τ => ∫ e, Pay (τ e, (e : E₁ × E₂).2) ∂(μ₁.prod μ₂).completion) ''
      times (μ₁.prod μ₂) (prodFilt G) A S) ∧
    valueProd μ₁ μ₂ G A S Pay = value₂ μ₂ G A S Pay

def statement : Prop := sectioningStatement

end Standalone.ContinuousAggregationSectioning
