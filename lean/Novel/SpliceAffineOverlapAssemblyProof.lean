import Standalone.SpliceAffineOverlapAssembly
import Novel.SpliceAffineOverlapAbsorbProof
import Novel.SpliceAffineOverlapNSProof
import Novel.AnalyticPrimitiveProof

open Set
open Standalone.SpliceAffineOverlapNS Standalone.SpliceAffineOverlapAssembly
namespace Novel.SpliceAffineOverlapAssemblyProof

lemma absorbFull : absorbFullStatement := fun N m φ hφ =>
  Novel.SpliceAffineOverlapAbsorbProof.absorb N m φ hφ fun i =>
    Novel.AnalyticPrimitiveProof.primitive (φ i) (hφ i)

lemma level : levelStatement := by
  intro m sZ hs i hi k
  have hii : ∑ l, sZ i l * sZ i l = 0 := by
    by_contra h; exact hi (hs i i h).1
  have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => mul_self_nonneg (sZ i l)).1 hii k
    (Finset.mem_univ _)
  exact mul_self_eq_zero.1 this

lemma shift : shiftStatement := by
  intro β c z x
  simp [FNS, phiNS, Fin.sum_univ_three, Pi.single_apply]
  ring

theorem spliceAffineOverlapAssembly : Standalone.SpliceAffineOverlapAssembly.statement := ⟨Novel.AnalyticPrimitiveProof.analyticPrimitive, absorbFull, Novel.SpliceAffineOverlapAbsorbProof.converse, Novel.SpliceAffineOverlapNSProof.spliceAffineOverlapNS, level, shift⟩

end Novel.SpliceAffineOverlapAssemblyProof
