/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Random sets avoiding a finite set

A `p`-random subset of `u` is disjoint from a finite set `T ⊆ u` with probability
`(1 - p) ^ #T`, which is at most `exp (-p * #T)`.
-/

public section

namespace ProbabilityTheory

open MeasureTheory unitInterval
open scoped ENNReal Finset

variable {ι : Type*}

lemma setBernoulli_disjoint (u : Set ι) (p : I) {T : Finset ι} (hT : (T : Set ι) ⊆ u) :
    setBer(u, p) {D | Disjoint D (T : Set ι)} = (toNNReal (σ p) : ℝ≥0∞) ^ #T := by
  have h : (fun q : ι → Prop ↦ {i | q i}) ⁻¹' {D | Disjoint D (T : Set ι)} =
      (T : Set ι).pi fun _ ↦ {False} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.disjoint_left, Set.mem_pi,
      Set.mem_singleton_iff, Finset.mem_coe]
    grind
  rw [setBernoulli_apply', h, Measure.infinitePi_pi _ (fun _ _ ↦ .of_discrete)]
  apply (Finset.prod_congr rfl _).trans (Finset.prod_const _)
  intro i hi
  exact bernoulliMeasure_apply_of_notMem_of_mem p .of_discrete (by simp [hT hi]) rfl

lemma toNNReal_symm_pow_le (p : I) {m : ℕ} {b : ℝ} (hb : b ≤ m) :
    (toNNReal (σ p) : ℝ≥0∞) ^ m ≤ ENNReal.ofReal (Real.exp (-(p * b))) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [NNReal.coe_pow, coe_toNNReal, coe_symm_eq]
  apply (pow_le_pow_left₀ (sub_nonneg.2 p.2.2) (Real.one_sub_le_exp_neg p) m).trans
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  nlinarith [p.2.1]

/-- A `p`-random subset of `u` is disjoint from a set containing at least `b` elements of `u`
with probability at most `exp (-p * b)`. -/
lemma setBernoulli_disjoint_le (u : Set ι) (p : I) {A : Set ι} {T : Finset ι}
    (hT : (T : Set ι) ⊆ A ∩ u) {b : ℝ} (hb : b ≤ #T) :
    setBer(u, p) {D | Disjoint A D} ≤ ENNReal.ofReal (Real.exp (-(p * b))) := by
  refine (measure_mono ?_).trans ((setBernoulli_disjoint u p ?_).trans_le
    (toNNReal_symm_pow_le p hb))
  · intro D hD
    exact (Set.disjoint_of_subset_left (hT.trans Set.inter_subset_left) hD).symm
  · exact hT.trans Set.inter_subset_right

end ProbabilityTheory
