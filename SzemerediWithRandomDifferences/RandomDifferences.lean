/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli
public import SzemerediWithRandomDifferences.Cover
import Mathlib.Analysis.Complex.ExponentialBounds
import SzemerediWithRandomDifferences.Ackermann
import SzemerediWithRandomDifferences.ArithmeticKakeya.Threshold
import SzemerediWithRandomDifferences.SetBernoulli

/-!
# Szemerédi's theorem with random differences

Let `D` be a `p`-random subset of `{1, …, n}`, let `c = ArithmeticKakeya.c` and let
`C = ack (4 * k + 2) (k + ⌈2 / δ⌉₊)`, a value of the Ackermann function. If
`p ≥ C * n ^ (-c / log (log k))`, then with probability at least
`1 - exp (-n ^ (1 - c / log (log k)))` every subset of `{1, …, n}` with at least `δ * n`
elements contains a `k`-term arithmetic progression with common difference in `D`. This is
Theorem 1.1 of Dahia, *Szemerédi's theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859), with explicit constants.

The proof is a union bound over the small cover of `RandomDifferences.exists_isCover_card_le`.
A set `S` that avoids `D` contains a member `F` of the cover, and `D` misses the `γ * n` common
differences of the progressions in `F` with probability at most `exp (-p * γ * n)`. No lower
bound on `n` is assumed, since `p ≤ 1` forces `n ≥ C`.

## Main statements

* `RandomDifferences.setBernoulli_isAvoidable_le_exp`: the main theorem.
-/

public section

namespace RandomDifferences

open ArithmeticKakeya Combinatorics.ArithmeticProgression Finset MeasureTheory ProbabilityTheory
  unitInterval

/-- Some subset of `{1, …, n}` with at least `δ * n` elements contains no `k`-term arithmetic
progression with common difference in `D`. -/
def IsAvoidable (k : ℕ) (δ : ℝ) (n : ℕ) (D : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧ Disjoint (commonDiffs k S) D

lemma isAvoidable_iff {k n : ℕ} {δ : ℝ} {D : Set ℕ} :
    IsAvoidable k δ n D ↔ ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧
      ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S := by
  simp [IsAvoidable, disjoint_commonDiffs_nat]

/-- The union bound over a cover. -/
lemma setBernoulli_isAvoidable_le {k n : ℕ} {δ b : ℝ} (p : I) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : IsCover 𝓕 {S | S ⊆ Icc 1 n ∧ δ * n ≤ #S})
    (hb : ∀ F ∈ 𝓕, b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard) :
    setBer(Set.Icc 1 n, p) {D | IsAvoidable k δ n D} ≤
      ENNReal.ofReal (#𝓕 * Real.exp (-(p * b))) := by
  have hmono : {D | IsAvoidable k δ n D} ⊆ ⋃ F ∈ 𝓕, {D | Disjoint (commonDiffs k F) D} := by
    rintro D ⟨S, hS, hSδ, hD⟩
    obtain ⟨F, hF, hFS⟩ := h𝓕.exists_subset ⟨hS, hSδ⟩
    rw [Set.mem_iUnion₂]
    exact ⟨F, hF, Set.disjoint_of_subset_left (commonDiffs_mono k fun _ hx ↦ hFS hx) hD⟩
  apply (measure_mono hmono).trans
  apply (measure_biUnion_finset_le _ _).trans
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro F hF
  have hfin := (Set.finite_Icc 1 n).inter_of_right (commonDiffs k F)
  apply setBernoulli_disjoint_le p hfin.coe_toFinset.subset
  rw [← Set.ncard_eq_toFinset_card _ hfin]
  exact hb F hF

lemma setBernoulli_isAvoidable_le_of_coverBound_le {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : coverBound k δ ≤ n) {p : I}
    (hp : 3 / coverDensity k δ * n ^ (-(c / Real.log (Real.log k))) ≤ p) :
    setBer(Set.Icc 1 n, p) {D | IsAvoidable k δ n D} ≤
      ENNReal.ofReal ((k * modulus k + 1) *
        (n * Real.exp (-(2 * n ^ (1 - c / Real.log (Real.log k)))))) := by
  obtain ⟨𝓕, h𝓕, hcard, hb⟩ := exists_isCover_card_le hk hδ hn
  have hγ := coverDensity_pos k δ
  have hn0 : (0 : ℝ) < n := mod_cast pos_of_coverBound_le hn
  rw [div_mul_eq_mul_div, div_le_iff₀ hγ] at hp
  have hpn := mul_le_mul_of_nonneg_right hp hn0.le
  rw [mul_assoc, ← Real.rpow_add_one hn0.ne', neg_add_eq_sub, mul_assoc] at hpn
  apply (setBernoulli_isAvoidable_le p h𝓕 hb).trans
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul hcard (Real.exp_le_exp.2 (neg_le_neg hpn)) (Real.exp_nonneg _)
    (by positivity)).trans_eq
  rw [mul_assoc, mul_assoc, ← Real.exp_add]
  ring_nf

private lemma two_mul_log_le_rpow {x θ : ℝ} (hx : 0 < x) (hθ : 22 / 25 ≤ θ) :
    2 * Real.log x ≤ x ^ θ := by
  have hy := Real.rpow_pos_of_pos hx θ
  have h := Real.log_le_sub_one_of_pos (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_rpow hx,
    sub_le_sub_iff_right, le_div_iff₀ (Real.exp_pos 1)] at h
  rcases le_or_gt (Real.log x) 0 with hl | hl
  · linarith
  · linarith [mul_nonneg (sub_nonneg.2 hθ) hl.le, mul_nonneg (mul_nonneg (by linarith : 0 ≤ θ)
      hl.le) (by linarith [Real.exp_one_gt_d9] : 0 ≤ Real.exp 1 - 5 / 2)]

private lemma mul_mul_exp_neg_le {a θ : ℝ} {n : ℕ} (han : a ≤ n) (hn : 0 < n)
    (hθ : 22 / 25 ≤ θ) : a * (n * Real.exp (-(2 * n ^ θ))) ≤ Real.exp (-n ^ θ) := by
  have hn' : (0 : ℝ) < n := mod_cast hn
  have h := Real.exp_le_exp.2 (two_mul_log_le_rpow hn' hθ)
  rw [two_mul, Real.exp_add, Real.exp_log hn'] at h
  rw [← mul_assoc]
  refine (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right han hn'.le).trans h)
    (Real.exp_nonneg _)).trans_eq ?_
  rw [← Real.exp_add]
  ring_nf

/-- A probability `p` with `C * n ^ (-γ) ≤ p` exists only if `C ≤ n`. -/
private lemma le_of_mul_rpow_neg_le {C n : ℕ} {γ : ℝ} {p : I} (hn : 0 < n) (hγ : γ ≤ 1)
    (hp : C * (n : ℝ) ^ (-γ) ≤ p) : C ≤ n := by
  have hn1 : (1 : ℝ) ≤ n := mod_cast hn
  have hpos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hn1) γ
  rw [Real.rpow_neg (Nat.cast_nonneg n), mul_inv_le_iff₀ hpos] at hp
  rw [← Nat.cast_le (α := ℝ)]
  apply hp.trans
  apply (mul_le_of_le_one_left hpos.le (le_one p)).trans
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hγ).trans_eq (Real.rpow_one _)

/-- **Szemerédi's theorem with random differences.** Let `k ≥ 3`, `δ > 0` and
`C = ack (4 * k + 2) (k + ⌈2 / δ⌉₊)`. Let `D` be a `p`-random subset of `{1, …, n}`, where
`p ≥ C * n ^ (-c / log (log k))`. The probability that some subset of `{1, …, n}` with at least
`δ * n` elements contains no `k`-term arithmetic progression with common difference in `D` is at
most `exp (-n ^ (1 - c / log (log k)))`. -/
theorem setBernoulli_isAvoidable_le_exp {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    {p : I} (hp : ack (4 * k + 2) (k + ⌈2 / δ⌉₊) * (n : ℝ) ^ (-c / Real.log (Real.log k)) ≤ p) :
    setBer(Set.Icc 1 n, p) {D | IsAvoidable k δ n D} ≤
      ENNReal.ofReal (Real.exp (-n ^ (1 - c / Real.log (Real.log k)))) := by
  have hc := c_div_log_log_le hk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Real.zero_rpow (by linarith), neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  rw [neg_div] at hp
  have hCn := le_of_mul_rpow_neg_le hn (by linarith) hp
  apply (setBernoulli_isAvoidable_le_of_coverBound_le hk hδ ((coverBound_le_ack hk δ).trans hCn)
    ((mul_le_mul_of_nonneg_right (three_div_coverDensity_le hk δ)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans hp)).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_mul_exp_neg_le (mod_cast (mul_modulus_add_one_le_ack (by grind)
    (Nat.le_add_right _ _)).trans hCn) hn (by linarith)

end RandomDifferences
