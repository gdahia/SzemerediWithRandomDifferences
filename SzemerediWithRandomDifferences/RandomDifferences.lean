/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli
public import SzemerediWithRandomDifferences.Fingerprint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SzemerediWithRandomDifferences.ArithmeticKakeya.Threshold
import SzemerediWithRandomDifferences.SetBernoulli

/-!
# Szemerédi's theorem with random differences

Let `D` be a `p`-random subset of `{1, …, n}`. If `p ≥ C * n ^ (-c / log (log k))`, then with
probability tending to `1` every subset of `{1, …, n}` with at least `δ * n` elements contains
a `k`-term arithmetic progression with common difference in `D`.

The proof is a union bound over the fingerprints of
`RandomDifferences.exists_card_le_forall_exists_subset_forall_le_ncard`. A set `S` that avoids
`D` contains a fingerprint `F`, and `D` misses the `γ * n` common differences of the progressions
in `F` with probability at most `exp (-p * γ * n)`.

## Main statements

* `RandomDifferences.exists_forall_tendsto_setBernoulli_isAvoidable`: the main theorem.
-/

public section

namespace RandomDifferences

open ArithmeticKakeya Combinatorics.ArithmeticProgression Filter Finset MeasureTheory
  ProbabilityTheory unitInterval
open scoped Topology

/-- Some subset of `{1, …, n}` with at least `δ * n` elements contains no `k`-term arithmetic
progression with common difference in `D`. -/
def IsAvoidable (k : ℕ) (δ : ℝ) (n : ℕ) (D : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧ Disjoint (commonDiffs k S) D

lemma isAvoidable_iff {k n : ℕ} {δ : ℝ} {D : Set ℕ} :
    IsAvoidable k δ n D ↔ ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧
      ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S := by
  simp only [IsAvoidable, disjoint_commonDiffs_nat]

/-- The union bound over a family of fingerprints. -/
lemma setBernoulli_isAvoidable_le {k n : ℕ} {δ b : ℝ} (p : I) {𝓕 : Finset (Finset ℕ)}
    (hsub : ∀ S : Finset ℕ, S ⊆ Icc 1 n → δ * n ≤ #S → ∃ F ∈ 𝓕, F ⊆ S)
    (hb : ∀ F ∈ 𝓕, b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard) :
    setBer(Set.Icc 1 n, p) {D | IsAvoidable k δ n D} ≤
      ENNReal.ofReal (#𝓕 * Real.exp (-(p * b))) := by
  have hmono : {D | IsAvoidable k δ n D} ⊆ ⋃ F ∈ 𝓕, {D | Disjoint (commonDiffs k F) D} := by
    rintro D ⟨S, hS, hSδ, hD⟩
    obtain ⟨F, hF, hFS⟩ := hsub S hS hSδ
    rw [Set.mem_iUnion₂]
    exact ⟨F, hF, Set.disjoint_of_subset_left (commonDiffs_mono k fun _ hx ↦ hFS hx) hD⟩
  apply (measure_mono hmono).trans
  apply (measure_biUnion_finset_le _ _).trans
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro F hF
  have hfin := (Set.finite_Icc 1 n).inter_of_right (commonDiffs k F)
  apply setBernoulli_disjoint_le _ p hfin.coe_toFinset.subset
  rw [← Set.ncard_eq_toFinset_card _ hfin]
  exact hb F hF

lemma setBernoulli_isAvoidable_le_ofReal {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : fingerprintBound k δ ≤ n) {p : I}
    (hp : 3 / fingerprintDensity k δ * (n : ℝ) ^ (-(c / Real.log (Real.log k))) ≤ p) :
    setBer(Set.Icc 1 n, p) {D | IsAvoidable k δ n D} ≤
      ENNReal.ofReal ((k * modulus k + 1) *
        (n * Real.exp (-(2 * (n : ℝ) ^ (1 - c / Real.log (Real.log k)))))) := by
  obtain ⟨𝓕, hcard, hsub, hb⟩ := exists_card_le_forall_exists_subset_forall_le_ncard hk hδ hn
  have hγ := fingerprintDensity_pos k hδ
  have hn0 : (0 : ℝ) < n := mod_cast pos_of_fingerprintBound_le hn
  rw [div_mul_eq_mul_div, div_le_iff₀ hγ] at hp
  have hpn := mul_le_mul_of_nonneg_right hp hn0.le
  rw [mul_assoc, ← Real.rpow_add_one hn0.ne', neg_add_eq_sub, mul_assoc] at hpn
  apply (setBernoulli_isAvoidable_le p hsub hb).trans
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul hcard (Real.exp_le_exp.2 (neg_le_neg hpn)) (Real.exp_nonneg _)
    (by positivity)).trans_eq
  rw [mul_assoc, mul_assoc, ← Real.exp_add]
  ring_nf

lemma tendsto_mul_exp_neg_rpow {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-(2 * (n : ℝ) ^ θ))) atTop (𝓝 0) := by
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero θ⁻¹ 2 two_pos).comp
    ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop)).congr ?_
  intro n
  simp only [Function.comp_apply]
  rw [Real.rpow_rpow_inv (Nat.cast_nonneg n) hθ.ne', neg_mul]

/-- Szemerédi's theorem with random differences, with explicit constants. -/
theorem tendsto_setBernoulli_isAvoidable {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {p : ℕ → I}
    (hp : ∀ᶠ n : ℕ in atTop,
      3 / fingerprintDensity k δ * (n : ℝ) ^ (-(c / Real.log (Real.log k))) ≤ p n) :
    Tendsto (fun n ↦ setBer(Set.Icc 1 n, p n) {D | IsAvoidable k δ n D}) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal ((tendsto_mul_exp_neg_rpow
    (by linarith [c_div_log_log_le hk] : 0 < 1 - c / Real.log (Real.log k))).const_mul
      ((k : ℝ) * modulus k + 1))
  rw [mul_zero, ENNReal.ofReal_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h (by simp)
  filter_upwards [hp, eventually_ge_atTop (fingerprintBound k δ)] with n hpn hn
  exact setBernoulli_isAvoidable_le_ofReal hk hδ hn hpn

/-- **Szemerédi's theorem with random differences.** There is `c > 0` such that for every
`k ≥ 3` and `δ > 0` there is `C > 0` with the following property. Let `D` be a `p n`-random
subset of `{1, …, n}`, where `p n ≥ C * n ^ (-c / log (log k))` for all large `n`. The probability
that some subset of `{1, …, n}` with at least `δ * n` elements contains no `k`-term arithmetic
progression with common difference in `D` tends to `0`. -/
theorem exists_forall_tendsto_setBernoulli_isAvoidable :
    ∃ c > (0 : ℝ), ∀ k ≥ (3 : ℕ), ∀ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : ℕ → I,
      (∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (-c / Real.log (Real.log k)) ≤ p n) →
      Tendsto (fun n ↦ setBer(Set.Icc 1 n, p n) {D | IsAvoidable k δ n D}) atTop (𝓝 0) := by
  refine ⟨c, c_pos, ?_⟩
  intro k hk δ hδ
  refine ⟨3 / fingerprintDensity k δ, div_pos three_pos (fingerprintDensity_pos k hδ), ?_⟩
  intro p hp
  simp only [neg_div] at hp
  exact tendsto_setBernoulli_isAvoidable hk hδ hp

end RandomDifferences
