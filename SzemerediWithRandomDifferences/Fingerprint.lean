/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
public import SzemerediWithRandomDifferences.Translate
import SzemerediWithRandomDifferences.ArithmeticKakeya
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus

/-!
# Fingerprints

A family of subsets of `{1, …, n}`, the fingerprints, such that every subset of `{1, …, n}` with
at least `δ * n` elements contains one of them, and each of them contains `k`-term arithmetic
progressions with at least `γ * n` common differences. The fingerprints are translates of
subsets of the Green–Ruzsa set, so there are at most `C * n * exp (n ^ (1 - c / log (log k)))`
of them.

## Main statements

* `RandomDifferences.exists_card_le_forall_exists_subset_forall_le_ncard`: the fingerprint
  lemma.
-/

public section

namespace Combinatorics.ArithmeticProgression

lemma supersaturationConstant_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < supersaturationConstant k δ := by
  have hC : 0 < ⌈16 * ((densityTheoremBound k (δ / 2) + 1 : ℕ) : ℝ) / δ⌉₊ :=
    Nat.ceil_pos.2 (by positivity)
  unfold supersaturationConstant
  positivity

end Combinatorics.ArithmeticProgression

namespace RandomDifferences

open ArithmeticKakeya Combinatorics Combinatorics.ArithmeticProgression Finset

/-- The sets `translate n u Y'` with `u < m` and `Y' ⊆ Y` that have at least `b` common
differences in `{1, …, n}`. -/
noncomputable def fingerprints (k n m : ℕ) (b : ℝ) (Y : Finset ℕ) : Finset (Finset ℕ) :=
  open Classical in
  {F ∈ (range m ×ˢ Y.powerset).image fun x ↦ translate n x.1 x.2 |
    b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard}

lemma mem_fingerprints {k n m : ℕ} {b : ℝ} {Y F : Finset ℕ} :
    F ∈ fingerprints k n m b Y ↔ (∃ u < m, ∃ Y' ⊆ Y, translate n u Y' = F) ∧
      b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard := by
  simp only [fingerprints, mem_filter, mem_image, mem_product, mem_range, mem_powerset,
    Prod.exists]
  grind

lemma card_fingerprints_le (k n m : ℕ) (b : ℝ) (Y : Finset ℕ) :
    #(fingerprints k n m b Y) ≤ m * 2 ^ #Y := by
  apply (card_filter_le _ _).trans
  apply card_image_le.trans
  simp

lemma card_fingerprints_le_mul_exp (k n m : ℕ) (b : ℝ) {Y : Finset ℕ} {x : ℝ} (hY : #Y ≤ x) :
    (#(fingerprints k n m b Y) : ℝ) ≤ m * Real.exp x := by
  apply (Nat.cast_le (α := ℝ).2 (card_fingerprints_le k n m b Y)).trans
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  apply (pow_le_pow_left₀ zero_le_two h2 _).trans
  rwa [← Real.exp_nat_mul, mul_one, Real.exp_le_exp]

/-- Varnavides' theorem for subsets of `{1, …, n}`. -/
lemma mul_sq_le_card_containedProgressions {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : supersaturationBound k (δ / 2) ≤ n) (hn0 : n ≠ 0) {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    (hSδ : δ * n ≤ #S) :
    supersaturationConstant k (δ / 2) * (n : ℝ) ^ 2 ≤ #(containedProgressions k (n + 1) S) := by
  have hn1 : (1 : ℝ) ≤ n := mod_cast Nat.pos_of_ne_zero hn0
  refine le_trans ?_ (exists_many_of_density_nat k hk (δ / 2) (half_pos hδ) (n + 1) (by grind) S
    ?_ ?_)
  · rw [Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (supersaturationConstant_pos k (half_pos hδ)).le
  · intro x hx
    grind [hS hx]
  · rw [Nat.cast_add, Nat.cast_one]
    linarith [mul_le_mul_of_nonneg_left hn1 hδ.le]

/-- The proportion of common differences in a fingerprint. -/
noncomputable def fingerprintDensity (k : ℕ) (δ : ℝ) : ℝ :=
  supersaturationConstant k (δ / 2) / (k * modulus k + 1)

lemma fingerprintDensity_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < fingerprintDensity k δ :=
  div_pos (supersaturationConstant_pos k (half_pos hδ)) (by positivity)

/-- A threshold for `n` in the fingerprint lemma. -/
noncomputable def fingerprintBound (k : ℕ) (δ : ℝ) : ℕ :=
  max (n₀ k) (supersaturationBound k (δ / 2))

lemma pos_of_fingerprintBound_le {k n : ℕ} {δ : ℝ} (hn : fingerprintBound k δ ≤ n) : 0 < n :=
  (pow_pos (modulus_pos k) _).trans_le ((le_max_left _ _).trans hn)

/-- The fingerprint lemma. For `k ≥ 3`, `δ > 0` and large `n` there is a family of subsets of
`{1, …, n}`, of size at most `C * n * exp (n ^ (1 - c / log (log k)))`, such that every
`S ⊆ {1, …, n}` with at least `δ * n` elements contains a member of the family, and every member
contains `k`-term arithmetic progressions with at least `γ * n` common differences. -/
theorem exists_card_le_forall_exists_subset_forall_le_ncard {k : ℕ} (hk : 3 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : fingerprintBound k δ ≤ n) :
    ∃ 𝓕 : Finset (Finset ℕ),
      (#𝓕 : ℝ) ≤
        (k * modulus k + 1) * n * Real.exp ((n : ℝ) ^ (1 - c / Real.log (Real.log k))) ∧
      (∀ S : Finset ℕ, S ⊆ Icc 1 n → δ * n ≤ #S → ∃ F ∈ 𝓕, F ⊆ S) ∧
      ∀ F ∈ 𝓕, fingerprintDensity k δ * n ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard := by
  have hn₀ : n₀ k ≤ n := (le_max_left _ _).trans hn
  have hn0 : n ≠ 0 := (pos_of_fingerprintBound_le hn).ne'
  obtain ⟨Y, hYM, hcard, hY⟩ := exists_card_le_rpow_forall_exists_arithmeticProgression hk hn₀
  refine ⟨fingerprints k n (k * modulus k * n + n) (fingerprintDensity k δ * n) Y, ?_, ?_, ?_⟩
  · apply (card_fingerprints_le_mul_exp k n _ _ hcard).trans_eq
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, add_one_mul]
  · intro S hS hSδ
    have hb : (k * modulus k * n + n) • (fingerprintDensity k δ * n) ≤
        (#(containedProgressions k (n + 1) S) : ℝ) := by
      refine le_of_eq_of_le ?_ (mul_sq_le_card_containedProgressions hk hδ
        ((le_max_right _ _).trans hn) hn0 hS hSδ)
      rw [nsmul_eq_mul, fingerprintDensity, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      field_simp
    obtain ⟨u, hu, Y', hY', hsub, hle⟩ :=
      exists_translate_subset_le_ncard (by grind) hn0 hYM hY hS hb
    exact ⟨_, mem_fingerprints.2 ⟨⟨u, hu, Y', hY', rfl⟩, hle⟩, hsub⟩
  · intro F hF
    exact (mem_fingerprints.1 hF).2

end RandomDifferences
