/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Rel.Cover
public import Mathlib.Computability.Ackermann
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
public import SzemerediWithRandomDifferences.Translate
import DensityHalesJewett.Main
import SzemerediWithRandomDifferences.Ackermann
import SzemerediWithRandomDifferences.ArithmeticKakeya
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus

/-!
# A small cover of the dense sets

A cover of a collection of sets is a family such that every set in the collection contains a
member of the family. This file gives a cover of the subsets of `{1, …, n}` with at least `δ * n`
elements whose members contain `k`-term arithmetic progressions with at least `γ * n` common
differences. The members are translates of subsets of the Green–Ruzsa set, so there are at most
`C * n * exp (n ^ (1 - c / log (log k)))` of them. This is Lemma 1.2 of Dahia, *Szemerédi's
theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859), proved in Section 2 there from Varnavides'
theorem (Theorem 2.1) and the Green–Ruzsa theorem (Theorem 2.2).

The terminology follows Alon and Pham, *Random Cayley graphs and random sumsets*,
[arXiv:2509.02561](https://arxiv.org/abs/2509.02561).

## Main definitions

* `RandomDifferences.IsCover`: the family `𝓕` is a cover of the collection `𝓗`.

## Main statements

* `RandomDifferences.isCover_iff_setRel_isCover`: a cover is a cover in the sense of
  `SetRel.IsCover`, for the relation of containing.
* `RandomDifferences.exists_isCover_card_le`: the covering lemma.
-/

public section

namespace RandomDifferences

open ArithmeticKakeya Combinatorics Combinatorics.ArithmeticProgression Finset

/-- `𝓕` is a cover of `𝓗`: every set in `𝓗` contains a member of `𝓕`. -/
def IsCover {α : Type*} (𝓕 : Finset (Finset α)) (𝓗 : Set (Finset α)) : Prop :=
  ∀ S ∈ 𝓗, ∃ F ∈ 𝓕, F ⊆ S

lemma IsCover.exists_subset {α : Type*} {𝓕 : Finset (Finset α)} {𝓗 : Set (Finset α)}
    (h : IsCover 𝓕 𝓗) {S : Finset α} (hS : S ∈ 𝓗) : ∃ F ∈ 𝓕, F ⊆ S :=
  h S hS

/-- A cover is a cover in the sense of `SetRel.IsCover`, for the relation of containing. -/
lemma isCover_iff_setRel_isCover {α : Type*} {𝓕 : Finset (Finset α)} {𝓗 : Set (Finset α)} :
    IsCover 𝓕 𝓗 ↔ SetRel.IsCover {(S, F) : Finset α × Finset α | F ⊆ S} 𝓗 𝓕 :=
  Iff.rfl

/-- The sets `translate t Y'` with `-M ≤ t < n` and `Y' ⊆ Y` that have at least `b` common
differences in `{1, …, n}`. -/
noncomputable def cover (k n M : ℕ) (b : ℝ) (Y : Finset ℕ) : Finset (Finset ℕ) :=
  open Classical in
  {F ∈ (Ico (-(M : ℤ)) n ×ˢ Y.powerset).image fun (t, Y') ↦ translate t Y' |
    b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard}

lemma mem_cover {k n M : ℕ} {b : ℝ} {Y F : Finset ℕ} :
    F ∈ cover k n M b Y ↔ (∃ t ∈ Ico (-(M : ℤ)) n, ∃ Y' ⊆ Y, translate t Y' = F) ∧
      b ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard := by
  simp only [cover, mem_filter, mem_image, mem_product, mem_powerset, Prod.exists]
  grind

lemma card_cover_le (k n M : ℕ) (b : ℝ) (Y : Finset ℕ) :
    #(cover k n M b Y) ≤ (M + n) * 2 ^ #Y := by
  apply (card_filter_le _ _).trans
  apply card_image_le.trans
  rw [card_product, Int.card_Ico, card_powerset]
  exact Nat.mul_le_mul_right _ (by grind)

lemma card_cover_le_mul_exp (k n M : ℕ) (b : ℝ) {Y : Finset ℕ} {x : ℝ} (hY : #Y ≤ x) :
    (#(cover k n M b Y) : ℝ) ≤ (M + n : ℕ) * Real.exp x := by
  apply (Nat.cast_le (α := ℝ).2 (card_cover_le k n M b Y)).trans
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  apply (pow_le_pow_left₀ zero_le_two
    (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1) _).trans
  rwa [← Real.exp_nat_mul, mul_one, Real.exp_le_exp]

/-- Varnavides' theorem for subsets of `{1, …, n}`. -/
lemma sq_div_ack_le_card_containedProgressions {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ n) {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    (hSδ : δ * n ≤ #S) :
    (n : ℝ) ^ 2 / ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ #(containedProgressions k (n + 1) S) := by
  have hn1 : (1 : ℝ) ≤ n := mod_cast (ack_pos _ _).trans_le hn
  have h := exists_many_of_density_nat hk (half_pos hδ) (n := n + 1)
  rw [one_div_div, Nat.cast_add, Nat.cast_one] at h
  refine le_trans ?_ (h (hn.trans n.le_succ) S ?_ ?_)
  · exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
  · intro x hx
    grind [hS hx]
  · linarith [mul_le_mul_of_nonneg_left hn1 hδ.le]

/-- The proportion of common differences in a member of the cover. -/
noncomputable def coverDensity (k : ℕ) (δ : ℝ) : ℝ :=
  1 / ((k * modulus k + 1) * ack (4 * k + 1) (k + ⌈2 / δ⌉₊))

lemma coverDensity_pos (k : ℕ) (δ : ℝ) : 0 < coverDensity k δ :=
  one_div_pos.2 (mul_pos (by positivity) (mod_cast ack_pos _ _))

lemma three_div_coverDensity_le {k : ℕ} (hk : 3 ≤ k) (δ : ℝ) :
    3 / coverDensity k δ ≤ ack (4 * k + 2) (k + ⌈2 / δ⌉₊) := by
  rw [coverDensity, one_div, div_inv_eq_mul]
  exact mod_cast three_mul_modulus_mul_ack_le_ack (by grind) (Nat.le_add_right _ _)

/-- A threshold for `n` in the covering lemma. -/
noncomputable def coverBound (k : ℕ) (δ : ℝ) : ℕ :=
  max (n₀ k) (ack (4 * k + 1) (k + ⌈2 / δ⌉₊))

lemma coverBound_le_ack {k : ℕ} (hk : 3 ≤ k) (δ : ℝ) :
    coverBound k δ ≤ ack (4 * k + 2) (k + ⌈2 / δ⌉₊) :=
  max_le (n₀_le_ack (by grind) (Nat.le_add_right _ _)) (ack_le_ack (by grind) le_rfl)

lemma pos_of_coverBound_le {k n : ℕ} {δ : ℝ} (hn : coverBound k δ ≤ n) : 0 < n :=
  (pow_pos (modulus_pos k) _).trans_le ((le_max_left _ _).trans hn)

/-- The covering lemma. For `k ≥ 3`, `δ > 0` and large `n`, the subsets of `{1, …, n}` with at
least `δ * n` elements have a cover of size at most `C * n * exp (n ^ (1 - c / log (log k)))`
whose members contain `k`-term arithmetic progressions with at least `γ * n` common differences
in `{1, …, n}`. -/
theorem exists_isCover_card_le {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : coverBound k δ ≤ n) :
    ∃ 𝓕 : Finset (Finset ℕ),
      IsCover 𝓕 {S | S ⊆ Icc 1 n ∧ δ * n ≤ #S} ∧
      #𝓕 ≤ (k * modulus k + 1) * n * Real.exp (n ^ (1 - c / Real.log (Real.log k))) ∧
      ∀ F ∈ 𝓕, coverDensity k δ * n ≤ (commonDiffs k F ∩ Set.Icc 1 n).ncard := by
  have hn₀ : n₀ k ≤ n := (le_max_left _ _).trans hn
  have hn0 : n ≠ 0 := (pos_of_coverBound_le hn).ne'
  obtain ⟨Y, hYM, hcard, hY⟩ := exists_card_le_rpow_forall_exists_arithmeticProgression hk hn₀
  refine ⟨cover k n (k * modulus k * n) (coverDensity k δ * n) Y, ?_, ?_, ?_⟩
  · rintro S ⟨hS, hSδ⟩
    have hA : ((ack (4 * k + 1) (k + ⌈2 / δ⌉₊) : ℕ) : ℝ) ≠ 0 := mod_cast (ack_pos _ _).ne'
    have hb : (k * modulus k * n + n) • (coverDensity k δ * n) ≤
        (#(containedProgressions k (n + 1) S) : ℝ) := by
      refine le_of_eq_of_le ?_ (sq_div_ack_le_card_containedProgressions hk hδ
        ((le_max_right _ _).trans hn) hS hSδ)
      rw [nsmul_eq_mul, coverDensity, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      field_simp
    obtain ⟨t, ht, Y', hY', hsub, hle⟩ :=
      exists_translate_subset_le_ncard (by grind) hn0 hYM hY hS hb
    exact ⟨_, mem_cover.2 ⟨⟨t, ht, Y', hY', rfl⟩, hle⟩, hsub⟩
  · apply (card_cover_le_mul_exp k n _ _ hcard).trans_eq
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, add_one_mul]
  · intro F hF
    obtain ⟨-, h⟩ := mem_cover.1 hF
    exact h

end RandomDifferences
