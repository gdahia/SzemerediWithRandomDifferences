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
public import SzemerediWithRandomDifferences.CommonDiffs
import SzemerediWithRandomDifferences.Ackermann
import SzemerediWithRandomDifferences.ArithmeticKakeya
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus
import SzemerediWithRandomDifferences.Translate
import SzemerediWithRandomDifferences.Varnavides

/-!
# A small cover of the dense sets

A cover of a collection of sets is a family such that every set in the collection contains a
member of the family. This file gives a cover of the subsets of `{1, …, n}` with at least `δ * n`
elements whose members contain `k`-term arithmetic progressions with at least `γ * n` common
differences. The members are subsets of translates of the Green–Ruzsa set, so there are at most
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

open ArithmeticKakeya Combinatorics Combinatorics.ArithmeticProgression Finset Pointwise

/-- `𝓕` is a cover of `𝓗`: every set in `𝓗` contains a member of `𝓕`. -/
def IsCover {α : Type*} (𝓕 : Finset (Finset α)) (𝓗 : Set (Finset α)) : Prop :=
  ∀ S ∈ 𝓗, ∃ F ∈ 𝓕, F ⊆ S

lemma IsCover.exists_subset {α : Type*} {𝓕 : Finset (Finset α)} {𝓗 : Set (Finset α)}
    (h : IsCover 𝓕 𝓗) {S : Finset α} (hS : S ∈ 𝓗) : ∃ F ∈ 𝓕, F ⊆ S :=
  h S hS

/-- A cover is a cover in the sense of `SetRel.IsCover`, for the relation of containing. -/
lemma isCover_iff_setRel_isCover {α : Type*} {𝓕 : Finset (Finset α)} {𝓗 : Set (Finset α)} :
    IsCover 𝓕 𝓗 ↔ SetRel.IsCover {(S, F) : Finset α × Finset α | F ⊆ S} 𝓗 𝓕 := by
  rfl

/-- The subsets of the translates `{t} + Y` with `-M ≤ t < n` that have at least `b` common
differences in `{1, …, n}`. -/
noncomputable def cover (k n M : ℕ) (b : ℝ) (Y : Finset ℤ) : Finset (Finset ℤ) := by
  classical
  exact {F ∈ (Ico (-(M : ℤ)) n).biUnion fun t ↦ ({t} + Y).powerset |
    b ≤ (commonDiffs k F ∩ Set.Icc 1 (n : ℤ)).ncard}

lemma mem_cover {k n M : ℕ} {b : ℝ} {Y F : Finset ℤ} :
    F ∈ cover k n M b Y ↔ (∃ t ∈ Ico (-(M : ℤ)) n, F ⊆ {t} + Y) ∧
      b ≤ (commonDiffs k F ∩ Set.Icc 1 (n : ℤ)).ncard := by
  simp [cover]

lemma card_cover_le (k n M : ℕ) (b : ℝ) (Y : Finset ℤ) :
    #(cover k n M b Y) ≤ (M + n) * 2 ^ #Y := by
  apply (card_filter_le _ _).trans
  apply card_biUnion_le.trans
  simp only [card_powerset, card_singleton_add, sum_const, Int.card_Ico, smul_eq_mul]
  exact Nat.mul_le_mul_right _ (by grind)

lemma card_cover_le_mul_exp (k n M : ℕ) (b : ℝ) {Y : Finset ℤ} {x : ℝ} (hY : #Y ≤ x) :
    (#(cover k n M b Y) : ℝ) ≤ (M + n : ℕ) * Real.exp x := by
  apply (Nat.cast_le (α := ℝ).2 (card_cover_le k n M b Y)).trans
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  apply (pow_le_pow_left₀ zero_le_two
    (by linarith [Real.add_one_le_exp 1] : (2 : ℝ) ≤ Real.exp 1) _).trans
  rwa [← Real.exp_nat_mul, mul_one, Real.exp_le_exp]

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
    ∃ 𝓕 : Finset (Finset ℤ),
      IsCover 𝓕 {S | S ⊆ Icc 1 (n : ℤ) ∧ δ * n ≤ #S} ∧
      #𝓕 ≤ (k * modulus k + 1) * n * Real.exp (n ^ (1 - c / Real.log (Real.log k))) ∧
      ∀ F ∈ 𝓕, coverDensity k δ * n ≤ (commonDiffs k F ∩ Set.Icc 1 (n : ℤ)).ncard := by
  have hn₀ : n₀ k ≤ n := (le_max_left _ _).trans hn
  have hn0 : n ≠ 0 := (pos_of_coverBound_le hn).ne'
  obtain ⟨Y, hYM, hcard, hY⟩ := exists_card_le_rpow_forall_mem_commonDiffs hk hn₀
  refine ⟨cover k n (k * modulus k * n) (coverDensity k δ * n) Y, ?_, ?_, ?_⟩
  · rintro S ⟨hS, hSδ⟩
    have hA : ((ack (4 * k + 1) (k + ⌈2 / δ⌉₊) : ℕ) : ℝ) ≠ 0 := mod_cast (ack_pos _ _).ne'
    have hb : (k * modulus k * n + n) • (coverDensity k δ * n) ≤
        (#(progressions k n S) : ℝ) := by
      refine le_of_eq_of_le ?_
        (sq_div_ack_le_card_progressions hk hδ ((le_max_right _ _).trans hn) hS hSδ)
      rw [nsmul_eq_mul, coverDensity, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
      field_simp
    obtain ⟨t, ht, hle⟩ :=
      exists_le_ncard_commonDiffs_singleton_add_inter (by grind) hn0 hYM hY hb
    exact ⟨_, mem_cover.2 ⟨⟨t, ht, inter_subset_left⟩, hle⟩, inter_subset_right⟩
  · apply (card_cover_le_mul_exp k n _ _ hcard).trans_eq
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, add_one_mul]
  · intro F hF
    obtain ⟨-, h⟩ := mem_cover.1 hF
    exact h

end RandomDifferences
