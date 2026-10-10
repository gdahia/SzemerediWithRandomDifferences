/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.Linarith

/-!
# The base set of the Green–Ruzsa construction

For a modulus `Q` and a length `k`, the base set is the union over `d < Q` of the `k`-term
progressions with common difference `d` starting at the residue of `d ^ 2` modulo `Q`. It lies
in `{0, …, k * Q - k}`, and its size is controlled by the residues of `d ^ 2 + j * d`.

## Main statements

* `ArithmeticKakeya.add_le_of_mem_baseSet`: the base set lies in `{0, …, k * Q - k}`.
* `ArithmeticKakeya.card_baseSet_le`: the base set has at most `k ^ 2 * r` elements when
  `d ^ 2 + j * d` takes at most `r` residues modulo `Q` for each `j < k`.
-/

public section

namespace ArithmeticKakeya

open Finset

/-- The base set of the Green–Ruzsa construction: the numbers `d ^ 2 % Q + j * d` with `d < Q`
and `j < k`. -/
def baseSet (Q k : ℕ) : Finset ℕ :=
  (range Q ×ˢ range k).image fun x ↦ x.1 ^ 2 % Q + x.2 * x.1

lemma mem_baseSet {Q k s : ℕ} :
    s ∈ baseSet Q k ↔ ∃ d < Q, ∃ j < k, d ^ 2 % Q + j * d = s := by
  simp only [baseSet, mem_image, mem_product, mem_range, Prod.exists]
  grind

lemma add_mul_mem_baseSet {Q k d j : ℕ} (hd : d < Q) (hj : j < k) :
    d ^ 2 % Q + j * d ∈ baseSet Q k :=
  mem_baseSet.2 ⟨d, hd, j, hj, rfl⟩

/-- The base set contains a `k`-term progression with every common difference below `Q`. -/
lemma exists_forall_add_mul_mem_baseSet (Q k : ℕ) :
    ∀ d < Q, ∃ a, ∀ j < k, a + j * d ∈ baseSet Q k := by
  intro d hd
  use d ^ 2 % Q
  intro j hj
  exact add_mul_mem_baseSet hd hj

lemma add_le_of_mem_baseSet {Q k s : ℕ} (hs : s ∈ baseSet Q k) : s + k ≤ k * Q := by
  obtain ⟨d, hd, j, hj, rfl⟩ := mem_baseSet.1 hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by grind : k ≠ 0)
  linarith [Nat.mod_lt (d ^ 2) (by grind : 0 < Q), Nat.mul_le_mul_right d (Nat.le_of_lt_succ hj),
    Nat.mul_le_mul_left k (Nat.succ_le_of_lt hd)]

lemma lt_of_mem_baseSet {Q k s : ℕ} (hs : s ∈ baseSet Q k) : s < k * Q := by
  obtain ⟨d, -, j, hj, -⟩ := mem_baseSet.1 hs
  grind [add_le_of_mem_baseSet hs]

/-- The residues of the base set modulo `Q` are residues of `d ^ 2 + j * d` for some
`j < k`. -/
lemma image_mod_baseSet_subset (Q k : ℕ) :
    (baseSet Q k).image (· % Q) ⊆ (range k).biUnion (residues Q) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
  obtain ⟨d, hd, j, hj, rfl⟩ := mem_baseSet.1 ha
  rw [mem_biUnion]
  refine ⟨j, mem_range.2 hj, ?_⟩
  simp only [Nat.mod_add_mod]
  exact mod_mem_residues (by grind) j d

/-- A set of numbers below `k * Q` has at most `k` elements in each residue class modulo
`Q`. -/
lemma card_le_mul_card_image_mod {s : Finset ℕ} {k Q : ℕ} (hs : ∀ a ∈ s, a < k * Q) :
    #s ≤ k * #(s.image (· % Q)) := by
  rcases Q.eq_zero_or_pos with rfl | hQ
  · obtain rfl : s = ∅ := eq_empty_of_forall_notMem (by grind)
    simp
  apply card_le_mul_card_image
  intro b _
  have h : (k * Q).count (· ≡ b [MOD Q]) = k := by simp [Nat.count_modEq_card _ hQ, hQ]
  rw [Nat.count_eq_card_filter_range] at h
  refine (card_le_card ?_).trans_eq h
  intro a ha
  obtain ⟨hmem, rfl⟩ := mem_filter.1 ha
  exact mem_filter.2 ⟨mem_range.2 (hs a hmem), (Nat.mod_modEq a Q).symm⟩

lemma card_baseSet_le {Q k r : ℕ} (hr : ∀ j < k, #(residues Q j) ≤ r) :
    #(baseSet Q k) ≤ k ^ 2 * r := by
  refine (card_le_mul_card_image_mod fun a ↦ lt_of_mem_baseSet).trans ?_
  rw [pow_two, mul_assoc]
  apply Nat.mul_le_mul_left
  apply (card_le_card (image_mod_baseSet_subset Q k)).trans
  apply card_biUnion_le.trans
  apply (sum_le_sum (g := fun _ ↦ r) ?_).trans_eq (by simp)
  grind

end ArithmeticKakeya
