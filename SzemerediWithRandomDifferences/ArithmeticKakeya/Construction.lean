/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Szemeredi
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues
import Mathlib.Tactic.Ring
import SzemerediWithRandomDifferences.ArithmeticKakeya.BaseSet
import SzemerediWithRandomDifferences.ArithmeticKakeya.DigitSet

/-!
# The Green–Ruzsa construction for a general modulus

For a modulus `Q` such that `d ^ 2 + j * d` takes at most `r` residues modulo `Q` for each
`j < k`, the numbers with `t` base-`Q` digits in the base set, shifted by one, form a subset of
`{1, …, k * Q ^ t}` of size at most `(k ^ 2 * r) ^ t` containing a `k`-term arithmetic
progression with every common difference in `{1, …, Q ^ t - 1}`.

## Main statements

* `ArithmeticKakeya.exists_card_le_pow_forall_exists_arithmeticProgression`: the construction
  with `t` digits.
* `ArithmeticKakeya.exists_card_le_pow_log_forall_exists_arithmeticProgression`: the construction
  for common differences up to `n`, taking `t = Nat.log Q n + 1`.
-/

public section

namespace ArithmeticKakeya

open Combinatorics Finset

lemma exists_card_le_pow_forall_exists_arithmeticProgression {Q k r : ℕ} (hk : k ≠ 0)
    (hr : ∀ j < k, #(residues Q j) ≤ r) (t : ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * Q ^ t) ∧ #Y ≤ (k ^ 2 * r) ^ t ∧
      ∀ d ∈ Ioo 0 (Q ^ t), ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  refine ⟨(digitSet Q (baseSet Q k) t).image (· + 1), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    rw [mem_Icc]
    grind [add_le_of_mem_digitSet (fun s ↦ add_le_of_mem_baseSet) ha]
  · apply card_image_le.trans
    apply (card_digitSet_le Q _ t).trans
    exact Nat.pow_le_pow_left (card_baseSet_le hr) t
  · intro d hd
    rw [mem_Ioo] at hd
    obtain ⟨a, ha⟩ :=
      exists_forall_add_mul_mem_digitSet (exists_forall_add_mul_mem_baseSet Q k) t d hd.2
    refine ⟨⟨a + 1, d, hd.1.ne'⟩, rfl, ?_⟩
    intro i
    rw [mem_image]
    refine ⟨a + i * d, ha i i.2, ?_⟩
    simp only [ArithmeticProgression.term, nsmul_eq_mul, Nat.cast_id]
    ring

lemma exists_card_le_pow_log_forall_exists_arithmeticProgression {Q k r n : ℕ} (hQ : 1 < Q)
    (hk : k ≠ 0) (hn : n ≠ 0) (hr : ∀ j < k, #(residues Q j) ≤ r) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * Q * n) ∧ #Y ≤ (k ^ 2 * r) ^ (Nat.log Q n + 1) ∧
      ∀ d ∈ Icc 1 n, ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  obtain ⟨Y, hY, hcard, hAP⟩ :=
    exists_card_le_pow_forall_exists_arithmeticProgression hk hr (Nat.log Q n + 1)
  refine ⟨Y, hY.trans (Icc_subset_Icc_right ?_), hcard, ?_⟩
  · rw [pow_succ, mul_assoc, mul_comm Q n]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_log_le_self Q hn))
  · intro d hd
    rw [mem_Icc] at hd
    exact hAP d (mem_Ioo.2 ⟨hd.1, hd.2.trans_lt (Nat.lt_pow_succ_log_self hQ n)⟩)

end ArithmeticKakeya
