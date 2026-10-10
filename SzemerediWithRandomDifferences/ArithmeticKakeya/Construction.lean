/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues
public import SzemerediWithRandomDifferences.ArithmeticProgression
import SzemerediWithRandomDifferences.ArithmeticKakeya.BaseSet
import SzemerediWithRandomDifferences.ArithmeticKakeya.DigitSet

/-!
# The Green–Ruzsa construction for a general modulus

For a modulus `Q` such that `d ^ 2 + j * d` takes at most `r` residues modulo `Q` for each
`j < k`, the numbers with `t` base-`Q` digits in the base set, shifted by one, form a subset of
`{1, …, k * Q ^ t}` of size at most `(k ^ 2 * r) ^ t` containing a `k`-term arithmetic
progression with every common difference in `{1, …, Q ^ t - 1}`.

## Main statements

* `ArithmeticKakeya.exists_subset_Icc_card_le_pow`: the construction with `t` digits.
* `ArithmeticKakeya.exists_subset_Icc_card_le_pow_log`: the construction for common differences
  up to `n`, taking `t = Nat.log Q n + 1`.
-/

public section

namespace ArithmeticKakeya

open Combinatorics Finset

theorem exists_subset_Icc_card_le_pow {Q k r : ℕ} (hk : k ≠ 0)
    (hr : ∀ j < k, #(residues Q j) ≤ r) (t : ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * Q ^ t) ∧ #Y ≤ (k ^ 2 * r) ^ t ∧
      ∀ d ∈ Ioo 0 (Q ^ t), ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  sorry

theorem exists_subset_Icc_card_le_pow_log {Q k r n : ℕ} (hQ : 1 < Q) (hk : k ≠ 0) (hn : n ≠ 0)
    (hr : ∀ j < k, #(residues Q j) ≤ r) :
    ∃ Y : Finset ℕ, Y ⊆ Icc 1 (k * Q * n) ∧ #Y ≤ (k ^ 2 * r) ^ (Nat.log Q n + 1) ∧
      ∀ d ∈ Icc 1 n, ∃ P : ArithmeticProgression ℕ k, P.diff = d ∧ P.IsSubset Y := by
  sorry

end ArithmeticKakeya
