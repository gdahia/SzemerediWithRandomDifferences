/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finset.NAry

/-!
# Numbers with digits in a given set

The set of numbers with `t` digits in base `Q`, each digit taken from a set `S`. Digits may
exceed `Q`. If `S` contains a `k`-term progression with every common difference below `Q`, then
this set contains one with every common difference below `Q ^ t`, obtained digit by digit.

## Main statements

* `ArithmeticKakeya.card_digitSet_le`: the set has at most `#S ^ t` elements.
* `ArithmeticKakeya.add_le_of_mem_digitSet`: if `S` lies in `{0, …, k * Q - k}` then the set
  lies in `{0, …, k * Q ^ t - k}`.
* `ArithmeticKakeya.exists_forall_add_mul_mem_digitSet`: the progressions.
-/

public section

namespace ArithmeticKakeya

open Finset

/-- The numbers `s₀ + s₁ * Q + ⋯ + sₜ₋₁ * Q ^ (t - 1)` with every `sᵢ` in `S`. -/
def digitSet (Q : ℕ) (S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | t + 1 => image₂ (fun s a ↦ s + Q * a) S (digitSet Q S t)

@[simp]
theorem digitSet_zero (Q : ℕ) (S : Finset ℕ) : digitSet Q S 0 = {0} := by
  rfl

@[simp]
theorem digitSet_succ (Q : ℕ) (S : Finset ℕ) (t : ℕ) :
    digitSet Q S (t + 1) = image₂ (fun s a ↦ s + Q * a) S (digitSet Q S t) := by
  rfl

theorem card_digitSet_le (Q : ℕ) (S : Finset ℕ) (t : ℕ) : #(digitSet Q S t) ≤ #S ^ t := by
  sorry

theorem add_le_of_mem_digitSet {Q k : ℕ} {S : Finset ℕ} (hS : ∀ s ∈ S, s + k ≤ k * Q) {t a : ℕ}
    (ha : a ∈ digitSet Q S t) : a + k ≤ k * Q ^ t := by
  sorry

theorem exists_forall_add_mul_mem_digitSet {Q k : ℕ} {S : Finset ℕ}
    (hS : ∀ d < Q, ∃ a, ∀ j < k, a + j * d ∈ S) (t : ℕ) :
    ∀ d < Q ^ t, ∃ a, ∀ j < k, a + j * d ∈ digitSet Q S t := by
  sorry

end ArithmeticKakeya
