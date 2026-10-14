/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

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
lemma digitSet_zero (Q : ℕ) (S : Finset ℕ) : digitSet Q S 0 = {0} := by
  rfl

@[simp]
lemma digitSet_succ (Q : ℕ) (S : Finset ℕ) (t : ℕ) :
    digitSet Q S (t + 1) = image₂ (fun s a ↦ s + Q * a) S (digitSet Q S t) := by
  rfl

lemma card_digitSet_le (Q : ℕ) (S : Finset ℕ) (t : ℕ) : #(digitSet Q S t) ≤ #S ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [digitSet_succ, pow_succ']
    exact (card_image₂_le _ _ _).trans (Nat.mul_le_mul_left _ ih)

lemma add_le_of_mem_digitSet {Q k : ℕ} {S : Finset ℕ} (hS : ∀ s ∈ S, s + k ≤ k * Q) {t a : ℕ}
    (ha : a ∈ digitSet Q S t) : a + k ≤ k * Q ^ t := by
  induction t generalizing a with
  | zero => simp_all
  | succ t ih =>
    obtain ⟨s, hs, b, hb, rfl⟩ := mem_image₂.1 ha
    rw [pow_succ]
    linarith [hS s hs, Nat.mul_le_mul_left Q (ih hb)]

lemma exists_forall_add_mul_mem_digitSet {Q k : ℕ} {S : Finset ℕ}
    (hS : ∀ d < Q, ∃ a, ∀ j < k, a + j * d ∈ S) {t d : ℕ} (hd : d < Q ^ t) :
    ∃ a, ∀ j < k, a + j * d ∈ digitSet Q S t := by
  induction t generalizing d with
  | zero =>
    use 0
    simp_all
  | succ t ih =>
    have hQ : 0 < Q := (pow_pos_iff t.succ_ne_zero).1 (Nat.zero_lt_of_lt hd)
    rw [pow_succ'] at hd
    obtain ⟨a₀, h₀⟩ := hS (d % Q) (Nat.mod_lt _ hQ)
    obtain ⟨a₁, h₁⟩ := ih (Nat.div_lt_of_lt_mul hd)
    use a₀ + Q * a₁
    intro j hj
    rw [digitSet_succ, mem_image₂]
    refine ⟨_, h₀ j hj, _, h₁ j hj, ?_⟩
    linear_combination j * Nat.mod_add_div d Q

end ArithmeticKakeya
