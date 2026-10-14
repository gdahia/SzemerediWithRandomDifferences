/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Computability.Ackermann
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
import DensityHalesJewett.Ackermann
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus

/-!
# The Green–Ruzsa parameters and the Ackermann function

Varnavides' theorem in the DensityHalesJewett project has the constant `ack (4 * k + 1) s`, and
the covering lemma multiplies it by `k * Q + 1`, where `Q = modulus k`. This factor and the
threshold `n₀ k` of the Green–Ruzsa theorem are absorbed by one more level of the Ackermann
function.

## Main statements

* `RandomDifferences.three_mul_modulus_mul_ack_le_ack`:
  `3 * ((k * Q + 1) * ack (4 * k + 1) s) ≤ ack (4 * k + 2) s` for `2 ≤ k ≤ s`.
* `RandomDifferences.n₀_le_ack`: `n₀ k ≤ ack (4 * k + 2) s` for `2 ≤ k ≤ s`.
-/

public section

namespace RandomDifferences

open ArithmeticKakeya DensityHalesJewett AckBounded

private lemma ackBounded_ten_mul (k : ℕ) : AckBounded 5 k 2 (10 * k) :=
  (num le_rfl 10).mul le_rfl (of_le le_rfl)

private lemma ackBounded_modulus (k : ℕ) : AckBounded 5 k 5 (modulus k) :=
  ((((ackBounded_ten_mul k).add le_rfl (num le_rfl 2)).pow le_rfl (num le_rfl 2)).pow le_rfl
    (ackBounded_ten_mul k)).le (modulus_le k)

lemma three_mul_modulus_le_ack {k : ℕ} (hk : 1 ≤ k) : 3 * (k * modulus k + 1) ≤ ack 8 k :=
  ((num le_rfl 3).mul le_rfl
    (((of_le le_rfl).mul le_rfl (ackBounded_modulus k)).add le_rfl (num le_rfl 1))).le_ack
      (by norm_num) (by grind) hk

lemma mul_modulus_add_one_le_ack {k s : ℕ} (hk : 2 ≤ k) (hs : k ≤ s) :
    k * modulus k + 1 ≤ ack (4 * k + 2) s :=
  (Nat.le_mul_of_pos_left _ three_pos).trans
    ((three_mul_modulus_le_ack (by grind)).trans (ack_le_ack (by grind) hs))

lemma three_mul_modulus_mul_ack_le_ack {k s : ℕ} (hk : 2 ≤ k) (hs : k ≤ s) :
    3 * ((k * modulus k + 1) * ack (4 * k + 1) s) ≤ ack (4 * k + 2) s := by
  have hF : 3 * (k * modulus k + 1) ≤ ack (4 * k + 1) s :=
    (three_mul_modulus_le_ack (by grind)).trans (ack_le_ack (by grind) hs)
  rw [← mul_assoc]
  apply (((of_le hF).mul (le_refl 5) (of_le le_rfl)).le_ack (by norm_num) (by grind)
    (ack_pos _ _)).trans
  apply (ack_le_ack (by grind : 5 + 3 ≤ 4 * k) le_rfl).trans
  rw [← ack_succ_succ]
  exact ack_succ_right_le_ack_succ_left _ _

private lemma ceil_ten_mul_log_log_le (k : ℕ) : ⌈10 * Real.log (Real.log k)⌉₊ ≤ 10 * k := by
  rw [Nat.ceil_le, Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left ((Real.log_le_self (Real.log_natCast_nonneg k)).trans
    (Real.log_le_self (Nat.cast_nonneg k))) (by norm_num)

lemma n₀_le_ack {k s : ℕ} (hk : 2 ≤ k) (hs : k ≤ s) : n₀ k ≤ ack (4 * k + 2) s := by
  rw [n₀]
  apply (Nat.pow_le_pow_right (modulus_pos k)
    (Nat.add_le_add_right (ceil_ten_mul_log_log_le k) 100)).trans
  exact (((ackBounded_modulus k).pow le_rfl
    ((ackBounded_ten_mul k).add le_rfl (num le_rfl 100))).le_ack (by norm_num) (by grind)
      (by grind)).trans (ack_le_ack (by grind) hs)

end RandomDifferences
