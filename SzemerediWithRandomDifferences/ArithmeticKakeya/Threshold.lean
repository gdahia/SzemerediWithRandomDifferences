/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import SzemerediWithRandomDifferences.ArithmeticKakeya.Modulus

/-!
# The size of the Green–Ruzsa construction

The construction for common differences up to `n` with modulus `Q` has size at most
`B ^ (Nat.log Q n + 1)`. This file bounds that quantity by `n ^ (1 - c / log (log k))` when
`Q = modulus k`, `B = sizeBound k` and `n ≥ n₀ k`.

## Main statements

* `ArithmeticKakeya.pow_log_succ_le_mul_rpow`: `B ^ (Nat.log Q n + 1) ≤ B * n ^ (log B / log Q)`.
* `ArithmeticKakeya.mul_rpow_le_rpow_of_pow_le`: `B * n ^ (log B / log Q) ≤ n ^ (1 - γ)` when
  `n ≥ Q ^ E` and `E * (1 - log B / log Q - γ) ≥ 1`.
* `ArithmeticKakeya.one_le_mul_saving`: the last hypothesis holds for the parameters of the
  construction.
-/

public section

namespace ArithmeticKakeya

/-! ### Inequalities for general parameters -/

private lemma natCast_rpow_log_div_log {B Q : ℕ} (hB : B ≠ 0) (hQ : 1 < Q) :
    (Q : ℝ) ^ (Real.log B / Real.log Q) = B := by
  rw [Real.log_div_log, Real.rpow_logb (mod_cast Nat.zero_lt_of_lt hQ) (mod_cast hQ.ne')
    (mod_cast Nat.pos_of_ne_zero hB)]

lemma pow_log_succ_le_mul_rpow {B Q n : ℕ} (hB : B ≠ 0) (hQ : 1 < Q) (hn : n ≠ 0) :
    (B : ℝ) ^ (Nat.log Q n + 1) ≤ B * (n : ℝ) ^ (Real.log B / Real.log Q) := by
  rw [pow_succ']
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg B)
  nth_rw 1 [← natCast_rpow_log_div_log hB hQ]
  rw [Real.rpow_pow_comm (Nat.cast_nonneg Q)]
  apply Real.rpow_le_rpow (by positivity) (mod_cast Nat.pow_log_le_self Q hn)
  exact div_nonneg (Real.log_natCast_nonneg B) (Real.log_natCast_nonneg Q)

lemma mul_rpow_le_rpow_of_pow_le {B Q E n : ℕ} {γ : ℝ} (hBQ : B ≤ Q) (hQ : 1 < Q)
    (hE : 1 ≤ E * (1 - Real.log B / Real.log Q - γ)) (hn : Q ^ E ≤ n) :
    B * (n : ℝ) ^ (Real.log B / Real.log Q) ≤ (n : ℝ) ^ (1 - γ) := by
  generalize Real.log B / Real.log Q = β at hE ⊢
  have hn' : (0 : ℝ) < n := mod_cast (pow_pos (Nat.zero_lt_of_lt hQ) E).trans_le hn
  have hδ : 0 ≤ 1 - β - γ := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) E) h.le]
  rw [← sub_add_cancel (1 - γ) β, Real.rpow_add hn', sub_right_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine le_trans ?_ (Real.rpow_le_rpow (by positivity) (Nat.cast_le (α := ℝ).2 hn) hδ)
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg Q)]
  refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (mod_cast hQ.le) hE)
  rw [Real.rpow_one]
  exact_mod_cast hBQ

/-! ### The saving for the parameters of the construction -/

/-- The inequality in `x = log (log k)` to which `one_le_mul_saving` reduces for `k ≥ 4`. -/
lemma one_le_mul_sub_of_le {x : ℝ} (hx : 27 / 100 ≤ x) :
    1 ≤ (10 * x + 100) * (3 / (22 * (x + 13 / 5)) - 1 / 100 / x) := by
  have hx0 : 0 < x := by linarith
  rw [div_div, div_sub_div _ _ (by positivity) (by positivity), mul_div_assoc',
    one_le_div (by positivity)]
  nlinarith

private lemma exp_le_inv_one_sub {x : ℝ} (hx : x < 1) : Real.exp x ≤ (1 - x)⁻¹ := by
  rw [le_inv_comm₀ (Real.exp_pos x) (by linarith), ← Real.exp_neg]
  linarith [Real.add_one_le_exp (-x)]

lemma le_log_log_four : 27 / 100 ≤ Real.log (Real.log 4) := by
  have h₄ := Real.log_mul (two_ne_zero' ℝ) (two_ne_zero' ℝ)
  norm_num at h₄
  have hexp := exp_le_inv_one_sub (by norm_num : (27 / 100 : ℝ) < 1)
  rw [Real.le_log_iff_exp_le (by linarith [Real.log_two_gt_d9]), h₄]
  norm_num at hexp
  linarith [Real.log_two_gt_d9]

private lemma le_log_log_three : 1 / 12 ≤ Real.log (Real.log 3) := by
  have hexp := exp_le_inv_one_sub (by norm_num : (1 / 12 : ℝ) < 1)
  rw [Real.le_log_iff_exp_le (by linarith [Real.log_three_gt_d9])]
  norm_num at hexp
  linarith [Real.log_three_gt_d9]

lemma c_div_log_log_le {k : ℕ} (hk : 3 ≤ k) : c / Real.log (Real.log k) ≤ 12 / 100 := by
  have h := le_log_log_three.trans (Real.log_le_log (by linarith [Real.log_three_gt_d9])
    (Real.log_le_log three_pos (mod_cast hk : (3 : ℝ) ≤ k)))
  rw [c, div_le_iff₀ (by linarith)]
  linarith

private lemma log_sizeBound_three_div_le :
    Real.log (sizeBound 3) / Real.log (modulus 3) ≤ 17 / 20 := by
  rw [sizeBound_three, modulus_three, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h := Real.log_le_log (by positivity)
    (by norm_num : (44677785600 : ℝ) ^ 20 ≤ 3710369067405 ^ 17)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h ⊢
  linarith

lemma one_le_mul_saving_three :
    1 ≤ ((⌈10 * Real.log (Real.log 3)⌉₊ + 100 : ℕ) : ℝ) *
      (1 - Real.log (sizeBound 3) / Real.log (modulus 3) - c / Real.log (Real.log 3)) := by
  have hc := c_div_log_log_le (le_refl 3)
  rw [Nat.cast_ofNat] at hc
  rw [Nat.cast_add, Nat.cast_ofNat]
  refine le_trans (by norm_num : (1 : ℝ) ≤ 100 * (3 / 100)) (mul_le_mul ?_ ?_ ?_ ?_)
  · linarith [Nat.cast_nonneg (α := ℝ) ⌈10 * Real.log (Real.log 3)⌉₊]
  · linarith [log_sizeBound_three_div_le]
  · norm_num
  · positivity

private lemma log_sizeBound_add_le {k : ℕ} (hk : k ≠ 0) :
    Real.log (sizeBound k) + 3 * Real.log k ≤ Real.log (modulus k) := by
  have hB := sizeBound_ne_zero hk
  have h := Real.log_le_log (by positivity)
    (Nat.cast_le (α := ℝ).2 (sizeBound_mul_pow_le_modulus k))
  rwa [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Nat.cast_ofNat] at h

private lemma three_div_le_one_sub {k : ℕ} (hk : 3 ≤ k) :
    3 / (22 * (Real.log (Real.log k) + 13 / 5)) ≤
      1 - Real.log (sizeBound k) / Real.log (modulus k) := by
  have hLL := Real.log_nonneg (one_le_log_of_three_le hk)
  have hQ : 0 < Real.log (modulus k) := Real.log_pos (mod_cast one_lt_modulus (by grind))
  rw [one_sub_div hQ.ne', div_le_div_iff₀ (by positivity) hQ]
  linarith [log_modulus_le hk, mul_le_mul_of_nonneg_right
    (by linarith [log_sizeBound_add_le (by grind : k ≠ 0)] :
      3 * Real.log k ≤ Real.log (modulus k) - Real.log (sizeBound k))
    (by positivity : 0 ≤ 22 * (Real.log (Real.log k) + 13 / 5))]

lemma one_le_mul_saving {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ ((⌈10 * Real.log (Real.log k)⌉₊ + 100 : ℕ) : ℝ) *
      (1 - Real.log (sizeBound k) / Real.log (modulus k) - c / Real.log (Real.log k)) := by
  rcases hk.eq_or_lt with rfl | hk4
  · exact_mod_cast one_le_mul_saving_three
  have hx := le_log_log_four.trans (Real.log_le_log (Real.log_pos (by norm_num))
    (Real.log_le_log four_pos (mod_cast hk4 : (4 : ℝ) ≤ k)))
  have hσ := three_div_le_one_sub hk
  generalize Real.log (Real.log k) = x at hx hσ ⊢
  have hx0 : 0 < x := by linarith
  have hf := one_le_mul_sub_of_le hx
  rw [Nat.cast_add, Nat.cast_ofNat, c]
  apply hf.trans (mul_le_mul _ (by linarith) _ (by positivity))
  · linarith [Nat.le_ceil (10 * x)]
  · exact ((pos_iff_pos_of_mul_pos (zero_lt_one.trans_le hf)).1 (by positivity)).le

end ArithmeticKakeya
