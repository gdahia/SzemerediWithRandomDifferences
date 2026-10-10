/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
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

theorem pow_log_succ_le_mul_rpow {B Q n : ℕ} (hB : B ≠ 0) (hQ : 1 < Q) (hn : n ≠ 0) :
    (B : ℝ) ^ (Nat.log Q n + 1) ≤ B * (n : ℝ) ^ (Real.log B / Real.log Q) := by
  sorry

theorem mul_rpow_le_rpow_of_pow_le {B Q E n : ℕ} {γ : ℝ} (hB : B ≠ 0) (hBQ : B ≤ Q) (hQ : 1 < Q)
    (hE : 1 ≤ E * (1 - Real.log B / Real.log Q - γ)) (hn : Q ^ E ≤ n) :
    B * (n : ℝ) ^ (Real.log B / Real.log Q) ≤ (n : ℝ) ^ (1 - γ) := by
  sorry

/-! ### The saving for the parameters of the construction -/

/-- The inequality in `x = log (log k)` to which `one_le_mul_saving` reduces for `k ≥ 4`. -/
theorem one_le_mul_sub_of_le {x : ℝ} (hx : 27 / 100 ≤ x) :
    1 ≤ (10 * x + 100) * (3 / (22 * (x + 13 / 5)) - 1 / 100 / x) := by
  sorry

theorem le_log_log_four : 27 / 100 ≤ Real.log (Real.log 4) := by
  sorry

theorem one_le_mul_saving_three :
    1 ≤ ((⌈10 * Real.log (Real.log 3)⌉₊ + 100 : ℕ) : ℝ) *
      (1 - Real.log (sizeBound 3) / Real.log (modulus 3) - c / Real.log (Real.log 3)) := by
  sorry

theorem one_le_mul_saving {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ ((⌈10 * Real.log (Real.log k)⌉₊ + 100 : ℕ) : ℝ) *
      (1 - Real.log (sizeBound k) / Real.log (modulus k) - c / Real.log (Real.log k)) := by
  sorry

end ArithmeticKakeya
