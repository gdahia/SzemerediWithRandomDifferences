/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.ArithmeticKakeya.Defs
public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues
import Mathlib.NumberTheory.Chebyshev

/-!
# Estimates for the Green–Ruzsa modulus

Bounds relating `modulus k`, the product of the first `⌈10 * log k⌉` odd primes, to
`sizeBound k`, and an upper bound on its logarithm.

## Main statements

* `ArithmeticKakeya.card_residues_modulus_le`: `d ^ 2 + j * d` takes at most
  `∏ p ∣ Q, (p + 1) / 2` residues modulo `Q = modulus k`.
* `ArithmeticKakeya.sizeBound_mul_pow_le_modulus`: `sizeBound k * k ^ 3 ≤ modulus k`.
* `Nat.nth_prime_le_add_two_sq`: the prime of index `n` is at most `(n + 2) ^ 2`.
* `ArithmeticKakeya.log_modulus_le`: `log (modulus k) ≤ 22 * log k * (log (log k) + 13 / 5)`.
-/

public section

/-- A polynomial bound on the primes, from Chebyshev's lower bound on the prime counting
function. -/
theorem Nat.nth_prime_le_add_two_sq (n : ℕ) : Nat.nth Nat.Prime n ≤ (n + 2) ^ 2 := by
  sorry

namespace ArithmeticKakeya

open Finset

theorem one_lt_modulus {k : ℕ} (hk : 2 ≤ k) : 1 < modulus k := by
  sorry

theorem sizeBound_ne_zero {k : ℕ} (hk : k ≠ 0) : sizeBound k ≠ 0 := by
  sorry

theorem card_residues_modulus_le (k j : ℕ) :
    #(residues (modulus k) j) ≤
      ∏ i ∈ range ⌈10 * Real.log k⌉₊, (Nat.nth Nat.Prime (i + 1) + 1) / 2 := by
  sorry

/-- Each factor `2 * p / (p + 1)` of `modulus k / sizeBound k * k ^ 2` is at least `7 / 4`,
except for `p = 3` and `p = 5`, and `(7 / 4) ^ 10 > e ^ 5`. -/
theorem sizeBound_mul_pow_le_modulus (k : ℕ) : sizeBound k * k ^ 3 ≤ modulus k := by
  sorry

theorem sizeBound_le_modulus {k : ℕ} (hk : k ≠ 0) : sizeBound k ≤ modulus k := by
  sorry

theorem log_modulus_le {k : ℕ} (hk : 3 ≤ k) :
    Real.log (modulus k) ≤ 22 * Real.log k * (Real.log (Real.log k) + 13 / 5) := by
  sorry

/-! ### The case `k = 3` -/

theorem ceil_ten_mul_log_three : ⌈10 * Real.log 3⌉₊ = 11 := by
  sorry

theorem modulus_three : modulus 3 = 3710369067405 := by
  sorry

theorem sizeBound_three : sizeBound 3 = 44677785600 := by
  sorry

end ArithmeticKakeya
