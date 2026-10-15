/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Nth

/-!
# Parameters of the Green–Ruzsa construction

The modulus, the constant in the exponent and the threshold for `n` that appear in the
statement of `ArithmeticKakeya.exists_card_le_rpow_forall_exists_arithmeticProgression`, together
with the bound on the size of the base set used in its proof.
-/

@[expose] public section

namespace ArithmeticKakeya

open Finset

/-- The modulus `Q` of the Green–Ruzsa construction for progressions of length `k`: the
product of the first `⌈10 * log k⌉` odd primes. -/
noncomputable def modulus (k : ℕ) : ℕ :=
  ∏ i ∈ range ⌈10 * Real.log k⌉₊, Nat.nth Nat.Prime (i + 1)

/-- The bound `B = k ^ 2 * ∏ p ∣ Q, (p + 1) / 2` on the size of the base set of the
Green–Ruzsa construction, where `Q = modulus k`. -/
noncomputable def sizeBound (k : ℕ) : ℕ :=
  k ^ 2 * ∏ i ∈ range ⌈10 * Real.log k⌉₊, (Nat.nth Nat.Prime (i + 1) + 1) / 2

/-- The constant in the exponent `1 - c / log (log k)` of the Green–Ruzsa bound.

With `Q = modulus k` and `B = sizeBound k`, the construction has size at most
`B * n ^ (log B / log Q)`, so a constant works for `k` when it is less than
`(1 - log B / log Q) * log (log k)`. This quantity is about `0.0144` for `k = 3` and is larger
for every `k ≥ 4`. -/
noncomputable def c : ℝ := 1 / 100

lemma c_pos : 0 < c := by
  norm_num [c]

/-- A threshold for `n` in the Green–Ruzsa bound for progressions of length `k`.

With `Q = modulus k`, `B = sizeBound k`, `β = log B / log Q` and `γ = c / log (log k)`, the
construction has size at most `B * n ^ β`, which is at most `n ^ (1 - γ)` once
`n ≥ Q ^ (1 / (1 - β - γ))`. The exponent `1 / (1 - β - γ)` is about `21.6` for `k = 3`, less
than `9` for `4 ≤ k ≤ 10`, and grows like `2 * log (log k)`. The exponent chosen here is larger,
so that the estimate follows from Chebyshev's bounds on primes.

As `Q = k ^ O(log (log k))`, this threshold is `k ^ O(log (log k) ^ 2)`. -/
noncomputable def n₀ (k : ℕ) : ℕ :=
  modulus k ^ (⌈10 * Real.log (Real.log k)⌉₊ + 100)

end ArithmeticKakeya
