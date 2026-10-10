/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.RandomDifferences

/-!
# Proof of Szemerédi's theorem with random differences

This module proves the declaration stated in `Challenge.lean`, deriving it from
`RandomDifferences.exists_forall_tendsto_setBernoulli_isAvoidable`.

The random set of differences is Mathlib's `setBer(Set.Icc 1 n, p)`, the distribution of the
subset of `{1, …, n}` that contains each element independently with probability `p`. A `k`-term
arithmetic progression with first term `a` and common difference `d ≠ 0` consists of the numbers
`a + i * d` for `i < k`.
-/

@[expose] public section

open Filter Finset ProbabilityTheory unitInterval
open scoped Topology

namespace RandomDifferences

/-- **Szemerédi's theorem with random differences.** There is `c > 0` such that for every
`k ≥ 3` and `δ > 0` there is `C > 0` with the following property. Let `D` be a `p n`-random
subset of `{1, …, n}`, where `p n ≥ C * n ^ (-c / log (log k))` for all large `n`. The probability
that some subset of `{1, …, n}` with at least `δ * n` elements contains no `k`-term arithmetic
progression with common difference in `D` tends to `0` as `n` tends to infinity. -/
theorem exists_forall_tendsto_setBernoulli_exists_forall_exists_notMem :
    ∃ c > (0 : ℝ), ∀ k ≥ (3 : ℕ), ∀ δ > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : ℕ → I,
      (∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (-c / Real.log (Real.log k)) ≤ p n) →
      Tendsto (fun n ↦ setBer(Set.Icc 1 n, p n)
        {D | ∃ S : Finset ℕ, S ⊆ Icc 1 n ∧ δ * n ≤ #S ∧
          ∀ d ∈ D, d ≠ 0 → ∀ a, ∃ i < k, a + i * d ∉ S}) atTop (𝓝 0) := by
  obtain ⟨c, hc, h⟩ := exists_forall_tendsto_setBernoulli_isAvoidable
  refine ⟨c, hc, ?_⟩
  intro k hk δ hδ
  obtain ⟨C, hC, hp⟩ := h k hk δ hδ
  refine ⟨C, hC, ?_⟩
  intro p hpC
  simpa only [isAvoidable_iff] using hp p hpC

end RandomDifferences
