/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import SzemerediWithRandomDifferences.CommonDiffs
public import SzemerediWithRandomDifferences.Progressions
import Mathlib.Combinatorics.Pigeonhole

/-!
# Translates of a set with a progression of every difference

Let `Y ⊆ {1, …, M}` contain a `k`-term arithmetic progression `P_d` with every common difference
`d ∈ {1, …, n}`. Every `k`-term progression in `{1, …, n}` with common difference `d` is
`{t} + P_d` for an integer `t` with `-M ≤ t < n`. If a set `S` contains many progressions, then
by the pigeonhole principle many of them share the same `t`, and `({t} + Y) ∩ S` has many
common differences.

## Main statements

* `RandomDifferences.exists_le_ncard_commonDiffs_singleton_add_inter`: the pigeonhole argument.
-/

public section

namespace RandomDifferences

open Combinatorics.ArithmeticProgression Finset Pointwise

/-- If `Y` contains the progression `y + i * d` and `S` contains the progression `a + i * d`
for `i < k`, then `d` is a common difference of `({a - y} + Y) ∩ S`. -/
lemma mem_commonDiffs_singleton_add_inter {k : ℕ} {Y S : Finset ℤ} {y a d : ℤ} (hd : d ≠ 0)
    (hy : ∀ i < k, y + i * d ∈ Y) (ha : ∀ i < k, a + i * d ∈ S) :
    d ∈ commonDiffs k (({a - y} + Y) ∩ S) := by
  refine mem_commonDiffs.2 ⟨hd, a, ?_⟩
  intro i hi
  exact mem_inter.2 ⟨mem_add.2 ⟨a - y, mem_singleton_self _, _, hy i hi, by ring⟩, ha i hi⟩

/-- Let `Y ⊆ {1, …, M}` contain a `k`-term progression with every common difference in
`{1, …, n}`, and let `S` contain at least `(M + n) * b` progressions with first term and common
difference in `{1, …, n}`. Then for some `t` with `-M ≤ t < n`, the set `({t} + Y) ∩ S` has at
least `b` common differences in `{1, …, n}`. -/
lemma exists_le_ncard_commonDiffs_singleton_add_inter {k n M : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    {Y S : Finset ℤ} (hYM : Y ⊆ Icc 1 (M : ℤ)) (hY : ∀ d ∈ Icc 1 (n : ℤ), d ∈ commonDiffs k Y)
    {b : ℝ} (hb : (M + n) • b ≤ #(progressions k n S)) :
    ∃ t ∈ Ico (-(M : ℤ)) n, b ≤ (commonDiffs k (({t} + Y) ∩ S) ∩ Set.Icc 1 (n : ℤ)).ncard := by
  choose! y hy using fun d hd ↦ (mem_commonDiffs.1 (hY d hd)).2
  have hmaps : ∀ p ∈ progressions k n S, (fun (a, d) ↦ a - y d) p ∈ Ico (-(M : ℤ)) n := by
    rintro ⟨a, d⟩ hp
    obtain ⟨ha, hd, -⟩ := mem_progressions.1 hp
    grind [hYM (hy d hd 0 (Nat.pos_of_ne_zero hk))]
  rw [← (Int.card_Ico _ _).trans (by grind : (n - -(M : ℤ)).toNat = M + n)] at hb
  obtain ⟨t, ht, hcard⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps (nonempty_Ico.2 (by grind)) hb
  refine ⟨t, ht, hcard.trans ?_⟩
  rw [← Set.ncard_coe_finset, Nat.cast_le]
  apply Set.ncard_le_ncard_of_injOn Prod.snd _ _ ((Set.finite_Icc _ _).inter_of_right _)
  · rintro ⟨a, d⟩ hp
    obtain ⟨hp', rfl⟩ := mem_filter.1 hp
    obtain ⟨-, hd, haS⟩ := mem_progressions.1 hp'
    exact ⟨mem_commonDiffs_singleton_add_inter (by grind) (hy d hd) haS, by simpa using hd⟩
  · rintro ⟨a, d⟩ hp ⟨a', d'⟩ hq hdd
    grind [mem_filter.1 hp, mem_filter.1 hq]

end RandomDifferences
