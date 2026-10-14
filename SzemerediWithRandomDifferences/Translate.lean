/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Varnavides
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import SzemerediWithRandomDifferences.CommonDiffs
import Mathlib.Combinatorics.Pigeonhole

/-!
# Translates of a set with a progression of every difference

Let `Y ⊆ {1, …, M}` contain a `k`-term arithmetic progression with every common difference in
`{1, …, n}`. Every `k`-term progression in a set `S ⊆ {1, …, n}` is a translate of one of them,
by an integer `t` with `-M ≤ t < n`. If `S` contains many progressions, then by the pigeonhole
principle some translate of `Y` meets `S` in a set with many common differences.

## Main statements

* `RandomDifferences.exists_translate_subset_le_ncard`: the pigeonhole argument.
-/

public section

namespace RandomDifferences

open Combinatorics Combinatorics.ArithmeticProgression Finset

/-- The natural numbers of the form `y + t` with `y ∈ Y`, for an integer `t`. -/
noncomputable def translate (t : ℤ) (Y : Finset ℕ) : Finset ℕ :=
  (Y.image fun y : ℕ ↦ (y : ℤ) + t).preimage Nat.cast Nat.cast_injective.injOn

lemma mem_translate {t : ℤ} {x : ℕ} {Y : Finset ℕ} :
    x ∈ translate t Y ↔ ∃ y ∈ Y, (y : ℤ) + t = x := by
  simp [translate]

/-- The pairs in `containedProgressions k (n + 1) S` are progressions in `S ⊆ {1, …, n}` with
common difference in `{1, …, n}`. -/
lemma of_mem_containedProgressions {k n : ℕ} (hk : k ≠ 0) {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    {a d : ℕ} (h : (a, d) ∈ containedProgressions k (n + 1) S) :
    a ∈ Icc 1 n ∧ d ∈ Icc 1 n ∧ ∀ i < k, a + i * d ∈ S := by
  simp only [containedProgressions, mem_filter, mem_product, mem_range] at h
  obtain ⟨⟨-, hd⟩, hd0, hS'⟩ := h
  have h₀ := hS' ⟨0, Nat.pos_of_ne_zero hk⟩
  rw [Fin.val_mk, zero_mul, add_zero] at h₀
  refine ⟨hS h₀, by grind, ?_⟩
  intro i hi
  exact hS' ⟨i, hi⟩

/-- If `Y ⊆ {1, …, M}` contains a `k`-term progression with every common difference in
`{1, …, n}` and `S ⊆ {1, …, n}` contains at least `(M + n) * b` progressions, then some
translate of a subset of `Y` is contained in `S` and has at least `b` common differences. -/
lemma exists_translate_subset_le_ncard {k n M : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) {Y S : Finset ℕ}
    (hYM : Y ⊆ Icc 1 M) (hY : ∀ d ∈ Icc 1 n, d ∈ commonDiffs k Y) (hS : S ⊆ Icc 1 n)
    {b : ℝ} (hb : (M + n) • b ≤ #(containedProgressions k (n + 1) S)) :
    ∃ t ∈ Ico (-(M : ℤ)) n, ∃ Y' ⊆ Y, translate t Y' ⊆ S ∧
      b ≤ (commonDiffs k (translate t Y') ∩ Set.Icc 1 n).ncard := by
  have hY' : ∀ d ∈ Icc 1 n, ∃ a, ∀ i < k, a + i * d ∈ Y := by
    intro d hd
    obtain ⟨-, h⟩ := mem_commonDiffs_nat.1 (hY d hd)
    exact h
  choose! y hy using hY'
  have hyM : ∀ d ∈ Icc 1 n, y d ∈ Icc 1 M := by
    intro d hd
    grind [hYM (hy d hd 0 (Nat.pos_of_ne_zero hk))]
  have hmaps : ∀ p ∈ containedProgressions k (n + 1) S,
      (fun (a, d) ↦ (a : ℤ) - y d) p ∈ Ico (-(M : ℤ)) n := by
    rintro ⟨a, d⟩ hp
    grind [of_mem_containedProgressions hk hS hp]
  have hI : #(Ico (-(M : ℤ)) n) = M + n := (Int.card_Ico _ _).trans (by grind)
  rw [← hI] at hb
  obtain ⟨t, ht, hcard⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps (nonempty_Ico.2 (by grind)) hb
  refine ⟨t, ht, {z ∈ Y | ∃ x ∈ S, (z : ℤ) + t = x}, filter_subset _ _, ?_, ?_⟩
  · intro x hx
    grind [mem_translate]
  · apply hcard.trans
    rw [← card_image_of_injOn (f := Prod.snd), ← Set.ncard_coe_finset, Nat.cast_le]
    · apply Set.ncard_le_ncard _ ((Set.finite_Icc 1 n).inter_of_right _)
      intro d' hd'
      obtain ⟨⟨a, d⟩, hp, rfl⟩ := mem_image.1 hd'
      obtain ⟨hp, hat⟩ := mem_filter.1 hp
      obtain ⟨ha, hd, haS⟩ := of_mem_containedProgressions hk hS hp
      refine ⟨mem_commonDiffs_nat.2 ⟨by grind, a, ?_⟩, by grind⟩
      intro i hi
      rw [mem_translate]
      refine ⟨y d + i * d, mem_filter.2 ⟨hy d hd i hi, a + i * d, haS i hi, ?_⟩, ?_⟩ <;> grind
    · rintro ⟨a, d⟩ hp ⟨a', d'⟩ hq hdd
      simp only [coe_filter, Set.mem_ofPred_eq] at hp hq
      grind

end RandomDifferences
