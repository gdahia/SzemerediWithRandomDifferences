/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import DensityHalesJewett.Varnavides
public import Mathlib.Data.Set.Card
public import SzemerediWithRandomDifferences.CommonDiffs

/-!
# Translates of a set with a progression of every difference

Let `Y ⊆ {1, …, M}` contain a `k`-term arithmetic progression with every common difference in
`{1, …, n}`. Every `k`-term progression in a set `S ⊆ {1, …, n}` is a translate of one of them.
If `S` contains many progressions, then by the pigeonhole principle some translate of `Y` meets
`S` in a set with many common differences.

Translations by negative integers are avoided by writing the translate of `Y` as the image of
`y ↦ y + n - u`.

## Main statements

* `RandomDifferences.exists_translate_subset_le_ncard`: the pigeonhole argument.
-/

public section

namespace RandomDifferences

open Combinatorics Combinatorics.ArithmeticProgression Finset

/-- The image of `Y` under `y ↦ y + n - u`. -/
def translate (n u : ℕ) (Y : Finset ℕ) : Finset ℕ :=
  Y.image (· + n - u)

lemma mem_translate {n u x : ℕ} {Y : Finset ℕ} : x ∈ translate n u Y ↔ ∃ y ∈ Y, y + n - u = x := by
  simp [translate]

/-- The pairs in `containedProgressions k (n + 1) S` are progressions in `S ⊆ {1, …, n}` with
common difference in `{1, …, n}`. -/
lemma of_mem_containedProgressions {k n : ℕ} (hk : k ≠ 0) {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    {p : ℕ × ℕ} (hp : p ∈ containedProgressions k (n + 1) S) :
    p.1 ∈ Icc 1 n ∧ p.2 ∈ Icc 1 n ∧ ∀ i < k, p.1 + i * p.2 ∈ S := by
  simp only [containedProgressions, mem_filter, mem_product, mem_range] at hp
  have h₀ := hp.2.2 ⟨0, Nat.pos_of_ne_zero hk⟩
  rw [Fin.val_mk, zero_mul, add_zero] at h₀
  refine ⟨hS h₀, by grind, ?_⟩
  intro i hi
  exact hp.2.2 ⟨i, hi⟩

/-- If `Y ⊆ {1, …, M}` contains a `k`-term progression with every common difference in
`{1, …, n}` and `S ⊆ {1, …, n}` contains at least `(M + n) * b` progressions, then some
translate of a subset of `Y` is contained in `S` and has at least `b` common differences. -/
lemma exists_translate_subset_le_ncard {k n M : ℕ} (hk : k ≠ 0) (hn : n ≠ 0) {Y S : Finset ℕ}
    (hYM : Y ⊆ Icc 1 M) (hY : ∀ d ∈ Icc 1 n, d ∈ commonDiffs k Y) (hS : S ⊆ Icc 1 n)
    {b : ℝ} (hb : (M + n) • b ≤ #(containedProgressions k (n + 1) S)) :
    ∃ u < M + n, ∃ Y' ⊆ Y, translate n u Y' ⊆ S ∧
      b ≤ (commonDiffs k (translate n u Y') ∩ Set.Icc 1 n).ncard := by
  have hY' : ∀ d ∈ Icc 1 n, ∃ a, ∀ i < k, a + i * d ∈ Y := by
    intro d hd
    exact (mem_commonDiffs_nat.1 (hY d hd)).2
  choose! y hy using hY'
  have hyM : ∀ d ∈ Icc 1 n, y d ≤ M := by
    intro d hd
    grind [hYM (hy d hd 0 (Nat.pos_of_ne_zero hk))]
  have hmaps : ∀ p ∈ containedProgressions k (n + 1) S, y p.2 + n - p.1 ∈ range (M + n) := by
    intro p hp
    grind [of_mem_containedProgressions hk hS hp]
  rw [← card_range (M + n)] at hb
  obtain ⟨u, hu, hcard⟩ :=
    exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps (by simp [hn]) hb
  refine ⟨u, mem_range.1 hu, {z ∈ Y | u ≤ z + n ∧ z + n - u ∈ S}, filter_subset _ _, ?_, ?_⟩
  · intro x hx
    grind [mem_translate]
  · apply hcard.trans
    rw [← card_image_of_injOn (f := Prod.snd), ← Set.ncard_coe_finset, Nat.cast_le]
    · apply Set.ncard_le_ncard _ ((Set.finite_Icc 1 n).inter_of_right _)
      intro d hd
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hd
      rw [mem_filter] at hp
      obtain ⟨hp₁, hp₂, hpS⟩ := of_mem_containedProgressions hk hS hp.1
      refine ⟨mem_commonDiffs_nat.2 ⟨by grind, p.1, ?_⟩, by grind⟩
      intro i hi
      rw [mem_translate]
      refine ⟨y p.2 + i * p.2, ?_, by grind⟩
      rw [mem_filter]
      exact ⟨hy p.2 hp₂ i hi, by grind, by grind [hpS i hi]⟩
    · intro p hp q hq hpq
      rw [mem_coe, mem_filter] at hp hq
      apply Prod.ext _ hpq
      grind [of_mem_containedProgressions hk hS hp.1, of_mem_containedProgressions hk hS hq.1]

end RandomDifferences
