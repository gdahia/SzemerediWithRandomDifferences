/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Computability.Ackermann
public import SzemerediWithRandomDifferences.Progressions
import DensityHalesJewett.Main

/-!
# Varnavides' theorem for subsets of `{1, …, n}`

Varnavides' theorem, `Combinatorics.ArithmeticProgression.exists_many_of_density_nat` from
DensityHalesJewett, bounds from below the number of `k`-term progressions in a set of natural
numbers. This file restates it for a set `S ⊆ {1, …, n}` of integers with at least `δ * n`
elements: `RandomDifferences.progressions k n S` has at least
`n ^ 2 / ack (4 * k + 1) (k + ⌈2 / δ⌉₊)` elements. This is Theorem 2.1 of Dahia,
*Szemerédi's theorem with random differences and arithmetic Kakeya*,
[arXiv:2610.18859](https://arxiv.org/abs/2610.18859).

## Main statements

* `RandomDifferences.sq_div_ack_le_card_progressions`: Varnavides' theorem for subsets of
  `{1, …, n}` in `ℤ`.
-/

public section

namespace RandomDifferences

open Combinatorics.ArithmeticProgression Finset

/-- The pairs in `containedProgressions k (n + 1) S` are progressions in `S ⊆ {1, …, n}` with
common difference in `{1, …, n}`. -/
private lemma of_mem_containedProgressions {k n : ℕ} (hk : k ≠ 0) {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    {a d : ℕ} (h : (a, d) ∈ containedProgressions k (n + 1) S) :
    a ∈ Icc 1 n ∧ d ∈ Icc 1 n ∧ ∀ i < k, a + i * d ∈ S := by
  simp only [containedProgressions, mem_filter, mem_product, mem_range] at h
  obtain ⟨⟨-, hd⟩, hd0, hS'⟩ := h
  have h₀ := hS' ⟨0, Nat.pos_of_ne_zero hk⟩
  rw [Fin.val_mk, zero_mul, add_zero] at h₀
  refine ⟨hS h₀, by grind, ?_⟩
  intro i hi
  exact hS' ⟨i, hi⟩

/-- Varnavides' theorem for subsets of `{1, …, n}` in `ℕ`. -/
private lemma sq_div_ack_le_card_containedProgressions {k : ℕ} (hk : 3 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) {n : ℕ} (hn : ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ n) {S : Finset ℕ}
    (hS : S ⊆ Icc 1 n) (hSδ : δ * n ≤ #S) :
    (n : ℝ) ^ 2 / ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ #(containedProgressions k (n + 1) S) := by
  have hn1 : (1 : ℝ) ≤ n := mod_cast (ack_pos _ _).trans_le hn
  have h := exists_many_of_density_nat hk (half_pos hδ) (n := n + 1)
  rw [one_div_div, Nat.cast_add, Nat.cast_one] at h
  refine le_trans ?_ (h (hn.trans n.le_succ) S ?_ ?_)
  · exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
  · intro x hx
    grind [hS hx]
  · linarith [mul_le_mul_of_nonneg_left hn1 hδ.le]

/-- **Varnavides' theorem** for subsets of `{1, …, n}` in `ℤ`. If `S ⊆ {1, …, n}` has at least
`δ * n` elements, then at least `n ^ 2 / ack (4 * k + 1) (k + ⌈2 / δ⌉₊)` pairs `(a, d)` with `a`
and `d` in `{1, …, n}` have `a + i * d ∈ S` for every `i < k`. -/
lemma sq_div_ack_le_card_progressions {k : ℕ} (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) {n : ℕ}
    (hn : ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ n) {S : Finset ℤ} (hS : S ⊆ Icc 1 (n : ℤ))
    (hSδ : δ * n ≤ #S) :
    (n : ℝ) ^ 2 / ack (4 * k + 1) (k + ⌈2 / δ⌉₊) ≤ #(progressions k n S) := by
  have hSn : S ⊆ (Icc 1 n).image (Nat.cast : ℕ → ℤ) := by
    intro x hx
    rw [mem_image]
    exact ⟨x.toNat, by grind [hS hx], by grind [hS hx]⟩
  obtain ⟨S', hS', rfl⟩ := subset_image_iff.1 hSn
  rw [card_image_of_injective _ Nat.cast_injective] at hSδ
  apply (sq_div_ack_le_card_containedProgressions hk hδ hn hS' hSδ).trans
  rw [Nat.cast_le]
  apply card_le_card_of_injOn fun (a, d) ↦ ((a : ℤ), (d : ℤ))
  · rintro ⟨a, d⟩ hp
    obtain ⟨ha, hd, haS⟩ := of_mem_containedProgressions (by grind) hS' hp
    refine mem_progressions.2 ⟨by simpa using ha, by simpa using hd, ?_⟩
    intro i hi
    exact mem_image.2 ⟨_, haS i hi, by simp⟩
  · rintro ⟨a, d⟩ - ⟨a', d'⟩ - h
    simp_all

end RandomDifferences
