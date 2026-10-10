/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import SzemerediWithRandomDifferences.ArithmeticKakeya.Residues

/-!
# The base set of the Green–Ruzsa construction

For a modulus `Q` and a length `k`, the base set is the union over `d < Q` of the `k`-term
progressions with common difference `d` starting at the residue of `d ^ 2` modulo `Q`. It lies
in `{0, …, k * Q - k}`, and its size is controlled by the residues of `d ^ 2 + j * d`.

## Main statements

* `ArithmeticKakeya.add_le_of_mem_baseSet`: the base set lies in `{0, …, k * Q - k}`.
* `ArithmeticKakeya.card_baseSet_le`: the base set has at most `k ^ 2 * r` elements when
  `d ^ 2 + j * d` takes at most `r` residues modulo `Q` for each `j < k`.
-/

public section

namespace ArithmeticKakeya

open Finset

/-- The base set of the Green–Ruzsa construction: the numbers `d ^ 2 % Q + j * d` with `d < Q`
and `j < k`. -/
def baseSet (Q k : ℕ) : Finset ℕ :=
  (range Q ×ˢ range k).image fun x ↦ x.1 ^ 2 % Q + x.2 * x.1

theorem mem_baseSet {Q k s : ℕ} :
    s ∈ baseSet Q k ↔ ∃ d < Q, ∃ j < k, d ^ 2 % Q + j * d = s := by
  sorry

theorem add_mul_mem_baseSet {Q k d j : ℕ} (hd : d < Q) (hj : j < k) :
    d ^ 2 % Q + j * d ∈ baseSet Q k := by
  sorry

theorem add_le_of_mem_baseSet {Q k s : ℕ} (hs : s ∈ baseSet Q k) : s + k ≤ k * Q := by
  sorry

/-- A set of numbers below `k * Q` has at most `k` elements in each residue class modulo
`Q`. -/
theorem card_le_mul_card_image_mod {s : Finset ℕ} {k Q : ℕ} (hs : ∀ a ∈ s, a < k * Q) :
    #s ≤ k * #(s.image (· % Q)) := by
  sorry

theorem card_baseSet_le {Q k r : ℕ} (hr : ∀ j < k, #(residues Q j) ≤ r) :
    #(baseSet Q k) ≤ k ^ 2 * r := by
  sorry

end ArithmeticKakeya
