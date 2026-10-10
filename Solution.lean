/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Nat.Notation
public import SzemerediWithRandomDifferences.Basic

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

public section

theorem SzemerediWithRandomDifferences.main_result (n : ℕ) : n + n = 2 * n := by
  exact add_self_eq_two_mul n
