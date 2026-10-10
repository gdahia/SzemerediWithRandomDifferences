/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

import Mathlib.Data.Nat.Notation

/-!
# Supporting proof development

Placeholder for the library containing the proof. Code imported only by
`Solution.lean` may use arbitrary pinned Git dependencies; the trusted
statement surface in `Challenge.lean` should stay much smaller.
-/

public section

namespace SzemerediWithRandomDifferences

/-- Placeholder library result used to prove the placeholder advertised statement. -/
theorem add_self_eq_two_mul (n : ℕ) : n + n = 2 * n := by
  exact (Nat.two_mul n).symm

end SzemerediWithRandomDifferences
