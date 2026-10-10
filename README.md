# SzemerediWithRandomDifferences

A Lean 4 formalization laid out for submission to the
[Palomar registry](https://palomar-registry.org/), following
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

> **Status: scaffold.** The advertised theorem in `Challenge.lean` is still the
> template's toy placeholder, the statements in the library are unproved, and
> most of `formalization.yaml` is unfilled. This repository is not yet
> submittable; see [Before submitting](#before-submitting).

## Contents

`SzemerediWithRandomDifferences/ArithmeticKakeya.lean` proves, from intermediate
statements that are still `sorry`, Theorem 1.2 of Green and Ruzsa,
[*On the arithmetic Kakeya conjecture of Katz and Tao*](https://arxiv.org/abs/1712.02108),
as `ArithmeticKakeya.exists_subset_Icc_card_le_rpow`: for every `k ≥ 3` and
`n ≥ n₀ k` there is a subset of `{1, …, k * Q * n}` of size at most
`n ^ (1 - c / log (log k))` containing a `k`-term arithmetic progression with
every common difference in `{1, …, n}`. The constants are explicit:

- `ArithmeticKakeya.modulus k`, written `Q`, is the product of the first
  `⌈10 * log k⌉` odd primes;
- `ArithmeticKakeya.c` is `1 / 100`;
- `ArithmeticKakeya.n₀ k` is `Q ^ (⌈10 * log (log k)⌉ + 100)`, which is
  `k ^ O(log (log k) ^ 2)`.

The intermediate statements are in `SzemerediWithRandomDifferences/ArithmeticKakeya/`:

| File | Contents |
| --- | --- |
| `Defs.lean` | The parameters `modulus`, `sizeBound`, `c` and `n₀` |
| `Residues.lean` | The number of residues of `d ^ 2 + j * d` modulo primes and products |
| `BaseSet.lean` | The union of progressions for one modulus |
| `DigitSet.lean` | Numbers whose base-`Q` digits lie in a given set |
| `Construction.lean` | The construction for a general modulus |
| `Modulus.lean` | Estimates for the product of the first odd primes |
| `Threshold.lean` | The bound `n ^ (1 - c / log (log k))` for `n ≥ n₀ k` |

`SzemerediWithRandomDifferences/ArithmeticProgression.lean` defines
`Combinatorics.ArithmeticProgression`, a nonconstant arithmetic progression of
length `k` given by its initial term and common difference.

Modules use `public import` only for what their statements mention and a plain
`import` for what only their proofs use, so a change to a proof rebuilds that
module alone.

## Repository map

- `Challenge.lean` is the small statement surface a reader audits: each
  advertised declaration is stated with `sorry`.
- `Solution.lean` proves the same declarations from the full development.
- `SzemerediWithRandomDifferences/` contains the proof development.
- `comparator.json` tells `lake comparator` which declarations must match.
- `formalization.yaml` records the public result description, provenance,
  authorship, automation, fidelity, and review information.
- `LICENSE` contains the Apache License 2.0 terms declared by
  `project.license`.
- `scripts/` holds the checks from the Palomar template that CI runs after the
  build.

## Checks

```text
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

CI runs all of these. `verify-comparator.sh` needs Linux with `bwrap`
(bubblewrap), which `lake comparator` uses to sandbox the build it judges; on
other platforms rely on the CI job. `validate-formalization.rb` fails, locally
and in CI, until every `TEMPLATE` value in `formalization.yaml` has been
replaced.

## Conventions Palomar enforces

- Every `.lean` file uses Lean's module system (`module` header, `public
  import`, public declarations) and has at most 10,000 lines; `Challenge.lean`
  is further limited to 1,000 lines and 100 KiB.
- The toolchain in `lean-toolchain` must be `leanprover/lean4:v4.35.0-rc2` or
  later, which is where `lake comparator` appears.
- `Challenge.lean` may transitively import only Lean core, Mathlib, Tau Ceti, or
  CSLib. Definitions it introduces need precise meanings and docstrings.
  Dependencies used only by the proof may be arbitrary pinned Git dependencies.
- Only `propext`, `Quot.sound`, and `Classical.choice` are permitted axioms.

## Before submitting

1. Replace the placeholder theorem in `Challenge.lean` with the real statement
   (kept statement-only with `sorry`), prove it in `Solution.lean`, and list
   every advertised declaration in `comparator.json`. Remove every `sorry` from
   the library.
2. Replace every `TEMPLATE` value in `formalization.yaml`, following the
   comments beside each field; `ruby scripts/validate-formalization.rb` lists
   the ones that remain.
3. Describe the result, its sources, and any divergences in this README, and
   remove the status note above.
4. Run the checks above and make sure CI is green.
5. Read the current
   [Palomar submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
   commit the final snapshot, and
   [open the submission form](https://submit.palomar-registry.org/) with the
   full 40-character commit SHA.

## GitHub configuration

The manually triggered `Update Dependencies` workflow opens pull requests, which
needs **Settings → Actions → General → Allow GitHub Actions to create and
approve pull requests**.
