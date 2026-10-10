# Szemerédi's theorem with random differences

Lean 4 proof of a threshold for Szemerédi's theorem with random differences, following the
preprint *Szemerédi's theorem with random differences and Arithmetic Kakeya* by Gabriel Dahia.
The proof uses the construction of Green and Ruzsa,
[*On the arithmetic Kakeya conjecture of Katz and Tao*](https://arxiv.org/abs/1712.02108),
which is also formalized here, and Varnavides' theorem from
[DensityHalesJewett](https://github.com/gdahia/DensityHalesJewett).

## Results

There is `c > 0` such that the following holds for every `k ≥ 3` and `δ > 0`, with a constant
`C` depending on `k` and `δ`. Let `D` be a `p`-random subset of `{1, …, n}` with
`p ≥ C * n ^ (-c / log (log k))`. With probability tending to `1` as `n` tends to infinity,
every subset of `{1, …, n}` with at least `δ * n` elements contains a `k`-term arithmetic
progression with common difference in `D`.

[Solution.lean](Solution.lean) proves this as
`RandomDifferences.exists_forall_tendsto_setBernoulli_exists_forall_exists_notMem`.
[Challenge.lean](Challenge.lean) contains the same statement with a `sorry` placeholder. The
library and solution contain no `sorry`. The random set is Mathlib's `setBer(Set.Icc 1 n, p)`.

The Green–Ruzsa theorem is
`ArithmeticKakeya.exists_card_le_rpow_forall_exists_arithmeticProgression`: for `k ≥ 3` and
`n ≥ n₀ k` there is a subset of `{1, …, k * Q * n}` with at most `n ^ (1 - c / log (log k))`
elements that contains a `k`-term arithmetic progression with every common difference in
`{1, …, n}`. The constants are explicit:

- `ArithmeticKakeya.modulus k`, written `Q`, is the product of the first `⌈10 * log k⌉` odd
  primes;
- `ArithmeticKakeya.c` is `1 / 100`;
- `ArithmeticKakeya.n₀ k` is `Q ^ (⌈10 * log (log k)⌉ + 100)`, which is
  `k ^ O(log (log k) ^ 2)`.

## Proof and files

By Varnavides' theorem a set `S ⊆ {1, …, n}` with at least `δ * n` elements contains `ε * n ^ 2`
progressions of length `k`. Each of them is a translate of a progression in the Green–Ruzsa set
`Y`. By the pigeonhole principle some translate of `Y` meets `S` in a set `F`, the fingerprint
of `S`, containing progressions with at least `γ * n` common differences. There are at most
`C * n * exp (n ^ (1 - c / log (log k)))` fingerprints, and a `p`-random set misses the common
differences of a given fingerprint with probability at most `exp (-p * γ * n)`. A union bound
over the fingerprints gives the theorem.

For the Green–Ruzsa set, take for each `d < Q` the progression of difference `d` starting at
the residue of `d ^ 2` modulo `Q`, and let `S` be the union of these progressions. Since
`4 * (d ^ 2 + j * d) = (2 * d + j) ^ 2 - j ^ 2`, the `j`-th terms lie in `(p + 1) / 2` residue
classes modulo each prime `p` dividing `Q`, so `S` has at most `B = k ^ 2 * ∏ p, (p + 1) / 2`
elements. The numbers with `t` digits in base `Q`, each digit in `S`, contain a progression
with every common difference below `Q ^ t`.

| Files in `SzemerediWithRandomDifferences/` | Contents |
| --- | --- |
| `CommonDiffs.lean` | Common differences of the progressions in a set |
| `Translate.lean` | The pigeonhole argument over translates |
| `Fingerprint.lean` | The fingerprint lemma |
| `SetBernoulli.lean` | The probability that a random set avoids a finite set |
| `RandomDifferences.lean` | The union bound and the main theorem |
| `ArithmeticKakeya/Parameters.lean` | The parameters `modulus`, `sizeBound`, `c` and `n₀` |
| `ArithmeticKakeya/Residues.lean` | Residues of `d ^ 2 + j * d` modulo primes and products |
| `ArithmeticKakeya/BaseSet.lean` | The set `S` |
| `ArithmeticKakeya/DigitSet.lean` | Numbers whose base-`Q` digits lie in a given set |
| `ArithmeticKakeya/Construction.lean` | The construction for a general modulus |
| `ArithmeticKakeya/Modulus.lean` | Estimates for `Q` and `B` |
| `ArithmeticKakeya/Threshold.lean` | The bound `n ^ (1 - c / log (log k))` for `n ≥ n₀ k` |
| `ArithmeticKakeya.lean` | The Green–Ruzsa theorem |

Green and Ruzsa state their theorem as a limit and for large `k` use a bound on
`∏ p, (1 + 1 / p)`. The formalization proves a finite statement for every `k ≥ 3`, using
Chebyshev's bound on the prime counting function from Mathlib and a direct computation for
`k = 3`. [formalization.yaml](formalization.yaml) records the differences from the sources,
the scope, and the use of an AI coding agent.

## Build

The Lean, Mathlib and DensityHalesJewett versions are pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warning from
`Challenge.lean` is expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
