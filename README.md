# Szemerédi's theorem with random differences

Lean 4 proof of a threshold for Szemerédi's theorem with random differences, following the
preprint *Szemerédi's theorem with random differences and Arithmetic Kakeya* by Gabriel Dahia.
The proof uses the construction of Green and Ruzsa,
[*On the arithmetic Kakeya conjecture of Katz and Tao*](https://arxiv.org/abs/1712.02108),
which is also formalized here, and Varnavides' theorem from
[DensityHalesJewett](https://github.com/gdahia/DensityHalesJewett).

## Results

There is $c > 0$ such that the following holds for every $k \ge 3$ and $\delta > 0$, with a
constant $C$ depending on $k$ and $\delta$. Let $D$ be a $p$-random subset of
$\lbrace 1, \dots, n \rbrace$ with $p \ge C n^{-c / \log \log k}$. With probability tending to
$1$ as $n$ tends to infinity, every subset of $\lbrace 1, \dots, n \rbrace$ with at least
$\delta n$ elements contains a $k$-term arithmetic progression with common difference in $D$.

[Solution.lean](Solution.lean) proves this as
`RandomDifferences.exists_forall_tendsto_setBernoulli_exists_forall_exists_notMem`.
[Challenge.lean](Challenge.lean) contains the same statement with a `sorry` placeholder.

The Green–Ruzsa theorem is
`ArithmeticKakeya.exists_card_le_rpow_forall_exists_arithmeticProgression`: for $k \ge 3$ and
$n \ge n_0$ there is a subset of $\lbrace 1, \dots, kQn \rbrace$ with at most
$n^{1 - c / \log \log k}$ elements that contains a $k$-term arithmetic progression with every
common difference in $\lbrace 1, \dots, n \rbrace$. The constants are explicit:

- $Q$ is `ArithmeticKakeya.modulus k`, the product of the first $\lceil 10 \log k \rceil$ odd
  primes;
- $c$ is `ArithmeticKakeya.c`, equal to $1/100$;
- $n_0$ is `ArithmeticKakeya.n₀ k`, equal to $Q^{\lceil 10 \log \log k \rceil + 100}$, which is
  $k^{O((\log \log k)^2)}$.

## Files

| Files in `SzemerediWithRandomDifferences/` | Contents |
| --- | --- |
| `CommonDiffs.lean` | Common differences of the progressions in a set |
| `Translate.lean` | The pigeonhole argument over translates |
| `Fingerprint.lean` | The fingerprint lemma |
| `SetBernoulli.lean` | The probability that a random set avoids a finite set |
| `RandomDifferences.lean` | The union bound and the main theorem |
| `ArithmeticKakeya/Parameters.lean` | The parameters `modulus`, `sizeBound`, `c` and `n₀` |
| `ArithmeticKakeya/Residues.lean` | Residues of $d^2 + jd$ modulo primes and products |
| `ArithmeticKakeya/BaseSet.lean` | The set $S$ |
| `ArithmeticKakeya/DigitSet.lean` | Numbers whose base-$Q$ digits lie in a given set |
| `ArithmeticKakeya/Construction.lean` | The construction for a general modulus |
| `ArithmeticKakeya/Modulus.lean` | Estimates for $Q$ and $B$ |
| `ArithmeticKakeya/Threshold.lean` | The bound $n^{1 - c / \log \log k}$ for $n \ge n_0$ |
| `ArithmeticKakeya.lean` | The Green–Ruzsa theorem |

Green and Ruzsa state their theorem as a limit and for large $k$ use a bound on
$\prod_p (1 + 1/p)$. The formalization proves a finite statement for every $k \ge 3$, using
Chebyshev's bound on the prime counting function from Mathlib and a direct computation for
$k = 3$.

## Build

The Lean, Mathlib and DensityHalesJewett versions are pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warning from
`Challenge.lean` is expected.
