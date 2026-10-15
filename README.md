# Szemerédi's theorem with random differences

Lean 4 proof of a threshold for Szemerédi's theorem with random differences, following the
preprint
[*Szemerédi's theorem with random differences and arithmetic Kakeya*](https://arxiv.org/abs/2610.18859)
by Gabriel Dahia.
The proof uses the construction of Green and Ruzsa,
[*On the arithmetic Kakeya conjecture of Katz and Tao*](https://arxiv.org/abs/1712.02108),
which is also formalized here, and Varnavides' theorem from
[DensityHalesJewett](https://github.com/gdahia/DensityHalesJewett).

## Results

Let $k \ge 3$ and $\delta > 0$, and let $c = 1/100$ and
$C = A(4k + 2, k + \lceil 2/\delta \rceil)$, where $A$ is the Ackermann function. Let $D$ be a
$p$-random subset of $\lbrace 1, \dots, n \rbrace$ with $p \ge C n^{-c / \log \log k}$. With
probability at least $1 - \exp(-n^{1 - c / \log \log k})$, every subset of
$\lbrace 1, \dots, n \rbrace$ with at least $\delta n$ elements contains a $k$-term arithmetic
progression with common difference in $D$.

[Solution.lean](Solution.lean) proves this as
`RandomDifferences.szemeredi_setBernoulli_exists_avoiding_le_exp`.
[Challenge.lean](Challenge.lean) contains the same statement with a `sorry` placeholder. The
constants are `RandomDifferences.c` and `RandomDifferences.C`, and $A$ is Mathlib's `ack`.

The Green–Ruzsa theorem, Theorem 1.2 of the arXiv version and Theorem 1.7 of the
[published version](https://doi.org/10.1007/s10998-018-0270-z), is
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
| `Cover.lean` | The covering lemma: a small cover of the dense sets |
| `SetBernoulli.lean` | The probability that a random set avoids a finite set |
| `Ackermann.lean` | The bounds $3 (kQ + 1) A(4k + 1, s) \le A(4k + 2, s)$ and $n_0 \le A(4k + 2, s)$ |
| `RandomDifferences.lean` | The union bound and the main theorem |
| `ArithmeticKakeya/Parameters.lean` | The parameters `modulus`, `sizeBound`, `c` and `n₀` |
| `ArithmeticKakeya/Residues.lean` | Residues of $d^2 + jd$ modulo primes and products |
| `ArithmeticKakeya/BaseSet.lean` | The set $S$ |
| `ArithmeticKakeya/DigitSet.lean` | Numbers whose digits in base $Q$ lie in a given set |
| `ArithmeticKakeya/Construction.lean` | The construction for a general modulus |
| `ArithmeticKakeya/Modulus.lean` | Estimates for $Q$ and $B$ |
| `ArithmeticKakeya/Threshold.lean` | The bound $n^{1 - c / \log \log k}$ for $n \ge n_0$ |
| `ArithmeticKakeya.lean` | The Green–Ruzsa theorem |

Green and Ruzsa state their theorem as a limit and for large $k$ use a bound on
$\prod_p (1 + 1/p)$. The formalization proves a finite statement for every $k \ge 3$, using
Chebyshev's bound on the prime counting function from Mathlib and a direct computation for
$k = 3$.

## Verification

`Challenge.lean` states the main theorem as
`RandomDifferences.szemeredi_setBernoulli_exists_avoiding_le_exp`, with the constants
`RandomDifferences.c` and `RandomDifferences.C`. It imports Mathlib alone and leaves the proof as
`sorry`; the progressions are written out as $a + i d$ with $i < k$. `Solution.lean` proves the
same declaration from `RandomDifferences.lean`.

`comparator.json` sets up the comparison of the two modules: it names the theorem and permits
only the axioms `propext`, `Quot.sound` and `Classical.choice`. A comparator checks that each
declaration in `Solution` has the same statement as in `Challenge` and that its proof uses no
other axioms.

## Build

The Lean, Mathlib and DensityHalesJewett versions are pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warning from
`Challenge.lean` is expected.
