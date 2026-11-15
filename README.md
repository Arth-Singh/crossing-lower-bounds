# Lower bounds for Naslund's crossing problem

Arth Singh, AIM Intelligence

**Result.** Let `P(n)` be the least `r + s` such that the tensor `[x1 = x4][x2 = x3]` on `[n]^4` is a sum of
`r` tensors of rank one along `{12|34}` and `s` tensors of rank one along `{13|24}`. Naslund
([Problem 12](https://arxiv.org/abs/1701.04475), JCTA 2020) asked whether `P(n) >= n^(1+eps)`. The only
lower bound we found in the literature is the trivial `P(n) >= n`. This repository proves, over **every
field**:

| Statement | Range | Lean theorem |
|---|---|---|
| `P(n) >= 5n/4` | `n >= 3` | `SwapSplit.swap_split_ge_five_quarters` |
| `P(n) >= n + 2` | `n >= 4` | `SwapSplit.swap_split_ge_add_two` |
| `P(n) >= n + 1` | `n >= 3` | `SwapSplit.swap_split_ge_succ` |
| `P(4) >= 6` | | `SwapSplit.swap_split_four_ge_six` |

Together with easy upper bounds, `P(3) = 4` and `6 <= P(4) <= 7`. These bounds are far from `n^(1+eps)`;
they are, to our knowledge, the first above `n`.

In matrix form, `P(n)` is the least `rank B + rank R(C)` over all splittings `S_n = B + C` of the swap matrix
of `F^n ⊗ F^n`, where `R` is the realignment (so `rank R(C)` is the operator Schmidt rank of `C`). The Lean
file states the theorems in this form.

- **Paper:** [`paper/crossing-lower-bounds.pdf`](paper/crossing-lower-bounds.pdf) (6 pages, with human-readable proofs)
- **Lean proof:** [`SwapSplit.lean`](SwapSplit.lean) (one file, imports Mathlib only)
- **Border splitting at n = 4:** [`border/`](border) (data and an exact-arithmetic checker)

## How the results were found

The theorems and their Lean proofs were found by AI agents in one run of an in-house multi-agent harness:
20 agents (Claude Opus 5.5) that work as a small research organization, with leads, workers and an advisor.
Agents set goals for each other and share a library of Lean files. A statement counts as proved only after
Lean accepts it, and a claim of novelty needs a literature search by the advisor agent.

1. One worker agent posed the lower-bound question as a goal and proved the trivial bound `n` in Lean.
2. A second worker proved `n + 1`, then `8n/7`, from identities between slices of a splitting. No person had
   asked for these bounds.
3. The operator then set the goal to go beyond them. The first worker proved `n + 2` and `5n/4`, with the
   second worker's slice identities and a new corank argument. The time from the goal to `5n/4` was 36
   minutes; the time from the first question to `5n/4` was about two and a half hours.
4. A third worker found a border splitting of `S_4` with `r + s = 6`. The advisor agent refereed the proofs,
   checked the border splitting with exact arithmetic, and searched the literature.

The standalone Lean file, the literature check and the text of the paper were prepared with AI assistance
(Claude). The author takes responsibility for the content.

## Verify it yourself

Lean theorems (Lean v4.33.1 and Mathlib v4.33.1 are pinned in `lean-toolchain` and `lake-manifest.json`):

```bash
lake exe cache get   # downloads the Mathlib build cache
lake build
```

The build prints, for each of the four theorems,

```
'SwapSplit.swap_split_ge_five_quarters' depends on axioms: [propext, Classical.choice, Quot.sound]
```

which are Lean's three standard axioms. The file contains no `sorry`.

Border splitting at `n = 4` (Python 3, standard library only):

```bash
python3 border/verify_border_n4.py
```

It checks with exact integer arithmetic that `B(t) + C(t) = c t^3 S_4 + O(t^4)` for the `16 x 3` polynomial
factor tables in `border/border_n4.json`, so `S_4` is a limit of sums of a matrix of rank at most 3 and a
matrix of operator Schmidt rank at most 3.

## What is and is not verified

- **Verified in Lean:** the four statements in the table, exactly as stated in `SwapSplit.lean` (definitions
  `swapMat` and `realign` at the top of the file).
- **Checked by script:** the border identity at `n = 4`.
- **Not formalized:** the translation between Naslund's tensor formulation and the matrix form (Section 1 of
  the paper), the upper bounds `P(3) <= 4` and `P(4) <= 7` (a one-paragraph argument in the paper), and the
  remarks.
- **Novelty:** we searched Naslund (JCTA 2020), Karam (arXiv:2310.11356), Hrubeš–Wigderson–Yehudayoff
  (JAMS 2011), Hrubeš (CCC 2024), Brand–Kaski–Wang (arXiv:2607.02241) and Appendix G of
  hexagon:2610.00577v1, and found no lower bound above `n`. This is a search result, not a proof of novelty.
  If you know an earlier bound, please open an issue.
- The paper is not peer reviewed.
