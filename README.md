# Lower bounds for Naslund's crossing problem

Arth Singh, AIM Intelligence

**Result.** Let `P(n)` be the least `r + s` such that the tensor `[x1 = x4][x2 = x3]` on `[n]^4` is a sum of
`r` tensors of rank one along `{12|34}` and `s` tensors of rank one along `{13|24}`. Naslund
([Problem 12](https://arxiv.org/abs/1701.04475), JCTA 2020) asked whether `P(n) >= n^(1+eps)`. The only
lower bound we found in the literature is the trivial `P(n) >= n`. This repository proves, over **every
field**:

| Statement | Range | Lean theorem |
|---|---|---|
| `P(n) >= 4n/3` | `n >= 3` | `SwapSplit.swap_split_ge_four_thirds` |
| `P(n) >= 15n/11` | `n >= 5` | `SwapSplit.swap_split_ge_fifteen_elevenths` |
| `P(n) >= n + 3` | `n >= 4` | `SwapSplit.swap_split_ge_add_three` |
| `P(4) = 7` (lower and upper bound) | | `SwapSplit.swap_split_four_eq_seven` |
| `P(5) >= 8` | | `SwapSplit.swap_split_five_ge_eight` |
| `P(6) >= 9` | | `SwapSplit.swap_split_six_ge_nine` |

With an easy upper bound, `P(3) = 4`, `P(4) = 7` and `8 <= P(5) <= 11`. The bound `4n/3` is attained at
`n = 3`. For `n >= 6`, `n + 3` follows from `15n/11`, so its new content is `n = 4` and `n = 5`. All the
bounds are linear in `n`. These bounds are far from `n^(1+eps)`; they are, to our knowledge, the first above `n`.

In matrix form, `P(n)` is the least `rank B + rank R(C)` over all splittings `S_n = B + C` of the swap matrix
of `F^n ⊗ F^n`, where `R` is the realignment (so `rank R(C)` is the operator Schmidt rank of `C`). The Lean
files state the theorems in this form.

- **Paper:** [`paper/crossing-lower-bounds.pdf`](paper/crossing-lower-bounds.pdf) (8 pages; a full proof of `4n/3`, a description of the `15n/11` certificate and an outline of `n + 3`)
- **Lean proofs:** [`SwapSplit.lean`](SwapSplit.lean) (298 lines: `4n/3`, imports Mathlib only) and
  [`SmallValues.lean`](SmallValues.lean) (4,917 lines: `n + 3`, `P(4) = 7`, `P(5) >= 8`, `P(6) >= 9`) and
  [`FifteenElevenths.lean`](FifteenElevenths.lean) (1,756 lines: `15n/11`)
- **Border splitting at n = 4:** [`border/`](border) (data and an exact-arithmetic checker)

## How the results were found

The theorems and their Lean proofs were found by AI agents in one run of an in-house multi-agent harness:
about 20 agents (Claude Opus 5.5) that work as a small research organization, with leads, workers and an advisor.
Agents set goals for each other and share a library of Lean files. A statement counts as proved only after
Lean accepts it, and a claim of novelty needs a literature search by the advisor agent.

1. One worker agent posed the lower-bound question as a goal and proved the trivial bound `n` in Lean.
2. A second worker proved `n + 1`, then `8n/7`, from identities between slices of a splitting. No person had
   asked for these bounds.
3. The operator then set the goal to go beyond them. The first worker proved `n + 2` and `5n/4`, with the
   second worker's slice identities and a new corank argument. The time from the goal to `5n/4` was 36
   minutes; the time from the first question to `5n/4` was about two and a half hours.
4. The operator then put the whole organization on the problem for 35 minutes. After 15 minutes a third
   worker proved `4n/3` (a rank form of the excess lemma, the transposed slice system, three rotations of a
   three-cycle). Another worker found the same constant independently with a linear-programming search.
   `P(5) >= 8` followed after 19 minutes, `P(4) = 7` over the rationals after 24 minutes and over every field
   after 33 minutes, and `P(6) >= 9`, which completes `n + 3` for every `n >= 4`, after 44 minutes (in an
   extension of the time). `15n/11` followed after 62 minutes: one worker had found the constant by a
   linear-programming search, the advisor and a second worker made the certificate exact, and a third worker
   proved its 189 inequalities in Lean. The earlier bounds `n + 1`, `8n/7`, `n + 2` and `5n/4` follow from `4n/3` and are
   no longer in the repository.
5. Another worker found a border splitting of `S_4` with `r + s = 6`. The advisor agent refereed the proofs,
   checked the border splitting with exact arithmetic, and searched the literature.

The Lean files of this repository, the literature check and the text of the paper were prepared with AI assistance
(Claude). The author takes responsibility for the content.

## Verify it yourself

Lean theorems (Lean v4.33.1 and Mathlib v4.33.1 are pinned in `lean-toolchain` and `lake-manifest.json`):

```bash
lake exe cache get   # downloads the Mathlib build cache
lake build
```

The build prints, for each theorem in the table,

```
'SwapSplit.swap_split_ge_four_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

which are Lean's three standard axioms. The files contain no `sorry` and no `axiom` declarations.

`SmallValues.lean` is long because its body is the dependency closure of 61 Lean files of the multi-agent run,
concatenated unchanged (one `section` per file). `FifteenElevenths.lean` adds 17 more files in the same way. The agents named the swap matrix `biancaSwapF` and the
realignment `biancaRealignF`; the last section of the file proves that these are the definitions `swapMat` and
`realign` of `SwapSplit.lean`, and states the results with them.

Border splitting at `n = 4` (Python 3, standard library only):

```bash
python3 border/verify_border_n4.py
```

It checks with exact integer arithmetic that `B(t) + C(t) = c t^3 S_4 + O(t^4)` for the `16 x 3` polynomial
factor tables in `border/border_n4.json`, so `S_4` is a limit of sums of a matrix of rank at most 3 and a
matrix of operator Schmidt rank at most 3.

## What is and is not verified

- **Verified in Lean:** the statements in the table, exactly as stated in the three files (definitions
  `swapMat` and `realign` at the top of `SwapSplit.lean`). The proof of `4n/3` is also written out in the
  paper and was checked by hand. The proofs of `15n/11`, `n + 3`, `P(4) >= 7`, `P(5) >= 8` and `P(6) >= 9` are
  only described in the paper, and no person has read them in full; their only complete proofs are the Lean
  proofs. The paper prints the Lean definitions and statements so that a reader can check what was proved.
- **Checked by script:** the border identity at `n = 4`.
- **Not formalized:** the translation between Naslund's tensor formulation and the matrix form (Section 1 of
  the paper), the upper bounds `P(3) <= 4` and `P(5) <= 11` (a one-paragraph argument in the paper), and the
  remarks.
- **Novelty:** we searched Naslund (JCTA 2020), Karam (arXiv:2310.11356), Hrubeš–Wigderson–Yehudayoff
  (JAMS 2011), Hrubeš (CCC 2024), Brand–Kaski–Wang (arXiv:2607.02241) and Appendix G of
  hexagon:2610.00577v1, and found no lower bound above `n`. This is a search result, not a proof of novelty.
  If you know an earlier bound, please open an issue.
- The paper is not peer reviewed.
