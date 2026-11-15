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
| `P(n) >= 67n/49` | `n >= 7` | `SwapSplit.swap_split_ge_sixtyseven_fortyninths` |
| `P(n) >= n + 3` | `n >= 4` | `SwapSplit.swap_split_ge_add_three` |
| `P(4) = 7` (lower and upper bound) | | `SwapSplit.swap_split_four_eq_seven` |
| `P(5) >= 8` | | `SwapSplit.swap_split_five_ge_eight` |
| `P(6) >= 9` | | `SwapSplit.swap_split_six_ge_nine` |

With an easy upper bound, `P(3) = 4`, `P(4) = 7` and `8 <= P(5) <= 11`. The bound `4n/3` is attained at
`n = 3`. For `n >= 6`, `n + 3` follows from `15n/11`, so its new content is `n = 4` and `n = 5`. To our
knowledge, these are the first lower bounds above `n`.

**What this does not do.** All the bounds are linear in `n`, so they do not answer Naslund's question. The
paper (Remark on the limits of the arguments) gives subspaces that satisfy every inequality the slice
arguments use, with `r + s = (2 - 2/L) n` for `L` slices. So no argument of this kind proves `2n`, and a
superlinear bound needs new ideas.

In matrix form, `P(n)` is the least `rank B + rank R(C)` over all splittings `S_n = B + C` of the swap matrix
of `F^n ⊗ F^n`, where `R` is the realignment (so `rank R(C)` is the operator Schmidt rank of `C`). The Lean
files state the theorems in this form.

## Contents

- **Paper:** [`paper/crossing-lower-bounds.pdf`](paper/crossing-lower-bounds.pdf) (8 pages: a full proof of
  `4n/3`, a description of the certificates, an outline of `n + 3`, and the Lean statements verbatim).
- **Statements to audit:** [`Challenge.lean`](Challenge.lean) (88 lines). It imports one Mathlib module and
  contains the two definitions and the seven statements, with `sorry`. [`Solution.lean`](Solution.lean)
  proves them from the files below.
- **Lean proofs:**
  - [`SwapSplit.lean`](SwapSplit.lean) (304 lines): the definitions and `4n/3`, with the proof of the paper.
  - [`SmallValues.lean`](SmallValues.lean) (4,922 lines): `n + 3`, `P(4) = 7`, `P(5) >= 8`, `P(6) >= 9`.
  - [`FifteenElevenths.lean`](FifteenElevenths.lean) (1,761 lines): `15n/11`.
  - [`SixtySevenFortyNinths.lean`](SixtySevenFortyNinths.lean) (1,294 lines): `67n/49`.
- **Registry metadata:** [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) and
  the [preflight workflow](.github/workflows/palomar-preflight.yml) for the
  [Palomar registry](https://palomar-registry.org/).
- **Border splitting at n = 4:** [`border/`](border) (data and an exact-arithmetic checker).

## Verify it yourself

Lean and Mathlib v4.35.0-rc2 are pinned in `lean-toolchain` and `lake-manifest.json`. Every Lean file uses the
Lean module system.

```bash
lake exe cache get   # downloads the Mathlib build cache
lake build
```

The build prints, for each theorem in the table, a line such as

```
'SwapSplit.swap_split_ge_four_thirds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. The files contain no `sorry` (except the statements of
`Challenge.lean`), no `axiom` declarations and no `native_decide`.

**Palomar preflight.** Palomar's mechanical check (build, Comparator on `Challenge.lean` against
`Solution.lean`, permitted axioms, kernel replay) passed on commit `3d30266`
([run 43769921534](https://github.com/Arth-Singh/crossing-lower-bounds/actions/runs/43769921534)). The
repository was submitted to the registry for this commit and is under review; it is not registered yet.

**Why the files are long.** The body of `SmallValues.lean` is the dependency closure of 61 Lean files of the
multi-agent run, concatenated unchanged (one `section` per file). `FifteenElevenths.lean` adds 17 more files
and `SixtySevenFortyNinths.lean` 11 more, in the same way; the only edits are two unused `open` lines and the
module headers. The agents named the swap matrix `biancaSwapF` and the realignment `biancaRealignF`. The last
section of `SmallValues.lean` proves that these are the definitions `swapMat` and `realign` of
`SwapSplit.lean`, and each file states its result with them.

**Border splitting at n = 4** (Python 3, standard library only):

```bash
python3 border/verify_border_n4.py
```

It checks with exact integer arithmetic that `B(t) + C(t) = c t^3 S_4 + O(t^4)` for the `16 x 3` polynomial
factor tables in `border/border_n4.json`. So `S_4` is a limit of sums of a matrix of rank at most 3 and a
matrix of operator Schmidt rank at most 3, while the exact value is `P(4) = 7`.

## What is and is not verified

- **Verified in Lean:** the seven statements, exactly as stated in `Challenge.lean`.
- **Checked by hand:** the proof of `4n/3` (Section 3 of the paper), by the author's side and in an
  independent review of a draft, which also found the shorter proof in the paper.
- **Lean only:** the proofs of `15n/11`, `67n/49`, `n + 3`, `P(4) >= 7`, `P(5) >= 8` and `P(6) >= 9`. The paper
  describes or outlines them, but no person has read them in full.
- **Checked by script:** the border identity at `n = 4`.
- **Not formalized:** the translation between Naslund's tensor form and the matrix form (Section 1 of the
  paper), the upper bounds `P(3) <= 4` and `P(5) <= 11` (one paragraph in the paper), and the remarks.
- **Novelty:** we searched Naslund (JCTA 2020), Karam (arXiv:2310.11356), Hrubeš–Wigderson–Yehudayoff
  (JAMS 2011), Hrubeš (CCC 2024), Brand–Kaski–Wang (arXiv:2607.02241) and Appendix G of
  hexagon:2610.00577v1, and found no lower bound above `n`. This is a search result, not a proof of novelty.
  If you know an earlier bound, please open an issue.
- The paper is not peer reviewed.

## How the results were found

The theorems and their Lean proofs were found by AI agents in one run of an in-house multi-agent harness:
about 20 agents (Claude Opus 5.5 workers and a Claude Fable 5.2 lead) that work as a small research
organization, with leads, workers and an advisor. Agents set goals for each other and share a library of Lean
files. A statement counts as proved only after Lean accepts it, and a claim of novelty needs a literature
search by the advisor agent.

1. One worker posed the lower-bound question as a goal and proved the trivial bound `n` in Lean.
2. A second worker proved `n + 1`, then `8n/7`, from identities between slices of a splitting. No person had
   asked for these bounds.
3. The operator then set the goal to go beyond them. The first worker proved `n + 2` and `5n/4` in 36 minutes.
4. The operator then put the whole organization on the problem. After 15 minutes a third worker proved `4n/3`
   (a rank form of the excess lemma, the transposed slice system, three rotations of a three-cycle); another
   worker found the same constant independently by a linear-programming search. `P(5) >= 8` followed after
   19 minutes, `P(4) = 7` over every field after 33 minutes, and `P(6) >= 9`, which completes `n + 3`, after
   44 minutes.
5. In a second phase, aimed at superlinear bounds, the agents extended the slice argument to 5 and 7 slices.
   `15n/11` followed after 62 minutes (a certificate of 189 inequalities) and `67n/49` after 74 minutes (a
   certificate for 7 slices, reduced by symmetry). In both, one worker found the constant by a
   linear-programming search, others made the certificate exact, and others proved its inequalities in Lean.
6. Another worker found the border splitting of `S_4` with `r + s = 6`. The advisor agent refereed the proofs,
   checked the border splitting with exact arithmetic, and searched the literature.

The earlier bounds `n + 1`, `8n/7`, `n + 2` and `5n/4` follow from `4n/3` and are no longer in the repository.
Across the four Lean files, the proofs use 89 files of the run, written by 12 agents; 131 of their 233
dependency links go from one agent's file to another agent's file.

The Lean files of this repository, the literature check and the text of the paper were prepared with AI
assistance (Claude). The author takes responsibility for the content.

## License

Apache License 2.0 (see [`LICENSE`](LICENSE)).
