module

public import SixtySevenFortyNinths

/-!
# Proved solution

The statements of `Challenge.lean`, proved by the theorems of `SwapSplit.lean`, `SmallValues.lean`,
`FifteenElevenths.lean` and `SixtySevenFortyNinths.lean`. The definitions `SwapSplit.swapMat` and
`SwapSplit.realign` come from `SwapSplit.lean`.
-/

@[expose] public section

namespace Crossing

open SwapSplit

/-- `P(N) ≥ 4N/3` for `N ≥ 3`: every split of the swap matrix has `4 N ≤ 3 (rank B + rank (R C))`. -/
theorem four_thirds {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 4 * N ≤ 3 * (B.rank + (realign C).rank) :=
  swap_split_ge_four_thirds N hN B C h

/-- `P(N) ≥ 15N/11` for `N ≥ 5`. -/
theorem fifteen_elevenths {F : Type*} [Field F] (N : ℕ) (hN : 5 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 15 * N ≤ 11 * (B.rank + (realign C).rank) :=
  swap_split_ge_fifteen_elevenths N hN B C h

/-- `P(N) ≥ 67N/49` for `N ≥ 7`. -/
theorem sixtyseven_fortyninths {F : Type*} [Field F] (N : ℕ) (hN : 7 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 67 * N ≤ 49 * (B.rank + (realign C).rank) :=
  swap_split_ge_sixtyseven_fortyninths N hN B C h

/-- `P(N) ≥ N + 3` for `N ≥ 4`. -/
theorem add_three {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 3 ≤ B.rank + (realign C).rank :=
  swap_split_ge_add_three N hN B C h

/-- `P(4) = 7`: some split of `S_4` has `rank B + rank (R C) = 7`, and every split has at least `7`. -/
theorem four_eq_seven (F : Type*) [Field F] :
    (∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C ∧ B.rank + (realign C).rank = 7) ∧
    ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C → 7 ≤ B.rank + (realign C).rank :=
  swap_split_four_eq_seven F

/-- `P(5) ≥ 8`. -/
theorem five_ge_eight {F : Type*} [Field F] (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F)
    (h : swapMat F 5 = B + C) : 8 ≤ B.rank + (realign C).rank :=
  swap_split_five_ge_eight B C h

/-- `P(6) ≥ 9`. -/
theorem six_ge_nine {F : Type*} [Field F] (B C : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) F)
    (h : swapMat F 6 = B + C) : 9 ≤ B.rank + (realign C).rank :=
  swap_split_six_ge_nine B C h

end Crossing
