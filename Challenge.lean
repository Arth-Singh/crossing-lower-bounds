module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lower bounds for Naslund's crossing problem

Let `F` be a field and `N ≥ 1`. Index the rows and the columns of an `N² × N²` matrix by pairs. The swap
matrix `S_N` of `F^N ⊗ F^N` has the entry `[u = y] [v = x]` in row `(x, y)` and column `(u, v)`. The
realignment `R C` of a matrix `C` has the entry `C (x, y) (u, v)` in row `(x, u)` and column `(y, v)`; the
rank of `R C` is the operator Schmidt rank of `C`.

Naslund (J. Combin. Theory Ser. A 174 (2020), Problem 12) asks for lower bounds on

  `P(N) = min { rank B + rank (R C) : S_N = B + C }`,

the least number of rank-one tensors along the two partitions `{12|34}` and `{13|24}` whose sum is the
tensor `[x₁ = x₄][x₂ = x₃]` on `[N]⁴`. The trivial bound is `P(N) ≥ N`. The statements below give

* `P(N) ≥ 4N/3` for `N ≥ 3`, `P(N) ≥ 15N/11` for `N ≥ 5` and `P(N) ≥ 67N/49` for `N ≥ 7`;
* `P(N) ≥ N + 3` for `N ≥ 4`, with `P(5) ≥ 8` and `P(6) ≥ 9`;
* `P(4) = 7`: some split attains `7`, and no split does better.

All statements hold over every field.
-/

@[expose] public section

namespace SwapSplit

/-- The swap matrix: rows (x, y), columns (u, v), entry [u = y][v = x]. -/
def swapMat (F : Type*) [Field F] (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The realignment (x, y), (u, v) ↦ (x, u), (y, v); its rank is the operator Schmidt rank. -/
def realign {F : Type*} [Field F] {N : ℕ} (C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => C (p.1, q.1) (p.2, q.2)

end SwapSplit

namespace Crossing

open SwapSplit

/-- `P(N) ≥ 4N/3` for `N ≥ 3`: every split of the swap matrix has `4 N ≤ 3 (rank B + rank (R C))`. -/
theorem four_thirds {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 4 * N ≤ 3 * (B.rank + (realign C).rank) := by
  sorry

/-- `P(N) ≥ 15N/11` for `N ≥ 5`. -/
theorem fifteen_elevenths {F : Type*} [Field F] (N : ℕ) (hN : 5 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 15 * N ≤ 11 * (B.rank + (realign C).rank) := by
  sorry

/-- `P(N) ≥ 67N/49` for `N ≥ 7`. -/
theorem sixtyseven_fortyninths {F : Type*} [Field F] (N : ℕ) (hN : 7 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 67 * N ≤ 49 * (B.rank + (realign C).rank) := by
  sorry

/-- `P(N) ≥ N + 3` for `N ≥ 4`. -/
theorem add_three {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 3 ≤ B.rank + (realign C).rank := by
  sorry

/-- `P(4) = 7`: some split of `S_4` has `rank B + rank (R C) = 7`, and every split has at least `7`. -/
theorem four_eq_seven (F : Type*) [Field F] :
    (∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C ∧ B.rank + (realign C).rank = 7) ∧
    ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C → 7 ≤ B.rank + (realign C).rank := by
  sorry

/-- `P(5) ≥ 8`. -/
theorem five_ge_eight {F : Type*} [Field F] (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F)
    (h : swapMat F 5 = B + C) : 8 ≤ B.rank + (realign C).rank := by
  sorry

/-- `P(6) ≥ 9`. -/
theorem six_ge_nine {F : Type*} [Field F] (B C : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) F)
    (h : swapMat F 6 = B + C) : 9 ≤ B.rank + (realign C).rank := by
  sorry

end Crossing
