/-
Lower bounds for splitting the swap matrix into a low-rank part and a part of low operator Schmidt rank.

Let F be a field. The swap matrix S_N of F^N ⊗ F^N has S_N[(x, y), (u, v)] = [u = y][v = x], and the
realignment of C is R C[(x, u), (y, v)] = C[(x, y), (u, v)] (its rank is the operator Schmidt rank of C).
For every split S_N = B + C:

* `swap_split_ge_four_thirds`           (N ≥ 3):  4 N ≤ 3 (rank B + rank (R C));
* `swap_split_ge_add_two`               (N ≥ 4):  N + 2 ≤ rank B + rank (R C);
* `swap_split_ge_add_three_of_ge_seven` (N ≥ 7):  N + 3 ≤ rank B + rank (R C).

The exact values P(4) = 7 and P(5) ≥ 8 are in SmallValues.lean.

Standalone: only Mathlib. Checked with Lean v4.33.1 and Mathlib v4.33.1 (commit 0df444a3). The proofs are those of
the library units rank_factorization_sum_of_rank_one, merge_level_ceiling_matrix_rank,
matrix_sylvester_rank_inequality, minsum_ge_five_quarters_N_every_field (submodularity) and
minsum_ge_four_thirds_N_every_field of an automated multi-agent run.
-/
import Mathlib

open Matrix

namespace SwapSplit

/-- The swap matrix: rows (x, y), columns (u, v), entry [u = y][v = x]. -/
def swapMat (F : Type*) [Field F] (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The realignment (x, y), (u, v) ↦ (x, u), (y, v); its rank is the operator Schmidt rank. -/
def realign {F : Type*} [Field F] {N : ℕ} (C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) F :=
  fun p q => C (p.1, q.1) (p.2, q.2)

/-! ### Rank facts -/

/-- Rank is subadditive. -/
theorem rank_add_le' {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (m → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Sylvester's rank inequality: rank A + rank B ≤ rank (A * B) + (inner dimension). -/
theorem sylvester_rank {F : Type*} [Field F] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq n] [DecidableEq p] (A : Matrix m n F) (B : Matrix n p F) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  classical
  set f := A.mulVecLin
  set g := B.mulVecLin
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hdim : Module.finrank F (LinearMap.range g) + Module.finrank F W = Fintype.card n := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    simpa using this
  have hrange : LinearMap.range f ≤ (LinearMap.range g).map f ⊔ W.map f := by
    rw [← Submodule.map_sup, hW.sup_eq_top, Submodule.map_top]
  have h1 : Module.finrank F (LinearMap.range f) ≤
      Module.finrank F ((LinearMap.range g).map f) + Module.finrank F (W.map f) :=
    le_trans (Submodule.finrank_mono hrange) (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have h2 : Module.finrank F (W.map f) ≤ Module.finrank F W := Submodule.finrank_map_le f W
  have h3 : (LinearMap.range g).map f = LinearMap.range (A * B).mulVecLin := by
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hA : A.rank = Module.finrank F (LinearMap.range f) := rfl
  have hB : B.rank = Module.finrank F (LinearMap.range g) := rfl
  have hAB : (A * B).rank = Module.finrank F (LinearMap.range (A * B).mulVecLin) := rfl
  rw [h3] at h1
  omega

/-- A matrix of rank r is a sum of r matrices of rank one. -/
theorem exists_sum_vecMulVec_of_rank {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (A : Matrix m n F) :
    ∃ (U : Fin A.rank → m → F) (V : Fin A.rank → n → F), A = ∑ k, Matrix.vecMulVec (U k) (V k) := by
  classical
  set W : Submodule F (m → F) := Submodule.span F (Set.range A.col) with hW
  have hr : Module.finrank F W = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
  let b : Module.Basis (Fin A.rank) F W := Module.finBasisOfFinrankEq F W hr
  have hcol : ∀ j, A.col j ∈ W := fun j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨fun k => (b k : m → F), fun k j => b.repr ⟨A.col j, hcol j⟩ k, ?_⟩
  ext i j
  have hsum := b.sum_repr ⟨A.col j, hcol j⟩
  have hi := congrArg (fun w : W => (w : m → F) i) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
  rw [Matrix.sum_apply]
  simp only [Matrix.vecMulVec_apply]
  have hA : A i j = A.col j i := rfl
  rw [hA, ← hi]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-! ### Slices of a split -/

/-- A split S_N = B + C gives slice matrices X_y, Y_u (width rank B) and P_u, Q_y (width rank (R C)) with
X_y Y_uᵀ + P_u Q_yᵀ = [y = u] 1. -/
theorem exists_slices {F : Type*} [Field F] (N : ℕ) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) :
    ∃ (X Y : Fin N → Matrix (Fin N) (Fin B.rank) F) (P Q : Fin N → Matrix (Fin N) (Fin (realign C).rank) F),
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) ∧ (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) := by
  obtain ⟨U, V, hB⟩ := exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hC⟩ := exists_sum_vecMulVec_of_rank (realign C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if u = y ∧ v = x then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = realign C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin B.rank) F := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin B.rank) F := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin (realign C).rank) F := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin (realign C).rank) F := fun y => Matrix.of fun v l => Q l (y, v)
  have hslice : ∀ y u, X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = if y = u then 1 else 0 := by
    intro y u
    ext x v
    have := hent x y u v
    simp only [X, Y, PP, QQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    by_cases hyu : y = u
    · subst hyu
      by_cases hxv : x = v
      · subst hxv; simp
      · have hvx : ¬ v = x := fun h' => hxv h'.symm
        simp [hxv, hvx]
    · have huy : ¬ u = y := fun h' => hyu h'.symm
      simp [hyu, huy]
  exact ⟨X, Y, PP, QQ, fun y => by simpa using hslice y y, fun y u hyu => by simpa [hyu] using hslice y u⟩

/-- Submodularity: dim (A ⊔ C) + dim B ≤ dim (A ⊔ B) + dim (B ⊔ C). -/
theorem finrank_sup_triangle {F : Type*} [Field F] {N : ℕ} (A B C : Submodule F (Fin N → F)) :
    Module.finrank F ↥(A ⊔ C) + Module.finrank F B ≤ Module.finrank F ↥(A ⊔ B) + Module.finrank F ↥(B ⊔ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (B ⊔ C)
  have h1 : Module.finrank F ↥(A ⊔ C) ≤ Module.finrank F ↥((A ⊔ B) ⊔ (B ⊔ C)) :=
    Submodule.finrank_mono (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
  have h2 : Module.finrank F B ≤ Module.finrank F ↥((A ⊔ B) ⊓ (B ⊔ C)) :=
    Submodule.finrank_mono (le_inf le_sup_right le_sup_left)
  omega

/-! ### The bound 4 N / 3 -/

/-- The rank form of the excess lemma. For slices a ≠ b, X_a Y_bᵀ = −P_b Q_aᵀ has its column space in
col X_a ⊓ col P_b, and by Sylvester its rank is at least rank X_a + rank Y_b − r and at least
rank P_b + rank Q_a − k. Hence dim (col X_a ⊔ col P_b) + rank Y_b ≤ dim col P_b + r and
dim (col P_b ⊔ col X_a) + rank Q_a ≤ dim col X_a + k. -/
theorem slice_excess_rank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b : Fin N) (hab : a ≠ b) :
    Module.finrank F ↥(LinearMap.range (X a).mulVecLin ⊔ LinearMap.range (P b).mulVecLin) + (Y b).rank ≤
        Module.finrank F (LinearMap.range (P b).mulVecLin) + r ∧
    Module.finrank F ↥(LinearMap.range (P b).mulVecLin ⊔ LinearMap.range (X a).mulVecLin) + (Q a).rank ≤
        Module.finrank F (LinearMap.range (X a).mulVecLin) + k := by
  have hcol : ∀ {m p : ℕ} (A : Matrix (Fin N) (Fin m) F) (G : Matrix (Fin m) (Fin p) F),
      LinearMap.range (A * G).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    intro m p A G
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have e : X a * (Y b)ᵀ = P b * (-(Q a)ᵀ) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left (ho a b hab)
  constructor
  · have hle : LinearMap.range (X a * (Y b)ᵀ).mulVecLin ≤
        LinearMap.range (X a).mulVecLin ⊓ LinearMap.range (P b).mulVecLin :=
      le_inf (hcol _ _) (by rw [e]; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (X a).mulVecLin)
      (LinearMap.range (P b).mulVecLin)
    have h3 := sylvester_rank (X a) (Y b)ᵀ
    simp only [Fintype.card_fin, Matrix.rank_transpose] at h3
    have h4 : (X a * (Y b)ᵀ).rank = Module.finrank F (LinearMap.range (X a * (Y b)ᵀ).mulVecLin) := rfl
    have h5 : (X a).rank = Module.finrank F (LinearMap.range (X a).mulVecLin) := rfl
    omega
  · have e' : P b * (Q a)ᵀ = X a * (-(Y b)ᵀ) := by
      rw [Matrix.mul_neg]
      exact eq_neg_of_add_eq_zero_right (ho a b hab)
    have hle : LinearMap.range (P b * (Q a)ᵀ).mulVecLin ≤
        LinearMap.range (P b).mulVecLin ⊓ LinearMap.range (X a).mulVecLin :=
      le_inf (hcol _ _) (by rw [e']; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h3 := sylvester_rank (P b) (Q a)ᵀ
    simp only [Fintype.card_fin, Matrix.rank_transpose] at h3
    have h4 : (P b * (Q a)ᵀ).rank = Module.finrank F (LinearMap.range (P b * (Q a)ᵀ).mulVecLin) := rfl
    have h5 : (P b).rank = Module.finrank F (LinearMap.range (P b).mulVecLin) := rfl
    omega

/-- The rank three-cycles. For distinct slices a, b, c:
N + rank Q_c + rank Y_b + rank Q_a ≤ rank X_a + r + 2 k, N + rank Y_c + rank Q_b + rank Y_a ≤ rank P_a + 2 r + k,
and N ≤ rank X_a + rank P_a. -/
theorem slice_rank_cycle {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    N + (Q c).rank + (Y b).rank + (Q a).rank ≤ (X a).rank + r + 2 * k ∧
    N + (Y c).rank + (Q b).rank + (Y a).rank ≤ (P a).rank + 2 * r + k ∧
    N ≤ (X a).rank + (P a).rank := by
  have hR3 : ∀ z, LinearMap.range (X z).mulVecLin ⊔ LinearMap.range (P z).mulVecLin = ⊤ := by
    intro z
    rw [eq_top_iff]
    intro x _
    have hx : x = (X z) *ᵥ ((Y z)ᵀ *ᵥ x) + (P z) *ᵥ ((Q z)ᵀ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hd z, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have htop : ∀ z, Module.finrank F ↥(LinearMap.range (X z).mulVecLin ⊔ LinearMap.range (P z).mulVecLin) = N := by
    intro z
    rw [hR3 z, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have htop' : ∀ z, Module.finrank F ↥(LinearMap.range (P z).mulVecLin ⊔ LinearMap.range (X z).mulVecLin) = N := by
    intro z
    rw [sup_comm]
    exact htop z
  have hX : ∀ z, (X z).rank = Module.finrank F (LinearMap.range (X z).mulVecLin) := fun z => rfl
  have hP : ∀ z, (P z).rank = Module.finrank F (LinearMap.range (P z).mulVecLin) := fun z => rfl
  refine ⟨?_, ?_, ?_⟩
  · have E1 := (slice_excess_rank X Y P Q ho c a (Ne.symm hac)).2
    have E2 := (slice_excess_rank X Y P Q ho c b (Ne.symm hbc)).1
    have E3 := (slice_excess_rank X Y P Q ho a b hab).2
    have T1 := finrank_sup_triangle (LinearMap.range (P a).mulVecLin) (LinearMap.range (X c).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (X c).mulVecLin) (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h1 := htop' a
    have h2 := hX a
    omega
  · have E1 := (slice_excess_rank X Y P Q ho a c hac).1
    have E2 := (slice_excess_rank X Y P Q ho b c hbc).2
    have E3 := (slice_excess_rank X Y P Q ho b a (Ne.symm hab)).1
    have T1 := finrank_sup_triangle (LinearMap.range (X a).mulVecLin) (LinearMap.range (P c).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (P c).mulVecLin) (LinearMap.range (X b).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have h1 := htop a
    have h2 := hP a
    omega
  · have h1 := htop a
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range (X a).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    rw [hX a, hP a]
    omega

/-- The slice identities force 4 N ≤ 3 (r + k) for N ≥ 3: the rank three-cycles on slices 0, 1, 2 in three
rotations, for the system and for its transpose Y_u X_yᵀ + Q_y P_uᵀ = [y = u] 1. -/
theorem slice_four_thirds {F : Type*} [Field F] {N r k : ℕ} (hN : 3 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : 4 * N ≤ 3 * (r + k) := by
  have hd' : ∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1 := fun y => by
    have := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have ho' : ∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0 := fun y u hyu => by
    have := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul, add_comm] using this
  set s0 : Fin N := ⟨0, by omega⟩
  set s1 : Fin N := ⟨1, by omega⟩
  set s2 : Fin N := ⟨2, by omega⟩
  have h01 : s0 ≠ s1 := by simp [s0, s1, Fin.ext_iff]
  have h02 : s0 ≠ s2 := by simp [s0, s2, Fin.ext_iff]
  have h12 : s1 ≠ s2 := by simp [s1, s2, Fin.ext_iff]
  have a1 := slice_rank_cycle X Y P Q hd ho s0 s1 s2 h01 h02 h12
  have a2 := slice_rank_cycle X Y P Q hd ho s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have a3 := slice_rank_cycle X Y P Q hd ho s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  have b1 := slice_rank_cycle Y X Q P hd' ho' s0 s1 s2 h01 h02 h12
  have b2 := slice_rank_cycle Y X Q P hd' ho' s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have b3 := slice_rank_cycle Y X Q P hd' ho' s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  omega

/-- For N ≥ 3, every split S_N = B + C over a field has 4 N ≤ 3 (rank B + rank (R C)). -/
theorem swap_split_ge_four_thirds {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 4 * N ≤ 3 * (B.rank + (realign C).rank) := by
  obtain ⟨X, Y, P, Q, hd, ho⟩ := exists_slices N B C h
  exact slice_four_thirds hN X Y P Q hd ho

/-- For N ≥ 4, every split has rank B + rank (R C) ≥ N + 2 (from 4 N / 3; at N = 4 this is P(4) ≥ 6). -/
theorem swap_split_ge_add_two {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 2 ≤ B.rank + (realign C).rank := by
  have := swap_split_ge_four_thirds N (by omega) B C h
  omega

/-- For N ≥ 7, every split has rank B + rank (R C) ≥ N + 3 (from 4 N / 3). -/
theorem swap_split_ge_add_three_of_ge_seven {F : Type*} [Field F] (N : ℕ) (hN : 7 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 3 ≤ B.rank + (realign C).rank := by
  have := swap_split_ge_four_thirds N (by omega) B C h
  omega

end SwapSplit

#print axioms SwapSplit.swap_split_ge_four_thirds
#print axioms SwapSplit.swap_split_ge_add_two
#print axioms SwapSplit.swap_split_ge_add_three_of_ge_seven
