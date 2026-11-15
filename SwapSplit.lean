/-
Lower bounds for splitting the swap matrix into a low-rank part and a part of low operator Schmidt rank.

Let F be a field. The swap matrix S_N of F^N ⊗ F^N has S_N[(x, y), (u, v)] = [u = y][v = x], and the
realignment of C is R C[(x, u), (y, v)] = C[(x, y), (u, v)] (its rank is the operator Schmidt rank of C).
For every split S_N = B + C:

* `swap_split_ge_five_quarters` (N ≥ 3):  5 N ≤ 4 (rank B + rank (R C));
* `swap_split_ge_succ`          (N ≥ 3):  N + 1 ≤ rank B + rank (R C);
* `swap_split_ge_add_two`       (N ≥ 4):  N + 2 ≤ rank B + rank (R C);
* `swap_split_four_ge_six`      (N = 4):  6 ≤ rank B + rank (R C).

At N = 3 the value 4 is attained (proved in the note, not here): S_3 = (S_3 - 1) + 1.

Standalone: only Mathlib. Checked with Lean v4.33.1 and Mathlib v4.33.1 (commit 0df444a3). The proofs are those of the library units rank_factorization_sum_of_rank_one,
merge_level_ceiling_matrix_rank, matrix_sylvester_rank_inequality, minsum_ge_five_quarters_N_every_field
and minsum_ge_N_plus_two_every_field of an automated multi-agent run.
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

/-! ### The bound 5 N / 4 -/

/-- A square matrix of full rank has nonzero determinant. -/
theorem det_ne_zero_of_rank_eq {F : Type*} [Field F] {r : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (h : A.rank = r) : A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
  have hA : A.rank = Module.finrank F (LinearMap.range A.mulVecLin) := rfl
  have h0 : Module.finrank F (LinearMap.ker A.mulVecLin) = 0 := by omega
  have hk : v ∈ LinearMap.ker A.mulVecLin := hv
  rw [Submodule.finrank_eq_zero.mp h0] at hk
  exact hv0 ((Submodule.mem_bot F).mp hk)

/-- Coranks: if X Yᵀ + P Qᵀ = 1 (N × N), then N ≤ rank (Yᵀ X) + rank (Qᵀ P), so the coranks of Yᵀ X and Qᵀ P
add up to at most r + k − N. Their kernels embed, by v ↦ (v, −Qᵀ X v) and u ↦ (−Yᵀ P u, u), into the kernel
of [X P] with trivial intersection. -/
theorem slice_corank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F)
    (hd : X * Yᵀ + P * Qᵀ = 1) : N ≤ (Yᵀ * X).rank + (Qᵀ * P).rank := by
  classical
  set G : Matrix (Fin N) (Fin r ⊕ Fin k) F := Matrix.fromCols X P with hG
  have hGH : G * (Matrix.fromCols Y Q)ᵀ = 1 := by
    rw [hG, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, hd]
  have hrank : G.rank = N := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height G
    · have := Matrix.rank_mul_le_left G (Matrix.fromCols Y Q)ᵀ
      rw [hGH] at this
      simpa [Matrix.rank_one] using this
  have hker : Module.finrank F (LinearMap.ker G.mulVecLin) + N = r + k := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    have hr : Module.finrank F (LinearMap.range G.mulVecLin) = N := hrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
    omega
  set f1 : (Fin r → F) →ₗ[F] (Fin r ⊕ Fin k → F) :=
    (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) F) (-(Qᵀ * X))).mulVecLin with hf1
  set f2 : (Fin k → F) →ₗ[F] (Fin r ⊕ Fin k → F) :=
    (Matrix.fromRows (-(Yᵀ * P)) (1 : Matrix (Fin k) (Fin k) F)).mulVecLin with hf2
  have hf1a : ∀ v, f1 v = Sum.elim v (-((Qᵀ * X) *ᵥ v)) := by
    intro v
    rw [hf1, Matrix.mulVecLin_apply, Matrix.fromRows_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec]
  have hf2a : ∀ u, f2 u = Sum.elim (-((Yᵀ * P) *ᵥ u)) u := by
    intro u
    rw [hf2, Matrix.mulVecLin_apply, Matrix.fromRows_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec]
  have hf1i : Function.Injective f1 := by
    intro v w h
    funext i
    have := congrFun h (Sum.inl i)
    simpa [hf1a] using this
  have hf2i : Function.Injective f2 := by
    intro v w h
    funext i
    have := congrFun h (Sum.inr i)
    simpa [hf2a] using this
  set K1 := LinearMap.ker (Yᵀ * X).mulVecLin
  set K2 := LinearMap.ker (Qᵀ * P).mulVecLin
  have hXv : ∀ v ∈ K1, X *ᵥ v = P *ᵥ ((Qᵀ * X) *ᵥ v) := by
    intro v hv
    have hv' : (Yᵀ * X) *ᵥ v = 0 := hv
    calc X *ᵥ v = (1 : Matrix (Fin N) (Fin N) F) *ᵥ (X *ᵥ v) := (Matrix.one_mulVec _).symm
      _ = (X * Yᵀ + P * Qᵀ) *ᵥ (X *ᵥ v) := by rw [hd]
      _ = X *ᵥ (Yᵀ *ᵥ (X *ᵥ v)) + P *ᵥ (Qᵀ *ᵥ (X *ᵥ v)) := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec (M := X) (N := Yᵀ),
            Matrix.mulVec_mulVec (M := P) (N := Qᵀ)]
      _ = P *ᵥ ((Qᵀ * X) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec (M := Yᵀ) (N := X), hv', Matrix.mulVec_zero, zero_add,
            Matrix.mulVec_mulVec (M := Qᵀ) (N := X)]
  have hPu : ∀ u ∈ K2, P *ᵥ u = X *ᵥ ((Yᵀ * P) *ᵥ u) := by
    intro u hu
    have hu' : (Qᵀ * P) *ᵥ u = 0 := hu
    calc P *ᵥ u = (1 : Matrix (Fin N) (Fin N) F) *ᵥ (P *ᵥ u) := (Matrix.one_mulVec _).symm
      _ = (X * Yᵀ + P * Qᵀ) *ᵥ (P *ᵥ u) := by rw [hd]
      _ = X *ᵥ (Yᵀ *ᵥ (P *ᵥ u)) + P *ᵥ (Qᵀ *ᵥ (P *ᵥ u)) := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec (M := X) (N := Yᵀ),
            Matrix.mulVec_mulVec (M := P) (N := Qᵀ)]
      _ = X *ᵥ ((Yᵀ * P) *ᵥ u) := by
          rw [Matrix.mulVec_mulVec (M := Qᵀ) (N := P), hu', Matrix.mulVec_zero, add_zero,
            Matrix.mulVec_mulVec (M := Yᵀ) (N := P)]
  have hL1 : K1.map f1 ≤ LinearMap.ker G.mulVecLin := by
    rintro w ⟨v, hv, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hf1a, hG, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_neg,
      ← hXv v hv, add_neg_cancel]
  have hL2 : K2.map f2 ≤ LinearMap.ker G.mulVecLin := by
    rintro w ⟨u, hu, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hf2a, hG, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_neg,
      ← hPu u hu, neg_add_cancel]
  have hinf : K1.map f1 ⊓ K2.map f2 = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨v, hv, rfl⟩, ⟨u, hu, hvu⟩⟩
    have hu' : (Qᵀ * P) *ᵥ u = 0 := hu
    have e1 : v = -((Yᵀ * P) *ᵥ u) := by
      funext i
      have := congrFun hvu (Sum.inl i)
      simpa [hf1a, hf2a] using this.symm
    have e2 : u = -((Qᵀ * X) *ᵥ v) := by
      funext i
      have := congrFun hvu (Sum.inr i)
      simpa [hf1a, hf2a] using this
    have hXv' : X *ᵥ v = -(P *ᵥ u) := by
      rw [e1, Matrix.mulVec_neg, ← hPu u hu]
    have hu0 : u = 0 := by
      rw [e2, ← Matrix.mulVec_mulVec, hXv', Matrix.mulVec_neg, neg_neg, Matrix.mulVec_mulVec, hu']
    have hv0 : v = 0 := by rw [e1, hu0, Matrix.mulVec_zero, neg_zero]
    rw [Submodule.mem_bot, hv0, map_zero]
  have hdim1 : Module.finrank F (K1.map f1) = Module.finrank F K1 :=
    (Submodule.equivMapOfInjective f1 hf1i K1).finrank_eq.symm
  have hdim2 : Module.finrank F (K2.map f2) = Module.finrank F K2 :=
    (Submodule.equivMapOfInjective f2 hf2i K2).finrank_eq.symm
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (K1.map f1) (K2.map f2)
  rw [hinf, finrank_bot] at hsup
  have hle : Module.finrank F ↥(K1.map f1 ⊔ K2.map f2) ≤ Module.finrank F (LinearMap.ker G.mulVecLin) :=
    Submodule.finrank_mono (sup_le hL1 hL2)
  have hrn1 : (Yᵀ * X).rank + Module.finrank F K1 = r := by
    have := LinearMap.finrank_range_add_finrank_ker (Yᵀ * X).mulVecLin
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact this
  have hrn2 : (Qᵀ * P).rank + Module.finrank F K2 = k := by
    have := LinearMap.finrank_range_add_finrank_ker (Qᵀ * P).mulVecLin
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact this
  omega

/-- Submodularity: dim (A ⊔ C) + dim B ≤ dim (A ⊔ B) + dim (B ⊔ C). -/
theorem finrank_sup_triangle {F : Type*} [Field F] {N : ℕ} (A B C : Submodule F (Fin N → F)) :
    Module.finrank F ↥(A ⊔ C) + Module.finrank F B ≤ Module.finrank F ↥(A ⊔ B) + Module.finrank F ↥(B ⊔ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (B ⊔ C)
  have h1 : Module.finrank F ↥(A ⊔ C) ≤ Module.finrank F ↥((A ⊔ B) ⊔ (B ⊔ C)) :=
    Submodule.finrank_mono (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
  have h2 : Module.finrank F B ≤ Module.finrank F ↥((A ⊔ B) ⊓ (B ⊔ C)) :=
    Submodule.finrank_mono (le_inf le_sup_right le_sup_left)
  omega

/-- Excess bounds for slices a ≠ b:
(i) dim (col X_a ⊔ col P_b) + rank (Y_bᵀ X_b) ≤ dim col P_b + r;
(ii) dim (col P_b ⊔ col X_a) + rank (Q_aᵀ P_a) ≤ dim col X_a + k. -/
theorem slice_excess {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b : Fin N) (hab : a ≠ b) :
    Module.finrank F ↥(LinearMap.range (X a).mulVecLin ⊔ LinearMap.range (P b).mulVecLin) + ((Y b)ᵀ * X b).rank ≤
        Module.finrank F (LinearMap.range (P b).mulVecLin) + r ∧
    Module.finrank F ↥(LinearMap.range (P b).mulVecLin ⊔ LinearMap.range (X a).mulVecLin) + ((Q a)ᵀ * P a).rank ≤
        Module.finrank F (LinearMap.range (X a).mulVecLin) + k := by
  have hcol : ∀ {m p : ℕ} (A : Matrix (Fin N) (Fin m) F) (G : Matrix (Fin m) (Fin p) F),
      LinearMap.range (A * G).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    intro m p A G
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  constructor
  · have e : X a * ((Y b)ᵀ * X b) = P b * (-((Q a)ᵀ * X b)) := by
      have h0 := congrArg (· * X b) (ho a b hab)
      simp only [Matrix.add_mul, Matrix.zero_mul] at h0
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact eq_neg_of_add_eq_zero_left h0
    have hle : LinearMap.range (X a * ((Y b)ᵀ * X b)).mulVecLin ≤
        LinearMap.range (X a).mulVecLin ⊓ LinearMap.range (P b).mulVecLin :=
      le_inf (hcol _ _) (by rw [e]; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (X a).mulVecLin)
      (LinearMap.range (P b).mulVecLin)
    have h3 := sylvester_rank (X a) ((Y b)ᵀ * X b)
    simp only [Fintype.card_fin] at h3
    have h4 : (X a * ((Y b)ᵀ * X b)).rank =
        Module.finrank F (LinearMap.range (X a * ((Y b)ᵀ * X b)).mulVecLin) := rfl
    have h5 : (X a).rank = Module.finrank F (LinearMap.range (X a).mulVecLin) := rfl
    omega
  · have e : P b * ((Q a)ᵀ * P a) = X a * (-((Y b)ᵀ * P a)) := by
      have h0 := congrArg (· * P a) (ho a b hab)
      simp only [Matrix.add_mul, Matrix.zero_mul] at h0
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact eq_neg_of_add_eq_zero_right h0
    have hle : LinearMap.range (P b * ((Q a)ᵀ * P a)).mulVecLin ≤
        LinearMap.range (P b).mulVecLin ⊓ LinearMap.range (X a).mulVecLin :=
      le_inf (hcol _ _) (by rw [e]; exact hcol _ _)
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h3 := sylvester_rank (P b) ((Q a)ᵀ * P a)
    simp only [Fintype.card_fin] at h3
    have h4 : (P b * ((Q a)ᵀ * P a)).rank =
        Module.finrank F (LinearMap.range (P b * ((Q a)ᵀ * P a)).mulVecLin) := rfl
    have h5 : (P b).rank = Module.finrank F (LinearMap.range (P b).mulVecLin) := rfl
    omega

/-- The three-cycle over distinct slices a, b, c. -/
theorem slice_three_cycle {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b c : Fin N) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    N + ((Q a)ᵀ * P a).rank + ((Y b)ᵀ * X b).rank + ((Q c)ᵀ * P c).rank ≤ 2 * r + 2 * k ∧
    N + ((Y a)ᵀ * X a).rank + ((Q b)ᵀ * P b).rank + ((Y c)ᵀ * X c).rank ≤ 2 * r + 2 * k := by
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
  have hXr : ∀ z, Module.finrank F (LinearMap.range (X z).mulVecLin) ≤ r := fun z => by
    have h0 : (X z).rank ≤ r := by simpa using Matrix.rank_le_card_width (X z)
    exact h0
  have hPk : ∀ z, Module.finrank F (LinearMap.range (P z).mulVecLin) ≤ k := fun z => by
    have h0 : (P z).rank ≤ k := by simpa using Matrix.rank_le_card_width (P z)
    exact h0
  constructor
  · have E1 := (slice_excess X Y P Q ho c a (Ne.symm hac)).2
    have E2 := (slice_excess X Y P Q ho c b (Ne.symm hbc)).1
    have E3 := (slice_excess X Y P Q ho a b hab).2
    have T1 := finrank_sup_triangle (LinearMap.range (P a).mulVecLin) (LinearMap.range (X c).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (X c).mulVecLin) (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h1 := htop' a
    have h2 := hXr a
    omega
  · have E1 := (slice_excess X Y P Q ho a c hac).1
    have E2 := (slice_excess X Y P Q ho b c hbc).2
    have E3 := (slice_excess X Y P Q ho b a (Ne.symm hab)).1
    have T1 := finrank_sup_triangle (LinearMap.range (X a).mulVecLin) (LinearMap.range (P c).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have T2 := finrank_sup_triangle (LinearMap.range (P c).mulVecLin) (LinearMap.range (X b).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have h1 := htop a
    have h2 := hPk a
    omega

/-- **Theorem 1.** For N ≥ 3, every split S_N = B + C over a field has 5 N ≤ 4 (rank B + rank (R C)): the six
rotations of the three-cycle on slices 0, 1, 2 plus the corank bound on each slice. -/
theorem swap_split_ge_five_quarters {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 5 * N ≤ 4 * (B.rank + (realign C).rank) := by
  obtain ⟨X, Y, P, Q, hd, ho⟩ := exists_slices N B C h
  set s0 : Fin N := ⟨0, by omega⟩
  set s1 : Fin N := ⟨1, by omega⟩
  set s2 : Fin N := ⟨2, by omega⟩
  have h01 : s0 ≠ s1 := by simp [s0, s1, Fin.ext_iff]
  have h02 : s0 ≠ s2 := by simp [s0, s2, Fin.ext_iff]
  have h12 : s1 ≠ s2 := by simp [s1, s2, Fin.ext_iff]
  have c0 := slice_corank (X s0) (Y s0) (P s0) (Q s0) (hd s0)
  have c1 := slice_corank (X s1) (Y s1) (P s1) (Q s1) (hd s1)
  have c2 := slice_corank (X s2) (Y s2) (P s2) (Q s2) (hd s2)
  have a1 := slice_three_cycle X Y P Q hd ho s0 s1 s2 h01 h02 h12
  have a2 := slice_three_cycle X Y P Q hd ho s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have a3 := slice_three_cycle X Y P Q hd ho s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  omega

/-- Corollary: for N ≥ 3, every split S_N = B + C has rank B + rank (R C) ≥ N + 1. -/
theorem swap_split_ge_succ {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 1 ≤ B.rank + (realign C).rank := by
  have := swap_split_ge_five_quarters N hN B C h
  omega

/-! ### The bound N + 2 (defect one) -/

/-- With r + k = N + 1 and N ≥ 4, both widths are at least 2 (Sylvester on an off-diagonal slice). -/
theorem slice_widths_ge_two {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 1)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : 2 ≤ r ∧ 2 ≤ k := by
  have h1 : (1 : Matrix (Fin N) (Fin N) F).rank = N := by simp [Matrix.rank_one]
  have hPk : ∀ y u, (P u * (Q y)ᵀ).rank ≤ k := fun y u =>
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width (P u))
  have hXr : ∀ y u, (X y * (Y u)ᵀ).rank ≤ r := fun y u =>
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width (X y))
  have hdiag : ∀ y, N ≤ (X y * (Y y)ᵀ).rank + k ∧ N ≤ (P y * (Q y)ᵀ).rank + r := by
    intro y
    have h2 := rank_add_le' (X y * (Y y)ᵀ) (P y * (Q y)ᵀ)
    rw [hd y, h1] at h2
    exact ⟨by have := hPk y y; omega, by have := hXr y y; omega⟩
  have hX : ∀ y, N ≤ (X y).rank + k := fun y =>
    le_trans (hdiag y).1 (Nat.add_le_add_right (Matrix.rank_mul_le_left _ _) _)
  have hY : ∀ y, N ≤ (Y y)ᵀ.rank + k := fun y =>
    le_trans (hdiag y).1 (Nat.add_le_add_right (Matrix.rank_mul_le_right _ _) _)
  have hP : ∀ y, N ≤ (P y).rank + r := fun y =>
    le_trans (hdiag y).2 (Nat.add_le_add_right (Matrix.rank_mul_le_left _ _) _)
  have hQ : ∀ y, N ≤ (Q y)ᵀ.rank + r := fun y =>
    le_trans (hdiag y).2 (Nat.add_le_add_right (Matrix.rank_mul_le_right _ _) _)
  set a : Fin N := ⟨0, by omega⟩
  set b : Fin N := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have e1 : X a * (Y b)ᵀ = -(P b * (Q a)ᵀ) := eq_neg_of_add_eq_zero_left (ho a b hab)
  have e2 : P b * (Q a)ᵀ = -(X a * (Y b)ᵀ) := eq_neg_of_add_eq_zero_right (ho a b hab)
  have s1 := sylvester_rank (X a) (Y b)ᵀ
  have s2 := sylvester_rank (P b) (Q a)ᵀ
  have rneg : ∀ A : Matrix (Fin N) (Fin N) F, (-A).rank ≤ A.rank := by
    intro A
    have := Matrix.rank_mul_le_right (-1 : Matrix (Fin N) (Fin N) F) A
    rwa [Matrix.neg_mul, Matrix.one_mul] at this
  have t1 : (X a * (Y b)ᵀ).rank ≤ k := by rw [e1]; exact le_trans (rneg _) (hPk a b)
  have t2 : (P b * (Q a)ᵀ).rank ≤ r := by rw [e2]; exact le_trans (rneg _) (hXr a b)
  simp only [Fintype.card_fin] at s1 s2
  have u1 := hX a
  have u2 := hY b
  have u3 := hP b
  have u4 := hQ a
  constructor <;> omega

/-- The defect-one dichotomy: if X Yᵀ + P Qᵀ = 1 (N × N) with r + k = N + 1, then Yᵀ X or Qᵀ P is
invertible, because their coranks add up to at most 1 (`slice_corank`). -/
theorem slice_dichotomy {F : Type*} [Field F] {N r k : ℕ} (hrk : r + k = N + 1)
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F)
    (hd : X * Yᵀ + P * Qᵀ = 1) : (Yᵀ * X).det ≠ 0 ∨ (Qᵀ * P).det ≠ 0 := by
  have hc := slice_corank X Y P Q hd
  have h1 : (Yᵀ * X).rank ≤ r := by simpa using Matrix.rank_le_card_width (Yᵀ * X)
  have h2 : (Qᵀ * P).rank ≤ k := by simpa using Matrix.rank_le_card_width (Qᵀ * P)
  by_cases hr : (Yᵀ * X).rank = r
  · exact Or.inl (det_ne_zero_of_rank_eq _ hr)
  · exact Or.inr (det_ne_zero_of_rank_eq _ (by omega))

/-- No mixed types: with column spaces CX z ⊔ CP z = ⊤, CX z ≠ ⊤, slices of type A (CP b ≤ CX a for b ≠ a)
or type B (CX a ≤ CP b for a ≠ b), and N ≥ 3, all slices have the same type. -/
theorem no_mixed_slices {F : Type*} [Field F] {N : ℕ} (hN : 3 ≤ N)
    (CX CP : Fin N → Submodule F (Fin N → F)) (A Bs : Fin N → Prop)
    (hAB : ∀ z, A z ∨ Bs z) (hR3 : ∀ z, CX z ⊔ CP z = ⊤)
    (hR1 : ∀ a b, A a → a ≠ b → CP b ≤ CX a) (hR2 : ∀ a b, Bs b → a ≠ b → CX a ≤ CP b)
    (hprop : ∀ z, CX z ≠ ⊤) : (∀ z, A z) ∨ (∀ z, Bs z) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := hcon
  have hb : Bs z1 := (hAB z1).resolve_left hz1
  have ha : A z2 := (hAB z2).resolve_right hz2
  have hne : z2 ≠ z1 := fun h => hz1 (h ▸ ha)
  have hV : CX z2 = CP z1 := le_antisymm (hR2 z2 z1 hb hne) (hR1 z2 z1 ha hne)
  obtain ⟨c, hc1, hc2⟩ : ∃ c : Fin N, c ≠ z1 ∧ c ≠ z2 := by
    have hcard : ({z1, z2} : Finset (Fin N)).card < (Finset.univ : Finset (Fin N)).card := by
      calc ({z1, z2} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
        _ < N := by omega
        _ = (Finset.univ : Finset (Fin N)).card := by simp
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    exact ⟨c, hc.1, hc.2⟩
  rcases hAB c with hcA | hcB
  · have h1 : CP z2 ≤ CX c := hR1 c z2 hcA hc2
    have h2 : CX c ≤ CP z1 := hR2 c z1 hb hc1
    have h3 : CP z2 ≤ CX z2 := hV ▸ le_trans h1 h2
    apply hprop z2
    rw [← hR3 z2, sup_eq_left.mpr h3]
  · have h1 : CX z1 ≤ CP c := hR2 z1 c hcB (Ne.symm hc1)
    have h2 : CP c ≤ CX z2 := hR1 z2 c ha (Ne.symm hc2)
    have h3 : CX z1 ≤ CP z1 := hV ▸ le_trans h1 h2
    apply hprop z2
    rw [hV, ← hR3 z1, sup_eq_right.mpr h3]

/-- Running supremum of the first j subspaces. -/
def chainSup {F : Type*} [Field F] {N : ℕ} (U : Fin N → Submodule F (Fin N → F)) : ℕ → Submodule F (Fin N → F)
  | 0 => ⊥
  | j + 1 => chainSup U j ⊔ (if h : j < N then U ⟨j, h⟩ else ⊥)

/-- The pure case: if U a ≤ V b for all a ≠ b, U z ⊔ V z = ⊤, V z ≠ ⊤ and dim U 0 ≥ 2, then the running
sums of the U's grow at every step, which gives more than N dimensions inside F^N. -/
theorem pure_slices_false {F : Type*} [Field F] {N : ℕ} (hN : 1 ≤ N)
    (U V : Fin N → Submodule F (Fin N → F)) (hR : ∀ a b, a ≠ b → U a ≤ V b)
    (hR3 : ∀ z, U z ⊔ V z = ⊤) (hV : ∀ z, V z ≠ ⊤)
    (hdim : 2 ≤ Module.finrank F (U ⟨0, by omega⟩)) : False := by
  have hle : ∀ j, ∀ b : Fin N, j ≤ b.val → chainSup U j ≤ V b := by
    intro j
    induction j with
    | zero => intro b _; exact bot_le
    | succ j ih =>
      intro b hb
      simp only [chainSup]
      refine sup_le (ih b (by omega)) ?_
      split_ifs with h
      · exact hR ⟨j, h⟩ b (by intro e; rw [← e] at hb; simp at hb)
      · exact bot_le
  have hnot : ∀ z, ¬ U z ≤ V z := by
    intro z h
    apply hV z
    rw [← hR3 z, sup_eq_right.mpr h]
  have hgrow : ∀ j, (h : j < N) → 1 ≤ j →
      Module.finrank F (chainSup U j) + 1 ≤ Module.finrank F (chainSup U (j + 1)) := by
    intro j h _
    have hlt : chainSup U j < chainSup U (j + 1) := by
      simp only [chainSup, dif_pos h]
      refine lt_of_le_of_ne le_sup_left ?_
      intro e
      apply hnot ⟨j, h⟩
      have : U ⟨j, h⟩ ≤ chainSup U j := by rw [e]; exact le_sup_right
      exact le_trans this (hle j ⟨j, h⟩ le_rfl)
    exact Submodule.finrank_lt_finrank_of_lt hlt
  have hone : 2 ≤ Module.finrank F (chainSup U 1) := by
    have e : chainSup U 1 = U ⟨0, by omega⟩ := by
      show chainSup U 0 ⊔ _ = _
      rw [dif_pos (by omega : 0 < N)]
      show ⊥ ⊔ _ = _
      exact bot_sup_eq _
    rw [e]
    exact hdim
  have hall : ∀ j, 1 ≤ j → j ≤ N → j + 1 ≤ Module.finrank F (chainSup U j) := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ j ih =>
      intro _ hj
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simpa using hone
      · have := ih hpos (by omega)
        have := hgrow j (by omega) hpos
        omega
  have hfin := hall N hN le_rfl
  have hup : Module.finrank F (chainSup U N) ≤ N := by
    have := Submodule.finrank_le (chainSup U N)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  omega

/-- Slice identities with widths r + k = N + 1 are impossible for N ≥ 4. -/
theorem defect_one_false {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 1)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : False := by
  classical
  obtain ⟨hr2, hk2⟩ := slice_widths_ge_two hN hrk X Y P Q hd ho
  let CX : Fin N → Submodule F (Fin N → F) := fun z => LinearMap.range (X z).mulVecLin
  let CP : Fin N → Submodule F (Fin N → F) := fun z => LinearMap.range (P z).mulVecLin
  have hcol : ∀ {m p : ℕ} (A : Matrix (Fin N) (Fin m) F) (G : Matrix (Fin m) (Fin p) F),
      LinearMap.range (A * G).mulVecLin ≤ LinearMap.range A.mulVecLin := by
    intro m p A G
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hR3 : ∀ z, CX z ⊔ CP z = ⊤ := by
    intro z
    rw [eq_top_iff]
    intro x _
    have hx : x = (X z) *ᵥ ((Y z)ᵀ *ᵥ x) + (P z) *ᵥ ((Q z)ᵀ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hd z, Matrix.one_mulVec]
    rw [hx]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have hR2 : ∀ a b, ((Y b)ᵀ * X b).det ≠ 0 → a ≠ b → CX a ≤ CP b := by
    intro a b hdet hab
    have e : X a * ((Y b)ᵀ * X b) = P b * (-((Q a)ᵀ * X b)) := by
      have h0 := congrArg (· * X b) (ho a b hab)
      simp only [Matrix.add_mul, Matrix.zero_mul] at h0
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact eq_neg_of_add_eq_zero_left h0
    have hu : IsUnit ((Y b)ᵀ * X b).det := isUnit_iff_ne_zero.mpr hdet
    have hinv : X a = P b * (-((Q a)ᵀ * X b) * ((Y b)ᵀ * X b)⁻¹) := by
      calc X a = X a * (((Y b)ᵀ * X b) * ((Y b)ᵀ * X b)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = P b * (-((Q a)ᵀ * X b) * ((Y b)ᵀ * X b)⁻¹) := by
            rw [← Matrix.mul_assoc, e, Matrix.mul_assoc]
    show LinearMap.range (X a).mulVecLin ≤ LinearMap.range (P b).mulVecLin
    rw [hinv]
    exact hcol _ _
  have hR1 : ∀ a b, ((Q a)ᵀ * P a).det ≠ 0 → a ≠ b → CP b ≤ CX a := by
    intro a b hdet hab
    have e : P b * ((Q a)ᵀ * P a) = X a * (-((Y b)ᵀ * P a)) := by
      have h0 := congrArg (· * P a) (ho a b hab)
      simp only [Matrix.add_mul, Matrix.zero_mul] at h0
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      exact eq_neg_of_add_eq_zero_right h0
    have hu : IsUnit ((Q a)ᵀ * P a).det := isUnit_iff_ne_zero.mpr hdet
    have hinv : P b = X a * (-((Y b)ᵀ * P a) * ((Q a)ᵀ * P a)⁻¹) := by
      calc P b = P b * (((Q a)ᵀ * P a) * ((Q a)ᵀ * P a)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
        _ = X a * (-((Y b)ᵀ * P a) * ((Q a)ᵀ * P a)⁻¹) := by
            rw [← Matrix.mul_assoc, e, Matrix.mul_assoc]
    show LinearMap.range (P b).mulVecLin ≤ LinearMap.range (X a).mulVecLin
    rw [hinv]
    exact hcol _ _
  have hAB : ∀ z, ((Q z)ᵀ * P z).det ≠ 0 ∨ ((Y z)ᵀ * X z).det ≠ 0 := fun z =>
    (slice_dichotomy hrk (X z) (Y z) (P z) (Q z) (hd z)).symm
  have hfin : ∀ S : Submodule F (Fin N → F), Module.finrank F S < N → S ≠ ⊤ := by
    intro S hS e
    rw [e, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hS
    omega
  have hCX : ∀ z, CX z ≠ ⊤ := fun z => hfin _ (by
    have : (X z).rank ≤ r := by simpa using Matrix.rank_le_card_width (X z)
    show (X z).rank < N
    omega)
  have hCP : ∀ z, CP z ≠ ⊤ := fun z => hfin _ (by
    have : (P z).rank ≤ k := by simpa using Matrix.rank_le_card_width (P z)
    show (P z).rank < N
    omega)
  rcases no_mixed_slices (by omega) CX CP (fun z => ((Q z)ᵀ * P z).det ≠ 0)
      (fun z => ((Y z)ᵀ * X z).det ≠ 0) hAB hR3 hR1 hR2 hCX with hA | hB
  · refine pure_slices_false (by omega) CP CX (fun a b hab => hR1 b a (hA b) (Ne.symm hab))
      (fun z => by rw [sup_comm]; exact hR3 z) hCX ?_
    have hu : IsUnit ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA _))
    have h1 : ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩).rank = k := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Q ⟨0, by omega⟩)ᵀ (P ⟨0, by omega⟩)
    show 2 ≤ (P ⟨0, by omega⟩).rank
    omega
  · refine pure_slices_false (by omega) CX CP (fun a b hab => hR2 a b (hB b) hab) hR3 hCP ?_
    have hu : IsUnit ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hB _))
    have h1 : ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩).rank = r := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Y ⟨0, by omega⟩)ᵀ (X ⟨0, by omega⟩)
    show 2 ≤ (X ⟨0, by omega⟩).rank
    omega

/-- **Theorem 2.** For N ≥ 4, every split S_N = B + C over a field has rank B + rank (R C) ≥ N + 2. -/
theorem swap_split_ge_add_two {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 2 ≤ B.rank + (realign C).rank := by
  have h54 := swap_split_ge_five_quarters N (by omega) B C h
  by_contra hlt
  have heq : B.rank + (realign C).rank = N + 1 := by omega
  obtain ⟨X, Y, P, Q, hd, ho⟩ := exists_slices N B C h
  exact defect_one_false hN heq X Y P Q hd ho

/-- Corollary: P(4) ≥ 6 over every field. -/
theorem swap_split_four_ge_six {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : swapMat F 4 = B + C) : 6 ≤ B.rank + (realign C).rank :=
  swap_split_ge_add_two 4 le_rfl B C h

end SwapSplit

#print axioms SwapSplit.swap_split_ge_five_quarters
#print axioms SwapSplit.swap_split_ge_succ
#print axioms SwapSplit.swap_split_ge_add_two
#print axioms SwapSplit.swap_split_four_ge_six
