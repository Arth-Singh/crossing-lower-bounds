/-
The values P(4) = 7, P(5) ≥ 8 and P(6) ≥ 9, and P(N) ≥ N + 3 for every N ≥ 4, over every field.

The body of this file is the dependency closure of the library units P4_ge_seven_every_field,
P4_eq_seven_upper_split_any_field, P5_ge_eight_every_field and
P_N_add_three_ge_six_and_P6_ge_nine_every_field of an automated multi-agent run, concatenated in
dependency order without changes (one section per unit). The agents' names for the swap matrix and the
realignment are `biancaSwapF` and `biancaRealignF`; the last section states the results with the definitions of
SwapSplit.lean and proves that the two pairs of definitions agree.
-/
import Mathlib
import SwapSplit

/-! ## unit T381_lemmaK_rank_one_slice_form_and_dual -/
section
open Matrix
-- T381 brick (i) of D22 update 7 (Gideon referee step 2: RIGHT). Slice convention: X_a = F(e_a), Y_b = G(e_b), P_b = P(e_b),
-- Q_a = Q(e_a), so hd/ho are Nadia's Eq.1 at basis vectors; column u of Eq.2 (Lemma K) is daria_lemmaK, column u of Eq.2' its dual.
-- Nadia's Lemma K (T381 plan, piece (b) for Daria) in her slice form hd/ho: with X(x) = Σ_y x_y X_y and Q(x) = Σ_y x_y Q_y,
-- if Q(x)ᵀ n = 0 then X(x) (Y_uᵀ n) = x_u n for every u; dually, if X(x)ᵀ m = 0 then Q(x) (P_uᵀ m) = x_u m.

/-- The slice identities in one form: X_y Y_uᵀ = δ_yu I − P_u Q_yᵀ. -/
theorem daria_slice_XY {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (y u : Fin N) :
    X y * (Y u)ᵀ = (if y = u then 1 else 0) - P u * (Q y)ᵀ := by
  by_cases h : y = u
  · subst h
    rw [if_pos rfl]
    exact eq_sub_of_add_eq (hd y)
  · rw [if_neg h, zero_sub]
    exact eq_neg_of_add_eq_zero_left (ho y u h)

/-- The transposed slice identities: Q_y P_uᵀ = δ_yu I − Y_u X_yᵀ. -/
theorem daria_slice_QP {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (y u : Fin N) :
    Q y * (P u)ᵀ = (if y = u then 1 else 0) - Y u * (X y)ᵀ := by
  by_cases h : y = u
  · subst h
    rw [if_pos rfl]
    have h1 := congrArg Matrix.transpose (hd y)
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h1
    rw [add_comm] at h1
    exact eq_sub_of_add_eq h1
  · rw [if_neg h, zero_sub]
    have h1 := congrArg Matrix.transpose (ho y u h)
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h1
    rw [add_comm] at h1
    exact eq_neg_of_add_eq_zero_left h1

/-- **Lemma K (slice form).** If Q(x)ᵀ n = 0, then X(x) (Y_uᵀ n) = x_u • n for every u. -/
theorem daria_lemmaK {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (x n : Fin N → F) (hn : (∑ y, x y • Q y)ᵀ *ᵥ n = 0) (u : Fin N) :
    (∑ y, x y • X y) *ᵥ ((Y u)ᵀ *ᵥ n) = x u • n := by
  have key : (∑ y, x y • X y) * (Y u)ᵀ = x u • (1 : Matrix (Fin N) (Fin N) F) - P u * (∑ y, x y • Q y)ᵀ := by
    rw [Matrix.sum_mul]
    simp_rw [Matrix.smul_mul, daria_slice_XY X Y P Q hd ho, smul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single u]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ u) h
    · rw [Matrix.transpose_sum, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.transpose_smul, Matrix.mul_smul]
  rw [Matrix.mulVec_mulVec, key, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hn, Matrix.mulVec_zero, sub_zero]

/-- **Dual Lemma K (slice form).** If X(x)ᵀ m = 0, then Q(x) (P_uᵀ m) = x_u • m for every u. -/
theorem daria_lemmaK_dual {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (x m : Fin N → F) (hm : (∑ y, x y • X y)ᵀ *ᵥ m = 0) (u : Fin N) :
    (∑ y, x y • Q y) *ᵥ ((P u)ᵀ *ᵥ m) = x u • m := by
  have key : (∑ y, x y • Q y) * (P u)ᵀ = x u • (1 : Matrix (Fin N) (Fin N) F) - Y u * (∑ y, x y • X y)ᵀ := by
    rw [Matrix.sum_mul]
    simp_rw [Matrix.smul_mul, daria_slice_QP X Y P Q hd ho, smul_sub, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single u]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ u) h
    · rw [Matrix.transpose_sum, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.transpose_smul, Matrix.mul_smul]
  rw [Matrix.mulVec_mulVec, key, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_zero, sub_zero]

/-- Non-vacuity (D14): the slice hypotheses hd/ho are satisfiable (N = r = k = 1, X = Y = 1, P = Q = 0). -/
theorem daria_lemmaK_witness : ∃ X Y P Q : Fin 1 → Matrix (Fin 1) (Fin 1) ℚ,
    (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) ∧ (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :=
  ⟨fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => by simp, fun y u h => absurd (Subsingleton.elim y u) h⟩
end

/-! ## unit rank_factorization_sum_of_rank_one -/
section
/-- Rank factorization (D11 piece (B), step 1): a matrix of rank r over a field is a sum of r matrices of
rank one, A = Σ_{k < r} u_k v_kᵀ, from a basis of the span of its columns. -/
theorem bianca_exists_sum_vecMulVec_of_rank {F m n : Type*} [Field F] [Fintype m] [Fintype n]
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
end

/-! ## unit merge_level_ceiling_matrix_rank -/
section
/-- Rank subadditivity for matrices (finite rank form). -/
theorem bianca_matrix_rank_add_le {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A B : Matrix m n K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (m → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Rank of a finite sum of matrices is at most the sum of the ranks. -/
theorem bianca_matrix_rank_sum_le {ι m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (s : Finset ι) (A : ι → Matrix m n K) : (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (bianca_matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

/-- The merge-level ceiling (Gideon's advisor note on Q40, conditions (a)-(c)), abstract form: if a level
writes a value whose flattening has rank at least 2^B as a sum of terms, each of which costs at least
its own flattening rank, and every term costs at most 2^c, then 2^B ≤ (number of terms)·2^c. -/
theorem bianca_merge_ceiling_card {ι m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (s : Finset ι) (A : ι → Matrix m n K) (B c : ℕ) (hfull : 2 ^ B ≤ (∑ i ∈ s, A i).rank)
    (hcost : ∀ i ∈ s, (A i).rank ≤ 2 ^ c) : 2 ^ B ≤ s.card * 2 ^ c := by
  refine hfull.trans ((bianca_matrix_rank_sum_le s A).trans ?_)
  have h := Finset.sum_le_card_nsmul s (fun i => (A i).rank) (2 ^ c) hcost
  simpa [smul_eq_mul] using h

/-- Exponent form: with at most 2^t terms, some cost bound c needs B ≤ t + c. So a level with 2^{o(B)}
terms has a term of cost 2^{B - o(B)}: the class that an R3 door (T69) has to leave is exactly the one
where (a) the terms are few, (b) each term is charged its flattening rank, (c) the flattening is full. -/
theorem bianca_merge_ceiling_exponent {ι m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (s : Finset ι) (A : ι → Matrix m n K) (B c t : ℕ) (hfull : 2 ^ B ≤ (∑ i ∈ s, A i).rank)
    (hcost : ∀ i ∈ s, (A i).rank ≤ 2 ^ c) (ht : s.card ≤ 2 ^ t) : B ≤ t + c := by
  have h := bianca_merge_ceiling_card s A B c hfull hcost
  have h2 : 2 ^ B ≤ 2 ^ (t + c) := h.trans (by rw [pow_add]; exact Nat.mul_le_mul_right _ ht)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
end

/-! ## unit minsum_le_two_sigma_over_any_field -/
section

/-- SWAP over a field F on index type X: rows (x, y), columns (u, v), entry [x = v][y = u]. -/
def biancaSwapF (F X : Type*) [Field F] [DecidableEq X] : Matrix (X × X) (X × X) F :=
  Matrix.of fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

/-- Operator-Schmidt flattening over a field F. -/
def biancaRealignF {F X : Type*} (M : Matrix (X × X) (X × X) F) : Matrix (X × X) (X × X) F :=
  Matrix.of fun a b => M (a.1, b.1) (a.2, b.2)

/-- I65 direction (A), over every field with 2 ≠ 0 (Leon's note, Silas's reading of R91): coefficient
tables ψ_k of a composition formula [|X|, |X|, |K|] over F satisfy the polarized identity
Σ_k ψ_k(x,y)ψ_k(v,u) + Σ_k ψ_k(x,u)ψ_k(v,y) = 2[x=v][y=u]; then SWAP = B + C with rank B ≤ |K| and
operator-Schmidt rank of C ≤ |K|. So minsum_F(N) ≤ 2σ_F(N), e.g. for complex formulas. -/
theorem bianca_minsumF_le_of_composition {F K X : Type*} [Field F] [Fintype K] [Fintype X] [DecidableEq X]
    (h2 : (2 : F) ≠ 0) (ψ : K → X → X → F)
    (h : ∀ x y u v : X, (∑ k, ψ k x y * ψ k v u) + (∑ k, ψ k x u * ψ k v y) =
      2 * (if x = v ∧ y = u then 1 else 0)) :
    ∃ B C : Matrix (X × X) (X × X) F,
      B + C = biancaSwapF F X ∧ B.rank ≤ Fintype.card K ∧ (biancaRealignF C).rank ≤ Fintype.card K := by
  let B : Matrix (X × X) (X × X) F :=
    ∑ k, Matrix.vecMulVec (fun a => (2 : F)⁻¹ * ψ k a.1 a.2) (fun b => ψ k b.2 b.1)
  have hB : B.rank ≤ Fintype.card K := by
    refine (bianca_matrix_rank_sum_le _ _).trans ?_
    calc ∑ k : K, (Matrix.vecMulVec (fun a : X × X => (2 : F)⁻¹ * ψ k a.1 a.2)
          (fun b : X × X => ψ k b.2 b.1)).rank ≤ ∑ _k : K, 1 :=
          Finset.sum_le_sum fun k _ => Matrix.rank_vecMulVec_le _ _
      _ = Fintype.card K := by simp
  refine ⟨B, biancaRealignF B, ?_, hB, ?_⟩
  · ext a b
    obtain ⟨x, y⟩ := a
    obtain ⟨u, v⟩ := b
    have hxy := h x y u v
    simp only [B, biancaRealignF, biancaSwapF, Matrix.add_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Matrix.of_apply, mul_assoc, ← Finset.mul_sum, ← mul_add]
    rw [hxy, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  · have : biancaRealignF (biancaRealignF B) = B := by
      ext a b; rfl
    rw [this]
    exact hB
end

/-! ## unit slice_system_of_split_shared_bridge_eq1_lemmaK -/
section
open Matrix
-- T381 brick L1 (Nadia 02:24; hi itself is Lena's lena_P4_hi). Bridge: an exact split SWAP_N = B + C with rank B ≤ r and OS C ≤ k gives Nadia's slice
-- system hd/ho of widths EXACTLY r and k (zero-padded). The slice construction is copied, with credit, from Nadia's
-- nadia_minsumF_ge_N_add_two (minsum_ge_N_plus_two_every_field), where it is inline; padding lets Lena's full-width
-- lena_slice_full_width_os_two_false (r = N) and widths-≤ statements be applied directly.

/-- A matrix of rank ≤ r is a sum of exactly r outer products (Bianca's factorization, zero-padded). -/
theorem daria_sum_vecMulVec_pad {F m n : Type*} [Field F] [Fintype m] [Fintype n] (A : Matrix m n F) (r : ℕ)
    (hr : A.rank ≤ r) : ∃ (U : Fin r → m → F) (V : Fin r → n → F), A = ∑ i, vecMulVec (U i) (V i) := by
  obtain ⟨U, V, hA⟩ := bianca_exists_sum_vecMulVec_of_rank A
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  refine ⟨Fin.append U (fun _ => 0), Fin.append V (fun _ => 0), ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_vecMulVec, Finset.sum_const_zero, add_zero]
  exact hA

/-- **Split to slices.** SWAP_N = B + C over any field, rank B ≤ r, OS C ≤ k ⟹ a slice system of widths r, k. -/
theorem daria_slices_of_split {F : Type*} [Field F] (N r k : ℕ)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hr : B.rank ≤ r) (hk : (biancaRealignF C).rank ≤ k) :
    ∃ (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F),
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) ∧ (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) := by
  obtain ⟨U, V, hB⟩ := daria_sum_vecMulVec_pad B r hr
  obtain ⟨P, Q, hC⟩ := daria_sum_vecMulVec_pad (biancaRealignF C) k hk
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if x = v ∧ y = u then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = biancaRealignF C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin r) F := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin r) F := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin k) F := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin k) F := fun y => Matrix.of fun v l => Q l (y, v)
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
      · simp [hxv]
    · simp [hyu]
  exact ⟨X, Y, PP, QQ, fun y => by simpa using hslice y y, fun y u hyu => by simpa [hyu] using hslice y u⟩

/-- **D22 update 10 shared bridge, word for word**: SWAP_N = B + C ⟹ slices of widths rank B and OS C with hd/ho. -/
theorem slice_system_of_split {F : Type*} [Field F] {N : ℕ} (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = B + C) :
    ∃ (X Y : Fin N → Matrix (Fin N) (Fin B.rank) F) (P Q : Fin N → Matrix (Fin N) (Fin (biancaRealignF C).rank) F),
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) ∧ (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :=
  daria_slices_of_split N B.rank (biancaRealignF C).rank B C h le_rfl le_rfl

/-- **Eq.1 in slice form** (Nadia's bilinear identity F(x) G(y)ᵀ + P(y) Q(x)ᵀ = (x ⬝ y) I). -/
theorem daria_slice_eq1 {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (x y : Fin N → F) :
    (∑ a, x a • X a) * (∑ b, y b • Y b)ᵀ + (∑ b, y b • P b) * (∑ a, x a • Q a)ᵀ =
      (∑ a, x a * y a) • (1 : Matrix (Fin N) (Fin N) F) := by
  have hs : ∀ a b, X a * (Y b)ᵀ + P b * (Q a)ᵀ = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b
    · subst h; rw [if_pos rfl]; exact hd a
    · rw [if_neg h]; exact ho a b h
  have h1 : (∑ a, x a • X a) * (∑ b, y b • Y b)ᵀ = ∑ a, ∑ b, (x a * y b) • (X a * (Y b)ᵀ) := by
    rw [Matrix.transpose_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (∑ b, y b • P b) * (∑ a, x a • Q a)ᵀ = ∑ a, ∑ b, (x a * y b) • (P b * (Q a)ᵀ) := by
    rw [Matrix.transpose_sum, Matrix.sum_mul]
    simp_rw [Matrix.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (y b) (x a)]
  rw [h1, h2, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_eq_single a]
  · rw [← smul_add, hs, if_pos rfl]
  · intro b _ hb
    rw [← smul_add, hs, if_neg (Ne.symm hb), smul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **T381 brick L1 (Nadia's list, 02:24)**: an exact split SWAP_N = B + C with rank B ≤ r, OS C ≤ k gives slices of
widths r, k satisfying Eq.1 for all x, y and Lemma K (daria_lemmaK) for every n with Q(x)ᵀ n = 0. -/
theorem daria_L1_eq1_lemmaK_of_split {F : Type*} [Field F] (N r k : ℕ)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hr : B.rank ≤ r) (hk : (biancaRealignF C).rank ≤ k) :
    ∃ (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F),
      (∀ x y : Fin N → F, (∑ a, x a • X a) * (∑ b, y b • Y b)ᵀ + (∑ b, y b • P b) * (∑ a, x a • Q a)ᵀ =
        (∑ a, x a * y a) • (1 : Matrix (Fin N) (Fin N) F)) ∧
      (∀ x n : Fin N → F, (∑ a, x a • Q a)ᵀ *ᵥ n = 0 → ∀ u, (∑ a, x a • X a) *ᵥ ((Y u)ᵀ *ᵥ n) = x u • n) := by
  obtain ⟨X, Y, P, Q, hd, ho⟩ := daria_slices_of_split N r k B C h hr hk
  exact ⟨X, Y, P, Q, daria_slice_eq1 X Y P Q hd ho, fun x n hn u => daria_lemmaK X Y P Q hd ho x n hn u⟩
end

/-! ## unit T414_L2a_eq1_rank_split_f_plus_q -/
section
open Matrix

/-- **L2 (a) (T414, Lena)**: from Nadia's Eq.1 in Daria's slice notation, at every x with x·x ≠ 0 the generic ranks add up:
rank X(x) + rank Q(x) ≥ N and rank Y(x) + rank P(x) ≥ N (Eq.1 at y = x is (x·x) I). -/
theorem lena_eq1_rank_split {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (x : Fin N → F) (hx : ∑ a, x a * x a ≠ 0) :
    N ≤ (∑ a, x a • X a).rank + (∑ a, x a • Q a).rank ∧
      N ≤ (∑ a, x a • Y a).rank + (∑ a, x a • P a).rank := by
  have h := daria_slice_eq1 X Y P Q hd ho x x
  have hu : IsUnit ((∑ a, x a * x a) • (1 : Matrix (Fin N) (Fin N) F)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (isUnit_iff_ne_zero.mpr hx).pow _
  have hN : ((∑ a, x a * x a) • (1 : Matrix (Fin N) (Fin N) F)).rank = N := by
    rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
  have h1 := bianca_matrix_rank_add_le ((∑ a, x a • X a) * (∑ b, x b • Y b)ᵀ) ((∑ b, x b • P b) * (∑ a, x a • Q a)ᵀ)
  rw [h, hN] at h1
  have e1 := Matrix.rank_mul_le_left (∑ a, x a • X a) (∑ b, x b • Y b)ᵀ
  have e2 := Matrix.rank_mul_le_right (∑ b, x b • P b) (∑ a, x a • Q a)ᵀ
  have e3 := Matrix.rank_mul_le_right (∑ a, x a • X a) (∑ b, x b • Y b)ᵀ
  have e4 := Matrix.rank_mul_le_left (∑ b, x b • P b) (∑ a, x a • Q a)ᵀ
  rw [Matrix.rank_transpose] at e2 e3
  constructor <;> omega
end

/-! ## unit T381_C2a_QF_zero_all_two -/
section
open Matrix

/-- Over Q a nonzero vector has nonzero sum of squares. -/
theorem nadia_sumsq_ne_zero (x : Fin 4 → ℚ) (hx : x ≠ 0) : ∑ a, x a * x a ≠ 0 := by
  intro h
  apply hx
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => mul_self_nonneg (x a))).mp h
  funext a
  exact mul_self_eq_zero.mp (h0 a (Finset.mem_univ a))

/-- C2 step (a) (Nadia): if rank Fx(x) ≤ 2 and rank Qx(x) ≤ 2 for every x, then Qx(x)ᵀ Fx(x) = 0 for every x. -/
theorem nadia_C2_QF_zero (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) ℚ)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → ℚ, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → ℚ, (∑ a, x a • Q a).rank ≤ 2)
    (x : Fin 4 → ℚ) : (∑ a, x a • Q a)ᵀ * (∑ a, x a • X a) = 0 := by
  classical
  by_cases hx : x = 0
  · subst hx; simp
  have hsplit := (lena_eq1_rank_split X Y P Q hd ho x (nadia_sumsq_ne_zero x hx)).1
  have hFx1 := hF x
  have hQx1 := hQ x
  set Fx := ∑ a, x a • X a with hFx
  set Qx := ∑ a, x a • Q a with hQx
  have hF2 : Fx.rank = 2 := by omega
  have hQ2 : Qx.rank = 2 := by omega
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra hall; push Not at hall; exact hx (funext hall)
  have hle : LinearMap.ker Qxᵀ.mulVecLin ≤ LinearMap.range Fx.mulVecLin := by
    intro n hn
    have hn' : Qxᵀ *ᵥ n = 0 := hn
    have hK := daria_lemmaK X Y P Q hd ho x n hn' b
    refine ⟨(x b)⁻¹ • ((Y b)ᵀ *ᵥ n), ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_smul, hK, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hdimK : Module.finrank ℚ (LinearMap.ker Qxᵀ.mulVecLin) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Qxᵀ.mulVecLin
    have h2 : Qxᵀ.rank = Module.finrank ℚ (LinearMap.range Qxᵀ.mulVecLin) := rfl
    rw [Matrix.rank_transpose, hQ2] at h2
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  have hdimR : Module.finrank ℚ (LinearMap.range Fx.mulVecLin) = 2 := hF2
  have heq : LinearMap.ker Qxᵀ.mulVecLin = LinearMap.range Fx.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimK, hdimR])
  ext i j
  have hw : Fx *ᵥ (Pi.single j 1) ∈ LinearMap.ker Qxᵀ.mulVecLin := by rw [heq]; exact ⟨_, rfl⟩
  have hw' : Qxᵀ *ᵥ (Fx *ᵥ (Pi.single j 1)) = 0 := hw
  rw [Matrix.mulVec_mulVec] at hw'
  have := congrFun hw' i
  simpa [Matrix.mulVec_single] using this
end

/-! ## unit matrix_sylvester_rank_inequality -/
section
/-- Sylvester's rank inequality (T331 step): rank A + rank B ≤ rank (A * B) + (inner dimension). -/
theorem nadia_rank_add_rank_le_rank_mul {F : Type*} [Field F] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
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
end

/-! ## unit T381_offdiag_rank_one_false -/
section
open Matrix

/-- T381 brick L5' (Nadia): if every G_s F_u - δ_su I (s, u ∈ Fin 3, 4 × 4) has rank ≤ 1, contradiction.
G_s F_s has rank ≥ 3, so rank G_0 ≥ 3 and rank F_1 ≥ 3, and Sylvester gives rank (G_0 F_1) ≥ 2 against ≤ 1. -/
theorem nadia_T381_offdiag_rank_one_false {F : Type*} [Field F]
    (G Fm : Fin 3 → Matrix (Fin 4) (Fin 4) F)
    (h : ∀ s u, (G s * Fm u - (if s = u then (1 : Matrix (Fin 4) (Fin 4) F) else 0)).rank ≤ 1) : False := by
  have hneg : ∀ A : Matrix (Fin 4) (Fin 4) F, (-A).rank ≤ A.rank := by
    intro A
    have := Matrix.rank_mul_le_right (-1 : Matrix (Fin 4) (Fin 4) F) A
    rwa [Matrix.neg_mul, Matrix.one_mul] at this
  have hdiag : ∀ s, 3 ≤ (G s * Fm s).rank := by
    intro s
    have e : (1 : Matrix (Fin 4) (Fin 4) F) = G s * Fm s + -(G s * Fm s - 1) := by abel
    have h1 : (1 : Matrix (Fin 4) (Fin 4) F).rank = 4 := by simp [Matrix.rank_one]
    have h2 := bianca_matrix_rank_add_le (G s * Fm s) (-(G s * Fm s - 1))
    rw [← e, h1] at h2
    have h3 : (G s * Fm s - 1).rank ≤ 1 := by simpa using h s s
    have h4 := le_trans (hneg _) h3
    omega
  have hG0 : 3 ≤ (G 0).rank := le_trans (hdiag 0) (Matrix.rank_mul_le_left _ _)
  have hF1 : 3 ≤ (Fm 1).rank := le_trans (hdiag 1) (Matrix.rank_mul_le_right _ _)
  have hsyl := nadia_rank_add_rank_le_rank_mul (G 0) (Fm 1)
  simp only [Fintype.card_fin] at hsyl
  have hoff : (G 0 * Fm 1).rank ≤ 1 := by simpa using h 0 1
  omega
end

/-! ## unit minsum_slice_bound_swap_rank_plus_os -/
section

/-- SWAP_N as a matrix: rows (x, y), columns (u, v), entry [u = y][v = x]. -/
def nadiaSwapMat (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℚ :=
  fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The realignment (x, y), (u, v) ↦ (x, u), (y, v); its rank is the operator Schmidt rank. -/
def nadiaRealignMat {N : ℕ} (C : Matrix (Fin N × Fin N) (Fin N × Fin N) ℚ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℚ :=
  fun p q => C (p.1, q.1) (p.2, q.2)

/-- **Slice bound (I62 floor, Lean):** if SWAP_N = B + C then N ≤ rank B + OS(C), where OS(C) is the rank of
the realignment of C. So minsum(N) ≥ N. -/
theorem nadia_minsum_slice_bound (N : ℕ) (hN : 0 < N) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) ℚ)
    (h : nadiaSwapMat N = B + C) : N ≤ B.rank + (nadiaRealignMat C).rank := by
  let x0 : Fin N := ⟨0, hN⟩
  let SB : Matrix (Fin N) (Fin N) ℚ := B.submatrix (fun y => (x0, y)) (fun u => (u, x0))
  let SC : Matrix (Fin N) (Fin N) ℚ := C.submatrix (fun y => (x0, y)) (fun u => (u, x0))
  have hsum : (1 : Matrix (Fin N) (Fin N) ℚ) = SB + SC := by
    ext y u
    have := congrFun (congrFun h (x0, y)) (u, x0)
    simp only [nadiaSwapMat, Matrix.add_apply] at this
    simp only [SB, SC, Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply]
    rw [← this]
    by_cases hyu : y = u
    · subst hyu; simp
    · have : ¬ u = y := fun h' => hyu h'.symm
      simp [hyu, this]
  have hB : SB.rank ≤ B.rank := Matrix.rank_submatrix_le B _ _
  have hCt : SC.transpose = (nadiaRealignMat C).submatrix (fun u => (x0, u)) (fun y => (y, x0)) := by
    ext u y; rfl
  have hC : SC.rank ≤ (nadiaRealignMat C).rank := by
    rw [← Matrix.rank_transpose SC, hCt]
    exact Matrix.rank_submatrix_le _ _ _
  have h1 : (1 : Matrix (Fin N) (Fin N) ℚ).rank = N := by simp
  have hadd := bianca_matrix_rank_add_le SB SC
  rw [← hsum, h1] at hadd
  omega
end

/-! ## unit minsum_ge_eight_sevenths_N_defect_three_cycle -/
section

open Matrix

/-- Defect blocks: if X·Yᵀ + P·Qᵀ = 1 (N × N), then 1 − Yᵀ X and 1 − Qᵀ P have rank ≤ r + k − N
(they are corners of 1 − W M, and M (1 − W M) = 0 with rank M = N). -/
theorem bianca_defect_rank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F)
    (h : X * Yᵀ + P * Qᵀ = 1) :
    (1 - Yᵀ * X).rank ≤ r + k - N ∧ (1 - Qᵀ * P).rank ≤ r + k - N := by
  let M : Matrix (Fin N) (Fin r ⊕ Fin k) F := Matrix.of fun x s => Sum.elim (X x) (P x) s
  let W : Matrix (Fin r ⊕ Fin k) (Fin N) F := Matrix.of fun s v => Sum.elim (Y v) (Q v) s
  have hMW : M * W = 1 := by
    rw [← h]
    ext x v
    simp only [M, W, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Matrix.add_apply, Matrix.transpose_apply]
  have hME : M * (1 - W * M) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hMW, Matrix.one_mul, sub_self]
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hME
  have hM : N ≤ M.rank := by
    have h1 : (M * W).rank ≤ M.rank := Matrix.rank_mul_le_left M W
    rw [hMW, Matrix.rank_one, Fintype.card_fin] at h1
    exact h1
  simp only [Fintype.card_sum, Fintype.card_fin] at hsum
  have hE : (1 - W * M).rank ≤ r + k - N := by omega
  have b1 : (1 - Yᵀ * X) = (1 - W * M).submatrix Sum.inl Sum.inl := by
    ext i j
    simp [M, W, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply]
  have b2 : (1 - Qᵀ * P) = (1 - W * M).submatrix Sum.inr Sum.inr := by
    ext i j
    simp [M, W, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply]
  refine ⟨?_, ?_⟩
  · rw [b1]; exact le_trans (Matrix.rank_submatrix_le _ _ _) hE
  · rw [b2]; exact le_trans (Matrix.rank_submatrix_le _ _ _) hE

/-- If X·Yt + P·Qt = 1 (N × N) and P = R − X·G, then N ≤ r + rank R. -/
theorem bianca_rank_one_split {F : Type*} [Field F] {N r k : ℕ}
    (X : Matrix (Fin N) (Fin r) F) (Yt : Matrix (Fin r) (Fin N) F)
    (P : Matrix (Fin N) (Fin k) F) (Qt : Matrix (Fin k) (Fin N) F)
    (R : Matrix (Fin N) (Fin k) F) (G : Matrix (Fin r) (Fin k) F)
    (h1 : X * Yt + P * Qt = 1) (hP : P = R - X * G) : N ≤ r + R.rank := by
  have e : X * (Yt - G * Qt) + R * Qt = 1 := by
    rw [← h1, hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hr := bianca_matrix_rank_add_le (X * (Yt - G * Qt)) (R * Qt)
  rw [e, Matrix.rank_one, Fintype.card_fin] at hr
  have ha : (X * (Yt - G * Qt)).rank ≤ r :=
    le_trans (Matrix.rank_mul_le_left _ _) (by simpa using Matrix.rank_le_card_width X)
  have hb : (R * Qt).rank ≤ R.rank := Matrix.rank_mul_le_left _ _
  omega

/-- rank (A − B + C) ≤ rank A + rank B + rank C. -/
theorem bianca_rank_sub_add_le {F : Type*} [Field F] {m n : Type*} [Fintype m] [Fintype n]
    (A B C : Matrix m n F) : (A - B + C).rank ≤ A.rank + B.rank + C.rank := by
  classical
  have h1 := bianca_matrix_rank_add_le (A - B) C
  have h2 := bianca_matrix_rank_add_le A (-B)
  rw [← sub_eq_add_neg] at h2
  have hn : (-B).rank ≤ B.rank := by
    have := Matrix.rank_mul_le_left B (-1 : Matrix n n F)
    rwa [Matrix.mul_neg, Matrix.mul_one] at this
  omega

/-- The defect chain over three slices: with defect blocks of rank ≤ d, N ≤ r + 3d and N ≤ k + 3d. -/
theorem bianca_defect_chain {F : Type*} [Field F] {N r k d : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (D : Fin N → Matrix (Fin r) (Fin r) F) (D' : Fin N → Matrix (Fin k) (Fin k) F)
    (hD : ∀ z, (Y z)ᵀ * X z = 1 - D z) (hD' : ∀ z, (Q z)ᵀ * P z = 1 - D' z)
    (hDr : ∀ z, (D z).rank ≤ d) (hD'r : ∀ z, (D' z).rank ≤ d)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (y u w : Fin N) (hyu : y ≠ u) (hyw : y ≠ w) (huw : u ≠ w) :
    N ≤ r + 3 * d ∧ N ≤ k + 3 * d := by
  -- (i) X a = X a D b − P b ((Q a)ᵀ X b)
  have hi : ∀ a b, a ≠ b → X a = X a * D b - P b * ((Q a)ᵀ * X b) := by
    intro a b hab
    have h := congrArg (· * X b) (ho a b hab)
    simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc] at h
    rw [hD b, Matrix.mul_sub, Matrix.mul_one] at h
    calc X a = (X a - X a * D b + P b * ((Q a)ᵀ * X b)) + (X a * D b - P b * ((Q a)ᵀ * X b)) := by abel
      _ = X a * D b - P b * ((Q a)ᵀ * X b) := by rw [h, zero_add]
  -- (ii) P b = P b D' a − X a ((Y b)ᵀ P a)
  have hii : ∀ a b, a ≠ b → P b = P b * D' a - X a * ((Y b)ᵀ * P a) := by
    intro a b hab
    have h := congrArg (· * P a) (ho a b hab)
    simp only [Matrix.add_mul, Matrix.zero_mul, Matrix.mul_assoc] at h
    rw [hD' a, Matrix.mul_sub, Matrix.mul_one] at h
    calc P b = (X a * ((Y b)ᵀ * P a) + (P b - P b * D' a)) + (P b * D' a - X a * ((Y b)ᵀ * P a)) := by abel
      _ = P b * D' a - X a * ((Y b)ᵀ * P a) := by rw [h, zero_add]
  refine ⟨?_, ?_⟩
  · -- P y = R − X y G with rank R ≤ 3d
    have c1 := hii w y (Ne.symm hyw)
    have c2 := hi w u (Ne.symm huw)
    have c3 := hii y u hyu
    set A := (Y y)ᵀ * P w
    set A' := (Q w)ᵀ * X u
    set A'' := (Y u)ᵀ * P y
    have key : P y = (P y * D' w - (X w * D u) * A + (P u * D' y) * (A' * A)) - X y * (A'' * (A' * A)) := by
      calc P y = P y * D' w - X w * A := c1
        _ = P y * D' w - (X w * D u - P u * A') * A := by rw [← c2]
        _ = P y * D' w - (X w * D u - (P u * D' y - X y * A'') * A') * A := by rw [← c3]
        _ = _ := by simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
    have hN := bianca_rank_one_split (X y) (Y y)ᵀ (P y) (Q y)ᵀ _ _ (hd y) key
    have hR := bianca_rank_sub_add_le (P y * D' w) ((X w * D u) * A) ((P u * D' y) * (A' * A))
    have r1 : (P y * D' w).rank ≤ d := le_trans (Matrix.rank_mul_le_right _ _) (hD'r w)
    have r2 : ((X w * D u) * A).rank ≤ d :=
      le_trans (Matrix.rank_mul_le_left _ _) (le_trans (Matrix.rank_mul_le_right _ _) (hDr u))
    have r3 : ((P u * D' y) * (A' * A)).rank ≤ d :=
      le_trans (Matrix.rank_mul_le_left _ _) (le_trans (Matrix.rank_mul_le_right _ _) (hD'r y))
    omega
  · -- X y = R' − P y G' with rank R' ≤ 3d
    have c1 := hi y u hyu
    have c2 := hii w u (Ne.symm huw)
    have c3 := hi w y (Ne.symm hyw)
    set A1 := (Q y)ᵀ * X u
    set A2 := (Y u)ᵀ * P w
    set A3 := (Q w)ᵀ * X y
    have key : X y = (X y * D u - (P u * D' w) * A1 + (X w * D y) * (A2 * A1)) - P y * (A3 * (A2 * A1)) := by
      calc X y = X y * D u - P u * A1 := c1
        _ = X y * D u - (P u * D' w - X w * A2) * A1 := by rw [← c2]
        _ = X y * D u - (P u * D' w - (X w * D y - P y * A3) * A2) * A1 := by rw [← c3]
        _ = _ := by simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel
    have h1' : P y * (Q y)ᵀ + X y * (Y y)ᵀ = 1 := by rw [add_comm]; exact hd y
    have hN := bianca_rank_one_split (P y) (Q y)ᵀ (X y) (Y y)ᵀ _ _ h1' key
    have hR := bianca_rank_sub_add_le (X y * D u) ((P u * D' w) * A1) ((X w * D y) * (A2 * A1))
    have r1 : (X y * D u).rank ≤ d := le_trans (Matrix.rank_mul_le_right _ _) (hDr u)
    have r2 : ((P u * D' w) * A1).rank ≤ d :=
      le_trans (Matrix.rank_mul_le_left _ _) (le_trans (Matrix.rank_mul_le_right _ _) (hD'r w))
    have r3 : ((X w * D y) * (A2 * A1)).rank ≤ d :=
      le_trans (Matrix.rank_mul_le_left _ _) (le_trans (Matrix.rank_mul_le_right _ _) (hDr y))
    omega

/-- **minsum(N) ≥ 8N/7 for N ≥ 3 (I62 lower side, a constant factor past the slice bound).** If SWAP_N = B + C
over ℚ and N ≥ 3, then 8N ≤ 7 (rank B + OS(C)). With d = rank B + OS C − N, every slice's defect blocks have
rank ≤ d, and the 3-cycle of slices y → u → w → y gives N ≤ rank B + 3d and N ≤ OS C + 3d. -/
theorem bianca_minsum_ge_eight_sevenths (N : ℕ) (hN : 3 ≤ N) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) ℚ)
    (h : nadiaSwapMat N = B + C) : 8 * N ≤ 7 * (B.rank + (nadiaRealignMat C).rank) := by
  have hs := nadia_minsum_slice_bound N (by omega) B C h
  obtain ⟨U, V, hB⟩ := bianca_exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hC⟩ := bianca_exists_sum_vecMulVec_of_rank (nadiaRealignMat C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if u = y ∧ v = x then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = nadiaRealignMat C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin B.rank) ℚ := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin B.rank) ℚ := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin (nadiaRealignMat C).rank) ℚ := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin (nadiaRealignMat C).rank) ℚ := fun y => Matrix.of fun v l => Q l (y, v)
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
  have hd : ∀ y, X y * (Y y)ᵀ + PP y * (QQ y)ᵀ = 1 := fun y => by simpa using hslice y y
  have ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = 0 := fun y u hyu => by
    simpa [hyu] using hslice y u
  have hch := bianca_defect_chain (d := B.rank + (nadiaRealignMat C).rank - N) X Y PP QQ
    (fun z => 1 - (Y z)ᵀ * X z) (fun z => 1 - (QQ z)ᵀ * PP z)
    (fun z => by simp) (fun z => by simp)
    (fun z => (bianca_defect_rank (X z) (Y z) (PP z) (QQ z) (hd z)).1)
    (fun z => (bianca_defect_rank (X z) (Y z) (PP z) (QQ z) (hd z)).2)
    hd ho ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  omega
end

/-! ## unit minsum_ge_eight_sevenths_N_every_field -/
section

open Matrix

/-- **minsum(N) ≥ 8N/7 for N ≥ 3 (I62 lower side, a constant factor past the slice bound).** If SWAP_N = B + C
over F and N ≥ 3, then 8N ≤ 7 (rank B + OS(C)). With d = rank B + OS C − N, every slice's defect blocks have
rank ≤ d, and the 3-cycle of slices y → u → w → y gives N ≤ rank B + 3d and N ≤ OS C + 3d. -/
theorem bianca_minsumF_ge_eight_sevenths {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = B + C) : 8 * N ≤ 7 * (B.rank + (biancaRealignF C).rank) := by
  obtain ⟨U, V, hB⟩ := bianca_exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hC⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if x = v ∧ y = u then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = biancaRealignF C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin B.rank) F := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin B.rank) F := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin (biancaRealignF C).rank) F := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin (biancaRealignF C).rank) F := fun y => Matrix.of fun v l => Q l (y, v)
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
        simp [hxv]
    · have huy : ¬ u = y := fun h' => hyu h'.symm
      simp [hyu]
  have hd : ∀ y, X y * (Y y)ᵀ + PP y * (QQ y)ᵀ = 1 := fun y => by simpa using hslice y y
  have ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = 0 := fun y u hyu => by
    simpa [hyu] using hslice y u
  have hch := bianca_defect_chain (d := B.rank + (biancaRealignF C).rank - N) X Y PP QQ
    (fun z => 1 - (Y z)ᵀ * X z) (fun z => 1 - (QQ z)ᵀ * PP z)
    (fun z => by simp) (fun z => by simp)
    (fun z => (bianca_defect_rank (X z) (Y z) (PP z) (QQ z) (hd z)).1)
    (fun z => (bianca_defect_rank (X z) (Y z) (PP z) (QQ z) (hd z)).2)
    hd ho ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  omega
end

/-! ## unit minsum_ge_N_plus_two_every_field -/
section

open Matrix


/-- T331 step S (Nadia): from Bianca's slice identities with r + k = N + 1 and N ≥ 4, both widths are at least 2.
From (hd), rank X_y, rank Y_y ≥ N − k and rank P_y, rank Q_y ≥ N − r; from (ho), rank (X_a Y_bᵀ) ≤ k and
rank (P_b Q_aᵀ) ≤ r; Sylvester then gives 2(N − k) ≤ k + r and 2(N − r) ≤ r + k. -/
theorem nadia_slice_widths_ge_two {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 1)
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
    have h2 := bianca_matrix_rank_add_le (X y * (Y y)ᵀ) (P y * (Q y)ᵀ)
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
  have s1 := nadia_rank_add_rank_le_rank_mul (X a) (Y b)ᵀ
  have s2 := nadia_rank_add_rank_le_rank_mul (P b) (Q a)ᵀ
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


/-- T331 step 1 (Nadia): the d = 1 dichotomy. If X Yᵀ + P Qᵀ = 1 (N × N) with widths r + k = N + 1, then
Yᵀ X or Qᵀ P is invertible. The kernel of [X P] has dimension 1; singular vectors v of Yᵀ X and u of Qᵀ P give
the kernel vectors (v, −Qᵀ X v) and (−Yᵀ P u, u), whose proportionality forces Qᵀ X v = 0 and = −c u ≠ 0. -/
theorem nadia_slice_dichotomy {F : Type*} [Field F] {N r k : ℕ} (hrk : r + k = N + 1)
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F)
    (hd : X * Yᵀ + P * Qᵀ = 1) : (Yᵀ * X).det ≠ 0 ∨ (Qᵀ * P).det ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hcon.1
  obtain ⟨u, hu0, hu⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hcon.2
  set G : Matrix (Fin N) (Fin r ⊕ Fin k) F := Matrix.fromCols X P with hG
  -- rank G = N, so the kernel has dimension 1
  have hGH : G * (Matrix.fromCols Y Q)ᵀ = 1 := by
    rw [hG, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, hd]
  have hrank : G.rank = N := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height G
    · have := Matrix.rank_mul_le_left G (Matrix.fromCols Y Q)ᵀ
      rw [hGH] at this
      simpa [Matrix.rank_one] using this
  have hker : Module.finrank F (LinearMap.ker G.mulVecLin) = 1 := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    have hr : Module.finrank F (LinearMap.range G.mulVecLin) = N := hrank
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
    omega
  -- the two kernel vectors
  have hXv : X *ᵥ v = P *ᵥ ((Qᵀ * X) *ᵥ v) := by
    calc X *ᵥ v = (1 : Matrix (Fin N) (Fin N) F) *ᵥ (X *ᵥ v) := (Matrix.one_mulVec _).symm
      _ = (X * Yᵀ + P * Qᵀ) *ᵥ (X *ᵥ v) := by rw [hd]
      _ = X *ᵥ (Yᵀ *ᵥ (X *ᵥ v)) + P *ᵥ (Qᵀ *ᵥ (X *ᵥ v)) := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec (M := X) (N := Yᵀ),
            Matrix.mulVec_mulVec (M := P) (N := Qᵀ)]
      _ = P *ᵥ ((Qᵀ * X) *ᵥ v) := by
          rw [Matrix.mulVec_mulVec (M := Yᵀ) (N := X), hv, Matrix.mulVec_zero, zero_add,
            Matrix.mulVec_mulVec (M := Qᵀ) (N := X)]
  have hPu : P *ᵥ u = X *ᵥ ((Yᵀ * P) *ᵥ u) := by
    calc P *ᵥ u = (1 : Matrix (Fin N) (Fin N) F) *ᵥ (P *ᵥ u) := (Matrix.one_mulVec _).symm
      _ = (X * Yᵀ + P * Qᵀ) *ᵥ (P *ᵥ u) := by rw [hd]
      _ = X *ᵥ (Yᵀ *ᵥ (P *ᵥ u)) + P *ᵥ (Qᵀ *ᵥ (P *ᵥ u)) := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec (M := X) (N := Yᵀ),
            Matrix.mulVec_mulVec (M := P) (N := Qᵀ)]
      _ = X *ᵥ ((Yᵀ * P) *ᵥ u) := by
          rw [Matrix.mulVec_mulVec (M := Qᵀ) (N := P), hu, Matrix.mulVec_zero, add_zero,
            Matrix.mulVec_mulVec (M := Yᵀ) (N := P)]
  set w1 : Fin r ⊕ Fin k → F := Sum.elim v (-((Qᵀ * X) *ᵥ v)) with hw1
  set w2 : Fin r ⊕ Fin k → F := Sum.elim (-((Yᵀ * P) *ᵥ u)) u with hw2
  have hw1k : w1 ∈ LinearMap.ker G.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hw1, hG, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_neg,
      ← hXv, add_neg_cancel]
  have hw2k : w2 ∈ LinearMap.ker G.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hw2, hG, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_neg,
      ← hPu, neg_add_cancel]
  have hw2ne : (⟨w2, hw2k⟩ : LinearMap.ker G.mulVecLin) ≠ 0 := by
    intro h0
    apply hu0
    funext i
    have := congrFun (congrArg Subtype.val h0) (Sum.inr i)
    simpa [hw2] using this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw2ne).mp hker ⟨w1, hw1k⟩
  have hc' : c • w2 = w1 := congrArg Subtype.val hc
  have hvl : v = c • (-((Yᵀ * P) *ᵥ u)) := by
    funext i
    have := congrFun hc' (Sum.inl i)
    simpa [hw1, hw2] using this.symm
  have hur : -((Qᵀ * X) *ᵥ v) = c • u := by
    funext i
    have := congrFun hc' (Sum.inr i)
    simpa [hw1, hw2] using this.symm
  -- Qᵀ X v = Qᵀ (X v) = −c Qᵀ P u = 0
  have hzero : (Qᵀ * X) *ᵥ v = 0 := by
    have h1 : X *ᵥ v = -(c • (P *ᵥ u)) := by
      rw [hvl, Matrix.mulVec_smul, Matrix.mulVec_neg, ← hPu, smul_neg]
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hu, smul_zero,
      neg_zero]
  rw [hzero, neg_zero] at hur
  have hc0 : c = 0 := by
    by_contra hcne
    apply hu0
    have := congrArg (fun z => c⁻¹ • z) hur
    simpa [smul_smul, inv_mul_cancel₀ hcne] using this.symm
  apply hv0
  rw [hvl, hc0, zero_smul]

/-- T331 step 3 (Nadia): no mixed configuration. Column spaces CX z, CP z of the slices with CX z ⊔ CP z = ⊤,
slices of type A (CP b ≤ CX a for b ≠ a) or type B (CX a ≤ CP b for a ≠ b), and CX z ≠ ⊤. With N ≥ 3 all
slices have the same type. -/
theorem nadia_no_mixed_slices {F : Type*} [Field F] {N : ℕ} (hN : 3 ≤ N)
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
  -- a third slice c
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

/-- Running supremum of the first j column spaces. -/
def nadiaChainSup {F : Type*} [Field F] {N : ℕ} (U : Fin N → Submodule F (Fin N → F)) : ℕ → Submodule F (Fin N → F)
  | 0 => ⊥
  | j + 1 => nadiaChainSup U j ⊔ (if h : j < N then U ⟨j, h⟩ else ⊥)

/-- T331 step 4 (Nadia): the pure case. If U a ≤ V b for all a ≠ b, U z ⊔ V z = ⊤, V z ≠ ⊤, and U 0 has
dimension ≥ 2, then the running sums of the U's grow by at least 1 at every step, which gives more than N
dimensions inside F^N. -/
theorem nadia_pure_slices_false {F : Type*} [Field F] {N : ℕ} (hN : 1 ≤ N)
    (U V : Fin N → Submodule F (Fin N → F)) (hR : ∀ a b, a ≠ b → U a ≤ V b)
    (hR3 : ∀ z, U z ⊔ V z = ⊤) (hV : ∀ z, V z ≠ ⊤)
    (hdim : 2 ≤ Module.finrank F (U ⟨0, by omega⟩)) : False := by
  -- the running sum up to j lies below V b for every b ≥ j
  have hle : ∀ j, ∀ b : Fin N, j ≤ b.val → nadiaChainSup U j ≤ V b := by
    intro j
    induction j with
    | zero => intro b _; exact bot_le
    | succ j ih =>
      intro b hb
      simp only [nadiaChainSup]
      refine sup_le (ih b (by omega)) ?_
      split_ifs with h
      · exact hR ⟨j, h⟩ b (by intro e; rw [← e] at hb; simp at hb)
      · exact bot_le
  -- U z is not below V z
  have hnot : ∀ z, ¬ U z ≤ V z := by
    intro z h
    apply hV z
    rw [← hR3 z, sup_eq_right.mpr h]
  -- growth
  have hgrow : ∀ j, (h : j < N) → 1 ≤ j →
      Module.finrank F (nadiaChainSup U j) + 1 ≤ Module.finrank F (nadiaChainSup U (j + 1)) := by
    intro j h _
    have hlt : nadiaChainSup U j < nadiaChainSup U (j + 1) := by
      simp only [nadiaChainSup, dif_pos h]
      refine lt_of_le_of_ne le_sup_left ?_
      intro e
      apply hnot ⟨j, h⟩
      have : U ⟨j, h⟩ ≤ nadiaChainSup U j := by rw [e]; exact le_sup_right
      exact le_trans this (hle j ⟨j, h⟩ le_rfl)
    exact Submodule.finrank_lt_finrank_of_lt hlt
  have hone : 2 ≤ Module.finrank F (nadiaChainSup U 1) := by
    have e : nadiaChainSup U 1 = U ⟨0, by omega⟩ := by
      show nadiaChainSup U 0 ⊔ _ = _
      rw [dif_pos (by omega : 0 < N)]
      show ⊥ ⊔ _ = _
      exact bot_sup_eq _
    rw [e]
    exact hdim
  have hall : ∀ j, 1 ≤ j → j ≤ N → j + 1 ≤ Module.finrank F (nadiaChainSup U j) := by
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
  have hup : Module.finrank F (nadiaChainSup U N) ≤ N := by
    have := Submodule.finrank_le (nadiaChainSup U N)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  omega


/-- T331 (Nadia): the slice identities with widths r + k = N + 1 are impossible for N ≥ 4. -/
theorem nadia_slice_d1_false {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 1)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : False := by
  classical
  obtain ⟨hr2, hk2⟩ := nadia_slice_widths_ge_two hN hrk X Y P Q hd ho
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
    (nadia_slice_dichotomy hrk (X z) (Y z) (P z) (Q z) (hd z)).symm
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
  rcases nadia_no_mixed_slices (by omega) CX CP (fun z => ((Q z)ᵀ * P z).det ≠ 0)
      (fun z => ((Y z)ᵀ * X z).det ≠ 0) hAB hR3 hR1 hR2 hCX with hA | hB
  · refine nadia_pure_slices_false (by omega) CP CX (fun a b hab => hR1 b a (hA b) (Ne.symm hab))
      (fun z => by rw [sup_comm]; exact hR3 z) hCX ?_
    have hu : IsUnit ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA _))
    have h1 : ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩).rank = k := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Q ⟨0, by omega⟩)ᵀ (P ⟨0, by omega⟩)
    show 2 ≤ (P ⟨0, by omega⟩).rank
    omega
  · refine nadia_pure_slices_false (by omega) CX CP (fun a b hab => hR2 a b (hB b) hab) hR3 hCP ?_
    have hu : IsUnit ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hB _))
    have h1 : ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩).rank = r := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Y ⟨0, by omega⟩)ᵀ (X ⟨0, by omega⟩)
    show 2 ≤ (X ⟨0, by omega⟩).rank
    omega

/-- **T331 (Nadia; Operator X217 target (d)). minsum(N) ≥ N + 2 for N ≥ 4, over every field.** If SWAP_N = B + C over a
field F and N ≥ 4, then rank B + OS(C) ≥ N + 2; in particular P(4) ≥ 6. Bianca's 8N/7 floor gives rank B + OS C ≥ N + 1,
and her slice factorization (copied from minsum_ge_eight_sevenths_N_every_field, with credit) turns the case
rank B + OS C = N + 1 into slice identities that nadia_slice_d1_false refutes. -/
theorem nadia_minsumF_ge_N_add_two {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    N + 2 ≤ B.rank + (biancaRealignF C).rank := by
  have h87 := bianca_minsumF_ge_eight_sevenths N (by omega) B C h
  by_contra hlt
  push Not at hlt
  have heq : B.rank + (biancaRealignF C).rank = N + 1 := by omega
  obtain ⟨U, V, hB⟩ := bianca_exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hC⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if x = v ∧ y = u then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hC (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = biancaRealignF C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  let X : Fin N → Matrix (Fin N) (Fin B.rank) F := fun y => Matrix.of fun x i => U i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin B.rank) F := fun u => Matrix.of fun v i => V i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin (biancaRealignF C).rank) F := fun u => Matrix.of fun x l => P l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin (biancaRealignF C).rank) F := fun y => Matrix.of fun v l => Q l (y, v)
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
        simp [hxv]
    · have huy : ¬ u = y := fun h' => hyu h'.symm
      simp [hyu]
  have hd : ∀ y, X y * (Y y)ᵀ + PP y * (QQ y)ᵀ = 1 := fun y => by simpa using hslice y y
  have ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = 0 := fun y u hyu => by
    simpa [hyu] using hslice y u
  exact nadia_slice_d1_false hN heq X Y PP QQ hd ho

/-- Corollary (Operator X217 (d)): P(4) ≥ 6 over every field. -/
theorem nadia_minsumF_four_ge_six {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : biancaSwapF F (Fin 4) = B + C) : 6 ≤ B.rank + (biancaRealignF C).rank :=
  nadia_minsumF_ge_N_add_two 4 le_rfl B C h
end

/-! ## unit T381_W_width_drop_common_kernel_false -/
section
open Matrix
-- T381 brick W (Nadia's plan shared/T381_lean_plan_Nadia.md): a slice system of widths (r, k) with r + k = N + 2, N ≥ 4, in which
-- all Y_u share a kernel vector v ≠ 0 (or all X_a do), drops to widths (r - 1, k) and is refuted by nadia_slice_d1_false.
-- Column drop: v_i ≠ 0, Y_u = Y''_u Rᵀ with Y'' = the columns ≠ i and R(j, j') = [j = i.succAbove j'] - [j = i] v_{i.succAbove j'} / v_i.

/-- **Brick W (Y-version).** N ≥ 4, r + k = N + 2, hd/ho, and v ≠ 0 with Y_u v = 0 for all u: impossible (any field). -/
theorem daria_W {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 2)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (v : Fin r → F) (hv : v ≠ 0) (hY : ∀ u, Y u *ᵥ v = 0) : False := by
  obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv (funext hc)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := i.pos; omega⟩
  let Y2 : Fin N → Matrix (Fin N) (Fin r') F := fun u => Matrix.of fun z j' => Y u z (i.succAbove j')
  let R : Matrix (Fin (r' + 1)) (Fin r') F := Matrix.of fun j j' =>
    (if j = i.succAbove j' then 1 else 0) - (if j = i then v (i.succAbove j') / v i else 0)
  let X2 : Fin N → Matrix (Fin N) (Fin r') F := fun y => X y * R
  have hYR : ∀ u, Y u = Y2 u * Rᵀ := by
    intro u
    ext z j
    simp only [Y2, R, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
    rcases eq_or_ne j i with rfl | hj
    · have hs : ∀ j', ¬ (j = j.succAbove j') := fun j' h => Fin.succAbove_ne j j' h.symm
      simp only [hs, if_false, mul_zero, Finset.sum_const_zero, if_true, zero_sub]
      have h0 := congrFun (hY u) z
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h0
      rw [Fin.sum_univ_succAbove _ j] at h0
      have hsum : ∑ j', Y u z (j.succAbove j') * (v (j.succAbove j') / v j) =
          (∑ j', Y u z (j.succAbove j') * v (j.succAbove j')) / v j := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j' _ => ?_
        rw [mul_div_assoc]
      have key : ∑ j', Y u z (j.succAbove j') * v (j.succAbove j') = -(Y u z j * v j) := by
        linear_combination h0
      rw [hsum, key, neg_div, neg_neg, mul_div_assoc, div_self hvi, mul_one]
    · obtain ⟨j0, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [hj]
  have hXY : ∀ y u, X2 y * (Y2 u)ᵀ = X y * (Y u)ᵀ := by
    intro y u
    rw [hYR u, Matrix.transpose_mul, Matrix.transpose_transpose]
    show X y * R * (Y2 u)ᵀ = X y * (R * (Y2 u)ᵀ)
    rw [Matrix.mul_assoc]
  exact nadia_slice_d1_false hN (by omega) X2 Y2 P Q (fun y => by rw [hXY]; exact hd y)
    (fun y u h => by rw [hXY]; exact ho y u h)

/-- The symmetry σ of the slice system: (X, Y, P, Q) ↦ (Y, X, Q, P) (transpose of hd/ho). -/
theorem daria_slice_sigma {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :
    (∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1) ∧ (∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0) := by
  refine ⟨fun y => ?_, fun y u h => ?_⟩
  · have h1 := congrArg Matrix.transpose (hd y)
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h1
  · have h1 := congrArg Matrix.transpose (ho u y (Ne.symm h))
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h1

/-- **Brick W (X-version)**, by σ: all X_a sharing a kernel vector v ≠ 0 is impossible. -/
theorem daria_W_X {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hrk : r + k = N + 2)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (v : Fin r → F) (hv : v ≠ 0) (hX : ∀ a, X a *ᵥ v = 0) : False := by
  obtain ⟨hd', ho'⟩ := daria_slice_sigma X Y P Q hd ho
  exact daria_W hN hrk Y X Q P hd' ho' v hv hX
end

/-! ## unit rank_le_one_outer_product_and_dual_vector -/
section
/-- A matrix of rank ≤ 1 is an outer product u rᵀ. -/
theorem xenia_eq_vecMulVec_of_rank_le_one {F m n : Type*} [Field F] [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n F) (h : M.rank ≤ 1) : ∃ (u : m → F) (r : n → F), M = Matrix.vecMulVec u r := by
  classical
  have h' : Module.finrank F (LinearMap.range M.mulVecLin) ≤ 1 := h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h'
  have hc : ∀ j : n, ∃ c : F, c • (v : m → F) = M.mulVec (Pi.single j 1) := by
    intro j
    obtain ⟨c, hc⟩ := hv ⟨M.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose c hc using hc
  refine ⟨v, c, ?_⟩
  ext i j
  have hij := congrFun (hc j) i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hij
  rw [Matrix.vecMulVec_apply, ← hij, mul_comm]

theorem xenia_vecMulVec_mulVec {F m n : Type*} [Field F] [Fintype n] (u : m → F) (r : n → F) (x : n → F) :
    (Matrix.vecMulVec u r).mulVec x = (dotProduct r x) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

/-- Two independent rows admit a dual pair: x with r1·x = 1, r2·x = 0. -/
theorem xenia_dual_vector {F n : Type*} [Field F] [Fintype n] (r1 r2 : n → F)
    (hr : LinearIndependent F ![r1, r2]) : ∃ x : n → F, dotProduct r1 x = 1 ∧ dotProduct r2 x = 0 := by
  classical
  let A : Matrix (Fin 2) n F := Matrix.of ![r1, r2]
  have hrank : A.rank = 2 := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Set.range A.row = Set.range ![r1, r2] := by
      congr 1
    rw [this, finrank_span_eq_card hr, Fintype.card_fin]
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank F (LinearMap.range A.mulVecLin) = A.rank from rfl, hrank]
    simp
  have hx : (![1, 0] : Fin 2 → F) ∈ LinearMap.range A.mulVecLin := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, ?_, ?_⟩
  · have := congrFun hx 0
    simpa [A, Matrix.mulVec] using this
  · have := congrFun hx 1
    simpa [A, Matrix.mulVec] using this
end

/-! ## unit T415_hii_H0_V1_rank_one_from_bilinear -/
section

/-- **(H0) for hii (Nadia's f = q = 2 route).** If (yᵀAx)(l'·x) = (yᵀA'x)(l·x) for all x, y, with l, l' independent,
then A kills the hyperplane l⊥, hence rank A ≤ 1. -/
theorem xenia_H0 {K : Type*} [Field K] (A A' : Matrix (Fin 4) (Fin 4) K) (l l' : Fin 4 → K)
    (hl : LinearIndependent K ![l, l'])
    (h : ∀ x y : Fin 4 → K, (dotProduct y (A.mulVec x)) * (dotProduct l' x) =
      (dotProduct y (A'.mulVec x)) * (dotProduct l x)) :
    (∀ x, dotProduct l x = 0 → A.mulVec x = 0) ∧ A.rank ≤ 1 := by
  classical
  -- pointwise form: (l'.x) Ax = (l.x) A'x
  have hp : ∀ x : Fin 4 → K, (dotProduct l' x) • A.mulVec x = (dotProduct l x) • A'.mulVec x := by
    intro x; funext i
    have := h x (Pi.single i 1)
    simp only [Pi.smul_apply, smul_eq_mul]
    simpa [dotProduct_single, mul_comm] using this
  -- a vector z with l.z = 0, l'.z = 1
  have hl' : LinearIndependent K ![l', l] := by
    rw [LinearIndependent.pair_iff] at hl ⊢
    intro s t hst; have := hl t s (by rw [add_comm]; exact hst); exact ⟨this.2, this.1⟩
  obtain ⟨z, hz1, hz0⟩ := xenia_dual_vector l' l hl'
  have hker1 : ∀ x, dotProduct l x = 0 → dotProduct l' x ≠ 0 → A.mulVec x = 0 := by
    intro x h0 h1
    have := hp x
    rw [h0, zero_smul] at this
    exact (smul_eq_zero.1 this).resolve_left h1
  have hker : ∀ x, dotProduct l x = 0 → A.mulVec x = 0 := by
    intro x h0
    by_cases h1 : dotProduct l' x = 0
    · have e1 : A.mulVec (x + z) = 0 := hker1 (x + z) (by rw [dotProduct_add, h0, hz0, add_zero])
        (by rw [dotProduct_add, h1, hz1, zero_add]; exact one_ne_zero)
      have e2 : A.mulVec z = 0 := hker1 z hz0 (by rw [hz1]; exact one_ne_zero)
      rw [Matrix.mulVec_add, e2, add_zero] at e1
      exact e1
    · exact hker1 x h0 h1
  refine ⟨hker, ?_⟩
  -- l ≠ 0, so pick w with l.w ≠ 0; then range A ⊆ span {A w}
  have hl0 : l ≠ 0 := by
    intro h0; have := hl.ne_zero 0; simp [h0] at this
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, dotProduct l w ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hl0; funext i; simpa [dotProduct_single] using hc (Pi.single i 1)
  have hrange : LinearMap.range A.mulVecLin ≤ Submodule.span K {A.mulVec w} := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨dotProduct l x / dotProduct l w, ?_⟩
    have hx : dotProduct l (x - (dotProduct l x / dotProduct l w) • w) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hw, sub_self]
    have := hker _ hx
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at this
    simp only [Matrix.mulVecLin_apply]
    exact this.symm
  calc A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := rfl
    _ ≤ Module.finrank K (Submodule.span K {A.mulVec w}) := Submodule.finrank_mono hrange
    _ ≤ 1 := by
      have := finrank_span_le_card (R := K) ({A.mulVec w} : Set (Fin 4 → K))
      simpa using this

/-- **(V1) for hii.** If (l·x) F(x) v = 0 for all x, with F(x) = Σ_s x_s F_s and l ≠ 0, then F(x) v = 0 for all x. -/
theorem xenia_V1 {K : Type*} [Field K] {d : ℕ} {m n : Type*} [Fintype m] [Fintype n]
    (Fs : Fin d → Matrix m n K) (v : n → K) (l : Fin d → K) (hl : l ≠ 0)
    (h : ∀ x : Fin d → K, (dotProduct l x) • (∑ s, x s • Fs s).mulVec v = 0) :
    ∀ x : Fin d → K, (∑ s, x s • Fs s).mulVec v = 0 := by
  classical
  have hadd : ∀ x y : Fin d → K, (∑ s, (x + y) s • Fs s).mulVec v =
      (∑ s, x s • Fs s).mulVec v + (∑ s, y s • Fs s).mulVec v := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, Matrix.add_mulVec]
  have hne : ∀ x, dotProduct l x ≠ 0 → (∑ s, x s • Fs s).mulVec v = 0 := fun x hx =>
    (smul_eq_zero.1 (h x)).resolve_left hx
  obtain ⟨w, hw⟩ : ∃ w : Fin d → K, dotProduct l w ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hl; funext i; simpa [dotProduct_single] using hc (Pi.single i 1)
  intro x
  by_cases hx : dotProduct l x = 0
  · have e1 := hne (x + w) (by rw [dotProduct_add, hx, zero_add]; exact hw)
    rw [hadd, hne w hw, add_zero] at e1
    exact e1
  · exact hne x hx
end

/-! ## unit T381_C2_all_two_case_false -/
section
open Matrix

/-- C2 entry identity (Nadia): ((∑ y_b Y_b)ᵀ (∑ x_a X_a))[s,u] = y ⬝ (G_s F_u) x with G_s[b,j] = Y_b[j,s], F_u[j,a] = X_a[j,u]. -/
theorem nadia_C2_entry (X Y : Fin 4 → Matrix (Fin 4) (Fin 3) ℚ) (x y : Fin 4 → ℚ) (s u : Fin 3) :
    ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u =
      y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u)) *ᵥ x) := by
  have lhs : ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u =
      ∑ j, ∑ b, ∑ a, (y b * Y b j s) * (x a * X a j u) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul_sum]
  have rhs : y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u)) *ᵥ x) =
      ∑ b, ∑ a, ∑ j, y b * (Y b j s * X a j u * x a) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [lhs, rhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- C2 step (b) (Nadia): in the all-≤2 case, Fx(x) (Y(y)ᵀ Fx(x)) = (x·y) Fx(x). -/
theorem nadia_C2_FYF (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) ℚ)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → ℚ, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → ℚ, (∑ a, x a • Q a).rank ≤ 2)
    (x y : Fin 4 → ℚ) :
    (∑ a, x a • X a) * ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) = (∑ a, x a * y a) • (∑ a, x a • X a) := by
  have e := congrArg (· * (∑ a, x a • X a)) (daria_slice_eq1 X Y P Q hd ho x y)
  have hQF := nadia_C2_QF_zero X Y P Q hd ho hF hQ x
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hQF, Matrix.mul_zero, add_zero] at e
  exact e

/-- Two vectors in the kernel of a rank-2 4 × 3 matrix are parallel. -/
theorem nadia_ker_one_parallel {K : Type*} [Field K] (M : Matrix (Fin 4) (Fin 3) K) (hM : M.rank = 2)
    (c v : Fin 3 → K) (hc : M *ᵥ c = 0) (hv : M *ᵥ v = 0) (s s' : Fin 3) : c s * v s' = c s' * v s := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 : M.rank = Module.finrank K (LinearMap.range M.mulVecLin) := rfl
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  have hk : Module.finrank K (LinearMap.ker M.mulVecLin) = 1 := by omega
  by_cases hv0 : v = 0
  · subst hv0; simp
  have hvk : v ∈ LinearMap.ker M.mulVecLin := hv
  have hck : c ∈ LinearMap.ker M.mulVecLin := hc
  have hne : (⟨v, hvk⟩ : LinearMap.ker M.mulVecLin) ≠ 0 := by
    intro h0; apply hv0; exact congrArg Subtype.val h0
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hk ⟨c, hck⟩
  have ht' : t • v = c := congrArg Subtype.val ht
  rw [← ht']
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- A dependent pair whose first vector is nonzero: the second is a multiple of the first. -/
theorem nadia_pair_dep {K : Type*} [Field K] (u w : Fin 4 → K) (hu : u ≠ 0) (h : ¬ LinearIndependent K ![u, w]) :
    ∃ c : K, w = c • u := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hb : b ≠ 0 := by
    intro hb0
    have ha : a • u = 0 := by simpa [hb0] using hab
    rcases smul_eq_zero.mp ha with h0 | h0
    · exact hne h0 hb0
    · exact hu h0
  refine ⟨-(a / b), ?_⟩
  have e : b • w = -(a • u) := eq_neg_of_add_eq_zero_right hab
  calc w = b⁻¹ • (b • w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = -(a / b) • u := by rw [e, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

/-- If no two rows of L are independent, rank L ≤ 1. -/
theorem nadia_rank_le_one_of_rows_dep {K : Type*} [Field K] (L : Matrix (Fin 3) (Fin 4) K)
    (h : ∀ s1 s2, ¬ LinearIndependent K ![L s1, L s2]) : L.rank ≤ 1 := by
  classical
  by_cases hL : ∀ s, L s = 0
  · have : L = 0 := by ext s a; simp [hL s]
    rw [this, Matrix.rank_zero]; omega
  push Not at hL
  obtain ⟨s0, hs0⟩ := hL
  rw [Matrix.rank_eq_finrank_span_row]
  have hle : Submodule.span K (Set.range L) ≤ Submodule.span K {L s0} := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨c, hc⟩ := nadia_pair_dep (L s0) (L s) hs0 (h s0 s)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨c, hc.symm⟩
  have := Submodule.finrank_mono hle
  rw [finrank_span_singleton hs0] at this
  exact this

/-- T381 brick C2 (Nadia): the all-≤2 case of hii is impossible, over Q, pointwise form. -/
theorem nadia_T381_C2 (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) ℚ)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → ℚ, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → ℚ, (∑ a, x a • Q a).rank ≤ 2) : False := by
  classical
  -- A s u as an explicit matrix
  have hAform : ∀ (s u : Fin 3) (x y : Fin 4 → ℚ),
      y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) ℚ) else 0)) *ᵥ x) =
      ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u - (if s = u then ∑ a, x a * y a else 0) := by
    intro s u x y
    rw [nadia_C2_entry X Y x y s u, Matrix.sub_mulVec, dotProduct_sub]
    split_ifs with h
    · rw [Matrix.one_mulVec]
      congr 1
      simp only [dotProduct]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    · rw [Matrix.zero_mulVec, dotProduct_zero]
  -- the columns of M(x,y) are in ker Fx(x)
  have hcol : ∀ (u : Fin 3) (x y : Fin 4 → ℚ), (∑ a, x a • X a) *ᵥ (fun s => y ⬝ᵥ
      ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) ℚ) else 0)) *ᵥ x)) = 0 := by
    intro u x y
    have hv : (fun s => y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) ℚ) else 0)) *ᵥ x)) =
        ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) *ᵥ Pi.single u 1 - (∑ a, x a * y a) • Pi.single u 1 := by
      funext s
      rw [hAform]
      by_cases h : s = u
      · subst h; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      · simp [h, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_mulVec, nadia_C2_FYF X Y P Q hd ho hF hQ x y, Matrix.mulVec_smul,
      Matrix.smul_mulVec, sub_self]
  -- the matrices A s u, the rank of Fx(x) at x ≠ 0, and the row matrices L y0 u
  set A : Fin 3 → Fin 3 → Matrix (Fin 4) (Fin 4) ℚ := fun s u =>
    Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
      (if s = u then (1 : Matrix (Fin 4) (Fin 4) ℚ) else 0) with hA
  have hrank2 : ∀ x : Fin 4 → ℚ, x ≠ 0 → (∑ a, x a • X a).rank = 2 := by
    intro x hx
    have h1 := (lena_eq1_rank_split X Y P Q hd ho x (nadia_sumsq_ne_zero x hx)).1
    have h2 := hF x
    have h3 := hQ x
    omega
  set L : (Fin 4 → ℚ) → Fin 3 → Matrix (Fin 3) (Fin 4) ℚ :=
    fun y0 u => Matrix.of (fun s a => ∑ b, y0 b * A s u b a) with hL
  have hLx : ∀ y0 u x, L y0 u *ᵥ x = fun s => y0 ⬝ᵥ (A s u *ᵥ x) := by
    intro y0 u x
    funext s
    simp only [hL, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by ring))
  have hLker : ∀ y0 u x, (∑ a, x a • X a) *ᵥ (L y0 u *ᵥ x) = 0 := by
    intro y0 u x
    rw [hLx]
    exact hcol u x y0
  -- the finish needs rank (A s u) ≤ 1 for all s, u
  suffices hfin : ∀ s u, (A s u).rank ≤ 1 by
    exact nadia_T381_offdiag_rank_one_false (fun s => Matrix.of (fun b j => Y b j s))
      (fun u => Matrix.of (fun j a => X a j u)) hfin
  by_cases hall : ∀ y0 u, L y0 u = 0
  · intro s u
    have hz : A s u = 0 := by
      ext b a
      have := congrFun (congrFun (hall (Pi.single b 1) u) s) a
      simpa [hL, Pi.single_apply] using this
    rw [hz, Matrix.rank_zero]; omega
  push Not at hall
  obtain ⟨y0, u0, hL0⟩ := hall
  set L0 := L y0 u0 with hL0def
  by_cases hpair : ∃ s1 s2, LinearIndependent ℚ ![L0 s1, L0 s2]
  swap
  · -- rank L0 ≤ 1: a common kernel vector of all X_a, killed by daria_W_X
    exfalso
    push Not at hpair
    have hr1 := nadia_rank_le_one_of_rows_dep L0 hpair
    obtain ⟨w, r, hwr⟩ := xenia_eq_vecMulVec_of_rank_le_one L0 hr1
    have hw : w ≠ 0 := by
      intro h0; apply hL0; rw [hwr, h0]; ext i j; simp [Matrix.vecMulVec_apply]
    have hr : r ≠ 0 := by
      intro h0; apply hL0; rw [hwr, h0]; ext i j; simp [Matrix.vecMulVec_apply]
    have hV : ∀ x : Fin 4 → ℚ, (r ⬝ᵥ x) • (∑ a, x a • X a) *ᵥ w = 0 := by
      intro x
      have := hLker y0 u0 x
      have hwr' : L y0 u0 = Matrix.vecMulVec w r := hwr
      rw [hwr', xenia_vecMulVec_mulVec, Matrix.mulVec_smul] at this
      exact this
    have hall0 := xenia_V1 X w r hr hV
    apply daria_W_X (N := 4) (r := 3) (k := 3) (by norm_num) (by norm_num) X Y P Q hd ho w hw
    intro a
    have := hall0 (Pi.single a 1)
    simpa [Pi.single_apply] using this
  obtain ⟨s1, s2, hI⟩ := hpair
  -- parallel identity
  have hpar : ∀ s s' u (x y : Fin 4 → ℚ),
      (y ⬝ᵥ (A s u *ᵥ x)) * (L0 s' ⬝ᵥ x) = (y ⬝ᵥ (A s' u *ᵥ x)) * (L0 s ⬝ᵥ x) := by
    intro s s' u x y
    by_cases hx : x = 0
    · subst hx; simp
    have hk := nadia_ker_one_parallel (∑ a, x a • X a) (hrank2 x hx) (fun t => y ⬝ᵥ (A t u *ᵥ x))
      (L0 *ᵥ x) (hcol u x y) (hLker y0 u0 x) s s'
    simpa [Matrix.mulVec] using hk
  have hne1 : L0 s1 ≠ 0 := hI.ne_zero 0
  have hne2 : L0 s2 ≠ 0 := hI.ne_zero 1
  intro s u
  by_cases hs0 : L0 s = 0
  · refine (xenia_H0 (A s u) 0 (L0 s2) (L0 s1) (LinearIndependent.pair_symm_iff.mp hI) ?_).2
    intro x y
    have := hpar s s1 u x y
    rw [hs0, zero_dotProduct, mul_zero] at this
    rw [this, Matrix.zero_mulVec, dotProduct_zero, zero_mul]
  by_cases hi1 : LinearIndependent ℚ ![L0 s, L0 s1]
  · exact (xenia_H0 (A s u) (A s1 u) (L0 s) (L0 s1) hi1 (fun x y => hpar s s1 u x y)).2
  have hi2 : LinearIndependent ℚ ![L0 s, L0 s2] := by
    by_contra hi2
    obtain ⟨c1, hc1⟩ := nadia_pair_dep (L0 s) (L0 s1) hs0 hi1
    obtain ⟨c2, hc2⟩ := nadia_pair_dep (L0 s) (L0 s2) hs0 hi2
    have hc10 : c1 ≠ 0 := by intro h0; apply hne1; rw [hc1, h0, zero_smul]
    rw [LinearIndependent.pair_iff] at hI
    have := hI c2 (-c1) (by rw [hc1, hc2, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, add_neg_cancel])
    exact hc10 (neg_eq_zero.mp this.2)
  exact (xenia_H0 (A s u) (A s2 u) (L0 s) (L0 s2) hi2 (fun x y => hpar s s2 u x y)).2
end

/-! ## unit T414_hii_G1_generic_vector_facts -/
section
open Matrix

/-- **G1 (o) (T414, Lena)**: at the generic point xg u = X u of K = FractionRing (MvPolynomial (Fin n) F), evaluation
`aeval xg` is the structure map MvPolynomial → K. -/
theorem lena_G1_aeval_eq {F : Type*} [Field F] {n : ℕ} (p : MvPolynomial (Fin n) F) :
    MvPolynomial.aeval (fun u => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
      (MvPolynomial.X u)) p = algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) p := by
  have e : MvPolynomial.aeval (fun u => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
      (MvPolynomial.X u)) = IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) := by
    apply MvPolynomial.algHom_ext
    intro u
    simp [IsScalarTower.toAlgHom_apply]
  rw [e, IsScalarTower.toAlgHom_apply]

/-- **G1 (iii) (T414, Lena)**: specialization. A polynomial that vanishes at the generic point vanishes everywhere. -/
theorem lena_G1_spec {F : Type*} [Field F] {n : ℕ} (p : MvPolynomial (Fin n) F)
    (h : MvPolynomial.aeval (fun u => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
      (MvPolynomial.X u)) p = 0) (x0 : Fin n → F) : MvPolynomial.eval x0 p = 0 := by
  rw [lena_G1_aeval_eq] at h
  have hp : p = 0 := by
    have hinj := IsFractionRing.injective (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
    exact hinj (by rw [h, map_zero])
  rw [hp, map_zero]

/-- **G1 (i) (T414, Lena)**: the generic vector satisfies no nonzero linear relation with coefficients in F. -/
theorem lena_G1_lin {F : Type*} [Field F] {n : ℕ} (l : Fin n → F)
    (h : ∑ u, algebraMap F (FractionRing (MvPolynomial (Fin n) F)) (l u) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X u) = 0) : l = 0 := by
  classical
  have e : ∀ u, algebraMap F (FractionRing (MvPolynomial (Fin n) F)) (l u) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X u) =
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
        (MvPolynomial.C (l u) * MvPolynomial.X u) := by
    intro u
    rw [map_mul, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)),
      MvPolynomial.algebraMap_eq]
  simp only [e, ← map_sum] at h
  have hp : (∑ u, MvPolynomial.C (l u) * MvPolynomial.X u : MvPolynomial (Fin n) F) = 0 := by
    have hinj := IsFractionRing.injective (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
    exact hinj (by rw [h, map_zero])
  funext u
  have := congrArg (MvPolynomial.eval (Pi.single u 1)) hp
  simpa [MvPolynomial.eval_X, MvPolynomial.eval_C, Pi.single_apply] using this

/-- Pointwise eigen-lemma: if A x is parallel to x for every x (in the 2x2-minor form), then A is scalar. -/
theorem lena_scalar_of_parallel {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (hpt : ∀ (x0 : Fin n → F) i k, (A *ᵥ x0) i * x0 k = (A *ᵥ x0) k * x0 i) :
    ∃ a : F, A = a • (1 : Matrix (Fin n) (Fin n) F) := by
  classical
  have hoff : ∀ i j, i ≠ j → A i j = 0 := by
    intro i j hij
    have h := hpt (Pi.single j 1) i j
    simpa [Matrix.mulVec_single, Pi.single_apply, hij] using h
  have hdiag : ∀ i j, A i i = A j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h := hpt (Pi.single i 1 + Pi.single j 1) i j
      have hji : j ≠ i := fun e => hij e.symm
      have hv : ∀ k, (A *ᵥ (Pi.single i 1 + Pi.single j 1)) k = A k i + A k j := by
        intro k
        simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_add, Finset.sum_add_distrib]
      rw [hv, hv] at h
      simp only [Pi.add_apply, Pi.single_apply, hij, hji, if_true, if_false, add_zero, zero_add, mul_one] at h
      rw [hoff i j hij, hoff j i hji] at h
      simpa using h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, by ext i; exact i.elim0⟩
  · refine ⟨A ⟨0, hn⟩ ⟨0, hn⟩, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag i ⟨0, hn⟩]
    · simp [hij, hoff i j hij]

/-- **G1 (ii) (T414, Lena)**: a matrix over F with the generic vector xg as an eigenvector (eigenvalue in K) is scalar. -/
theorem lena_G1_scalar {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (lam : FractionRing (MvPolynomial (Fin n) F))
    (h : (A.map (algebraMap F (FractionRing (MvPolynomial (Fin n) F)))) *ᵥ
      (fun u => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X u)) =
      lam • (fun u => algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X u))) :
    ∃ a : F, A = a • (1 : Matrix (Fin n) (Fin n) F) := by
  classical
  apply lena_scalar_of_parallel
  intro x0 i k
  have hi := congrFun h i
  have hk := congrFun h k
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hi hk
  have e : ∀ i', (∑ j, algebraMap F (FractionRing (MvPolynomial (Fin n) F)) (A i' j) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X j)) =
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F))
        (∑ j, MvPolynomial.C (A i' j) * MvPolynomial.X j) := by
    intro i'
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)),
      MvPolynomial.algebraMap_eq]
  have hK : (∑ j, algebraMap F (FractionRing (MvPolynomial (Fin n) F)) (A i j) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X j)) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X k) =
      (∑ j, algebraMap F (FractionRing (MvPolynomial (Fin n) F)) (A k j) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X j)) *
      algebraMap (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) (MvPolynomial.X i) := by
    rw [hi, hk]; ring
  rw [e i, e k, ← map_mul, ← map_mul] at hK
  have hp := IsFractionRing.injective (MvPolynomial (Fin n) F) (FractionRing (MvPolynomial (Fin n) F)) hK
  have := congrArg (MvPolynomial.eval x0) hp
  simpa [Matrix.mulVec, dotProduct, MvPolynomial.eval_X, MvPolynomial.eval_C] using this
end

/-! ## unit T453_rank_transfer_every_field -/
section
open Matrix

/-- A 4 × 3 matrix of rank 3 over any field has a left inverse. -/
theorem nadia_left_inverse_of_rank_three {F : Type*} [Field F] (M : Matrix (Fin 4) (Fin 3) F) (h : 3 ≤ M.rank) :
    ∃ N : Matrix (Fin 3) (Fin 4) F, N * M = 1 := by
  classical
  have hinj : Function.Injective M.mulVecLin := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h2 : M.rank = Module.finrank F (LinearMap.range M.mulVecLin) := rfl
    have h3 : M.rank ≤ 3 := by simpa using Matrix.rank_le_card_width M
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have h4 : Module.finrank F (LinearMap.ker M.mulVecLin) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp h4
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ M.mulVecLin) = LinearMap.toMatrix' (LinearMap.id : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := by
    rw [hg]
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have hM : LinearMap.toMatrix' M.mulVecLin = M := LinearMap.toMatrix'_toLin' M
  rw [hM] at this
  exact this

/-- Every-field transfer (Nadia, T453): rank ≤ 2 at the generic point of FractionRing (MvPolynomial (Fin 4) F)
gives rank ≤ 2 at every point of F⁴. Via det (N · Fx) for every constant N and a left inverse. -/
theorem nadia_rank_transfer_le_two_any {F : Type*} [Field F] (X : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (h : (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2)
    (x0 : Fin 4 → F) : (∑ a, x0 a • X a).rank ≤ 2 := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨N, hN⟩ := nadia_left_inverse_of_rank_three _ (by omega : 3 ≤ (∑ a, x0 a • X a).rank)
  set xg : Fin 4 → FractionRing (MvPolynomial (Fin 4) F) :=
    fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u) with hxg
  set Fp : Matrix (Fin 4) (Fin 3) (MvPolynomial (Fin 4) F) :=
    ∑ a, (MvPolynomial.X a : MvPolynomial (Fin 4) F) • (X a).map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) with hFp
  set FK := ∑ a, xg a • (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) with hFK
  set p : MvPolynomial (Fin 4) F := (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) * Fp).det with hp
  set g : MvPolynomial (Fin 4) F →+* FractionRing (MvPolynomial (Fin 4) F) :=
    (MvPolynomial.aeval (R := F) xg).toRingHom with hg
  have hmapK : Fp.map g = FK := by
    ext i j
    simp [Fp, FK, g, Matrix.sum_apply, Matrix.map_apply, map_sum, MvPolynomial.aeval_X]
  have hmap0 : Fp.map (MvPolynomial.eval x0) = ∑ a, x0 a • X a := by
    ext i j
    simp [Fp, Matrix.sum_apply, Matrix.map_apply, map_sum]
  have hNK : (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F)).map g = N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) := by
    ext i j
    simp [g, Matrix.map_apply]
  have hN0 : (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F)).map (MvPolynomial.eval x0) = N := by
    ext i j
    simp [Matrix.map_apply]
  have hK0 : (N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) * FK).det = 0 := by
    by_contra hne
    have hu : IsUnit (N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) * FK) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
    have h3 : (N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) * FK).rank = 3 := by
      rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
    have h4 := Matrix.rank_mul_le_right (N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))) FK
    have h5 : FK.rank ≤ 2 := h
    omega
  have hpz : MvPolynomial.aeval xg p = 0 := by
    have e : g p = 0 := by
      have h1 : g p = (g.mapMatrix (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) * Fp)).det := RingHom.map_det g _
      have hprod : g.mapMatrix (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) * Fp) =
          N.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) * FK := by
        ext i j
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [map_mul, ← hmapK]
        simp [g, Matrix.map_apply]
      rw [h1, hprod, hK0]
    simpa [g] using e
  have he := lena_G1_spec p hpz x0
  have h2 : (MvPolynomial.eval x0) p = ((MvPolynomial.eval x0).mapMatrix (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) * Fp)).det :=
    RingHom.map_det _ _
  have hprod0 : (MvPolynomial.eval x0).mapMatrix (N.map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) * Fp) = N * ∑ a, x0 a • X a := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, ← hmap0]
    simp [Matrix.map_apply]
  rw [h2, hprod0, hN, Matrix.det_one] at he
  exact one_ne_zero he
end

/-! ## unit T381_slice_system_base_change -/
section
open Matrix
-- T381 helper for Nadia's route (Q280, 02:25): apply the slice lemmas over K = FractionRing (MvPolynomial (Fin 4) ℚ).
-- A slice system hd/ho over F stays a slice system after any ring hom f : F →+* K (e.g. algebraMap ℚ K), entrywise.

/-- One slice entry commutes with `map f`. -/
theorem daria_slice_entry_map {F K : Type*} [Field F] [Field K] (f : F →+* K) {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F) (y u : Fin N) :
    (X y).map f * ((Y u).map f)ᵀ + (P u).map f * ((Q y).map f)ᵀ = (X y * (Y u)ᵀ + P u * (Q y)ᵀ).map f := by
  rw [Matrix.map_add f (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]

/-- **Base change of a slice system**: hd/ho over F give hd/ho for the mapped slices over K. -/
theorem daria_slice_map {F K : Type*} [Field F] [Field K] (f : F →+* K) {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :
    (∀ y, (X y).map f * ((Y y).map f)ᵀ + (P y).map f * ((Q y).map f)ᵀ = 1) ∧
      (∀ y u, y ≠ u → (X y).map f * ((Y u).map f)ᵀ + (P u).map f * ((Q y).map f)ᵀ = 0) := by
  refine ⟨fun y => ?_, fun y u h => ?_⟩
  · rw [daria_slice_entry_map f X Y P Q y y, hd y, Matrix.map_one f (map_zero f) (map_one f)]
  · rw [daria_slice_entry_map f X Y P Q y u, ho y u h, Matrix.map_zero f (map_zero f)]

/-- Non-vacuity (D14): ℚ → ℝ base change of the N = 1 system X = Y = 1, P = Q = 0. -/
theorem daria_slice_map_witness :
    ∀ _y : Fin 1, ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ)) *
      ((1 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))ᵀ +
      ((0 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ)) *
      ((0 : Matrix (Fin 1) (Fin 1) ℚ).map (algebraMap ℚ ℝ))ᵀ = 1 :=
  (daria_slice_map (algebraMap ℚ ℝ) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℚ)) (fun _ => 1) (fun _ => 0) (fun _ => 0)
    (fun _ => by simp) (fun y u h => absurd (Subsingleton.elim y u) h)).1
end

/-! ## unit T381_C3_case_f3_image_trick -/
section
open Matrix

/-- T381 brick C3 (Nadia): the case f = 3 of hii, the image trick, over a field map φ : F →+* K and a vector xg in K⁴.
Hypotheses: (g1) xg satisfies no nonzero F-linear relation; (g2) an F-matrix with xg as eigenvector is scalar;
(hW) no nonzero v with Y_u v = 0 for all u (width drop, brick W); (hF) rank Fx(xg) ≥ 3 over K. -/
theorem nadia_T381_C3 {F K : Type*} [Field F] [Field K] (φ : F →+* K)
    (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (xg : Fin 4 → K)
    (g1 : ∀ l : Fin 4 → F, (∑ u, φ (l u) * xg u) = 0 → l = 0)
    (g2 : ∀ (A : Matrix (Fin 4) (Fin 4) F) (c : K), (A.map φ) *ᵥ xg = c • xg → ∃ a : F, A = a • 1)
    (hW : ∀ v : Fin 3 → F, v ≠ 0 → (∀ u, Y u *ᵥ v = 0) → False)
    (hF : 3 ≤ (∑ a, xg a • (X a).map φ).rank) : False := by
  classical
  obtain ⟨hdK, hoK⟩ := daria_slice_map φ X Y P Q hd ho
  set Fx : Matrix (Fin 4) (Fin 3) K := ∑ a, xg a • (X a).map φ with hFx
  set Qx : Matrix (Fin 4) (Fin 3) K := ∑ a, xg a • (Q a).map φ with hQx
  -- a nonzero n with Qxᵀ n = 0
  obtain ⟨n, hnk, hn0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt (f := Qxᵀ.mulVecLin) (by simp))
  have hn : Qxᵀ *ᵥ n = 0 := hnk
  -- Lemma K over K
  have hK : ∀ u, Fx *ᵥ (((Y u).map φ)ᵀ *ᵥ n) = xg u • n := fun u =>
    daria_lemmaK (fun a => (X a).map φ) (fun a => (Y a).map φ) (fun a => (P a).map φ) (fun a => (Q a).map φ)
      hdK hoK xg n hn u
  -- Fx is injective
  have hinj : Function.Injective Fx.mulVecLin := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Fx.mulVecLin
    have h2 : Fx.rank = Module.finrank K (LinearMap.range Fx.mulVecLin) := rfl
    have h3 : Fx.rank ≤ 3 := by simpa using Matrix.rank_le_card_width Fx
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have h4 : Module.finrank K (LinearMap.ker Fx.mulVecLin) = 0 := by omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp h4
  -- some coordinate of xg is nonzero
  obtain ⟨b, hb⟩ : ∃ b, xg b ≠ 0 := by
    by_contra hall
    push Not at hall
    have := g1 (Pi.single 0 1) (by simp [hall])
    have h0 := congrFun this 0
    simp at h0
  set c : Fin 3 → K := (xg b)⁻¹ • (((Y b).map φ)ᵀ *ᵥ n) with hc
  have hFc : Fx *ᵥ c = n := by
    rw [hc, Matrix.mulVec_smul, hK b, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hYn : ∀ u, ((Y u).map φ)ᵀ *ᵥ n = xg u • c := by
    intro u
    apply hinj
    simp only [Matrix.mulVecLin_apply]
    rw [hK u, Matrix.mulVec_smul, hFc]
  have hc0 : c ≠ 0 := by
    intro h0
    apply hn0
    rw [← hFc, h0, Matrix.mulVec_zero]
  obtain ⟨s, hs⟩ : ∃ s, c s ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc0 (funext hall)
  -- the G-matrices
  set G : Fin 3 → Matrix (Fin 4) (Fin 4) F := fun t => Matrix.of (fun u j => Y u j t) with hG
  have hGn : ∀ t, ((G t).map φ) *ᵥ n = c t • xg := by
    intro t
    funext u
    have := congrFun (hYn u) t
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hG, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [this, Pi.smul_apply, smul_eq_mul, mul_comm]
  -- G s is invertible (image trick)
  have hdet : (G s).det ≠ 0 := by
    intro h0
    obtain ⟨l, hl0, hl⟩ := (Matrix.exists_vecMul_eq_zero_iff).mpr h0
    apply hl0
    apply g1 l
    have e1 : (φ ∘ l) ⬝ᵥ (((G s).map φ) *ᵥ n) = 0 := by
      rw [Matrix.dotProduct_mulVec]
      have : (φ ∘ l) ᵥ* (G s).map φ = 0 := by
        funext i
        rw [← RingHom.map_vecMul, hl]
        simp
      rw [this, zero_dotProduct]
    rw [hGn s, dotProduct_smul, smul_eq_mul] at e1
    rcases mul_eq_zero.mp e1 with h | h
    · exact absurd h hs
    · simpa [dotProduct] using h
  -- every G t is a multiple of G s
  have hmul : ∀ t, ∃ a : F, G t = a • G s := by
    intro t
    have hGi : IsUnit (G s).det := isUnit_iff_ne_zero.mpr hdet
    obtain ⟨a, ha⟩ := g2 (G t * (G s)⁻¹) (c t / c s) (by
      have e2 : ((G s)⁻¹).map φ *ᵥ (c s • xg) = n := by
        rw [← hGn s, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hGi, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
      have e3 : ((G s)⁻¹).map φ *ᵥ xg = (c s)⁻¹ • n := by
        rw [← e2, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, e3, Matrix.mulVec_smul, hGn t, smul_smul, div_eq_mul_inv, mul_comm])
    refine ⟨a, ?_⟩
    have hGi' : IsUnit (G s) := (Matrix.isUnit_iff_isUnit_det _).mpr hGi
    calc G t = G t * (G s)⁻¹ * G s := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGi, Matrix.mul_one]
      _ = a • G s := by rw [ha, Matrix.smul_mul, Matrix.one_mul]
  choose a ha using hmul
  -- a nonzero v with sum_t a_t v_t = 0
  obtain ⟨v, hvk, hv0⟩ := (Submodule.ne_bot_iff _).mp
    (LinearMap.ker_ne_bot_of_finrank_lt
      (f := (Matrix.of (fun (_ : Fin 1) t => a t) : Matrix (Fin 1) (Fin 3) F).mulVecLin) (by simp))
  have hv : ∑ t, a t * v t = 0 := by
    have := congrFun (show (Matrix.of (fun (_ : Fin 1) t => a t) : Matrix (Fin 1) (Fin 3) F) *ᵥ v = 0 from hvk) 0
    simpa [Matrix.mulVec, dotProduct] using this
  apply hW v hv0
  intro u
  funext j
  have hY : ∀ t, Y u j t = a t * Y u j s := by
    intro t
    have := congrFun (congrFun (ha t) u) j
    simpa [hG] using this
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  calc ∑ t, Y u j t * v t = ∑ t, a t * v t * Y u j s :=
        Finset.sum_congr rfl (fun t _ => by rw [hY t]; ring)
    _ = (∑ t, a t * v t) * Y u j s := by rw [Finset.sum_mul]
    _ = 0 := by rw [hv, zero_mul]
end

/-! ## unit R62_kernel_dim_induction_step -/
section
/-! T320 (R62 exact), induction step. `gretaKer A B` = {Z : Zᵀ = A Z Bᵀ} (entrywise
`Z j i = Σ_k Σ_l A i k * Z k l * B j l`), the kernel of SWAP_N - A ⊗ B in matrix form.
If the first columns of `A` and `B` are multiples of `e₀`, then
`dim K(A, B) ≤ (n + 1) + dim K(A', B')` for the lower-right blocks `A'`, `B'`:
the map `Z ↦ (row 0 of Z, lower-right block of Z)` is injective on `K(A, B)` and lands in
`F^(n+1) × K(A', B')`. -/

/-- The kernel `{Z : Zᵀ = A Z Bᵀ}` as a submodule. -/
def gretaKer {n : ℕ} {F : Type*} [Field F] (A B : Matrix (Fin n) (Fin n) F) :
    Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {Z | ∀ i j, Z j i = ∑ k, ∑ l, A i k * Z k l * B j l}
  add_mem' := by
    intro X Y hX hY i j
    simp only [Set.mem_setOf_eq] at hX hY
    simp only [Matrix.add_apply]
    rw [hX i j, hY i j, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c X hX i j
    simp only [Set.mem_setOf_eq] at hX
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [hX i j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring

/-- The lower-right block of a kernel element lies in the kernel of the lower-right blocks. -/
theorem greta_ker_submatrix_mem {n : ℕ} {F : Type*} [Field F]
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hA : ∀ i : Fin n, A i.succ 0 = 0) (hB : ∀ j : Fin n, B j.succ 0 = 0)
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hZ : Z ∈ gretaKer A B) :
    Z.submatrix Fin.succ Fin.succ ∈
      gretaKer (A.submatrix Fin.succ Fin.succ) (B.submatrix Fin.succ Fin.succ) := by
  intro i j
  have h := hZ i.succ j.succ
  simp only [Matrix.submatrix_apply]
  rw [h, Fin.sum_univ_succ]
  simp only [hA i, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Fin.sum_univ_succ]
  simp [hB j]

/-- **Induction step:** `dim K(A, B) ≤ (n + 1) + dim K(A', B')` when the first columns of `A` and `B`
are multiples of `e₀`. -/
theorem greta_ker_finrank_step {n : ℕ} {F : Type*} [Field F]
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hA : ∀ i : Fin n, A i.succ 0 = 0) (hB : ∀ j : Fin n, B j.succ 0 = 0) :
    Module.finrank F (gretaKer A B) ≤
      (n + 1) + Module.finrank F
        (gretaKer (A.submatrix Fin.succ Fin.succ) (B.submatrix Fin.succ Fin.succ)) := by
  let f1 : gretaKer A B →ₗ[F] (Fin (n + 1) → F) :=
    { toFun := fun Z j => Z.1 0 j
      map_add' := by intro X Y; rfl
      map_smul' := by intro c X; rfl }
  let f2 : gretaKer A B →ₗ[F]
      gretaKer (A.submatrix Fin.succ Fin.succ) (B.submatrix Fin.succ Fin.succ) :=
    { toFun := fun Z => ⟨Z.1.submatrix Fin.succ Fin.succ, greta_ker_submatrix_mem A B hA hB Z.1 Z.2⟩
      map_add' := by intro X Y; rfl
      map_smul' := by intro c X; rfl }
  have hinj : Function.Injective (f1.prod f2) := by
    rw [injective_iff_map_eq_zero]
    intro Z hZ0
    have h1 : ∀ j, Z.1 0 j = 0 := fun j => congrFun (congrArg Prod.fst hZ0) j
    have h2 : ∀ i j : Fin n, Z.1 i.succ j.succ = 0 := fun i j =>
      congrFun (congrFun (congrArg Subtype.val (congrArg Prod.snd hZ0)) i) j
    apply Subtype.ext
    ext r c
    refine Fin.cases ?_ (fun r' => ?_) r
    · exact h1 c
    · refine Fin.cases ?_ (fun c' => ?_) c
      · have hZ := Z.2 0 r'.succ
        show Z.1 r'.succ 0 = 0
        rw [hZ, Fin.sum_univ_succ]
        simp only [h1, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
        refine Finset.sum_eq_zero (fun k _ => ?_)
        rw [Fin.sum_univ_succ]
        simp [hB r', h2]
      · exact h2 r' c'
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_fin_fun] at this
  exact this
end

/-! ## unit R62_kernel_change_of_basis -/
section
open Matrix
/-! T320 (R62 exact), change of basis: `K(A, B)` embeds into `K(R⁻¹ A P, P⁻¹ B R)` via `Z ↦ P⁻¹ Z R⁻ᵀ`. -/

/-- Matrix form of the kernel condition. -/
theorem greta_mem_ker_iff {n : ℕ} {F : Type*} [Field F] (A B Z : Matrix (Fin n) (Fin n) F) :
    Z ∈ gretaKer A B ↔ Zᵀ = A * Z * Bᵀ := by
  constructor
  · intro h
    ext i j
    rw [Matrix.transpose_apply, h i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [Matrix.transpose_apply] at h'
    rw [h']
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    exact Finset.sum_comm

/-- Change of basis: `dim K(A, B) ≤ dim K(R⁻¹ A P, P⁻¹ B R)` for invertible `P`, `R`
(inverses `Pi`, `Ri`). -/
theorem greta_ker_finrank_le_conj {n : ℕ} {F : Type*} [Field F]
    (A B P Pi R Ri : Matrix (Fin n) (Fin n) F) (hP : P * Pi = 1)
    (hR : R * Ri = 1) :
    Module.finrank F (gretaKer A B) ≤ Module.finrank F (gretaKer (Ri * A * P) (Pi * B * R)) := by
  have e1 : Riᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  have hmem : ∀ Z ∈ gretaKer A B, Pi * Z * Riᵀ ∈ gretaKer (Ri * A * P) (Pi * B * R) := by
    intro Z hZ
    rw [greta_mem_ker_iff] at hZ ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hZ,
      Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Pi, hP, Matrix.one_mul, ← Matrix.mul_assoc Riᵀ Rᵀ, e1, Matrix.one_mul]
  let f : gretaKer A B →ₗ[F] gretaKer (Ri * A * P) (Pi * B * R) :=
    { toFun := fun Z => ⟨Pi * Z.1 * Riᵀ, hmem Z.1 Z.2⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    intro X Y hXY
    have h := congrArg Subtype.val hXY
    change Pi * X.1 * Riᵀ = Pi * Y.1 * Riᵀ at h
    apply Subtype.ext
    have hX : X.1 = P * (Pi * X.1 * Riᵀ) * Rᵀ := by
      simp only [Matrix.mul_assoc]
      rw [e1, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    have hY : Y.1 = P * (Pi * Y.1 * Riᵀ) * Rᵀ := by
      simp only [Matrix.mul_assoc]
      rw [e1, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]
    rw [hX, hY, h]
  exact LinearMap.finrank_le_finrank_of_injective hinj
end

/-! ## unit R62_kernel_basis_and_eigen_pair -/
section
open Matrix
/-! T320 (R62 exact), two existence steps:
(C2) an invertible matrix `P` (two-sided inverse `Pi`) with a prescribed nonzero first column;
(C3) over an algebraically closed field, nonzero `p`, `r` with `A p ∈ F r` and `B r ∈ F p`
(from an eigenvector of `B A`). -/

/-- (C2) An invertible matrix with prescribed nonzero first column. -/
theorem greta_exists_inv_col0 {n : ℕ} {F : Type*} [Field F] (v : Fin (n + 1) → F) (hv : v ≠ 0) :
    ∃ P Pi : Matrix (Fin (n + 1)) (Fin (n + 1)) F, P * Pi = 1 ∧ Pi * P = 1 ∧ ∀ i, P i 0 = v i := by
  classical
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl (Submodule.span F {v})
  have hfin : Module.finrank F N = n := by
    have h := Submodule.finrank_add_eq_of_isCompl hN
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin n) F N := Module.finBasisOfFinrankEq F N hfin
  have hli : ∀ (c : F), ∀ x ∈ N, c • v + x = 0 → c = 0 := by
    intro c x hx h
    by_contra hc
    have h1 : c • v ∈ N := by
      have : c • v = -x := eq_neg_of_add_eq_zero_left h
      rw [this]
      exact N.neg_mem hx
    have h2 : c • v ∈ Submodule.span F {v} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have h0 : c • v = 0 := (Submodule.disjoint_def.mp hN.disjoint) _ h2 h1
    exact hv ((smul_eq_zero.mp h0).resolve_left hc)
  have hsp : ∀ z : Fin (n + 1) → F, ∃ c : F, z + c • v ∈ N := by
    intro z
    have hz : z ∈ Submodule.span F {v} ⊔ N := by
      rw [hN.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨-a, ?_⟩
    have : a • v + w + -a • v = w := by
      rw [neg_smul]
      abel
    rw [this]
    exact hw
  let bas := Module.Basis.mkFinCons v b hli hsp
  refine ⟨(Pi.basisFun F (Fin (n + 1))).toMatrix bas, bas.toMatrix (Pi.basisFun F (Fin (n + 1))),
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  intro i
  rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.coe_mkFinCons]
  rfl

/-- (C3) Over an algebraically closed field: nonzero `p`, `r` with `A p ∈ F r` and `B r ∈ F p`. -/
theorem greta_exists_pair_vec {n : ℕ} {F : Type*} [Field F] [IsAlgClosed F]
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    ∃ p r : Fin (n + 1) → F, p ≠ 0 ∧ r ≠ 0 ∧ (∃ α : F, A *ᵥ p = α • r) ∧ (∃ β : F, B *ᵥ r = β • p) := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (B * A))
  obtain ⟨p, hp⟩ := hμ.exists_hasEigenvector
  have hp0 : p ≠ 0 := hp.2
  have hBA : (B * A) *ᵥ p = μ • p := by
    have h := hp.apply_eq_smul
    rwa [Matrix.toLin'_apply] at h
  by_cases hAp : A *ᵥ p = 0
  · by_cases hB : ∃ r : Fin (n + 1) → F, r ≠ 0 ∧ B *ᵥ r = 0
    · obtain ⟨r, hr, hBr⟩ := hB
      exact ⟨p, r, hp0, hr, ⟨0, by rw [hAp, zero_smul]⟩, ⟨0, by rw [hBr, zero_smul]⟩⟩
    · have hinj : Function.Injective (Matrix.toLin' B) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro r hr
        by_contra h
        exact hB ⟨r, h, by rwa [Matrix.toLin'_apply] at hr⟩
      obtain ⟨r, hr⟩ := (LinearMap.injective_iff_surjective.mp hinj) p
      rw [Matrix.toLin'_apply] at hr
      refine ⟨p, r, hp0, ?_, ⟨0, by rw [hAp, zero_smul]⟩, ⟨1, by rw [hr, one_smul]⟩⟩
      intro h
      apply hp0
      rw [← hr, h, Matrix.mulVec_zero]
  · refine ⟨p, A *ᵥ p, hp0, hAp, ⟨1, by rw [one_smul]⟩, ⟨μ, ?_⟩⟩
    rw [Matrix.mulVec_mulVec, hBA]
end

/-! ## unit R62_kernel_dim_le_half_n_n_plus_one -/
section
open Matrix
/-! T320 (R62 exact), the kernel bound: over an algebraically closed field,
`2 * dim {Z : Zᵀ = A Z Bᵀ} ≤ n (n + 1)` for all `A`, `B`. Induction on `n`: the eigen pair
(greta_exists_pair_vec) and two bases with prescribed first vectors (greta_exists_inv_col0) put the
first columns of `A`, `B` in triangular form after a change of basis (greta_ker_finrank_le_conj);
then greta_ker_finrank_step reduces to the lower-right blocks. -/

theorem greta_ker_finrank_le {F : Type*} [Field F] [IsAlgClosed F] :
    ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
      2 * Module.finrank F (gretaKer A B) ≤ n * (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro A B
    have h := Submodule.finrank_le (gretaKer A B)
    have h0 : Module.finrank F (Matrix (Fin 0) (Fin 0) F) = 0 := Module.finrank_zero_of_subsingleton
    omega
  | succ n ih =>
    intro A B
    obtain ⟨p, r, hp, hr, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := greta_exists_pair_vec A B
    obtain ⟨P, Pi, hPPi, hPiP, hPcol⟩ := greta_exists_inv_col0 p hp
    obtain ⟨Q, Qi, hQQi, hQiQ, hQcol⟩ := greta_exists_inv_col0 r hr
    have h1 := greta_ker_finrank_le_conj A B P Pi Q Qi hPPi hQQi
    have hcolA : ∀ k, (A * P) k 0 = α * Q k 0 := by
      intro k
      rw [Matrix.mul_apply, hQcol k]
      have h : (A *ᵥ p) k = α * r k := by rw [hα]; rfl
      simp only [Matrix.mulVec, dotProduct] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun j _ => by rw [hPcol j])
    have hcolB : ∀ k, (B * Q) k 0 = β * P k 0 := by
      intro k
      rw [Matrix.mul_apply, hPcol k]
      have h : (B *ᵥ r) k = β * p k := by rw [hβ]; rfl
      simp only [Matrix.mulVec, dotProduct] at h
      rw [← h]
      exact Finset.sum_congr rfl (fun j _ => by rw [hQcol j])
    have hA1 : ∀ i : Fin n, (Qi * A * P) i.succ 0 = 0 := by
      intro i
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      have h : ∑ k, Qi i.succ k * (A * P) k 0 = α * (Qi * Q) i.succ 0 := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [hcolA k]; ring)
      rw [h, hQiQ, Matrix.one_apply_ne (Fin.succ_ne_zero i), mul_zero]
    have hB1 : ∀ j : Fin n, (Pi * B * Q) j.succ 0 = 0 := by
      intro j
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      have h : ∑ k, Pi j.succ k * (B * Q) k 0 = β * (Pi * P) j.succ 0 := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [hcolB k]; ring)
      rw [h, hPiP, Matrix.one_apply_ne (Fin.succ_ne_zero j), mul_zero]
    have h2 := greta_ker_finrank_step (Qi * A * P) (Pi * B * Q) hA1 hB1
    have h3 := ih ((Qi * A * P).submatrix Fin.succ Fin.succ) ((Pi * B * Q).submatrix Fin.succ Fin.succ)
    have e : (n + 1) * (n + 1 + 1) = 2 * (n + 1) + n * (n + 1) := by ring
    omega
end

/-! ## unit R62_rank_swap_minus_kron_alg_closed -/
section
open Matrix
/-! T320 (R62 exact), rank form over an algebraically closed field:
rank(SWAP_N - X ⊗ Y) ≥ N(N-1)/2, and the OS ≤ 1 case of a split SWAP_N = B + C:
if OS(C) ≤ 1 then rank B ≥ N(N-1)/2 (the CTO's X225 case for the Operator's target (d)). -/

/-- `(SWAP - X ⊗ Y) v` at `(i, j)` in kernel coordinates. -/
theorem greta_swap_sub_kron_mulVec {F : Type*} [Field F] (N : ℕ) (X Y : Matrix (Fin N) (Fin N) F)
    (v : Fin N × Fin N → F) (i j : Fin N) :
    ((biancaSwapF F (Fin N) - Matrix.kroneckerMap (· * ·) X Y) *ᵥ v) (i, j) =
      v (j, i) - ∑ k, ∑ l, X i k * v (k, l) * Y j l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single (j, i)]
    · simp [biancaSwapF]
    · intro b _ hb
      have hne : ¬ ((i, j).1 = b.2 ∧ (i, j).2 = b.1) := by
        rintro ⟨h1, h2⟩
        exact hb (Prod.ext h2.symm h1.symm)
      simp [biancaSwapF, hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [Matrix.kroneckerMap_apply]
    ring

/-- **R62, rank form** (algebraically closed field): `N(N-1) ≤ 2 rank(SWAP_N - X ⊗ Y)`. -/
theorem greta_rank_swap_sub_kron {F : Type*} [Field F] [IsAlgClosed F] (N : ℕ)
    (X Y : Matrix (Fin N) (Fin N) F) :
    N * (N - 1) ≤ 2 * (biancaSwapF F (Fin N) - Matrix.kroneckerMap (· * ·) X Y).rank := by
  set M := biancaSwapF F (Fin N) - Matrix.kroneckerMap (· * ·) X Y with hM
  let f := M.mulVecLin
  have hmem : ∀ v ∈ LinearMap.ker f, (Matrix.of fun i j => v (i, j)) ∈ gretaKer X Y := by
    intro v hv i j
    have h0 : (M *ᵥ v) (i, j) = 0 := by
      have := LinearMap.mem_ker.mp hv
      rw [Matrix.mulVecLin_apply] at this
      rw [this]
      rfl
    rw [hM, greta_swap_sub_kron_mulVec] at h0
    simp only [Matrix.of_apply]
    rw [sub_eq_zero] at h0
    rw [h0]
  let g : LinearMap.ker f →ₗ[F] gretaKer X Y :=
    { toFun := fun v => ⟨Matrix.of fun i j => v.1 (i, j), hmem v.1 v.2⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply Subtype.ext
    funext p
    have := congrFun (congrFun (congrArg Subtype.val hv) p.1) p.2
    exact this
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := greta_ker_finrank_le N X Y
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  have h4 : Module.finrank F (Fin N × Fin N → F) = N * N := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
  have hrank : M.rank = Module.finrank F (LinearMap.range f) := rfl
  have e1 : N * (N + 1) = N * N + N := by ring
  have e2 : N * (N - 1) + N = N * N := by
    cases N with
    | zero => rfl
    | succ m => simp only [Nat.add_sub_cancel]; ring
  rw [hrank]
  omega

/-- **The OS ≤ 1 case** (algebraically closed field): if `SWAP_N = B + C` and the realignment of `C`
has rank ≤ 1 (so `C = X ⊗ Y`), then `N(N-1) ≤ 2 rank B`. -/
theorem greta_rank_ge_of_os_le_one {F : Type*} [Field F] [IsAlgClosed F] (N : ℕ)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hC : (biancaRealignF C).rank ≤ 1) : N * (N - 1) ≤ 2 * B.rank := by
  obtain ⟨U, V, hUV⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hsub : Subsingleton (Fin (biancaRealignF C).rank) := by
    rw [Fin.subsingleton_iff_le_one]
    exact hC
  let X : Matrix (Fin N) (Fin N) F := Matrix.of fun i k => ∑ t, U t (i, k)
  let Y : Matrix (Fin N) (Fin N) F := Matrix.of fun j l => ∑ t, V t (j, l)
  have hCXY : C = Matrix.kroneckerMap (· * ·) X Y := by
    ext p q
    have hpq := congrFun (congrFun hUV (p.1, q.1)) (p.2, q.2)
    simp only [biancaRealignF, Matrix.of_apply] at hpq
    rw [hpq, Matrix.sum_apply, Matrix.kroneckerMap_apply]
    simp only [X, Y, Matrix.of_apply, Matrix.vecMulVec_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    haveI : Subsingleton (Fin (Matrix.of fun (a b : Fin N × Fin N) => C (a.1, b.1) (a.2, b.2)).rank) :=
      hsub
    exact (Fintype.sum_subsingleton (fun j => U t (p.1, q.1) * V j (p.2, q.2)) t).symm
  have hB : B = biancaSwapF F (Fin N) - Matrix.kroneckerMap (· * ·) X Y := by
    rw [h, hCXY]
    abel
  rw [hB]
  exact greta_rank_swap_sub_kron N X Y
end

/-! ## unit matrix_rank_map_le_field_hom -/
section
/-- Rank does not grow under a ring map of fields applied entrywise (e.g. ℚ → ℂ): the columns of `A.map f`
are `L`-combinations of the images of a `K`-basis of the column span of `A`. -/
theorem nadia_rank_map_le {m n K L : Type*} [Fintype m] [Fintype n] [Field K] [Field L] (f : K →+* L)
    (A : Matrix m n K) : (A.map f).rank ≤ A.rank := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  set S := Submodule.span K (Set.range A.transpose) with hS
  let b := Module.finBasis K S
  let φ : (m → K) → (m → L) := fun v i => f (v i)
  have hφadd : ∀ v w, φ (v + w) = φ v + φ w := by intro v w; funext i; simp [φ]
  have hφsmul : ∀ (c : K) v, φ (c • v) = f c • φ v := by intro c v; funext i; simp [φ]
  have hφsum : ∀ (s : Finset (Fin (Module.finrank K S))) (g : Fin (Module.finrank K S) → (m → K)),
      φ (∑ i ∈ s, g i) = ∑ i ∈ s, φ (g i) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => funext i; simp [φ]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hφadd, ih]
  have hsub : Submodule.span L (Set.range (A.map f).transpose) ≤
      Submodule.span L (Set.range (fun i => φ ((b i : S) : m → K))) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : A.transpose j ∈ S := Submodule.subset_span ⟨j, rfl⟩
    have hrepr := b.sum_repr ⟨A.transpose j, hj⟩
    have hcol : (A.map f).transpose j = φ (A.transpose j) := by funext i; rfl
    have hexp : A.transpose j = ∑ i, (b.repr ⟨A.transpose j, hj⟩ i) • ((b i : S) : m → K) := by
      have h2 : (((∑ i, b.repr ⟨A.transpose j, hj⟩ i • b i : S)) : m → K) = A.transpose j := by
        rw [hrepr]
      rw [Submodule.coe_sum] at h2
      simp only [Submodule.coe_smul] at h2
      exact h2.symm
    rw [hcol, hexp, hφsum]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [hφsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (Submodule.span L (Set.range (A.map f).transpose))
      ≤ Module.finrank L (Submodule.span L (Set.range (fun i => φ ((b i : S) : m → K)))) :=
        Submodule.finrank_mono hsub
    _ ≤ Fintype.card (Fin (Module.finrank K S)) := finrank_range_le_card _
    _ = Module.finrank K S := Fintype.card_fin _
end

/-! ## unit R62_rank_swap_minus_kron_every_field -/
section
open Matrix
/-! T333: R62 over EVERY field (CTO X247). The algebraic-closure bound greta_rank_swap_sub_kron
transfers down by Nadia's nadia_rank_map_le (rank does not grow under a field hom). -/

/-- Mapping `SWAP_N - X ⊗ Y` entrywise by a ring hom of fields. -/
theorem greta_swap_sub_kron_map {K L : Type*} [Field K] [Field L] (f : K →+* L) (N : ℕ)
    (X Y : Matrix (Fin N) (Fin N) K) :
    (biancaSwapF K (Fin N) - Matrix.kroneckerMap (· * ·) X Y).map f =
      biancaSwapF L (Fin N) - Matrix.kroneckerMap (· * ·) (X.map f) (Y.map f) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.kroneckerMap_apply, biancaSwapF,
    Matrix.of_apply, map_sub, map_mul]
  split_ifs <;> simp

/-- **R62 over every field:** `N(N-1) ≤ 2 rank(SWAP_N - X ⊗ Y)`. -/
theorem greta_rank_swap_sub_kron_field {K : Type*} [Field K] (N : ℕ)
    (X Y : Matrix (Fin N) (Fin N) K) :
    N * (N - 1) ≤ 2 * (biancaSwapF K (Fin N) - Matrix.kroneckerMap (· * ·) X Y).rank := by
  have h := greta_rank_swap_sub_kron (F := AlgebraicClosure K) N
    (X.map (algebraMap K (AlgebraicClosure K))) (Y.map (algebraMap K (AlgebraicClosure K)))
  rw [← greta_swap_sub_kron_map] at h
  have h2 := nadia_rank_map_le (algebraMap K (AlgebraicClosure K))
    (biancaSwapF K (Fin N) - Matrix.kroneckerMap (· * ·) X Y)
  omega

/-- **The OS ≤ 1 case over every field:** `SWAP_N = B + C` with `OS(C) ≤ 1` gives
`N(N-1) ≤ 2 rank B`. -/
theorem greta_rank_ge_of_os_le_one_field {F : Type*} [Field F] (N : ℕ)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hC : (biancaRealignF C).rank ≤ 1) : N * (N - 1) ≤ 2 * B.rank := by
  obtain ⟨U, V, hUV⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hsub : Subsingleton (Fin (biancaRealignF C).rank) := by
    rw [Fin.subsingleton_iff_le_one]
    exact hC
  let X : Matrix (Fin N) (Fin N) F := Matrix.of fun i k => ∑ t, U t (i, k)
  let Y : Matrix (Fin N) (Fin N) F := Matrix.of fun j l => ∑ t, V t (j, l)
  have hCXY : C = Matrix.kroneckerMap (· * ·) X Y := by
    ext p q
    have hpq := congrFun (congrFun hUV (p.1, q.1)) (p.2, q.2)
    simp only [biancaRealignF, Matrix.of_apply] at hpq
    rw [hpq, Matrix.sum_apply, Matrix.kroneckerMap_apply]
    simp only [X, Y, Matrix.of_apply, Matrix.vecMulVec_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact (@Fintype.sum_subsingleton _ _ _ _ hsub (fun j => U t (p.1, q.1) * V j (p.2, q.2)) t).symm
  have hB : B = biancaSwapF F (Fin N) - Matrix.kroneckerMap (· * ·) X Y := by
    rw [h, hCXY]
    abel
  rw [hB]
  exact greta_rank_swap_sub_kron_field N X Y

/-- Nadia's SWAP over ℚ is Bianca's SWAP over ℚ. -/
theorem greta_nadiaSwap_eq_biancaSwapF (N : ℕ) : nadiaSwapMat N = biancaSwapF ℚ (Fin N) := by
  ext p q
  simp only [nadiaSwapMat, biancaSwapF, Matrix.of_apply]
  split_ifs with h1 h2 h2 <;>
    first
    | rfl
    | exact absurd ⟨h1.2.symm, h1.1.symm⟩ h2
    | exact absurd ⟨h2.2.symm, h2.1.symm⟩ h1

/-- **R62 over ℚ in Nadia's form:** `N(N-1) ≤ 2 rank(nadiaSwapMat N - X ⊗ Y)`. -/
theorem greta_rank_nadiaSwap_sub_kron (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℚ) :
    N * (N - 1) ≤ 2 * (nadiaSwapMat N - Matrix.kroneckerMap (· * ·) X Y).rank := by
  rw [greta_nadiaSwap_eq_biancaSwapF]
  exact greta_rank_swap_sub_kron_field N X Y
end

/-! ## unit minsum_certificate_template_factor_tables -/
section
/-! T245 (Nadia's I62 certificate template): any four factor tables of a numeric split, rounded to rationals (or
integers with a common denominator d), certify minsum(N) ≤ r + k. Statement form of Bianca's
`bianca_minsumF_le_of_composition` (biancaSwapF, biancaRealignF). -/

/-- The operator-Schmidt realignment is ℚ-linear in scalars. -/
theorem uri_realignF_smul {F X : Type*} [Field F] (c : F) (M : Matrix (X × X) (X × X) F) :
    biancaRealignF (c • M) = c • biancaRealignF M := by
  ext a b
  simp [biancaRealignF]

/-- The realignment is an involution. -/
theorem uri_realignF_realignF {F X : Type*} [Field F] (M : Matrix (X × X) (X × X) F) :
    biancaRealignF (biancaRealignF M) = M := by
  ext a b
  simp [biancaRealignF]

/-- **T245, the certificate template.** If U·V + realign(P·Q) = d·SWAP_X for factor tables U : (X×X)×R,
V : R×(X×X), P : (X×X)×S, Q : S×(X×X) and d ≠ 0, then SWAP_X = B + C with rank B ≤ |R| and
rank(realign C) ≤ |S|, i.e. minsum(|X|) ≤ |R| + |S|. -/
theorem uri_minsumF_le_of_factor_tables {F X R S : Type*} [Field F] [Fintype X] [DecidableEq X]
    [Fintype R] [Fintype S] (d : F) (hd : d ≠ 0)
    (U : Matrix (X × X) R F) (V : Matrix R (X × X) F) (P : Matrix (X × X) S F) (Q : Matrix S (X × X) F)
    (h : U * V + biancaRealignF (P * Q) = d • biancaSwapF F X) :
    ∃ B C : Matrix (X × X) (X × X) F,
      B + C = biancaSwapF F X ∧ B.rank ≤ Fintype.card R ∧ (biancaRealignF C).rank ≤ Fintype.card S := by
  refine ⟨U * (d⁻¹ • V), biancaRealignF (P * (d⁻¹ • Q)), ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_smul, uri_realignF_smul, ← smul_add, h, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · rw [uri_realignF_realignF]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- The unscaled form (d = 1): SWAP_X = U·V + realign(P·Q) certifies minsum(|X|) ≤ |R| + |S|. -/
theorem uri_minsumF_le_of_factor_tables_one {F X R S : Type*} [Field F] [Fintype X] [DecidableEq X]
    [Fintype R] [Fintype S]
    (U : Matrix (X × X) R F) (V : Matrix R (X × X) F) (P : Matrix (X × X) S F) (Q : Matrix S (X × X) F)
    (h : U * V + biancaRealignF (P * Q) = biancaSwapF F X) :
    ∃ B C : Matrix (X × X) (X × X) F,
      B + C = biancaSwapF F X ∧ B.rank ≤ Fintype.card R ∧ (biancaRealignF C).rank ≤ Fintype.card S :=
  uri_minsumF_le_of_factor_tables 1 one_ne_zero U V P Q (by rw [one_smul]; exact h)
end

/-! ## unit three_piece_split_middle_floor_every_field -/
section
/-! T336: three-piece floor. For SWAP_N = P0 + M + P2 with OS(P0) ≤ 1 (a product) and rank P2 ≤ 1,
both flattening ranks of the middle piece are at least N(N-1)/2 - 1 (over every field). The exact
closed form of R152 (unit swap4_three_piece_split_16_1_6_6_1_16 at N = 4: (16,1)+(6,6)+(1,16))
attains N(N-1)/2, so it is optimal up to 1, and every 3-piece family of this shape has
S ≥ N(N-1)/2 - 1, i.e. rho → 1. -/

/-- SWAP is fixed by the realignment (every field). -/
theorem greta_realignF_swapF {F : Type*} [Field F] (N : ℕ) :
    biancaRealignF (biancaSwapF F (Fin N)) = biancaSwapF F (Fin N) := by
  ext a b
  simp only [biancaRealignF, biancaSwapF, Matrix.of_apply]
  split_ifs with h1 h2 h2 <;>
    first
    | rfl
    | exact absurd ⟨h1.1, h1.2.symm⟩ h2
    | exact absurd ⟨h2.1, h2.2.symm⟩ h1

/-- **Three-piece floor** (every field). -/
theorem greta_three_piece_middle_floor {F : Type*} [Field F] (N : ℕ)
    (P0 M P2 : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = P0 + M + P2) (h0 : (biancaRealignF P0).rank ≤ 1)
    (h2 : P2.rank ≤ 1) :
    N * (N - 1) ≤ 2 * (M.rank + 1) ∧ N * (N - 1) ≤ 2 * ((biancaRealignF M).rank + 1) := by
  constructor
  · have h1 := greta_rank_ge_of_os_le_one_field N (M + P2) P0 (by rw [h]; abel) h0
    have hr := bianca_matrix_rank_add_le M P2
    omega
  · have hsplit : biancaSwapF F (Fin N) =
        (biancaRealignF P0 + biancaRealignF M) + biancaRealignF P2 := by
      calc biancaSwapF F (Fin N) = biancaRealignF (biancaSwapF F (Fin N)) :=
            (greta_realignF_swapF N).symm
        _ = biancaRealignF (P0 + M + P2) := by rw [← h]
        _ = (biancaRealignF P0 + biancaRealignF M) + biancaRealignF P2 := by
            ext a b
            simp [biancaRealignF]
    have h2' : (biancaRealignF (biancaRealignF P2)).rank ≤ 1 := by
      rw [uri_realignF_realignF]
      exact h2
    have h1 := greta_rank_ge_of_os_le_one_field N _ _ hsplit h2'
    have hr := bianca_matrix_rank_add_le (biancaRealignF P0) (biancaRealignF M)
    omega
end

/-! ## unit four_piece_split_floor_every_field -/
section
/-! T344: four-piece floor (every field, N ≥ 4). For SWAP_N = P0 + P1 + P2 + P3 with OS(P0) ≤ 1 and
rank(P3) ≤ 1, writing rᵢ = rank Pᵢ and cᵢ = OS Pᵢ:
r1 + r2 ≥ N(N-1)/2 - 1, c1 + c2 ≥ N(N-1)/2 - 1 (R62), and r1 + c2 ≥ N, r2 + c1 ≥ N (Nadia's N + 2
floor on the bipartitions {P1, P3} | {P0, P2} and {P2, P3} | {P0, P1}). The COMPUTED S floor from these
(work/Greta/four_piece_floor.out) is above the T3 threshold N^√2 at t = 2..5. -/

/-- The realignment is additive. -/
theorem greta_realignF_add {F : Type*} [Field F] (N : ℕ) (A B : Matrix (Fin N × Fin N) (Fin N × Fin N) F) :
    biancaRealignF (A + B) = biancaRealignF A + biancaRealignF B := by
  ext a b
  simp [biancaRealignF]

/-- **Four-piece floor** (every field, `N ≥ 4`). -/
theorem greta_four_piece_floor {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (P0 P1 P2 P3 : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = P0 + P1 + P2 + P3) (h0 : (biancaRealignF P0).rank ≤ 1)
    (h3 : P3.rank ≤ 1) :
    N * (N - 1) ≤ 2 * (P1.rank + P2.rank + 1) ∧
      N * (N - 1) ≤ 2 * ((biancaRealignF P1).rank + (biancaRealignF P2).rank + 1) ∧
      N ≤ P1.rank + (biancaRealignF P2).rank ∧ N ≤ P2.rank + (biancaRealignF P1).rank := by
  have hM : biancaSwapF F (Fin N) = P0 + (P1 + P2) + P3 := by rw [h]; abel
  obtain ⟨hr, hc⟩ := greta_three_piece_middle_floor N P0 (P1 + P2) P3 hM h0 h3
  have hr12 := bianca_matrix_rank_add_le P1 P2
  rw [greta_realignF_add] at hc
  have hc12 := bianca_matrix_rank_add_le (biancaRealignF P1) (biancaRealignF P2)
  refine ⟨by omega, by omega, ?_, ?_⟩
  · have hs := nadia_minsumF_ge_N_add_two N hN (P1 + P3) (P0 + P2) (by rw [h]; abel)
    have e1 := bianca_matrix_rank_add_le P1 P3
    rw [greta_realignF_add] at hs
    have e2 := bianca_matrix_rank_add_le (biancaRealignF P0) (biancaRealignF P2)
    omega
  · have hs := nadia_minsumF_ge_N_add_two N hN (P2 + P3) (P0 + P1) (by rw [h]; abel)
    have e1 := bianca_matrix_rank_add_le P2 P3
    rw [greta_realignF_add] at hs
    have e2 := bianca_matrix_rank_add_le (biancaRealignF P0) (biancaRealignF P1)
    omega
end

/-! ## unit P4_exact_shapes_one_five_excluded -/
section
-- T380 (piece of Milo's T378, P(4) = 7): the dual of Greta's R62 corollary by realignment, so the shapes
-- (rank B, OS C) = (1, k) and (r, 1) with total N(N-1)/2 are impossible for exact splits SWAP_N = B + C (every field).

/-- **Dual R62 corollary**: in SWAP_N = B + C over any field, rank B ≤ 1 forces OS C ≥ N(N-1)/2. -/
theorem daria_os_ge_of_rank_le_one_field {F : Type*} [Field F] (N : ℕ)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hB : B.rank ≤ 1) : N * (N - 1) ≤ 2 * (biancaRealignF C).rank := by
  have h' : biancaSwapF F (Fin N) = biancaRealignF C + biancaRealignF B := by
    rw [← greta_realignF_swapF, h, greta_realignF_add, add_comm]
  exact greta_rank_ge_of_os_le_one_field N (biancaRealignF C) (biancaRealignF B) h'
    (by rw [uri_realignF_realignF]; exact hB)

/-- **T378 shapes (1,5) and (5,1) excluded** at N = 4 over any field: rank B = 1 forces OS C ≥ 6, and OS C = 1
forces rank B ≥ 6, so neither gives total 6. -/
theorem daria_P4_shapes_one_five {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : biancaSwapF F (Fin 4) = B + C) :
    (B.rank = 1 → 6 ≤ (biancaRealignF C).rank) ∧ ((biancaRealignF C).rank = 1 → 6 ≤ B.rank) := by
  constructor
  · intro hB
    have := daria_os_ge_of_rank_le_one_field 4 B C h (by omega)
    omega
  · intro hC
    have := greta_rank_ge_of_os_le_one_field 4 B C h (by omega)
    omega
end

/-! ## unit P4_seven_assembly_from_two_pieces -/
section
-- T378 (P(4) = 7), assembly: over any field, every EXACT split SWAP_4 = B + C has rank B + OS C ≥ 7, given
-- (i)  OS C ≤ 2 forces rank B ≥ 5  (Gideon's (i), my piece), and
-- (ii) rank B ≤ 3 and OS C ≤ 3 cannot both hold  (Nadia's T381).
-- The other total-6 shapes are closed here: (1,5)/(5,1) by T380, (2,4) by (i) on the realigned split, (0,6)/(6,0) by
-- rank SWAP_4 = 16; totals ≤ 5 by Nadia's N + 2 floor.

/-- SWAP_N is an involution over any field. -/
theorem daria_swapF_mul_self {F : Type*} [Field F] (N : ℕ) :
    biancaSwapF F (Fin N) * biancaSwapF F (Fin N) = 1 := by
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (p.2, p.1)]
  · by_cases h : p = q
    · subst h; simp [biancaSwapF]
    · simp only [biancaSwapF, Matrix.of_apply, true_and, and_self, if_true, one_mul, if_neg h]
      split_ifs with h1
      · exact absurd (Prod.ext h1.2.symm h1.1.symm).symm h
      · rfl
  · intro b _ hb
    have : ¬ (p.1 = b.2 ∧ p.2 = b.1) := fun hc => hb (Prod.ext hc.2.symm hc.1.symm)
    simp [biancaSwapF, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- SWAP_N has full rank N^2 over any field. -/
theorem daria_swapF_rank {F : Type*} [Field F] (N : ℕ) : (biancaSwapF F (Fin N)).rank = N * N := by
  have hdet : (biancaSwapF F (Fin N)).det * (biancaSwapF F (Fin N)).det = 1 := by
    rw [← Matrix.det_mul, daria_swapF_mul_self, Matrix.det_one]
  have hu : IsUnit (biancaSwapF F (Fin N)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one _ hdet
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_prod, Fintype.card_fin]

/-- A matrix of rank 0 is zero. -/
theorem daria_eq_zero_of_rank_zero {F : Type*} [Field F] {n : ℕ}
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) F) (h : M.rank = 0) : M = 0 := by
  unfold Matrix.rank at h
  rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

/-- **T378 assembly**: given (i) and (ii), every exact split SWAP_4 = B + C over any field has rank B + OS C ≥ 7. -/
theorem daria_P4_ge_seven_of_pieces {F : Type*} [Field F]
    (hi : ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F, biancaSwapF F (Fin 4) = B + C →
      (biancaRealignF C).rank ≤ 2 → 5 ≤ B.rank)
    (hii : ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F, biancaSwapF F (Fin 4) = B + C →
      B.rank ≤ 3 → (biancaRealignF C).rank ≤ 3 → False)
    (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F) (h : biancaSwapF F (Fin 4) = B + C) :
    7 ≤ B.rank + (biancaRealignF C).rank := by
  have h6 := nadia_minsumF_ge_N_add_two 4 le_rfl B C h
  -- the realigned split SWAP = R C + R B
  have hR : biancaSwapF F (Fin 4) = biancaRealignF C + biancaRealignF B := by
    rw [← greta_realignF_swapF, h, greta_realignF_add, add_comm]
  have hRB : (biancaRealignF (biancaRealignF B)).rank = B.rank := by rw [uri_realignF_realignF]
  have hsw : (biancaSwapF F (Fin 4)).rank = 16 := by rw [daria_swapF_rank]
  have h15 := daria_P4_shapes_one_five B C h
  by_contra hlt
  push_neg at hlt
  have hr6 : B.rank ≤ 6 := by omega
  rcases (by omega : B.rank = 0 ∨ B.rank = 1 ∨ B.rank = 2 ∨ B.rank = 3 ∨ B.rank = 4 ∨ B.rank = 5 ∨ B.rank = 6)
    with h0 | h1 | h2 | h3 | h4 | h5 | h6'
  · -- (0, 6): B = 0, so C = SWAP and OS C = 16
    have hB0 := daria_eq_zero_of_rank_zero B h0
    have hC : C = biancaSwapF F (Fin 4) := by rw [h, hB0, zero_add]
    have : (biancaRealignF C).rank = 16 := by rw [hC, greta_realignF_swapF, hsw]
    omega
  · have := h15.1 h1; omega
  · -- (2, 4): (i) on the realigned split
    have := hi (biancaRealignF C) (biancaRealignF B) hR (by rw [hRB]; omega)
    omega
  · exact hii B C h (by omega) (by omega)
  · have := hi B C h (by omega); omega
  · have := h15.2 (by omega); omega
  · -- (6, 0): R C = 0, so C = 0, B = SWAP, rank 16
    have hRC0 := daria_eq_zero_of_rank_zero (biancaRealignF C) (by omega)
    have hC0 : C = 0 := by
      rw [← uri_realignF_realignF C, hRC0]
      ext a b
      simp [biancaRealignF]
    have hB : B = biancaSwapF F (Fin 4) := by rw [h, hC0, add_zero]
    rw [hB, hsw] at h6'
    omega
end

/-! ## unit slice_exists_double_corank_type_C -/
section

open Matrix

/-- T381 step (Nadia): in any exact split with slice widths 2 <= r, k < N (N >= 3), some slice has BOTH Y^T X and Q^T P singular
(a 'type C' slice). Otherwise every slice is of type A or B and the no-mixed and pure-case lemmas of T331 give a contradiction. -/
theorem nadia_slice_exists_double_corank {F : Type*} [Field F] {N r k : ℕ} (hN : 3 ≤ N)
    (hr : 2 ≤ r) (hrN : r < N) (hk : 2 ≤ k) (hkN : k < N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :
    ∃ z, ((Y z)ᵀ * X z).det = 0 ∧ ((Q z)ᵀ * P z).det = 0 := by
  classical
  by_contra hcon
  have hAB0 : ∀ z, ((Q z)ᵀ * P z).det ≠ 0 ∨ ((Y z)ᵀ * X z).det ≠ 0 := by
    intro z
    by_cases h1 : ((Y z)ᵀ * X z).det = 0
    · left; intro h2; exact hcon ⟨z, h1, h2⟩
    · right; exact h1
  have hr2 : 2 ≤ r := hr
  have hk2 : 2 ≤ k := hk
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
  have hAB := hAB0
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
  rcases nadia_no_mixed_slices (by omega) CX CP (fun z => ((Q z)ᵀ * P z).det ≠ 0)
      (fun z => ((Y z)ᵀ * X z).det ≠ 0) hAB hR3 hR1 hR2 hCX with hA | hB
  · refine nadia_pure_slices_false (by omega) CP CX (fun a b hab => hR1 b a (hA b) (Ne.symm hab))
      (fun z => by rw [sup_comm]; exact hR3 z) hCX ?_
    have hu : IsUnit ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA _))
    have h1 : ((Q ⟨0, by omega⟩)ᵀ * P ⟨0, by omega⟩).rank = k := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Q ⟨0, by omega⟩)ᵀ (P ⟨0, by omega⟩)
    show 2 ≤ (P ⟨0, by omega⟩).rank
    omega
  · refine nadia_pure_slices_false (by omega) CX CP (fun a b hab => hR2 a b (hB b) hab) hR3 hCP ?_
    have hu : IsUnit ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hB _))
    have h1 : ((Y ⟨0, by omega⟩)ᵀ * X ⟨0, by omega⟩).rank = r := by
      simpa using Matrix.rank_of_isUnit _ hu
    have h2 := Matrix.rank_mul_le_right (Y ⟨0, by omega⟩)ᵀ (X ⟨0, by omega⟩)
    show 2 ≤ (X ⟨0, by omega⟩).rank
    omega
end

/-! ## unit slice_full_width_rank_slices_singular -/
section
open Matrix

/-- **Lemma A (T360 / T378 (4,2) brick)**: in the slice form of an exact split SWAP_N = B + C (Nadia's T331/T381 format)
with full-width rank slices (r = N) and OS width k with 2k ≤ N (N ≥ 3), no rank slice X_z is invertible.
Proof: on K = ker (Q z)ᵀ every Y_wᵀ (w ≠ z) vanishes; then (Q y)ᵀ embeds K into ker P_u and K ⊆ range P_u, so
2 dim K ≤ k, while dim K ≥ N - k ≥ k. -/
theorem ada_slice_X_singular {F : Type*} [Field F] {N k : ℕ} (hN : 3 ≤ N) (hk : 2 * k ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin N) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N) : (X z).det = 0 := by
  classical
  by_contra hz
  have hu : IsUnit (X z).det := isUnit_iff_ne_zero.mpr hz
  have hcard : 1 < (Finset.univ.erase z).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨y, hy, u, hu', hyu⟩ := Finset.one_lt_card.1 hcard
  have hyz : y ≠ z := Finset.ne_of_mem_erase hy
  have huz : u ≠ z := Finset.ne_of_mem_erase hu'
  have key : ∀ a b (v : Fin N → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  let K : Submodule F (Fin N → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  have hKv : ∀ v ∈ K, (Q z)ᵀ *ᵥ v = 0 := fun v hv => hv
  have hY : ∀ w, z ≠ w → ∀ v ∈ K, (Y w)ᵀ *ᵥ v = 0 := by
    intro w hw v hv
    have h := congrArg (· *ᵥ v) (ho z w hw)
    simp only [key, Matrix.zero_mulVec] at h
    rw [hKv v hv, Matrix.mulVec_zero, add_zero] at h
    have e : (X z)⁻¹ *ᵥ (X z *ᵥ ((Y w)ᵀ *ᵥ v)) = (Y w)ᵀ *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    rw [← e, h, Matrix.mulVec_zero]
  have hdiag : ∀ a, z ≠ a → ∀ v ∈ K, v = P a *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a ha v hv
    have h := congrArg (· *ᵥ v) (hd a)
    have h' : X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
      rw [← key]; simpa using h
    rw [hY a ha v hv, Matrix.mulVec_zero, zero_add] at h'
    exact h'.symm
  have hb : ∀ v ∈ K, P u *ᵥ ((Q y)ᵀ *ᵥ v) = 0 := by
    intro v hv
    have h := congrArg (· *ᵥ v) (ho y u hyu)
    have h' : X y *ᵥ ((Y u)ᵀ *ᵥ v) + P u *ᵥ ((Q y)ᵀ *ᵥ v) = 0 := by
      rw [← key]; simpa using h
    rwa [hY u (Ne.symm huz) v hv, Matrix.mulVec_zero, zero_add] at h'
  -- dim K ≥ N - k
  have hK : N ≤ Module.finrank F K + k := by
    have h := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
    have hr : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) ≤ k := by
      have := Submodule.finrank_le (LinearMap.range ((Q z)ᵀ.mulVecLin))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show N ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin) + k
    omega
  -- (Q y)ᵀ embeds K into ker P_u
  have h1 : Module.finrank F K ≤ Module.finrank F (LinearMap.ker (P u).mulVecLin) := by
    let φ : K →ₗ[F] LinearMap.ker (P u).mulVecLin :=
      LinearMap.codRestrict _ (((Q y)ᵀ.mulVecLin).comp K.subtype) (fun v => by
        show (P u).mulVecLin ((Q y)ᵀ.mulVecLin v.1) = 0
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
        exact hb v.1 v.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    intro v w hvw
    have e : (Q y)ᵀ *ᵥ v.1 = (Q y)ᵀ *ᵥ w.1 := by
      exact congrArg Subtype.val hvw
    apply Subtype.ext
    rw [hdiag y (Ne.symm hyz) v.1 v.2, hdiag y (Ne.symm hyz) w.1 w.2, e]
  -- K ⊆ range P_u
  have h2 : Module.finrank F K ≤ Module.finrank F (LinearMap.range (P u).mulVecLin) := by
    refine Submodule.finrank_mono ?_
    intro v hv
    exact ⟨(Q u)ᵀ *ᵥ v, by simpa using (hdiag u (Ne.symm huz) v hv).symm⟩
  have h3 := LinearMap.finrank_range_add_finrank_ker ((P u).mulVecLin)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h3
  omega

/-- Lemma A for the column slices Y (by transposing the slice system). -/
theorem ada_slice_Y_singular {F : Type*} [Field F] {N k : ℕ} (hN : 3 ≤ N) (hk : 2 * k ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin N) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N) : (Y z).det = 0 := by
  refine ada_slice_X_singular hN hk Y X Q P (fun y => ?_) (fun y u hyu => ?_) z
  · have h := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
  · have h := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
end

/-! ## unit T386_slice_os_widths_rank_ge_two -/
section
open Matrix

/-- **Lemma B (T386, Lena)**: in the slice form of an exact split SWAP_N = B + C (Nadia's / Ada's hd/ho format) with
rank width r ≤ N, OS width k with 2k ≤ N and N ≥ 4, no OS slice Q_z has rank ≤ 1.
Proof: V := ker (Q z)ᵀ has dim ≥ N - 1; on V, X_z Y_zᵀ = id, so dim ker X_z ≤ 1; ho(z,w) puts Y_wᵀ V in ker X_z;
hd(u) gives V ≤ X_u(ker X_z) + range P_u, so P_u is injective (and N = 4, k = 2); then on V the map P_u Q_yᵀ has range
in X_y(ker X_z) and kernel in X_y(ker X_z) (by hd(y)), so dim V ≤ 2 < 3. -/
theorem lena_slice_Q_rank_ge_two {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hk : 2 * k ≤ N) (hr : r ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N) : 2 ≤ (Q z).rank := by
  classical
  by_contra hlt
  push Not at hlt
  have hcard : 1 < (Finset.univ.erase z).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨y, hy, u, hu', hyu⟩ := Finset.one_lt_card.1 hcard
  have hyz : y ≠ z := Finset.ne_of_mem_erase hy
  have huz : u ≠ z := Finset.ne_of_mem_erase hu'
  have key : ∀ a b (v : Fin N → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hdv : ∀ a (v : Fin N → F), X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
    intro a v
    rw [← key, hd a, Matrix.one_mulVec]
  have hov : ∀ a b, a ≠ b → ∀ (v : Fin N → F), X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) = 0 := by
    intro a b hab v
    rw [← key, ho a b hab, Matrix.zero_mulVec]
  let V : Submodule F (Fin N → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  let KX : Submodule F (Fin r → F) := LinearMap.ker (X z).mulVecLin
  have hV0 : ∀ v ∈ V, (Q z)ᵀ *ᵥ v = 0 := fun v hv => hv
  -- dim V ≥ N - 1
  have hV : N ≤ Module.finrank F V + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
    have hr1 : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) ≤ 1 := by
      have e : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) = (Q z)ᵀ.rank := rfl
      rw [e, Matrix.rank_transpose]; omega
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show N ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin) + 1
    omega
  -- ho(z, w): Y_wᵀ V ⊆ ker X_z
  have hY : ∀ w, z ≠ w → ∀ v ∈ V, (Y w)ᵀ *ᵥ v ∈ KX := by
    intro w hw v hv
    have h := hov z w hw v
    rw [hV0 v hv, Matrix.mulVec_zero, add_zero] at h
    show (X z).mulVecLin ((Y w)ᵀ *ᵥ v) = 0
    rw [Matrix.mulVecLin_apply]; exact h
  -- dim ker X_z ≤ 1
  have hKX : Module.finrank F KX ≤ 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((X z).mulVecLin)
    have hle : Module.finrank F V ≤ Module.finrank F (LinearMap.range (X z).mulVecLin) := by
      refine Submodule.finrank_mono ?_
      intro v hv
      refine ⟨(Y z)ᵀ *ᵥ v, ?_⟩
      have h1 := hdv z v
      rw [hV0 v hv, Matrix.mulVec_zero, add_zero] at h1
      rw [Matrix.mulVecLin_apply]; exact h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show Module.finrank F (LinearMap.ker (X z).mulVecLin) ≤ 1
    omega
  -- hd(u): V ≤ X_u(ker X_z) + range P_u
  have hPu : N ≤ Module.finrank F (LinearMap.range (P u).mulVecLin) + 2 := by
    have hsub : V ≤ Submodule.map (X u).mulVecLin KX ⊔ LinearMap.range (P u).mulVecLin := by
      intro v hv
      have h1 := hdv u v
      rw [← h1]
      refine Submodule.add_mem_sup (Submodule.mem_map.mpr ⟨(Y u)ᵀ *ᵥ v, hY u (Ne.symm huz) v hv, rfl⟩)
        (LinearMap.mem_range.mpr ⟨(Q u)ᵀ *ᵥ v, rfl⟩)
    have h1 := Submodule.finrank_mono hsub
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.map (X u).mulVecLin KX)
      (LinearMap.range (P u).mulVecLin)
    have h3 : Module.finrank F (Submodule.map (X u).mulVecLin KX) ≤ Module.finrank F KX :=
      Submodule.finrank_map_le _ _
    omega
  have hrk : Module.finrank F (LinearMap.range (P u).mulVecLin) ≤ k := by
    have := LinearMap.finrank_range_le (P u).mulVecLin
    simpa using this
  -- so P_u is injective
  have hker : LinearMap.ker (P u).mulVecLin = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker ((P u).mulVecLin)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hinj : ∀ w : Fin k → F, P u *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hw' : w ∈ LinearMap.ker (P u).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hw
    rw [hker] at hw'
    exact (Submodule.mem_bot F).mp hw'
  -- f = P_u Q_yᵀ on V
  let f : V →ₗ[F] (Fin N → F) := ((P u).mulVecLin ∘ₗ (Q y)ᵀ.mulVecLin) ∘ₗ V.subtype
  have hrange : Module.finrank F (LinearMap.range f) ≤ 1 := by
    have hle : LinearMap.range f ≤ Submodule.map (X y).mulVecLin KX := by
      rintro _ ⟨v, rfl⟩
      have h := hov y u hyu v.1
      refine Submodule.mem_map.mpr ⟨-((Y u)ᵀ *ᵥ v.1), KX.neg_mem (hY u (Ne.symm huz) v.1 v.2), ?_⟩
      show X y *ᵥ (-((Y u)ᵀ *ᵥ v.1)) = P u *ᵥ ((Q y)ᵀ *ᵥ v.1)
      rw [Matrix.mulVec_neg]
      linear_combination -h
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank F (Submodule.map (X y).mulVecLin KX) ≤ Module.finrank F KX :=
      Submodule.finrank_map_le _ _
    omega
  have hkerf : Module.finrank F (LinearMap.ker f) ≤ 1 := by
    let φ : LinearMap.ker f →ₗ[F] Submodule.map (X y).mulVecLin KX :=
      LinearMap.codRestrict _ (V.subtype ∘ₗ (LinearMap.ker f).subtype) (fun v => by
        have hv0 : P u *ᵥ ((Q y)ᵀ *ᵥ (v.1).1) = 0 := v.2
        have hq : (Q y)ᵀ *ᵥ (v.1).1 = 0 := hinj _ hv0
        have h1 := hdv y (v.1).1
        rw [hq, Matrix.mulVec_zero, add_zero] at h1
        exact Submodule.mem_map.mpr ⟨(Y y)ᵀ *ᵥ (v.1).1, hY y (Ne.symm hyz) _ (v.1).2, h1⟩)
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := φ) (by
      intro a b hab
      have e : ((φ a : Submodule.map (X y).mulVecLin KX) : Fin N → F) = φ b := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext e))
    have h2 : Module.finrank F (Submodule.map (X y).mulVecLin KX) ≤ Module.finrank F KX :=
      Submodule.finrank_map_le _ _
    omega
  have h := LinearMap.finrank_range_add_finrank_ker f
  omega

/-- Lemma B for the rank-width slices P (by transposing the slice system): no P_z has rank ≤ 1. -/
theorem lena_slice_P_rank_ge_two {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hk : 2 * k ≤ N) (hr : r ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N) : 2 ≤ (P z).rank := by
  refine lena_slice_Q_rank_ge_two hN hk hr Y X Q P (fun y => ?_) (fun y u hyu => ?_) z
  · have h := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
  · have h := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
end

/-! ## unit T386_full_width_slices_os_two_impossible -/
section
open Matrix

/-- **Lemma C (T386, Lena)**: the full-width slice system (r = N) with OS width k ≤ 2, 2k ≤ N, N ≥ 4 has no solution.
Proof: Ada's Lemma A gives w_i ≠ 0 with w_i X_i = 0; Lemma B makes every Q_i injective, so ho(i,u) gives w_i P_u = 0
(u ≠ i) and hd(i) gives w_i P_i ≠ 0. Then g ↦ Σ g_i w_i is injective on {g : g_u = 0} and lands in the left kernel of
P_u, so rank P_u ≤ 1, against Lemma B for P. -/
theorem lena_slice_full_width_os_two_false {F : Type*} [Field F] {N k : ℕ} (hN : 4 ≤ N) (hk : 2 * k ≤ N)
    (hk2 : k ≤ 2) (X Y : Fin N → Matrix (Fin N) (Fin N) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : False := by
  classical
  have hQ := lena_slice_Q_rank_ge_two hN hk le_rfl X Y P Q hd ho
  have hP2 := lena_slice_P_rank_ge_two hN hk le_rfl X Y P Q hd ho
  -- every Q_i is injective
  have hQinj : ∀ i (c : Fin k → F), Q i *ᵥ c = 0 → c = 0 := by
    intro i c hc
    have h := LinearMap.finrank_range_add_finrank_ker ((Q i).mulVecLin)
    have e : Module.finrank F (LinearMap.range ((Q i).mulVecLin)) = (Q i).rank := rfl
    have hw := Matrix.rank_le_width (Q i)
    have hq := hQ i
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    have hker : LinearMap.ker (Q i).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hc' : c ∈ LinearMap.ker (Q i).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hc
    rw [hker] at hc'
    exact (Submodule.mem_bot F).mp hc'
  -- left kernel vectors of the X_i (Lemma A)
  have hw : ∀ i, ∃ v : Fin N → F, v ≠ 0 ∧ v ᵥ* X i = 0 := by
    intro i
    obtain ⟨v, hv, h⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (ada_slice_X_singular (by omega) hk X Y P Q hd ho i)
    exact ⟨v, hv, h⟩
  choose w hw0 hwX using hw
  have hdw : ∀ i, (w i ᵥ* P i) ᵥ* (Q i)ᵀ = w i := by
    intro i
    have h := congrArg (fun M => w i ᵥ* M) (hd i)
    simp only [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hwX i, Matrix.zero_vecMul, zero_add,
      Matrix.vecMul_one] at h
    exact h
  have how : ∀ i u, i ≠ u → (w i ᵥ* P u) ᵥ* (Q i)ᵀ = 0 := by
    intro i u hiu
    have h := congrArg (fun M => w i ᵥ* M) (ho i u hiu)
    simp only [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hwX i, Matrix.zero_vecMul, zero_add,
      Matrix.vecMul_zero] at h
    exact h
  have hP0 : ∀ i u, i ≠ u → w i ᵥ* P u = 0 := by
    intro i u hiu
    apply hQinj i
    rw [← Matrix.vecMul_transpose]
    exact how i u hiu
  have hP1 : ∀ i, w i ᵥ* P i ≠ 0 := by
    intro i h
    apply hw0 i
    rw [← hdw i, h, Matrix.zero_vecMul]
  have hsum : ∀ (g : Fin N → F) j, (g ᵥ* Matrix.of w) ᵥ* P j = g j • (w j ᵥ* P j) := by
    intro g j
    have e : ∀ s, ((g ᵥ* Matrix.of w) ᵥ* P j) s = ∑ i, g i * (w i ᵥ* P j) s := by
      intro s
      rw [Matrix.vecMul_vecMul]
      rfl
    ext s
    rw [e s, Finset.sum_eq_single j]
    · simp [Pi.smul_apply, smul_eq_mul]
    · intro i _ hij
      rw [hP0 i j hij]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  let u : Fin N := ⟨0, by omega⟩
  have hD : N ≤ Module.finrank F (LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)) + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)
    have h1 : Module.finrank F (LinearMap.range (LinearMap.proj u : (Fin N → F) →ₗ[F] F)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (LinearMap.proj u : (Fin N → F) →ₗ[F] F))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let φ : LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F) →ₗ[F] LinearMap.ker (P u)ᵀ.mulVecLin :=
    LinearMap.codRestrict (LinearMap.ker (P u)ᵀ.mulVecLin)
      ((Matrix.of w).vecMulLinear ∘ₗ (LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)).subtype)
      (fun g => by
        have hg : g.1 u = 0 := g.2
        show (P u)ᵀ.mulVecLin (g.1 ᵥ* Matrix.of w) = 0
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, hsum, hg, zero_smul])
  have hinjφ : Function.Injective φ := by
    intro a b hab
    have e := congrArg Subtype.val hab
    change a.1 ᵥ* Matrix.of w = b.1 ᵥ* Matrix.of w at e
    apply Subtype.ext
    funext j
    have h1 := congrArg (fun v => v ᵥ* P j) e
    simp only [hsum] at h1
    exact smul_left_injective F (hP1 j) h1
  have h1 := LinearMap.finrank_le_finrank_of_injective hinjφ
  have h2 := LinearMap.finrank_range_add_finrank_ker ((P u)ᵀ.mulVecLin)
  have e3 : Module.finrank F (LinearMap.range ((P u)ᵀ.mulVecLin)) = (P u).rank := by
    rw [← Matrix.rank_transpose]; rfl
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  have := hP2 u
  omega
end

/-! ## unit T386_P4_hi_os_two_forces_rank_five -/
section
open Matrix

/-- Padding a `Fin r`-indexed sum by zeros to `Fin n` (r ≤ n) does not change it. -/
theorem lena_sum_fin_pad {M : Type*} [AddCommMonoid M] {r n : ℕ} (hr : r ≤ n) (f : Fin r → M) :
    ∑ i : Fin n, (if h : i.1 < r then f ⟨i.1, h⟩ else 0) = ∑ i : Fin r, f i := by
  have h1 := Fin.sum_univ_eq_sum_range (fun m => if h : m < r then f ⟨m, h⟩ else 0) n
  have h2 := Fin.sum_univ_eq_sum_range (fun m => if h : m < r then f ⟨m, h⟩ else 0) r
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hr,
    Finset.sum_eq_zero (s := Finset.Ico r n) (fun m hm => dif_neg (by
      have := (Finset.mem_Ico.mp hm).1; omega)), add_zero, ← h2]
  exact Finset.sum_congr rfl (fun i _ => dif_pos i.2)

/-- **T386 = piece `hi` of Daria's T378 assembly (Lena)**: over any field, every exact split SWAP_4 = B + C with
OS C ≤ 2 has rank B ≥ 5. No Le Bruyn-Procesi: the split gives (zero-padded) full-width slices r = 4, k = 2, which
Lemma C (lena_slice_full_width_os_two_false; Ada's Lemma A + Lena's Lemma B) refutes when rank B ≤ 4.
The split-to-slice step copies Nadia's T331 block (nadia_minsumF_ge_N_add_two), with credit. -/
theorem lena_P4_hi {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : biancaSwapF F (Fin 4) = B + C) (hC : (biancaRealignF C).rank ≤ 2) : 5 ≤ B.rank := by
  classical
  by_contra hlt
  push Not at hlt
  have hB4 : B.rank ≤ 4 := by omega
  obtain ⟨U, V, hB⟩ := bianca_exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hCm⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hent : ∀ x y u v : Fin 4, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if x = v ∧ y = u then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hCm (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = biancaRealignF C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  -- zero padding to r = 4, k = 2
  let U' : Fin 4 → (Fin 4 × Fin 4 → F) := fun i => if hi : i.1 < B.rank then U ⟨i.1, hi⟩ else 0
  let V' : Fin 4 → (Fin 4 × Fin 4 → F) := fun i => if hi : i.1 < B.rank then V ⟨i.1, hi⟩ else 0
  let P' : Fin 2 → (Fin 4 × Fin 4 → F) := fun i =>
    if hi : i.1 < (biancaRealignF C).rank then P ⟨i.1, hi⟩ else 0
  let Q' : Fin 2 → (Fin 4 × Fin 4 → F) := fun i =>
    if hi : i.1 < (biancaRealignF C).rank then Q ⟨i.1, hi⟩ else 0
  have hpB : ∀ p q, ∑ i : Fin 4, U' i p * V' i q = ∑ i, U i p * V i q := by
    intro p q
    rw [← lena_sum_fin_pad hB4 (fun i => U i p * V i q)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.1 < B.rank
    · simp [U', V', hi]
    · simp [U', V', hi]
  have hpC : ∀ p q, ∑ i : Fin 2, P' i p * Q' i q = ∑ i, P i p * Q i q := by
    intro p q
    rw [← lena_sum_fin_pad hC (fun i => P i p * Q i q)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.1 < (biancaRealignF C).rank
    · simp [P', Q', hi]
    · simp [P', Q', hi]
  let X : Fin 4 → Matrix (Fin 4) (Fin 4) F := fun y => Matrix.of fun x i => U' i (x, y)
  let Y : Fin 4 → Matrix (Fin 4) (Fin 4) F := fun u => Matrix.of fun v i => V' i (u, v)
  let PP : Fin 4 → Matrix (Fin 4) (Fin 2) F := fun u => Matrix.of fun x l => P' l (x, u)
  let QQ : Fin 4 → Matrix (Fin 4) (Fin 2) F := fun y => Matrix.of fun v l => Q' l (y, v)
  have hslice : ∀ y u, X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = if y = u then 1 else 0 := by
    intro y u
    ext x v
    have := hent x y u v
    rw [← hpB, ← hpC] at this
    simp only [X, Y, PP, QQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    by_cases hyu : y = u
    · subst hyu
      by_cases hxv : x = v
      · subst hxv; simp
      · simp [hxv]
    · simp [hyu]
  have hd : ∀ y, X y * (Y y)ᵀ + PP y * (QQ y)ᵀ = 1 := fun y => by simpa using hslice y y
  have ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = 0 := fun y u hyu => by
    simpa [hyu] using hslice y u
  exact lena_slice_full_width_os_two_false le_rfl (by norm_num) le_rfl X Y PP QQ hd ho

/-- The dual shape by realignment (Daria's (2,4) pattern): rank B ≤ 2 forces OS C ≥ 5. -/
theorem lena_P4_hi_dual {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : biancaSwapF F (Fin 4) = B + C) (hB : B.rank ≤ 2) : 5 ≤ (biancaRealignF C).rank := by
  have hR : biancaSwapF F (Fin 4) = biancaRealignF C + biancaRealignF B := by
    rw [← greta_realignF_swapF, h, greta_realignF_add, add_comm]
  exact lena_P4_hi (biancaRealignF C) (biancaRealignF B) hR (by rw [uri_realignF_realignF]; exact hB)
end

/-! ## unit P4_seven_socket_from_hii_alone -/
section

/-- **P(4) >= 7 from hii alone (L4 socket, D22)**: with Lena's `lena_P4_hi` (piece hi, VERIFIED) plugged into Daria's
assembly, every exact split SWAP_4 = B + C over any field has rank B + OS C >= 7 as soon as the (3,3) shape is excluded
(piece hii, Nadia's T381). Once hii is in Lean, P(4) = 7 is this theorem applied to it. -/
theorem pavel_P4_ge_seven_of_hii {F : Type*} [Field F]
    (hii : ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F, biancaSwapF F (Fin 4) = B + C → B.rank ≤ 3 →
      (biancaRealignF C).rank ≤ 3 → False)
    (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F) (h : biancaSwapF F (Fin 4) = B + C) :
    7 ≤ B.rank + (biancaRealignF C).rank :=
  daria_P4_ge_seven_of_pieces (fun B C h hC => lena_P4_hi B C h hC) hii B C h
end

/-! ## unit T381_FINAL_hii_and_P4_seven_from_C2 -/
section
open Matrix
-- T381/T378 FINAL (Nadia's plan, brick FINAL; Pavel Q291: under T378). Over ANY field F, with K = FractionRing (MvPolynomial (Fin 4) F)
-- and the generic vector xg: hii follows from C2 (case rank F(xg) ≤ 2 and rank Q(xg) ≤ 2, Nadia's brick, taken here as hC2);
-- the case rank F(xg) = 3 is nadia_T381_C3, the case rank Q(xg) = 3 is nadia_T381_C3 on the τσ system (Q, P, Y, X).
-- Then P(4) ≥ 7 by pavel_P4_ge_seven_of_hii.

/-- **FINAL, hii from C2** (any field). -/
theorem daria_hii_of_C2 {F : Type*} [Field F]
    (hC2 : ∀ X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F,
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) → (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) →
      (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2 →
      (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (Q a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2 → False)
    (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F) (h : biancaSwapF F (Fin 4) = B + C)
    (hB : B.rank ≤ 3) (hC : (biancaRealignF C).rank ≤ 3) : False := by
  obtain ⟨X, Y, P, Q, hd, ho⟩ := daria_slices_of_split 4 3 3 B C h hB hC
  have g1 : ∀ l : Fin 4 → F, (∑ u, algebraMap F (FractionRing (MvPolynomial (Fin 4) F)) (l u) *
      (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) u) = 0 →
      l = 0 := fun l hl => lena_G1_lin l hl
  have g2 : ∀ (A : Matrix (Fin 4) (Fin 4) F) (c : FractionRing (MvPolynomial (Fin 4) F)),
      (A.map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))) *ᵥ
        (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) =
        c • (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) →
      ∃ a : F, A = a • 1 := fun A c hc => lena_G1_scalar A c hc
  by_cases hF : 3 ≤ (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))
      (MvPolynomial.X u)) a • (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank
  · exact nadia_T381_C3 (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) X Y P Q hd ho _ g1 g2
      (fun v hv hY => daria_W (N := 4) (r := 3) (k := 3) le_rfl rfl X Y P Q hd ho v hv hY) hF
  by_cases hQ : 3 ≤ (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F))
      (MvPolynomial.X u)) a • (Q a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank
  · obtain ⟨hd', ho'⟩ := daria_slice_sigma X Y P Q hd ho
    have hd2 : ∀ y, Q y * (P y)ᵀ + Y y * (X y)ᵀ = 1 := fun y => by rw [add_comm]; exact hd' y
    have ho2 : ∀ y u, y ≠ u → Q y * (P u)ᵀ + Y u * (X y)ᵀ = 0 := fun y u hyu => by
      rw [add_comm]; exact ho' u y (Ne.symm hyu)
    exact nadia_T381_C3 (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) Q P Y X hd2 ho2 _ g1 g2
      (fun v hv hP => daria_W (N := 4) (r := 3) (k := 3) le_rfl rfl Q P Y X hd2 ho2 v hv hP) hQ
  · exact hC2 X Y P Q hd ho (by omega) (by omega)

/-- **P(4) ≥ 7 from C2** (any field): every exact split SWAP_4 = B + C has rank B + OS C ≥ 7, given Nadia's C2. -/
theorem daria_P4_ge_seven_of_C2 {F : Type*} [Field F]
    (hC2 : ∀ X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F,
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) → (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) →
      (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2 →
      (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (Q a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2 → False)
    (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F) (h : biancaSwapF F (Fin 4) = B + C) :
    7 ≤ B.rank + (biancaRealignF C).rank :=
  pavel_P4_ge_seven_of_hii (fun B' C' h' hB hC => daria_hii_of_C2 hC2 B' C' h' hB hC) B C h
end

/-! ## unit T381_S_rank_split_any_xy -/
section
open Matrix
-- T381 L2, first half (Nadia's generic-rank split f + q ≥ N, g + p ≥ N, shared/T381_generic_rank_reduction_Nadia.md line 9):
-- from Eq.1 (daria_slice_eq1), at ANY x, y with x ⬝ y ≠ 0 (over ℚ: y = x ≠ 0; over K = FractionRing (MvPolynomial ..):
-- the generic vector, x ⬝ x = Σ X_i² ≠ 0), rank F(x) + rank Q(x) ≥ N and rank G(y) + rank P(y) ≥ N.

/-- **Generic-rank split (slice form).** If x ⬝ y ≠ 0 then N ≤ rank F(x) + rank Q(x) and N ≤ rank G(y) + rank P(y),
with F(x) = Σ x_a X_a, Q(x) = Σ x_a Q_a, G(y) = Σ y_b Y_b, P(y) = Σ y_b P_b. -/
theorem daria_slice_rank_split {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (x y : Fin N → F) (hxy : ∑ a, x a * y a ≠ 0) :
    N ≤ (∑ a, x a • X a).rank + (∑ a, x a • Q a).rank ∧
      N ≤ (∑ b, y b • Y b).rank + (∑ b, y b • P b).rank := by
  have e := daria_slice_eq1 X Y P Q hd ho x y
  have hu : IsUnit ((∑ a, x a * y a) • (1 : Matrix (Fin N) (Fin N) F)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hxy)
  have hN : ((∑ a, x a * y a) • (1 : Matrix (Fin N) (Fin N) F)).rank = N := by
    rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
  rw [← e] at hN
  have hadd := bianca_matrix_rank_add_le ((∑ a, x a • X a) * (∑ b, y b • Y b)ᵀ)
    ((∑ b, y b • P b) * (∑ a, x a • Q a)ᵀ)
  rw [hN] at hadd
  constructor
  · have h1 := Matrix.rank_mul_le_left (∑ a, x a • X a) (∑ b, y b • Y b)ᵀ
    have h2 := Matrix.rank_mul_le_right (∑ b, y b • P b) (∑ a, x a • Q a)ᵀ
    rw [Matrix.rank_transpose] at h2
    omega
  · have h1 := Matrix.rank_mul_le_right (∑ a, x a • X a) (∑ b, y b • Y b)ᵀ
    have h2 := Matrix.rank_mul_le_left (∑ b, y b • P b) (∑ a, x a • Q a)ᵀ
    rw [Matrix.rank_transpose] at h1
    omega

/-- **Over ℚ (or any ordered field)**: for every x ≠ 0, rank F(x) + rank Q(x) ≥ N and rank G(x) + rank P(x) ≥ N. -/
theorem daria_slice_rank_split_rat {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) ℚ) (P Q : Fin N → Matrix (Fin N) (Fin k) ℚ)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (x : Fin N → ℚ) (hx : x ≠ 0) :
    N ≤ (∑ a, x a • X a).rank + (∑ a, x a • Q a).rank ∧
      N ≤ (∑ b, x b • Y b).rank + (∑ b, x b • P b).rank := by
  apply daria_slice_rank_split X Y P Q hd ho x x
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (funext hc)
  have hpos : 0 < ∑ a, x a * x a := by
    have hle : x i * x i ≤ ∑ a, x a * x a :=
      Finset.single_le_sum (f := fun a => x a * x a) (fun a _ => mul_self_nonneg (x a)) (Finset.mem_univ i)
    have : 0 < x i * x i := mul_self_pos.mpr hi
    linarith
  exact ne_of_gt hpos
end

/-! ## unit P4_ge_seven_every_field -/
section
open Matrix

/-- C2 step (a) over any field (Nadia, T453): if rank Fx(x) ≤ 2 and rank Qx(x) ≤ 2 for every x, then Qx(x)ᵀ Fx(x) = 0 for every x. -/
theorem nadia_C2_QF_zero_any {F : Type*} [Field F] (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → F, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → F, (∑ a, x a • Q a).rank ≤ 2)
    (x : Fin 4 → F) : (∑ a, x a • Q a)ᵀ * (∑ a, x a • X a) = 0 := by
  classical
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
    by_contra hall; push Not at hall; exact hx (funext hall)
  have hsplit := (daria_slice_rank_split X Y P Q hd ho x (Pi.single b 1) (by simpa [Pi.single_apply] using hb)).1
  have hFx1 := hF x
  have hQx1 := hQ x
  set Fx := ∑ a, x a • X a with hFx
  set Qx := ∑ a, x a • Q a with hQx
  have hF2 : Fx.rank = 2 := by omega
  have hQ2 : Qx.rank = 2 := by omega
  have hle : LinearMap.ker Qxᵀ.mulVecLin ≤ LinearMap.range Fx.mulVecLin := by
    intro n hn
    have hn' : Qxᵀ *ᵥ n = 0 := hn
    have hK := daria_lemmaK X Y P Q hd ho x n hn' b
    refine ⟨(x b)⁻¹ • ((Y b)ᵀ *ᵥ n), ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_smul, hK, smul_smul, inv_mul_cancel₀ hb, one_smul]
  have hdimK : Module.finrank F (LinearMap.ker Qxᵀ.mulVecLin) = 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Qxᵀ.mulVecLin
    have h2 : Qxᵀ.rank = Module.finrank F (LinearMap.range Qxᵀ.mulVecLin) := rfl
    rw [Matrix.rank_transpose, hQ2] at h2
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    omega
  have hdimR : Module.finrank F (LinearMap.range Fx.mulVecLin) = 2 := hF2
  have heq : LinearMap.ker Qxᵀ.mulVecLin = LinearMap.range Fx.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimK, hdimR])
  ext i j
  have hw : Fx *ᵥ (Pi.single j 1) ∈ LinearMap.ker Qxᵀ.mulVecLin := by rw [heq]; exact ⟨_, rfl⟩
  have hw' : Qxᵀ *ᵥ (Fx *ᵥ (Pi.single j 1)) = 0 := hw
  rw [Matrix.mulVec_mulVec] at hw'
  have := congrFun hw' i
  simpa [Matrix.mulVec_single] using this


/-- C2 entry identity (Nadia): ((∑ y_b Y_b)ᵀ (∑ x_a X_a))[s,u] = y ⬝ (G_s F_u) x with G_s[b,j] = Y_b[j,s], F_u[j,a] = X_a[j,u]. -/
theorem nadia_C2_entry_any {F : Type*} [Field F] (X Y : Fin 4 → Matrix (Fin 4) (Fin 3) F) (x y : Fin 4 → F) (s u : Fin 3) :
    ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u =
      y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u)) *ᵥ x) := by
  have lhs : ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u =
      ∑ j, ∑ b, ∑ a, (y b * Y b j s) * (x a * X a j u) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul_sum]
  have rhs : y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u)) *ᵥ x) =
      ∑ b, ∑ a, ∑ j, y b * (Y b j s * X a j u * x a) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  rw [lhs, rhs, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- C2 step (b) (Nadia): in the all-≤2 case, Fx(x) (Y(y)ᵀ Fx(x)) = (x·y) Fx(x). -/
theorem nadia_C2_FYF_any {F : Type*} [Field F] (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → F, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → F, (∑ a, x a • Q a).rank ≤ 2)
    (x y : Fin 4 → F) :
    (∑ a, x a • X a) * ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) = (∑ a, x a * y a) • (∑ a, x a • X a) := by
  have e := congrArg (· * (∑ a, x a • X a)) (daria_slice_eq1 X Y P Q hd ho x y)
  have hQF := nadia_C2_QF_zero_any X Y P Q hd ho hF hQ x
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hQF, Matrix.mul_zero, add_zero] at e
  exact e

/-- T453 (Nadia): the all-≤2 case of hii is impossible over ANY field, pointwise form. -/
theorem nadia_T381_C2_any {F : Type*} [Field F] (X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hF : ∀ x : Fin 4 → F, (∑ a, x a • X a).rank ≤ 2) (hQ : ∀ x : Fin 4 → F, (∑ a, x a • Q a).rank ≤ 2) : False := by
  classical
  -- A s u as an explicit matrix
  have hAform : ∀ (s u : Fin 3) (x y : Fin 4 → F),
      y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) F) else 0)) *ᵥ x) =
      ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) s u - (if s = u then ∑ a, x a * y a else 0) := by
    intro s u x y
    rw [nadia_C2_entry_any X Y x y s u, Matrix.sub_mulVec, dotProduct_sub]
    split_ifs with h
    · rw [Matrix.one_mulVec]
      congr 1
      simp only [dotProduct]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    · rw [Matrix.zero_mulVec, dotProduct_zero]
  -- the columns of M(x,y) are in ker Fx(x)
  have hcol : ∀ (u : Fin 3) (x y : Fin 4 → F), (∑ a, x a • X a) *ᵥ (fun s => y ⬝ᵥ
      ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) F) else 0)) *ᵥ x)) = 0 := by
    intro u x y
    have hv : (fun s => y ⬝ᵥ ((Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
        (if s = u then (1 : Matrix (Fin 4) (Fin 4) F) else 0)) *ᵥ x)) =
        ((∑ b, y b • Y b)ᵀ * (∑ a, x a • X a)) *ᵥ Pi.single u 1 - (∑ a, x a * y a) • Pi.single u 1 := by
      funext s
      rw [hAform]
      by_cases h : s = u
      · subst h; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      · simp [h, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, Matrix.mulVec_sub, Matrix.mulVec_mulVec, nadia_C2_FYF_any X Y P Q hd ho hF hQ x y, Matrix.mulVec_smul,
      Matrix.smul_mulVec, sub_self]
  -- the matrices A s u, the rank of Fx(x) at x ≠ 0, and the row matrices L y0 u
  set A : Fin 3 → Fin 3 → Matrix (Fin 4) (Fin 4) F := fun s u =>
    Matrix.of (fun b j => Y b j s) * Matrix.of (fun j a => X a j u) -
      (if s = u then (1 : Matrix (Fin 4) (Fin 4) F) else 0) with hA
  have hrank2 : ∀ x : Fin 4 → F, x ≠ 0 → (∑ a, x a • X a).rank = 2 := by
    intro x hx
    obtain ⟨b, hb⟩ : ∃ b, x b ≠ 0 := by
      by_contra hall; push Not at hall; exact hx (funext hall)
    have h1 := (daria_slice_rank_split X Y P Q hd ho x (Pi.single b 1) (by simpa [Pi.single_apply] using hb)).1
    have h2 := hF x
    have h3 := hQ x
    omega
  set L : (Fin 4 → F) → Fin 3 → Matrix (Fin 3) (Fin 4) F :=
    fun y0 u => Matrix.of (fun s a => ∑ b, y0 b * A s u b a) with hL
  have hLx : ∀ y0 u x, L y0 u *ᵥ x = fun s => y0 ⬝ᵥ (A s u *ᵥ x) := by
    intro y0 u x
    funext s
    simp only [hL, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => by ring))
  have hLker : ∀ y0 u x, (∑ a, x a • X a) *ᵥ (L y0 u *ᵥ x) = 0 := by
    intro y0 u x
    rw [hLx]
    exact hcol u x y0
  -- the finish needs rank (A s u) ≤ 1 for all s, u
  suffices hfin : ∀ s u, (A s u).rank ≤ 1 by
    exact nadia_T381_offdiag_rank_one_false (fun s => Matrix.of (fun b j => Y b j s))
      (fun u => Matrix.of (fun j a => X a j u)) hfin
  by_cases hall : ∀ y0 u, L y0 u = 0
  · intro s u
    have hz : A s u = 0 := by
      ext b a
      have := congrFun (congrFun (hall (Pi.single b 1) u) s) a
      simpa [hL, Pi.single_apply] using this
    rw [hz, Matrix.rank_zero]; omega
  push Not at hall
  obtain ⟨y0, u0, hL0⟩ := hall
  set L0 := L y0 u0 with hL0def
  by_cases hpair : ∃ s1 s2, LinearIndependent F ![L0 s1, L0 s2]
  swap
  · -- rank L0 ≤ 1: a common kernel vector of all X_a, killed by daria_W_X
    exfalso
    push Not at hpair
    have hr1 := nadia_rank_le_one_of_rows_dep L0 hpair
    obtain ⟨w, r, hwr⟩ := xenia_eq_vecMulVec_of_rank_le_one L0 hr1
    have hw : w ≠ 0 := by
      intro h0; apply hL0; rw [hwr, h0]; ext i j; simp [Matrix.vecMulVec_apply]
    have hr : r ≠ 0 := by
      intro h0; apply hL0; rw [hwr, h0]; ext i j; simp [Matrix.vecMulVec_apply]
    have hV : ∀ x : Fin 4 → F, (r ⬝ᵥ x) • (∑ a, x a • X a) *ᵥ w = 0 := by
      intro x
      have := hLker y0 u0 x
      have hwr' : L y0 u0 = Matrix.vecMulVec w r := hwr
      rw [hwr', xenia_vecMulVec_mulVec, Matrix.mulVec_smul] at this
      exact this
    have hall0 := xenia_V1 X w r hr hV
    apply daria_W_X (N := 4) (r := 3) (k := 3) (by norm_num) (by norm_num) X Y P Q hd ho w hw
    intro a
    have := hall0 (Pi.single a 1)
    simpa [Pi.single_apply] using this
  obtain ⟨s1, s2, hI⟩ := hpair
  -- parallel identity
  have hpar : ∀ s s' u (x y : Fin 4 → F),
      (y ⬝ᵥ (A s u *ᵥ x)) * (L0 s' ⬝ᵥ x) = (y ⬝ᵥ (A s' u *ᵥ x)) * (L0 s ⬝ᵥ x) := by
    intro s s' u x y
    by_cases hx : x = 0
    · subst hx; simp
    have hk := nadia_ker_one_parallel (∑ a, x a • X a) (hrank2 x hx) (fun t => y ⬝ᵥ (A t u *ᵥ x))
      (L0 *ᵥ x) (hcol u x y) (hLker y0 u0 x) s s'
    simpa [Matrix.mulVec] using hk
  have hne1 : L0 s1 ≠ 0 := hI.ne_zero 0
  have hne2 : L0 s2 ≠ 0 := hI.ne_zero 1
  intro s u
  by_cases hs0 : L0 s = 0
  · refine (xenia_H0 (A s u) 0 (L0 s2) (L0 s1) (LinearIndependent.pair_symm_iff.mp hI) ?_).2
    intro x y
    have := hpar s s1 u x y
    rw [hs0, zero_dotProduct, mul_zero] at this
    rw [this, Matrix.zero_mulVec, dotProduct_zero, zero_mul]
  by_cases hi1 : LinearIndependent F ![L0 s, L0 s1]
  · exact (xenia_H0 (A s u) (A s1 u) (L0 s) (L0 s1) hi1 (fun x y => hpar s s1 u x y)).2
  have hi2 : LinearIndependent F ![L0 s, L0 s2] := by
    by_contra hi2
    obtain ⟨c1, hc1⟩ := nadia_pair_dep (L0 s) (L0 s1) hs0 hi1
    obtain ⟨c2, hc2⟩ := nadia_pair_dep (L0 s) (L0 s2) hs0 hi2
    have hc10 : c1 ≠ 0 := by intro h0; apply hne1; rw [hc1, h0, zero_smul]
    rw [LinearIndependent.pair_iff] at hI
    have := hI c2 (-c1) (by rw [hc1, hc2, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, add_neg_cancel])
    exact hc10 (neg_eq_zero.mp this.2)
  exact (xenia_H0 (A s u) (A s2 u) (L0 s) (L0 s2) hi2 (fun x y => hpar s s2 u x y)).2

/-- T453 (Nadia): P(4) ≥ 7 over EVERY field: every exact split SWAP_4 = B + C has rank B + OS C ≥ 7.
Daria's generic FINAL with the field-free C2 and the left-inverse rank transfer. -/
theorem nadia_P4_ge_seven_any_field {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : biancaSwapF F (Fin 4) = B + C) : 7 ≤ B.rank + (biancaRealignF C).rank :=
  daria_P4_ge_seven_of_C2 (F := F)
    (fun X Y P Q hd ho hFg hQg => nadia_T381_C2_any X Y P Q hd ho
      (fun x => nadia_rank_transfer_le_two_any X hFg x) (fun x => nadia_rank_transfer_le_two_any Q hQg x)) B C h
end

/-! ## unit T381_C2_rank_transfer_generic_to_points -/
section
open Matrix

/-- Over Q: if det(Mᵀ M) = 0 for a 4 × 3 matrix M, then rank M ≤ 2. -/
theorem nadia_rank_le_two_of_gram_det {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (M : Matrix (Fin 4) (Fin 3) F) (h : (Mᵀ * M).det = 0) : M.rank ≤ 2 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h
  have hMv : M *ᵥ v = 0 := by
    have e : (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = 0 := by
      have := congrArg (fun w => v ⬝ᵥ w) hv
      simp only [dotProduct_zero] at this
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
      rw [dotProduct_comm]; exact this
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg ((M *ᵥ v) i))).mp e
    funext i
    exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ i))
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 : M.rank = Module.finrank F (LinearMap.range M.mulVecLin) := rfl
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  have hk : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    intro hb
    apply hv0
    have : v ∈ LinearMap.ker M.mulVecLin := hMv
    rw [hb] at this
    exact (Submodule.mem_bot F).mp this
  have hk1 : 1 ≤ Module.finrank F (LinearMap.ker M.mulVecLin) :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => hk (Submodule.finrank_eq_zero.mp h0))
  omega

/-- C2 transfer (Nadia): rank ≤ 2 at the generic point over K = FractionRing (MvPolynomial (Fin 4) F) gives rank ≤ 2
at every rational point. -/
theorem nadia_rank_transfer_le_two {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (X : Fin 4 → Matrix (Fin 4) (Fin 3) F)
    (h : (∑ a, (fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u)) a •
        (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F)))).rank ≤ 2)
    (x0 : Fin 4 → F) : (∑ a, x0 a • X a).rank ≤ 2 := by
  classical
  set xg : Fin 4 → FractionRing (MvPolynomial (Fin 4) F) :=
    fun u => algebraMap (MvPolynomial (Fin 4) F) (FractionRing (MvPolynomial (Fin 4) F)) (MvPolynomial.X u) with hxg
  set Fp : Matrix (Fin 4) (Fin 3) (MvPolynomial (Fin 4) F) :=
    ∑ a, (MvPolynomial.X a : MvPolynomial (Fin 4) F) • (X a).map (MvPolynomial.C : F →+* MvPolynomial (Fin 4) F) with hFp
  set FK := ∑ a, xg a • (X a).map (algebraMap F (FractionRing (MvPolynomial (Fin 4) F))) with hFK
  set p : MvPolynomial (Fin 4) F := (Fpᵀ * Fp).det with hp
  set g : MvPolynomial (Fin 4) F →+* FractionRing (MvPolynomial (Fin 4) F) :=
    (MvPolynomial.aeval (R := F) xg).toRingHom with hg
  have hmapK : Fp.map g = FK := by
    ext i j
    simp [Fp, FK, g, Matrix.sum_apply, Matrix.map_apply, map_sum, MvPolynomial.aeval_X]
  have hmap0 : Fp.map (MvPolynomial.eval x0) = ∑ a, x0 a • X a := by
    ext i j
    simp [Fp, Matrix.sum_apply, Matrix.map_apply, map_sum]
  have hdetK : g p = (FKᵀ * FK).det := by
    rw [hp, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, hmapK]
  have hK0 : (FKᵀ * FK).det = 0 := by
    by_contra hne
    have hu : IsUnit (FKᵀ * FK) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
    have h3 : (FKᵀ * FK).rank = 3 := by rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]
    have h4 := Matrix.rank_mul_le_right FKᵀ FK
    have h5 : FK.rank ≤ 2 := h
    omega
  have hpz : MvPolynomial.aeval (R := F) xg p = 0 := by
    have : g p = 0 := by rw [hdetK, hK0]
    simpa [g] using this
  have he := lena_G1_spec p hpz x0
  have hdet0 : ((∑ a, x0 a • X a)ᵀ * (∑ a, x0 a • X a)).det = 0 := by
    rw [← he, hp, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, hmap0]
  exact nadia_rank_le_two_of_gram_det _ hdet0
end

/-! ## unit T381_FINAL_P4_from_pointwise_C2 -/
section
open Matrix
-- T381/T378 FINAL over any ORDERED field (ℚ included) with Nadia's POINTWISE C2 (her C2a binder): P(4) ≥ 7 from
-- C2 : (∀ x, rank F(x) ≤ 2) → (∀ x, rank Q(x) ≤ 2) → False, via daria_hii_of_C2 and Nadia's nadia_rank_transfer_le_two.

/-- **FINAL (ordered field)**: P(4) ≥ 7 from Nadia's pointwise C2. -/
theorem daria_P4_ge_seven_of_pointwise_C2 {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hC2 : ∀ X Y P Q : Fin 4 → Matrix (Fin 4) (Fin 3) F,
      (∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) → (∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) →
      (∀ x : Fin 4 → F, (∑ a, x a • X a).rank ≤ 2) → (∀ x : Fin 4 → F, (∑ a, x a • Q a).rank ≤ 2) → False)
    (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F) (h : biancaSwapF F (Fin 4) = B + C) :
    7 ≤ B.rank + (biancaRealignF C).rank :=
  daria_P4_ge_seven_of_C2 (fun X Y P Q hd ho hF hQ =>
    hC2 X Y P Q hd ho (nadia_rank_transfer_le_two X hF) (nadia_rank_transfer_le_two Q hQ)) B C h
end

/-! ## unit P4_ge_seven_over_Q -/
section
open Matrix

/-- P(4) ≥ 7 over Q (T381 / T378): every exact split SWAP_4 = B + C over Q has rank B + OS C ≥ 7.
Daria's pointwise FINAL applied to Nadia's C2. With the border value 6 (swap4_border_rank3_os3_exact_tables)
this is an exact/border gap at N = 4. -/
theorem nadia_P4_ge_seven_rat (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℚ)
    (h : biancaSwapF ℚ (Fin 4) = B + C) : 7 ≤ B.rank + (biancaRealignF C).rank :=
  daria_P4_ge_seven_of_pointwise_C2 (F := ℚ)
    (fun X Y P Q hd ho hF hQ => nadia_T381_C2 X Y P Q hd ho hF hQ) B C h
end

/-! ## unit P4_eq_seven_upper_split_any_field -/
section
open Matrix
-- T378 upper side (CTO/CEO on Q302: new statement): over EVERY field, SWAP_N = (SWAP_N - I) + I with
-- SWAP_N - I = U V, U (ab) p = [ab = p] - [ab.swap = p], V p (cd) = [cd.swap = p] - [cd = p], p over the pairs x < y,
-- and realign(I) = vec(I) vec(I)ᵀ (OS 1). So P(N) ≤ #{x < y} + 1 = N(N-1)/2 + 1, and P(4) ≤ 7.

/-- Summing an indicator over the pairs p = (x, y) with x < y. -/
theorem daria_sum_lt_pairs_ind {N : ℕ} {F : Type*} [AddCommMonoid F] (q : Fin N × Fin N)
    (g : {p : Fin N × Fin N // p.1 < p.2} → F) :
    (∑ p, if q = p.1 then g p else 0) = if h : q.1 < q.2 then g ⟨q, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨q, h⟩]
    · simp
    · intro p _ hp
      rw [if_neg]
      intro hq
      exact hp (Subtype.ext hq.symm)
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun p _ => if_neg fun hq => h ?_
    rw [hq]; exact p.2

/-- **SWAP_N - I factors through the pairs x < y** (any field). -/
theorem daria_swap_sub_one_factor {F : Type*} [Field F] (N : ℕ) :
    (Matrix.of fun (ab : Fin N × Fin N) (p : {p : Fin N × Fin N // p.1 < p.2}) =>
        ((if ab = p.1 then 1 else 0) - (if ab.swap = p.1 then 1 else 0) : F)) *
      (Matrix.of fun (p : {p : Fin N × Fin N // p.1 < p.2}) (cd : Fin N × Fin N) =>
        ((if cd.swap = p.1 then 1 else 0) - (if cd = p.1 then 1 else 0) : F)) =
      biancaSwapF F (Fin N) - 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [daria_sum_lt_pairs_ind (a, b), daria_sum_lt_pairs_ind ((a, b).swap)]
  simp only [biancaSwapF, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, Prod.swap_prod_mk, Prod.mk.injEq]
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [dif_pos hab, dif_neg (not_lt.mpr hab.le)]
    by_cases h1 : a = d <;> by_cases h2 : b = c <;> by_cases h3 : a = c <;> by_cases h4 : b = d <;>
      simp_all [eq_comm]
  · subst hab
    by_cases h1 : a = d <;> by_cases h3 : a = c <;> simp_all [eq_comm]
  · rw [dif_neg (not_lt.mpr hab.le), dif_pos hab]
    by_cases h1 : a = d <;> by_cases h2 : b = c <;> by_cases h3 : a = c <;> by_cases h4 : b = d <;>
      simp_all [eq_comm]

/-- realign(I) is the outer product vec(I) vec(I)ᵀ. -/
theorem daria_realign_one {F : Type*} [Field F] (N : ℕ) :
    biancaRealignF (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) F) =
      vecMulVec (fun p : Fin N × Fin N => if p.1 = p.2 then (1 : F) else 0)
        (fun p : Fin N × Fin N => if p.1 = p.2 then (1 : F) else 0) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [biancaRealignF, Matrix.of_apply, Matrix.one_apply, vecMulVec_apply, Prod.mk.injEq]
  by_cases h1 : a = b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- **Upper bound, every field**: SWAP_N = B + C with rank B ≤ #{x < y} and OS C ≤ 1. -/
theorem daria_minsumF_le_pairs_add_one {F : Type*} [Field F] (N : ℕ) :
    ∃ B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F, biancaSwapF F (Fin N) = B + C ∧
      B.rank ≤ Fintype.card {p : Fin N × Fin N // p.1 < p.2} ∧ (biancaRealignF C).rank ≤ 1 := by
  refine ⟨biancaSwapF F (Fin N) - 1, 1, (sub_add_cancel _ _).symm, ?_, ?_⟩
  · rw [← daria_swap_sub_one_factor N]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)
  · rw [daria_realign_one]
    exact Matrix.rank_vecMulVec_le _ _

/-- **P(4) ≤ 7** (every field): the split (SWAP_4 - I) + I has rank 6 + OS 1. -/
theorem daria_P4_le_seven {F : Type*} [Field F] :
    ∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F, biancaSwapF F (Fin 4) = B + C ∧
      B.rank + (biancaRealignF C).rank ≤ 7 := by
  obtain ⟨B, C, h, hB, hC⟩ := daria_minsumF_le_pairs_add_one (F := F) 4
  have hcard : Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by decide
  exact ⟨B, C, h, by omega⟩

/-- **P(4) = 7 over ℚ**: the minimum of rank B + OS C over exact splits SWAP_4 = B + C is attained and equals 7
(lower bound: Nadia's nadia_P4_ge_seven_rat; upper bound: the split (SWAP_4 - I) + I). -/
theorem daria_P4_eq_seven :
    (∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℚ, biancaSwapF ℚ (Fin 4) = B + C ∧
      B.rank + (biancaRealignF C).rank = 7) ∧
    ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℚ, biancaSwapF ℚ (Fin 4) = B + C →
      7 ≤ B.rank + (biancaRealignF C).rank := by
  obtain ⟨B, C, h, hle⟩ := daria_P4_le_seven (F := ℚ)
  exact ⟨⟨B, C, h, le_antisymm hle (nadia_P4_ge_seven_rat B C h)⟩, nadia_P4_ge_seven_rat⟩
end

/-! ## unit slice_injective_rank_slice_os_kernel_bound -/
section
open Matrix

/-- **Lemma B'(a) (T420, piece h5 of P(5) ≥ 8)**: in a slice system with N ≥ 3, if the rank slice X_z is injective and
V = ker (Q z)ᵀ has 2 dim V > k, there is no solution. Proof: Y_uᵀ V = 0 for u ≠ z; then V ⊆ range P_u (diag u) and
(Q y)ᵀ embeds V into ker P_u (off (y,u), diag y), so 2 dim V ≤ k. -/
theorem ada_slice_Ba {F : Type*} [Field F] {N r k : ℕ} (hN : 3 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N)
    (hXz : ∀ c : Fin r → F, X z *ᵥ c = 0 → c = 0)
    (hdim : k < 2 * Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin)) : False := by
  classical
  have key : ∀ a b (v : Fin N → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hdv : ∀ a (v : Fin N → F), X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
    intro a v
    rw [← key, hd a, Matrix.one_mulVec]
  have hov : ∀ a b, a ≠ b → ∀ (v : Fin N → F), X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) = 0 := by
    intro a b hab v
    rw [← key, ho a b hab, Matrix.zero_mulVec]
  have hcard : 1 < (Finset.univ.erase z).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨y, hy, u, hu', hyu⟩ := Finset.one_lt_card.1 hcard
  have hyz : y ≠ z := Finset.ne_of_mem_erase hy
  have huz : u ≠ z := Finset.ne_of_mem_erase hu'
  let V : Submodule F (Fin N → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  have hY : ∀ w, w ≠ z → ∀ v ∈ V, (Y w)ᵀ *ᵥ v = 0 := by
    intro w hw v hv
    have h := hov z w (Ne.symm hw) v
    have hq : (Q z)ᵀ *ᵥ v = 0 := hv
    rw [hq, Matrix.mulVec_zero, add_zero] at h
    exact hXz _ h
  have hdiag : ∀ a, a ≠ z → ∀ v ∈ V, v = P a *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a ha v hv
    have h := hdv a v
    rw [hY a ha v hv, Matrix.mulVec_zero, zero_add] at h
    exact h.symm
  have hb : ∀ v ∈ V, P u *ᵥ ((Q y)ᵀ *ᵥ v) = 0 := by
    intro v hv
    have h := hov y u hyu v
    rwa [hY u huz v hv, Matrix.mulVec_zero, zero_add] at h
  have h1 : Module.finrank F V ≤ Module.finrank F (LinearMap.ker (P u).mulVecLin) := by
    let φ : V →ₗ[F] LinearMap.ker (P u).mulVecLin :=
      LinearMap.codRestrict _ (((Q y)ᵀ.mulVecLin).comp V.subtype) (fun v => by
        show (P u).mulVecLin ((Q y)ᵀ.mulVecLin v.1) = 0
        rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
        exact hb v.1 v.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    intro v w hvw
    have e : (Q y)ᵀ *ᵥ v.1 = (Q y)ᵀ *ᵥ w.1 := congrArg Subtype.val hvw
    apply Subtype.ext
    rw [hdiag y hyz v.1 v.2, hdiag y hyz w.1 w.2, e]
  have h2 : Module.finrank F V ≤ Module.finrank F (LinearMap.range (P u).mulVecLin) := by
    refine Submodule.finrank_mono ?_
    intro v hv
    exact ⟨(Q u)ᵀ *ᵥ v, by rw [Matrix.mulVecLin_apply]; exact (hdiag u huz v hv).symm⟩
  have h3 := LinearMap.finrank_range_add_finrank_ker ((P u).mulVecLin)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h3
  have hV : Module.finrank F V = Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin) := rfl
  omega
end

/-! ## unit h5_Bprime_glue_Q_rank_three_N5 -/
section
-- Sprint D (T435, for Ada's h5 = T420): the B' GLUE at N = 5, r = 4, k = 3. In the slice system (hd, ho) of a split
-- with rank widths 4 and OS widths 3, every Q z has rank 3, given Ada's case (b) as the hypothesis hBb. Case rank X z = 4
-- is ada_slice_Ba (X z injective, 2 dim ker (Q z)^T >= 6 > 3). Any field.
open Matrix

/-- **B' glue (N = 5, r = 4, k = 3).** If rank Q z ≤ 2 then ker (Q z)^T (dim ≥ 3) lies in range X z, so rank X z ∈ {3, 4};
rank 4 is excluded by ada_slice_Ba and rank 3 by the hypothesis hBb (Ada's B'(b)). -/
theorem nolan_P5_Q_rank_three {F : Type*} [Field F]
    (X Y : Fin 5 → Matrix (Fin 5) (Fin 4) F) (P Q : Fin 5 → Matrix (Fin 5) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hBb : ∀ z, (X z).rank = 3 → (Q z).rank ≤ 2 → False) (z : Fin 5) :
    3 ≤ (Q z).rank := by
  by_contra hlt
  have hQ2 : (Q z).rank ≤ 2 := by omega
  have hrn := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
  rw [Module.finrank_fin_fun] at hrn
  have hrk : Module.finrank F (LinearMap.range (Q z)ᵀ.mulVecLin) = (Q z).rank :=
    (rfl : Module.finrank F (LinearMap.range (Q z)ᵀ.mulVecLin) = ((Q z)ᵀ).rank).trans (Matrix.rank_transpose _)
  have hVX : LinearMap.ker (Q z)ᵀ.mulVecLin ≤ LinearMap.range (X z).mulVecLin := by
    intro v hv
    have hv' : (Q z)ᵀ *ᵥ v = 0 := by
      have h0 := LinearMap.mem_ker.mp hv
      rwa [Matrix.mulVecLin_apply] at h0
    have h := congrArg (fun M => M *ᵥ v) (hd z)
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero,
      add_zero] at h
    exact LinearMap.mem_range.mpr ⟨(Y z)ᵀ *ᵥ v, by simpa using h⟩
  have hmono := Submodule.finrank_mono hVX
  have hXr : (X z).rank = Module.finrank F (LinearMap.range (X z).mulVecLin) := rfl
  have hX4 : (X z).rank ≤ 4 := Matrix.rank_le_width (X z)
  rcases (by omega : (X z).rank = 3 ∨ (X z).rank = 4) with h | h
  · exact hBb z h hQ2
  · refine ada_slice_Ba (by norm_num) X Y P Q hd ho z ?_ (by omega)
    intro c hc
    have hrn2 := LinearMap.finrank_range_add_finrank_ker ((X z).mulVecLin)
    rw [Module.finrank_fin_fun] at hrn2
    have hk0 : Module.finrank F (LinearMap.ker (X z).mulVecLin) = 0 := by omega
    have hker : LinearMap.ker (X z).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hk0
    have hcm : c ∈ LinearMap.ker (X z).mulVecLin := by simpa using hc
    rw [hker] at hcm
    simpa using hcm
end

/-! ## unit h5_Bprime_glue_dual_P_rank_three_N5 -/
section
-- Sprint D (T435, for Ada's h5 = T420): the DUAL B' glue at N = 5, r = 4, k = 3. The transposed slice system (Y, X, Q, P)
-- satisfies hd/ho (transposes of hd y and ho u y), so nolan_P5_Q_rank_three gives 3 <= rank P z from the transposed case-(b)
-- hypothesis. This is ada_slice_C5's hP2 (every P u has rank >= 2) in h5. Any field.
open Matrix

/-- **Dual B' glue (N = 5, r = 4, k = 3).** -/
theorem nolan_P5_P_rank_three {F : Type*} [Field F]
    (X Y : Fin 5 → Matrix (Fin 5) (Fin 4) F) (P Q : Fin 5 → Matrix (Fin 5) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hBb' : ∀ z, (Y z).rank = 3 → (P z).rank ≤ 2 → False) (z : Fin 5) :
    3 ≤ (P z).rank := by
  refine nolan_P5_Q_rank_three Y X Q P (fun y => ?_) (fun y u hyu => ?_) hBb' z
  · have h := congrArg Matrix.transpose (hd y)
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using h
  · have h := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
end

/-! ## unit h5_Bprime_b_rank_three_slice_impossible -/
section
open Matrix

/-- **Lemma B'(b) (T420, piece h5 of P(5) ≥ 8)**: in the slice system at N = 5 with rank width 4 and OS width 3, no
slice has rank X_z = 3 together with rank Q_z ≤ 2. Proof: V = ker (Q z)ᵀ = range X_z (dim 3), Pm = X_z Y_zᵀ projects onto
V, ker X_z = span κ. With W_u = range (Pm P_u) ⊆ V: if some W_u = V, then Pm P_u is injective and (Q y)ᵀ V has dim ≤ 1, so
diag(y) puts V in a space of dim ≤ 2; otherwise x'_y = Pm X_y κ lies in W_u for y ≠ u but x'_u ∉ W_u, so the four x'_y
are independent in V (dim 3). -/
theorem ada_slice_Bb {F : Type*} [Field F]
    (X Y : Fin 5 → Matrix (Fin 5) (Fin 4) F) (P Q : Fin 5 → Matrix (Fin 5) (Fin 3) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin 5)
    (hX3 : (X z).rank = 3) (hQ2 : (Q z).rank ≤ 2) : False := by
  classical
  have key : ∀ a b (v : Fin 5 → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hdv : ∀ a (v : Fin 5 → F), X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
    intro a v
    rw [← key, hd a, Matrix.one_mulVec]
  have hov : ∀ a b, a ≠ b → ∀ (v : Fin 5 → F), X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) = 0 := by
    intro a b hab v
    rw [← key, ho a b hab, Matrix.zero_mulVec]
  let V : Submodule F (Fin 5 → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  let R : Submodule F (Fin 5 → F) := LinearMap.range (X z).mulVecLin
  have hVq : ∀ v ∈ V, (Q z)ᵀ *ᵥ v = 0 := fun v hv => hv
  -- dim V ≥ 3
  have hV3 : 3 ≤ Module.finrank F V := by
    have h := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
    have e : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) = (Q z).rank := by
      rw [← Matrix.rank_transpose]; rfl
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show 3 ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin)
    omega
  -- V ≤ R, so V = R and dim V = 3
  have hVR : V ≤ R := by
    intro v hv
    have h := hdv z v
    rw [hVq v hv, Matrix.mulVec_zero, add_zero] at h
    exact ⟨(Y z)ᵀ *ᵥ v, by rw [Matrix.mulVecLin_apply]; exact h⟩
  have hR3 : Module.finrank F R = 3 := hX3
  have hVeqR : V = R := Submodule.eq_of_le_of_finrank_le hVR (by omega)
  have hVle3 : Module.finrank F V ≤ 3 := by rw [hVeqR]; omega
  -- the projection Pm
  let Pm : Matrix (Fin 5) (Fin 5) F := X z * (Y z)ᵀ
  have hPmV : ∀ v ∈ V, Pm *ᵥ v = v := by
    intro v hv
    have h := hdv z v
    rw [hVq v hv, Matrix.mulVec_zero, add_zero] at h
    show (X z * (Y z)ᵀ) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec]; exact h
  have hPmR : ∀ x, Pm *ᵥ x ∈ V := by
    intro x
    rw [hVeqR]
    exact ⟨(Y z)ᵀ *ᵥ x, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
  -- ker X_z is a line span κ
  let KX : Submodule F (Fin 4 → F) := LinearMap.ker (X z).mulVecLin
  have hKX : Module.finrank F KX = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((X z).mulVecLin)
    have e : Module.finrank F (LinearMap.range ((X z).mulVecLin)) = (X z).rank := rfl
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show Module.finrank F (LinearMap.ker (X z).mulVecLin) = 1
    omega
  obtain ⟨κ0, -, hκ⟩ := finrank_eq_one_iff'.1 hKX
  let κ : Fin 4 → F := κ0
  have hYκ : ∀ u, u ≠ z → ∀ v ∈ V, ∃ c : F, (Y u)ᵀ *ᵥ v = c • κ := by
    intro u hu v hv
    have h := hov z u (Ne.symm hu) v
    rw [hVq v hv, Matrix.mulVec_zero, add_zero] at h
    have hm : (Y u)ᵀ *ᵥ v ∈ KX := by
      show (X z).mulVecLin ((Y u)ᵀ *ᵥ v) = 0
      rw [Matrix.mulVecLin_apply]; exact h
    obtain ⟨c, hc⟩ := hκ ⟨_, hm⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  let x' : Fin 5 → (Fin 5 → F) := fun y => Pm *ᵥ (X y *ᵥ κ)
  -- projected equations
  have hdiagπ : ∀ u (v : Fin 5 → F), v ∈ V →
      v = Pm *ᵥ (X u *ᵥ ((Y u)ᵀ *ᵥ v)) + (Pm * P u) *ᵥ ((Q u)ᵀ *ᵥ v) := by
    intro u v hv
    have h := congrArg (fun w => Pm *ᵥ w) (hdv u v)
    simp only [Matrix.mulVec_add, hPmV v hv] at h
    have e : (Pm * P u) *ᵥ ((Q u)ᵀ *ᵥ v) = Pm *ᵥ (P u *ᵥ ((Q u)ᵀ *ᵥ v)) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [e]
    exact h.symm
  have hoffπ : ∀ y u, y ≠ u → ∀ (v : Fin 5 → F),
      Pm *ᵥ (X y *ᵥ ((Y u)ᵀ *ᵥ v)) + (Pm * P u) *ᵥ ((Q y)ᵀ *ᵥ v) = 0 := by
    intro y u hyu v
    have h := congrArg (fun w => Pm *ᵥ w) (hov y u hyu v)
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h
    have e : (Pm * P u) *ᵥ ((Q y)ᵀ *ᵥ v) = Pm *ᵥ (P u *ᵥ ((Q y)ᵀ *ᵥ v)) := (Matrix.mulVec_mulVec _ _ _).symm
    rw [e]
    exact h
  have hsc : ∀ y (c : F), Pm *ᵥ (X y *ᵥ (c • κ)) = c • x' y := by
    intro y c
    simp only [x', Matrix.mulVec_smul]
  let W : Fin 5 → Submodule F (Fin 5 → F) := fun u => LinearMap.range (Pm * P u).mulVecLin
  have hWmem : ∀ u (a : Fin 3 → F), (Pm * P u) *ᵥ a ∈ W u := fun u a => ⟨a, rfl⟩
  by_cases hcase : ∃ u, u ≠ z ∧ V ≤ W u
  · -- Case 1: Pm P_u fills V
    obtain ⟨u, huz, hVW⟩ := hcase
    have hW3 : 3 ≤ Module.finrank F (W u) := le_trans hV3 (Submodule.finrank_mono hVW)
    have hinj : ∀ a : Fin 3 → F, (Pm * P u) *ᵥ a = 0 → a = 0 := by
      intro a ha
      have h := LinearMap.finrank_range_add_finrank_ker ((Pm * P u).mulVecLin)
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      have hk : LinearMap.ker (Pm * P u).mulVecLin = ⊥ :=
        Submodule.finrank_eq_zero.mp (by
          have : Module.finrank F (W u) = Module.finrank F (LinearMap.range (Pm * P u).mulVecLin) := rfl
          omega)
      have ha' : a ∈ LinearMap.ker (Pm * P u).mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact ha
      rw [hk] at ha'
      exact (Submodule.mem_bot F).mp ha'
    -- an index y outside {u, z}
    have hcard : 2 < ((Finset.univ.erase z).erase u).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨huz, Finset.mem_univ u⟩),
        Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]
      norm_num
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (by omega : 0 < ((Finset.univ.erase z).erase u).card)
    have hyu : y ≠ u := Finset.ne_of_mem_erase hy
    have hyz : y ≠ z := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
    let S : Submodule F (Fin 5 → F) := Submodule.span F {x' y}
    have hS : Module.finrank F S ≤ 1 := by
      have := finrank_span_le_card (R := F) ({x' y} : Set (Fin 5 → F))
      simpa using this
    let M : Submodule F (Fin 3 → F) := S.comap (Pm * P u).mulVecLin
    have hM : Module.finrank F M ≤ 1 := by
      let φ : M →ₗ[F] S := LinearMap.codRestrict S (((Pm * P u).mulVecLin).comp M.subtype)
        (fun a => a.2)
      have hφ : Function.Injective φ := by
        intro a b hab
        have e : (Pm * P u) *ᵥ a.1 = (Pm * P u) *ᵥ b.1 := congrArg Subtype.val hab
        apply Subtype.ext
        have := hinj (a.1 - b.1) (by rw [Matrix.mulVec_sub, e, sub_self])
        exact sub_eq_zero.mp this
      exact (LinearMap.finrank_le_finrank_of_injective hφ).trans hS
    have hVle : V ≤ S ⊔ M.map (Pm * P y).mulVecLin := by
      intro v hv
      obtain ⟨c, hc⟩ := hYκ y hyz v hv
      obtain ⟨c', hc'⟩ := hYκ u huz v hv
      have e := hdiagπ y v hv
      rw [hc, hsc] at e
      rw [e]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span rfl)) ?_
      refine ⟨(Q y)ᵀ *ᵥ v, ?_, by rw [Matrix.mulVecLin_apply]⟩
      show (Pm * P u).mulVecLin ((Q y)ᵀ *ᵥ v) ∈ S
      have e2 := hoffπ y u hyu v
      rw [hc', hsc] at e2
      rw [Matrix.mulVecLin_apply, eq_neg_of_add_eq_zero_right e2]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    have h1 := Submodule.finrank_mono hVle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank S (M.map (Pm * P y).mulVecLin)
    have h3 := Submodule.finrank_map_le (Pm * P y).mulVecLin M
    omega
  · -- Case 2: every W_u is proper in V
    push_neg at hcase
    have hG1 : ∀ u, u ≠ z → ∃ v ∈ V, ∃ c : F, c ≠ 0 ∧ (Y u)ᵀ *ᵥ v = c • κ := by
      intro u hu
      by_contra hno
      push_neg at hno
      apply hcase u hu
      intro v hv
      obtain ⟨c, hc⟩ := hYκ u hu v hv
      have hc0 : c = 0 := by
        by_contra h0; exact hno v hv c h0 hc
      have e := hdiagπ u v hv
      rw [hc, hc0, zero_smul, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add] at e
      rw [e]; exact hWmem u _
    have hG2 : ∀ u, u ≠ z → ∀ y, y ≠ u → x' y ∈ W u := by
      intro u hu y hyu
      obtain ⟨v, hv, c, hc0, hc⟩ := hG1 u hu
      have e := hoffπ y u hyu v
      rw [hc, hsc] at e
      have e2 : c • x' y = -((Pm * P u) *ᵥ ((Q y)ᵀ *ᵥ v)) := eq_neg_of_add_eq_zero_left e
      have : x' y = c⁻¹ • (-((Pm * P u) *ᵥ ((Q y)ᵀ *ᵥ v))) := by
        rw [← e2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (hWmem u _))
    have hG3 : ∀ u, u ≠ z → x' u ∉ W u := by
      intro u hu hxu
      apply hcase u hu
      intro v hv
      obtain ⟨c, hc⟩ := hYκ u hu v hv
      have e := hdiagπ u v hv
      rw [hc, hsc] at e
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hxu) (hWmem u _)
    -- the four x'_y (y ≠ z) are independent in V
    let s : Finset (Fin 5) := Finset.univ.erase z
    have hli : LinearIndependent F (fun y : s => x' y) := by
      rw [linearIndependent_iff']
      intro t g hg i hi
      by_contra hgi
      have hiz : (i : Fin 5) ≠ z := Finset.ne_of_mem_erase i.2
      apply hG3 i hiz
      have hsplit := Finset.add_sum_erase t (fun j => g j • x' j) hi
      rw [hg] at hsplit
      have hrest : ∑ j ∈ t.erase i, g j • x' j ∈ W i := by
        refine Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _ ?_)
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        exact hG2 i hiz j (fun h => hji (Subtype.ext h))
      have : g i • x' i = -(∑ j ∈ t.erase i, g j • x' j) := eq_neg_of_add_eq_zero_left hsplit
      have hx : x' i = (g i)⁻¹ • (-(∑ j ∈ t.erase i, g j • x' j)) := by
        rw [← this, smul_smul, inv_mul_cancel₀ hgi, one_smul]
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hrest)
    have hspan : Submodule.span F (Set.range (fun y : s => x' y)) ≤ V := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact hPmR _
    have h4 := finrank_span_eq_card hli
    have hcard : Fintype.card s = 4 := by
      simp [s, Finset.card_erase_of_mem]
    have := Submodule.finrank_mono hspan
    omega
end

/-! ## unit slice_rank_slice_kernel_line_impossible -/
section
open Matrix

/-- **Lemma D5 (T360 at N = 4, rank width N + 1)**: in a slice system with N ≥ 4, OS width k ≤ N - 2, all P_u injective,
no rank slice X_z has kernel of dimension ≤ 1. Proof: K = ker (Q z)ᵀ has dim ≥ 2 and (Y u)ᵀ maps K into ker X_z (a line),
so each K_u = K ∩ ker (Y u)ᵀ (u ≠ z) is nonzero; K_a ∩ K_b = 0 for a ≠ b (diag a, off (a,b), P_b injective); and every
v ∈ K_a ∪ K_b lies in the line X_c (ker X_z) (off (c,u), diag c). So K_a = K_b, a contradiction. -/
theorem ada_slice_D5 {F : Type*} [Field F] {N r k : ℕ} (hN : 4 ≤ N) (hk : k + 2 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hP : ∀ u (c : Fin k → F), P u *ᵥ c = 0 → c = 0) (z : Fin N)
    (hz : Module.finrank F (LinearMap.ker (X z).mulVecLin) ≤ 1) : False := by
  classical
  have key : ∀ a b (v : Fin N → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hdv : ∀ a (v : Fin N → F), X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
    intro a v
    rw [← key, hd a, Matrix.one_mulVec]
  have hov : ∀ a b, a ≠ b → ∀ (v : Fin N → F), X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) = 0 := by
    intro a b hab v
    rw [← key, ho a b hab, Matrix.zero_mulVec]
  -- three indices a, b, c distinct from z
  have hcard : 2 < (Finset.univ.erase z).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcard
  have haz : a ≠ z := Finset.ne_of_mem_erase ha
  have hbz : b ≠ z := Finset.ne_of_mem_erase hb
  have hcz : c ≠ z := Finset.ne_of_mem_erase hc
  let K : Submodule F (Fin N → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  let KX : Submodule F (Fin r → F) := LinearMap.ker (X z).mulVecLin
  -- (Y w)ᵀ maps K into ker X_z
  have hYK : ∀ w, w ≠ z → ∀ v ∈ K, (Y w)ᵀ *ᵥ v ∈ KX := by
    intro w hw v hv
    have h := hov z w (Ne.symm hw) v
    have hq : (Q z)ᵀ *ᵥ v = 0 := hv
    rw [hq, Matrix.mulVec_zero, add_zero] at h
    show (X z).mulVecLin ((Y w)ᵀ *ᵥ v) = 0
    rw [Matrix.mulVecLin_apply]; exact h
  -- dim K ≥ 2
  have hK : 2 ≤ Module.finrank F K := by
    have h := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
    have hr : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) ≤ k := by
      have := Submodule.finrank_le (LinearMap.range ((Q z)ᵀ.mulVecLin))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show 2 ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin)
    omega
  -- each K_u (u ≠ z) has a nonzero vector
  have hex : ∀ u, u ≠ z → ∃ v ∈ K, v ≠ 0 ∧ (Y u)ᵀ *ᵥ v = 0 := by
    intro u hu
    let ψ : K →ₗ[F] KX := LinearMap.codRestrict _ (((Y u)ᵀ.mulVecLin).comp K.subtype)
      (fun v => by
        show (Y u)ᵀ *ᵥ v.1 ∈ KX
        exact hYK u hu v.1 v.2)
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    have hr : Module.finrank F (LinearMap.range ψ) ≤ 1 :=
      (Submodule.finrank_le (LinearMap.range ψ)).trans hz
    have hpos : 0 < Module.finrank F (LinearMap.ker ψ) := by omega
    have hne : LinearMap.ker ψ ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hpos
      exact lt_irrefl _ hpos
    obtain ⟨w, hwk, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨w.1, w.2, ?_, ?_⟩
    · intro h0
      apply hw0
      exact Subtype.ext h0
    · rw [LinearMap.mem_ker] at hwk
      exact congrArg Subtype.val hwk
  -- K_a ∩ K_b = 0
  have hsep : ∀ v : Fin N → F, (Y a)ᵀ *ᵥ v = 0 → (Y b)ᵀ *ᵥ v = 0 → v = 0 := by
    intro v h1 h2
    have e1 := hov a b hab v
    rw [h2, Matrix.mulVec_zero, zero_add] at e1
    have e2 := hP b _ e1
    have e3 := hdv a v
    rw [h1, e2, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero] at e3
    exact e3.symm
  -- every v ∈ K with (Y u)ᵀ v = 0 (u ∈ {a, b}) lies in X_c (ker X_z)
  let L : Submodule F (Fin N → F) := KX.map (X c).mulVecLin
  have hL : Module.finrank F L ≤ 1 := (Submodule.finrank_map_le _ _).trans hz
  have hin : ∀ u, u ≠ c → ∀ v ∈ K, (Y u)ᵀ *ᵥ v = 0 → v ∈ L := by
    intro u huc v hv hy
    have e1 := hov c u (Ne.symm huc) v
    rw [hy, Matrix.mulVec_zero, zero_add] at e1
    have e2 := hP u _ e1
    have e3 := hdv c v
    rw [e2, Matrix.mulVec_zero, add_zero] at e3
    refine ⟨(Y c)ᵀ *ᵥ v, hYK c hcz v hv, ?_⟩
    rw [Matrix.mulVecLin_apply]; exact e3
  obtain ⟨va, hva, hva0, hya⟩ := hex a haz
  obtain ⟨vb, hvb, hvb0, hyb⟩ := hex b hbz
  have hLa := hin a hac va hva hya
  have hLb := hin b hbc vb hvb hyb
  -- in the ≤ 1-dim space L, vb is a multiple of va
  obtain ⟨g, hg⟩ := (finrank_le_one_iff (K := F) (V := L)).1 hL
  obtain ⟨ca, hca⟩ := hg ⟨va, hLa⟩
  obtain ⟨cb, hcb⟩ := hg ⟨vb, hLb⟩
  have hca' : ca • (g : Fin N → F) = va := congrArg Subtype.val hca
  have hcb' : cb • (g : Fin N → F) = vb := congrArg Subtype.val hcb
  have hca0 : ca ≠ 0 := by
    intro h0; apply hva0; rw [← hca', h0, zero_smul]
  have hmul : vb = (cb / ca) • va := by
    rw [← hca', ← hcb', smul_smul, div_mul_cancel₀ _ hca0]
  apply hvb0
  apply hsep vb
  · rw [hmul, Matrix.mulVec_smul, hya, smul_zero]
  · exact hyb
end

/-! ## unit slice_left_kernels_all_ranks_impossible -/
section
open Matrix

/-- **Lemma C5 (T360 at N = 4; Lena's Lemma C core for ANY rank width r)**: if every Q_i is injective, every P_u has rank
>= 2, and every rank slice X_i has a nonzero left-kernel vector, the slice system has no solution. (Proof copied from
lena_slice_full_width_os_two_false with Lemma A replaced by the hypothesis hw.) -/
theorem ada_slice_C5 {F : Type*} [Field F] {N r k : ℕ} (hN : 1 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0)
    (hQinj : ∀ i (c : Fin k → F), Q i *ᵥ c = 0 → c = 0) (hP2 : ∀ u, 2 ≤ (P u).rank)
    (hw : ∀ i, ∃ v : Fin N → F, v ≠ 0 ∧ v ᵥ* X i = 0) : False := by
  classical
  choose w hw0 hwX using hw
  have hdw : ∀ i, (w i ᵥ* P i) ᵥ* (Q i)ᵀ = w i := by
    intro i
    have h := congrArg (fun M => w i ᵥ* M) (hd i)
    simp only [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hwX i, Matrix.zero_vecMul, zero_add,
      Matrix.vecMul_one] at h
    exact h
  have how : ∀ i u, i ≠ u → (w i ᵥ* P u) ᵥ* (Q i)ᵀ = 0 := by
    intro i u hiu
    have h := congrArg (fun M => w i ᵥ* M) (ho i u hiu)
    simp only [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, hwX i, Matrix.zero_vecMul, zero_add,
      Matrix.vecMul_zero] at h
    exact h
  have hP0 : ∀ i u, i ≠ u → w i ᵥ* P u = 0 := by
    intro i u hiu
    apply hQinj i
    rw [← Matrix.vecMul_transpose]
    exact how i u hiu
  have hP1 : ∀ i, w i ᵥ* P i ≠ 0 := by
    intro i h
    apply hw0 i
    rw [← hdw i, h, Matrix.zero_vecMul]
  have hsum : ∀ (g : Fin N → F) j, (g ᵥ* Matrix.of w) ᵥ* P j = g j • (w j ᵥ* P j) := by
    intro g j
    have e : ∀ s, ((g ᵥ* Matrix.of w) ᵥ* P j) s = ∑ i, g i * (w i ᵥ* P j) s := by
      intro s
      rw [Matrix.vecMul_vecMul]
      rfl
    ext s
    rw [e s, Finset.sum_eq_single j]
    · simp [Pi.smul_apply, smul_eq_mul]
    · intro i _ hij
      rw [hP0 i j hij]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  let u : Fin N := ⟨0, by omega⟩
  have hD : N ≤ Module.finrank F (LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)) + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)
    have h1 : Module.finrank F (LinearMap.range (LinearMap.proj u : (Fin N → F) →ₗ[F] F)) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range (LinearMap.proj u : (Fin N → F) →ₗ[F] F))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let φ : LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F) →ₗ[F] LinearMap.ker (P u)ᵀ.mulVecLin :=
    LinearMap.codRestrict (LinearMap.ker (P u)ᵀ.mulVecLin)
      ((Matrix.of w).vecMulLinear ∘ₗ (LinearMap.ker (LinearMap.proj u : (Fin N → F) →ₗ[F] F)).subtype)
      (fun g => by
        have hg : g.1 u = 0 := g.2
        show (P u)ᵀ.mulVecLin (g.1 ᵥ* Matrix.of w) = 0
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, hsum, hg, zero_smul])
  have hinjφ : Function.Injective φ := by
    intro a b hab
    have e := congrArg Subtype.val hab
    change a.1 ᵥ* Matrix.of w = b.1 ᵥ* Matrix.of w at e
    apply Subtype.ext
    funext j
    have h1 := congrArg (fun v => v ᵥ* P j) e
    simp only [hsum] at h1
    exact smul_left_injective F (hP1 j) h1
  have h1 := LinearMap.finrank_le_finrank_of_injective hinjφ
  have h2 := LinearMap.finrank_range_add_finrank_ker ((P u)ᵀ.mulVecLin)
  have e3 : Module.finrank F (LinearMap.range ((P u)ᵀ.mulVecLin)) = (P u).rank := by
    rw [← Matrix.rank_transpose]; rfl
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
  have := hP2 u
  omega
end

/-! ## unit T412_hi_general_N_os_two_rank_N_plus_one -/
section
open Matrix

/-- **T412 (Lena)**: general-N hi. Over any field and every N ≥ 4, an exact split SWAP_N = B + C with OS C ≤ 2 has
rank B ≥ N + 1 (so rank B + OS C ≥ N + 3 on this slice). Same proof as lena_P4_hi: zero-pad the slices to r = N, k = 2
(lena_sum_fin_pad) and apply lena_slice_full_width_os_two_false. Split-to-slice block after Nadia's T331, with credit. -/
theorem lena_hi_general {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = B + C) (hC : (biancaRealignF C).rank ≤ 2) : N + 1 ≤ B.rank := by
  classical
  by_contra hlt
  push Not at hlt
  have hB4 : B.rank ≤ N := by omega
  obtain ⟨U, V, hB⟩ := bianca_exists_sum_vecMulVec_of_rank B
  obtain ⟨P, Q, hCm⟩ := bianca_exists_sum_vecMulVec_of_rank (biancaRealignF C)
  have hent : ∀ x y u v : Fin N, (∑ i, U i (x, y) * V i (u, v)) + (∑ l, P l (x, u) * Q l (y, v)) =
      if x = v ∧ y = u then 1 else 0 := by
    intro x y u v
    have e1 : B (x, y) (u, v) = ∑ i, U i (x, y) * V i (u, v) := by
      have := congrFun (congrFun hB (x, y)) (u, v)
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    have e2 : C (x, y) (u, v) = ∑ l, P l (x, u) * Q l (y, v) := by
      have := congrFun (congrFun hCm (x, u)) (y, v)
      have h0' : C (x, y) (u, v) = biancaRealignF C (x, u) (y, v) := rfl
      rw [h0']
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    rw [← e1, ← e2, ← Matrix.add_apply, ← h]
    rfl
  -- zero padding to r = 4, k = 2
  let U' : Fin N → (Fin N × Fin N → F) := fun i => if hi : i.1 < B.rank then U ⟨i.1, hi⟩ else 0
  let V' : Fin N → (Fin N × Fin N → F) := fun i => if hi : i.1 < B.rank then V ⟨i.1, hi⟩ else 0
  let P' : Fin 2 → (Fin N × Fin N → F) := fun i =>
    if hi : i.1 < (biancaRealignF C).rank then P ⟨i.1, hi⟩ else 0
  let Q' : Fin 2 → (Fin N × Fin N → F) := fun i =>
    if hi : i.1 < (biancaRealignF C).rank then Q ⟨i.1, hi⟩ else 0
  have hpB : ∀ p q, ∑ i : Fin N, U' i p * V' i q = ∑ i, U i p * V i q := by
    intro p q
    rw [← lena_sum_fin_pad hB4 (fun i => U i p * V i q)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.1 < B.rank
    · simp [U', V', hi]
    · simp [U', V', hi]
  have hpC : ∀ p q, ∑ i : Fin 2, P' i p * Q' i q = ∑ i, P i p * Q i q := by
    intro p q
    rw [← lena_sum_fin_pad hC (fun i => P i p * Q i q)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : i.1 < (biancaRealignF C).rank
    · simp [P', Q', hi]
    · simp [P', Q', hi]
  let X : Fin N → Matrix (Fin N) (Fin N) F := fun y => Matrix.of fun x i => U' i (x, y)
  let Y : Fin N → Matrix (Fin N) (Fin N) F := fun u => Matrix.of fun v i => V' i (u, v)
  let PP : Fin N → Matrix (Fin N) (Fin 2) F := fun u => Matrix.of fun x l => P' l (x, u)
  let QQ : Fin N → Matrix (Fin N) (Fin 2) F := fun y => Matrix.of fun v l => Q' l (y, v)
  have hslice : ∀ y u, X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = if y = u then 1 else 0 := by
    intro y u
    ext x v
    have := hent x y u v
    rw [← hpB, ← hpC] at this
    simp only [X, Y, PP, QQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    by_cases hyu : y = u
    · subst hyu
      by_cases hxv : x = v
      · subst hxv; simp
      · simp [hxv]
    · simp [hyu]
  have hd : ∀ y, X y * (Y y)ᵀ + PP y * (QQ y)ᵀ = 1 := fun y => by simpa using hslice y y
  have ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + PP u * (QQ y)ᵀ = 0 := fun y u hyu => by
    simpa [hyu] using hslice y u
  exact lena_slice_full_width_os_two_false hN (by omega) le_rfl X Y PP QQ hd ho
end

/-! ## unit P5_ge_eight_reduced_to_shape_4_3 -/
section

/-- **P(5) ≥ 8 reduced to one shape (sprint D, T419), any field.** If no exact split SWAP_5 = B + C has rank B ≤ 4
and OS C ≤ 3, then every split has rank B + OS C ≥ 8. Totals ≤ 6 are excluded by the N + 2 floor
(nadia_minsumF_ge_N_add_two); of the total-7 shapes, (0,7)/(7,0) by rank SWAP_5 = 25, (1,6) by R62's dual
(daria_os_ge_of_rank_le_one_field), (6,1) by R62 (greta_rank_ge_of_os_le_one_field), (5,2) by lena_hi_general,
(2,5) by lena_hi_general on the realigned split, (4,3) by the hypothesis and (3,4) by it on the realigned split. -/
theorem xenia_P5_ge_eight_of_piece {F : Type*} [Field F]
    (h5 : ∀ B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F, biancaSwapF F (Fin 5) = B + C →
      B.rank ≤ 4 → (biancaRealignF C).rank ≤ 3 → False)
    (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F) (h : biancaSwapF F (Fin 5) = B + C) :
    8 ≤ B.rank + (biancaRealignF C).rank := by
  have h7 := nadia_minsumF_ge_N_add_two 5 (by norm_num) B C h
  have hR : biancaSwapF F (Fin 5) = biancaRealignF C + biancaRealignF B := by
    rw [← greta_realignF_swapF, h, greta_realignF_add, add_comm]
  have hRB : (biancaRealignF (biancaRealignF B)).rank = B.rank := by rw [uri_realignF_realignF]
  have hsw : (biancaSwapF F (Fin 5)).rank = 25 := by rw [daria_swapF_rank]
  by_contra hlt
  push_neg at hlt
  rcases (by omega : B.rank = 0 ∨ B.rank = 1 ∨ B.rank = 2 ∨ B.rank = 3 ∨ B.rank = 4 ∨ B.rank = 5 ∨
      B.rank = 6 ∨ B.rank = 7) with h0 | h1 | h2 | h3 | h4 | h5' | h6 | h7'
  · have hB0 := daria_eq_zero_of_rank_zero B h0
    have hC : C = biancaSwapF F (Fin 5) := by rw [h, hB0, zero_add]
    have : (biancaRealignF C).rank = 25 := by rw [hC, greta_realignF_swapF, hsw]
    omega
  · have := daria_os_ge_of_rank_le_one_field 5 B C h (by omega)
    omega
  · have := lena_hi_general 5 (by norm_num) (biancaRealignF C) (biancaRealignF B) hR (by rw [hRB]; omega)
    omega
  · exact h5 (biancaRealignF C) (biancaRealignF B) hR (by omega) (by rw [hRB]; omega)
  · exact h5 B C h (by omega) (by omega)
  · have := lena_hi_general 5 (by norm_num) B C h (by omega)
    omega
  · have := greta_rank_ge_of_os_le_one_field 5 B C h (by omega)
    omega
  · have hRC0 := daria_eq_zero_of_rank_zero (biancaRealignF C) (by omega)
    have hC0 : C = 0 := by
      rw [← uri_realignF_realignF C, hRC0]
      ext a b
      simp [biancaRealignF]
    have hB : B = biancaSwapF F (Fin 5) := by rw [h, hC0, add_zero]
    rw [hB, hsw] at h7'
    omega
end

/-! ## unit P5_ge_eight_every_field -/
section
open Matrix

/-- **h5 (T420)**: no exact split SWAP_5 = B + C over any field has rank B ≤ 4 and OS C ≤ 3. Slice system of widths (4,3)
(Daria's padded bridge); every Q_z and P_z has rank 3 (Nolan's glue on Ada's B'(a), B'(b), for the system and its
transpose); every X_i (5 × 4) has a left-kernel vector; then Ada's C5. -/
theorem ada_h5 {F : Type*} [Field F] (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F)
    (h : biancaSwapF F (Fin 5) = B + C) (hB : B.rank ≤ 4) (hC : (biancaRealignF C).rank ≤ 3) : False := by
  classical
  obtain ⟨X, Y, P, Q, hd, ho⟩ := daria_slices_of_split 5 4 3 B C h hB hC
  have hdT : ∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1 := fun y => by
    have := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have hoT : ∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0 := fun y u hyu => by
    have := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have hQ3 : ∀ z, 3 ≤ (Q z).rank := nolan_P5_Q_rank_three X Y P Q hd ho (fun z => ada_slice_Bb X Y P Q hd ho z)
  have hP3 : ∀ z, 3 ≤ (P z).rank := nolan_P5_P_rank_three X Y P Q hd ho (fun z => ada_slice_Bb Y X Q P hdT hoT z)
  have hQinj : ∀ i (c : Fin 3 → F), Q i *ᵥ c = 0 → c = 0 := by
    intro i c hc
    have h1 := LinearMap.finrank_range_add_finrank_ker ((Q i).mulVecLin)
    have e : Module.finrank F (LinearMap.range ((Q i).mulVecLin)) = (Q i).rank := rfl
    have hq := hQ3 i
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have hker : LinearMap.ker (Q i).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hc' : c ∈ LinearMap.ker (Q i).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hc
    rw [hker] at hc'
    exact (Submodule.mem_bot F).mp hc'
  have hw : ∀ i, ∃ v : Fin 5 → F, v ≠ 0 ∧ v ᵥ* X i = 0 := by
    intro i
    have h1 := LinearMap.finrank_range_add_finrank_ker ((X i)ᵀ.mulVecLin)
    have hr : Module.finrank F (LinearMap.range ((X i)ᵀ.mulVecLin)) ≤ 4 := by
      have := Submodule.finrank_le (LinearMap.range ((X i)ᵀ.mulVecLin))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have hne : LinearMap.ker (X i)ᵀ.mulVecLin ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at h1
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨v, hv0, ?_⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at hv
    exact hv
  exact ada_slice_C5 (by norm_num) X Y P Q hd ho hQinj (fun u => le_trans (by norm_num) (hP3 u)) hw

/-- **P(5) ≥ 8 over every field**: every exact split SWAP_5 = B + C has rank B + OS C ≥ 8 (Xenia's reduction to h5). -/
theorem ada_P5_ge_eight {F : Type*} [Field F] (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F)
    (h : biancaSwapF F (Fin 5) = B + C) : 8 ≤ B.rank + (biancaRealignF C).rank :=
  xenia_P5_ge_eight_of_piece (fun B C h hB hC => ada_h5 B C h hB hC) B C h
end

/-! ## unit T454_slice_Btype_general_width_of_counting -/
section
open Matrix

/-- The counting-lemma interface (Xenia's brick (a), Q303), as a hypothesis shape. -/
def AdaCountingLemma (F : Type*) [Field F] (N k : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (π : Matrix (Fin N) (Fin N) F) (x l : ι → Fin N → F)
    (A B : ι → Matrix (Fin N) (Fin k) F),
    (∀ y u, Matrix.vecMulVec (x y) (l u) + A u * (B y)ᵀ = if y = u then π else 0) →
    Fintype.card ι * π.rank ≤ (Matrix.of fun y i => x y i).rank * (Matrix.of fun u j => l u j).rank + k

/-- **B-type lemma at general width (T454)**: in a slice system with N ≥ 6, r + k = N + 2, 3 ≤ k ≤ r, every OS slice
Q_z has full rank k, given the counting lemma. Case rank X_z = r: ada_slice_Ba. Case rank X_z = r - 1: π = X_z Y_zᵀ projects
onto V = ker (Q z)ᵀ = range X_z, and π (hd/ho) π is a reduced system of N - 1 indices with a rank-one first term, so
(N - 1)(r - 1) ≤ (r - 1)² + k, false. -/
theorem ada_slice_Bgen {F : Type*} [Field F] {N r k : ℕ} (hN : 6 ≤ N) (hrk : r + k = N + 2) (hk3 : 3 ≤ k)
    (hkr : k ≤ r) (hcount : AdaCountingLemma F N k)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (z : Fin N) : k ≤ (Q z).rank := by
  classical
  by_contra hlt
  push_neg at hlt
  have key : ∀ a b (v : Fin N → F), (X a * (Y b)ᵀ + P b * (Q a)ᵀ) *ᵥ v =
      X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) := by
    intro a b v
    simp only [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have hdv : ∀ a (v : Fin N → F), X a *ᵥ ((Y a)ᵀ *ᵥ v) + P a *ᵥ ((Q a)ᵀ *ᵥ v) = v := by
    intro a v
    rw [← key, hd a, Matrix.one_mulVec]
  have hov : ∀ a b, a ≠ b → ∀ (v : Fin N → F), X a *ᵥ ((Y b)ᵀ *ᵥ v) + P b *ᵥ ((Q a)ᵀ *ᵥ v) = 0 := by
    intro a b hab v
    rw [← key, ho a b hab, Matrix.zero_mulVec]
  let V : Submodule F (Fin N → F) := LinearMap.ker (Q z)ᵀ.mulVecLin
  let R : Submodule F (Fin N → F) := LinearMap.range (X z).mulVecLin
  have hVq : ∀ v ∈ V, (Q z)ᵀ *ᵥ v = 0 := fun v hv => hv
  have hV : r - 1 ≤ Module.finrank F V := by
    have h := LinearMap.finrank_range_add_finrank_ker ((Q z)ᵀ.mulVecLin)
    have e : Module.finrank F (LinearMap.range ((Q z)ᵀ.mulVecLin)) = (Q z).rank := by
      rw [← Matrix.rank_transpose]; rfl
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show r - 1 ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin)
    omega
  have hVR : V ≤ R := by
    intro v hv
    have h := hdv z v
    rw [hVq v hv, Matrix.mulVec_zero, add_zero] at h
    exact ⟨(Y z)ᵀ *ᵥ v, by rw [Matrix.mulVecLin_apply]; exact h⟩
  have hRr : Module.finrank F R = (X z).rank := rfl
  have hXr : (X z).rank ≤ r := by simpa using Matrix.rank_le_width (X z)
  have hRV := Submodule.finrank_mono hVR
  have hKX := LinearMap.finrank_range_add_finrank_ker ((X z).mulVecLin)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hKX
  have hKXe : Module.finrank F (LinearMap.range (X z).mulVecLin) = (X z).rank := rfl
  rcases (show (X z).rank = r ∨ (X z).rank = r - 1 by omega) with hfull | hdef
  · -- X_z injective: ada_slice_Ba
    have hinj : ∀ c : Fin r → F, X z *ᵥ c = 0 → c = 0 := by
      intro c hc
      have hker : LinearMap.ker (X z).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have hc' : c ∈ LinearMap.ker (X z).mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hc
      rw [hker] at hc'
      exact (Submodule.mem_bot F).mp hc'
    exact ada_slice_Ba (by omega) X Y P Q hd ho z hinj (by
      show k < 2 * Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin)
      have : r - 1 ≤ Module.finrank F (LinearMap.ker (Q z)ᵀ.mulVecLin) := hV
      omega)
  · -- rank X_z = r - 1
    have hVeq : V = R := Submodule.eq_of_le_of_finrank_le hVR (by omega)
    have hVd : Module.finrank F V = r - 1 := by rw [hVeq]; omega
    let KX : Submodule F (Fin r → F) := LinearMap.ker (X z).mulVecLin
    have hK1 : Module.finrank F KX = 1 := by
      show Module.finrank F (LinearMap.ker (X z).mulVecLin) = 1
      omega
    obtain ⟨κ0, hκ0, hκ⟩ := finrank_eq_one_iff'.1 hK1
    let κ : Fin r → F := κ0
    have hκne : κ ≠ 0 := fun h => hκ0 (Subtype.ext h)
    obtain ⟨i0, hi0⟩ : ∃ i, κ i ≠ 0 := by
      by_contra hh; push_neg at hh; exact hκne (funext hh)
    let μ : Fin r → F := Pi.single i0 (κ i0)⁻¹
    have hμκ : μ ⬝ᵥ κ = 1 := by
      simp [μ, dotProduct, Pi.single_apply, inv_mul_cancel₀ hi0]
    let Pm : Matrix (Fin N) (Fin N) F := X z * (Y z)ᵀ
    have hPmV : ∀ v ∈ V, Pm *ᵥ v = v := by
      intro v hv
      have h := hdv z v
      rw [hVq v hv, Matrix.mulVec_zero, add_zero] at h
      show (X z * (Y z)ᵀ) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec]; exact h
    have hPmR : ∀ w, Pm *ᵥ w ∈ V := by
      intro w
      rw [hVeq]
      exact ⟨(Y z)ᵀ *ᵥ w, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
    have hPm2 : ∀ w, Pm *ᵥ (Pm *ᵥ w) = Pm *ᵥ w := fun w => hPmV _ (hPmR w)
    -- Y_uᵀ (π w) is a multiple of κ for u ≠ z
    have hYκ : ∀ u, u ≠ z → ∀ w, (Y u)ᵀ *ᵥ (Pm *ᵥ w) = (μ ⬝ᵥ ((Y u)ᵀ *ᵥ (Pm *ᵥ w))) • κ := by
      intro u hu w
      have h := hov z u (Ne.symm hu) (Pm *ᵥ w)
      rw [hVq _ (hPmR w), Matrix.mulVec_zero, add_zero] at h
      have hm : (Y u)ᵀ *ᵥ (Pm *ᵥ w) ∈ KX := by
        show (X z).mulVecLin _ = 0
        rw [Matrix.mulVecLin_apply]; exact h
      obtain ⟨c, hc⟩ := hκ ⟨_, hm⟩
      have hc' : c • κ = (Y u)ᵀ *ᵥ (Pm *ᵥ w) := congrArg Subtype.val hc
      rw [← hc', dotProduct_smul, hμκ, smul_eq_mul, mul_one]
    let ι : Type := {y : Fin N // y ≠ z}
    let x : ι → Fin N → F := fun y => Pm *ᵥ (X y.1 *ᵥ κ)
    let l : ι → Fin N → F := fun u => Pmᵀ *ᵥ (Y u.1 *ᵥ μ)
    let A : ι → Matrix (Fin N) (Fin k) F := fun u => Pm * P u.1
    let B : ι → Matrix (Fin N) (Fin k) F := fun y => Pmᵀ * Q y.1
    have hid : ∀ y u : ι, Matrix.vecMulVec (x y) (l u) + A u * (B y)ᵀ = if y = u then Pm else 0 := by
      intro y u
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      simp only [Matrix.toLin'_apply]
      have hl : l u ⬝ᵥ w = μ ⬝ᵥ ((Y u.1)ᵀ *ᵥ (Pm *ᵥ w)) := by
        calc l u ⬝ᵥ w = (Pmᵀ *ᵥ (Y u.1 *ᵥ μ)) ⬝ᵥ w := rfl
          _ = ((Y u.1 *ᵥ μ) ᵥ* Pm) ⬝ᵥ w := by rw [Matrix.mulVec_transpose]
          _ = (Y u.1 *ᵥ μ) ⬝ᵥ (Pm *ᵥ w) := (Matrix.dotProduct_mulVec _ _ _).symm
          _ = (μ ᵥ* (Y u.1)ᵀ) ⬝ᵥ (Pm *ᵥ w) := by rw [Matrix.vecMul_transpose]
          _ = μ ⬝ᵥ ((Y u.1)ᵀ *ᵥ (Pm *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
      have h1 : Matrix.vecMulVec (x y) (l u) *ᵥ w = Pm *ᵥ (X y.1 *ᵥ ((Y u.1)ᵀ *ᵥ (Pm *ᵥ w))) := by
        rw [xenia_vecMulVec_mulVec, hl]
        conv_rhs => rw [hYκ u.1 u.2 w, Matrix.mulVec_smul, Matrix.mulVec_smul]
      have h2 : (A u * (B y)ᵀ) *ᵥ w = Pm *ᵥ (P u.1 *ᵥ ((Q y.1)ᵀ *ᵥ (Pm *ᵥ w))) := by
        simp only [A, B, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Matrix.add_mulVec, h1, h2, ← Matrix.mulVec_add]
      by_cases hyu : y = u
      · subst hyu
        rw [hdv, hPm2, if_pos rfl]
      · have hne : y.1 ≠ u.1 := fun h => hyu (Subtype.ext h)
        rw [hov y.1 u.1 hne, Matrix.mulVec_zero, if_neg hyu, Matrix.zero_mulVec]
    have hc := hcount ι Pm x l A B hid
    have hcard : Fintype.card ι = N - 1 := by
      simp [ι, Fintype.card_subtype_compl]
    have hPmrank : Pm.rank = r - 1 := by
      have hrange : LinearMap.range Pm.mulVecLin = V := by
        apply le_antisymm
        · rintro _ ⟨w, rfl⟩; exact hPmR w
        · intro v hv; exact ⟨v, by rw [Matrix.mulVecLin_apply]; exact hPmV v hv⟩
      show Module.finrank F (LinearMap.range Pm.mulVecLin) = r - 1
      rw [hrange, hVd]
    have hXr' : (Matrix.of fun y i => x y i).rank ≤ r - 1 := by
      rw [← Matrix.rank_transpose]
      show Module.finrank F (LinearMap.range (Matrix.of fun y i => x y i)ᵀ.mulVecLin) ≤ r - 1
      rw [Matrix.range_mulVecLin]
      rw [← hVd]
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact hPmR (X y.1 *ᵥ κ)
    have hLr' : (Matrix.of fun u j => l u j).rank ≤ r - 1 := by
      rw [← Matrix.rank_transpose]
      show Module.finrank F (LinearMap.range (Matrix.of fun u j => l u j)ᵀ.mulVecLin) ≤ r - 1
      rw [Matrix.range_mulVecLin]
      have hT : Module.finrank F (LinearMap.range Pmᵀ.mulVecLin) = r - 1 := by
        show Pmᵀ.rank = r - 1
        rw [Matrix.rank_transpose, hPmrank]
      rw [← hT]
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro _ ⟨u, rfl⟩
      exact ⟨Y u.1 *ᵥ μ, rfl⟩
    rw [hcard, hPmrank] at hc
    have h3 := Nat.mul_le_mul hXr' hLr'
    have h4 : (N - 1) * (r - 1) ≤ (r - 1) * (r - 1) + k := le_trans hc (by omega)
    obtain ⟨s, rfl⟩ : ∃ s, N = s + 6 := ⟨N - 6, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    have e1 : s + 6 - 1 = s + 5 := by omega
    have e2 : t + 1 - 1 = t := by omega
    rw [e1, e2] at h4
    nlinarith
end

/-! ## unit P_N_plus_three_reduced_to_general_hii -/
section

/-- Dual of `lena_hi_general` (by realignment): rank B ≤ 2 forces OS C ≥ N + 1, every N ≥ 4, any field. -/
theorem xenia_hi_general_dual {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hB : B.rank ≤ 2) : N + 1 ≤ (biancaRealignF C).rank := by
  have hR : biancaSwapF F (Fin N) = biancaRealignF C + biancaRealignF B := by
    rw [← greta_realignF_swapF, h, greta_realignF_add, add_comm]
  have hRB : (biancaRealignF (biancaRealignF B)).rank = B.rank := by rw [uri_realignF_realignF]
  exact lena_hi_general N hN (biancaRealignF C) (biancaRealignF B) hR (by rw [hRB]; exact hB)

/-- **P(N) ≥ N + 3 is EXACTLY the general hii (sprint D, any field, every N ≥ 4).** If no exact split of SWAP_N has
3 ≤ rank B, 3 ≤ OS C and rank B + OS C ≤ N + 2, then every split has rank B + OS C ≥ N + 3. Totals ≤ N + 1 fall to the
N + 2 floor; shapes with rank B ≤ 2 or OS C ≤ 2 fall to R62, its dual, lena_hi_general and its dual, and rank SWAP = N².
At N = 4 the hypothesis is hii (the (3,3) shape); at N = 5 it is h5 ((3,4)/(4,3)). -/
theorem xenia_ge_N_add_three_of_piece {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (hpiece : ∀ B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F, biancaSwapF F (Fin N) = B + C →
      3 ≤ B.rank → 3 ≤ (biancaRealignF C).rank → B.rank + (biancaRealignF C).rank ≤ N + 2 → False)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    N + 3 ≤ B.rank + (biancaRealignF C).rank := by
  have hfloor := nadia_minsumF_ge_N_add_two N hN B C h
  have hsw : (biancaSwapF F (Fin N)).rank = N * N := daria_swapF_rank N
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 4 := ⟨N - 4, by omega⟩
  have hNN : 2 * (k + 4 + 2) ≤ (k + 4) * (k + 4 - 1) := by
    have : k + 4 - 1 = k + 3 := by omega
    rw [this]; nlinarith
  have hsq : k + 4 + 3 ≤ (k + 4) * (k + 4) := by nlinarith
  by_contra hlt
  push_neg at hlt
  by_cases hB2 : B.rank ≤ 2
  · rcases (by omega : B.rank = 0 ∨ B.rank = 1 ∨ B.rank = 2) with h0 | h1 | h2
    · have hB0 := daria_eq_zero_of_rank_zero B h0
      have hC : C = biancaSwapF F (Fin (k + 4)) := by rw [h, hB0, zero_add]
      have : (biancaRealignF C).rank = (k + 4) * (k + 4) := by rw [hC, greta_realignF_swapF, hsw]
      omega
    · have := daria_os_ge_of_rank_le_one_field (k + 4) B C h (by omega)
      omega
    · have := xenia_hi_general_dual (k + 4) hN B C h (by omega)
      omega
  · by_cases hC2 : (biancaRealignF C).rank ≤ 2
    · rcases (by omega : (biancaRealignF C).rank = 0 ∨ (biancaRealignF C).rank = 1 ∨
          (biancaRealignF C).rank = 2) with h0 | h1 | h2
      · have hRC0 := daria_eq_zero_of_rank_zero (biancaRealignF C) h0
        have hC0 : C = 0 := by
          rw [← uri_realignF_realignF C, hRC0]
          ext a b
          simp [biancaRealignF]
        have hB : B = biancaSwapF F (Fin (k + 4)) := by rw [h, hC0, add_zero]
        rw [hB, hsw] at hlt
        omega
      · have := greta_rank_ge_of_os_le_one_field (k + 4) B C h (by omega)
        omega
      · have := lena_hi_general (k + 4) hN B C h (by omega)
        omega
    · exact hpiece B C h (by omega) (by omega) (by omega)
end

/-! ## unit T454_wrapper_n_add_three_one_sided -/
section

-- T454 WRAPPER (Uri, for Ada's T454, Q307): from Ada's hcase (the case 3 <= OS C <= rank B, total N + 2) to the full piece of
-- xenia_ge_N_add_three_of_piece and to N + 3 <= rank B + OS C, any field, N >= 6. Totals <= N + 1 fall to
-- nadia_minsumF_ge_N_add_two; the case OS C > rank B is the realigned split SWAP = R C + R B.

/-- The full piece of xenia_ge_N_add_three_of_piece from the one-sided case hcase. -/
theorem uri_T454_piece_of_hcase {F : Type*} [Field F] (N : ℕ) (hN : 6 ≤ N)
    (hcase : ∀ B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F, biancaSwapF F (Fin N) = B + C →
      3 ≤ (biancaRealignF C).rank → (biancaRealignF C).rank ≤ B.rank →
      B.rank + (biancaRealignF C).rank = N + 2 → False) :
    ∀ B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F, biancaSwapF F (Fin N) = B + C → 3 ≤ B.rank →
      3 ≤ (biancaRealignF C).rank → B.rank + (biancaRealignF C).rank ≤ N + 2 → False := by
  intro B C h hB hC htot
  have h2 := nadia_minsumF_ge_N_add_two N (by omega) B C h
  have heq : B.rank + (biancaRealignF C).rank = N + 2 := by omega
  by_cases hle : (biancaRealignF C).rank ≤ B.rank
  · exact hcase B C h hC hle heq
  · have h' : biancaSwapF F (Fin N) = biancaRealignF C + biancaRealignF B := by
      have e := congrArg biancaRealignF h
      rw [greta_realignF_swapF, greta_realignF_add] at e
      rw [e, add_comm]
    have hRR : biancaRealignF (biancaRealignF B) = B := uri_realignF_realignF B
    apply hcase (biancaRealignF C) (biancaRealignF B) h'
    · rw [hRR]; exact hB
    · rw [hRR]; omega
    · rw [hRR]; omega

/-- **T454 wrapper.** For N >= 6 over any field, Ada's one-sided case hcase gives N + 3 <= rank B + OS C for every
exact split SWAP_N = B + C. -/
theorem uri_T454_ge_N_add_three {F : Type*} [Field F] (N : ℕ) (hN : 6 ≤ N)
    (hcase : ∀ B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F, biancaSwapF F (Fin N) = B + C →
      3 ≤ (biancaRealignF C).rank → (biancaRealignF C).rank ≤ B.rank →
      B.rank + (biancaRealignF C).rank = N + 2 → False)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    N + 3 ≤ B.rank + (biancaRealignF C).rank :=
  xenia_ge_N_add_three_of_piece N (by omega) (uri_T454_piece_of_hcase N hN hcase) B C h
end

/-! ## unit T454_hcase_and_n_add_three_of_counting -/
section
open Matrix

/-- **T454 one-sided case (Ada's hcase)**: for N ≥ 6, given the counting lemma (AdaCountingLemma, basis-free), no exact
split SWAP_N = B + C has 3 ≤ OS C ≤ rank B with rank B + OS C = N + 2, over any field. Slices of widths (rank B, OS C)
(Daria's bridge); ada_slice_Bgen on the system and on its transpose makes every Q_z and P_u of full rank OS C; every
N × rank B slice X_i has a left kernel since rank B < N; then ada_slice_C5. -/
theorem ada_T454_hcase {F : Type*} [Field F] (N : ℕ) (hN : 6 ≤ N) (hcount : ∀ k, AdaCountingLemma F N k)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C)
    (hk3 : 3 ≤ (biancaRealignF C).rank) (hkr : (biancaRealignF C).rank ≤ B.rank)
    (htot : B.rank + (biancaRealignF C).rank = N + 2) : False := by
  classical
  obtain ⟨X, Y, P, Q, hd, ho⟩ := daria_slices_of_split N B.rank (biancaRealignF C).rank B C h le_rfl le_rfl
  have hdT : ∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1 := fun y => by
    have := congrArg Matrix.transpose (hd y)
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have hoT : ∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0 := fun y u hyu => by
    have := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using this
  have hQ := ada_slice_Bgen hN htot hk3 hkr (hcount _) X Y P Q hd ho
  have hP := ada_slice_Bgen hN htot hk3 hkr (hcount _) Y X Q P hdT hoT
  have hQinj : ∀ i (c : Fin (biancaRealignF C).rank → F), Q i *ᵥ c = 0 → c = 0 := by
    intro i c hc
    have h1 := LinearMap.finrank_range_add_finrank_ker ((Q i).mulVecLin)
    have e : Module.finrank F (LinearMap.range ((Q i).mulVecLin)) = (Q i).rank := rfl
    have hq := hQ i
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have hker : LinearMap.ker (Q i).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hc' : c ∈ LinearMap.ker (Q i).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hc
    rw [hker] at hc'
    exact (Submodule.mem_bot F).mp hc'
  have hw : ∀ i, ∃ v : Fin N → F, v ≠ 0 ∧ v ᵥ* X i = 0 := by
    intro i
    have h1 := LinearMap.finrank_range_add_finrank_ker ((X i)ᵀ.mulVecLin)
    have hr : Module.finrank F (LinearMap.range ((X i)ᵀ.mulVecLin)) ≤ B.rank := by
      have := Submodule.finrank_le (LinearMap.range ((X i)ᵀ.mulVecLin))
      simpa using this
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
    have hne : LinearMap.ker (X i)ᵀ.mulVecLin ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at h1
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨v, hv0, ?_⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at hv
    exact hv
  exact ada_slice_C5 (by omega) X Y P Q hd ho hQinj (fun u => le_trans (by omega) (hP u)) hw

/-- **P(N) ≥ N + 3 for every N ≥ 6, given the counting lemma** (any field), through Uri's wrapper. -/
theorem ada_ge_N_add_three_of_counting {F : Type*} [Field F] (N : ℕ) (hN : 6 ≤ N)
    (hcount : ∀ k, AdaCountingLemma F N k) (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : biancaSwapF F (Fin N) = B + C) : N + 3 ≤ B.rank + (biancaRealignF C).rank :=
  uri_T454_ge_N_add_three N hN (fun B C h hk3 hkr htot => ada_T454_hcase N hN hcount B C h hk3 hkr htot) B C h
end

/-! ## unit T463_ada_counting_lemma_basis_free -/
section
open Matrix

-- T463 (Uri): Ada's AdaCountingLemma F N k, basis-free, any field. Reshuffle rows to (y, j) and columns to (u, i):
-- M = Am + Bt Atᵀ with M[(y,j),(u,i)] = [y = u] π i j (card ι block copies of πᵀ), Am[(y,j),(u,i)] = x y i * l u j.

/-- Block copies of πᵀ: card ι * rank π ≤ rank M, via an injective map (ι → range πᵀ) → range M. -/
theorem uri_block_copies_rank_le {F : Type*} [Field F] {N : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι]
    (π : Matrix (Fin N) (Fin N) F) :
    Fintype.card ι * π.rank ≤
      (Matrix.of fun (a b : ι × Fin N) => if a.1 = b.1 then π b.2 a.2 else 0).rank := by
  set W := LinearMap.range (πᵀ).mulVecLin
  let φ : (ι → W) →ₗ[F] (ι × Fin N → F) :=
    { toFun := fun f a => (f a.1 : Fin N → F) a.2
      map_add' := by intro f g; ext a; simp
      map_smul' := by intro c f; ext a; simp }
  have hinj : Function.Injective φ := by
    intro f g hfg
    funext y; apply Subtype.ext; funext j
    exact congrFun hfg (y, j)
  have hle : LinearMap.range φ ≤
      LinearMap.range (Matrix.of fun (a b : ι × Fin N) => if a.1 = b.1 then π b.2 a.2 else 0).mulVecLin := by
    rintro _ ⟨f, rfl⟩
    choose v hv using fun y => (f y).2
    refine ⟨fun b => v b.1 b.2, ?_⟩
    funext ⟨y, j⟩
    have e := congrFun (hv y) j
    simp only [Matrix.mulVecLin_apply] at e
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, ite_mul,
      zero_mul]
    show _ = (f y : Fin N → F) j
    rw [← e]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single y (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have h1 : Module.finrank F (ι → W) = Fintype.card ι * π.rank := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    congr 1
    have := Matrix.rank_transpose π
    unfold Matrix.rank at this
    exact this
  have h2 := LinearMap.finrank_range_of_inj hinj
  have h3 := Submodule.finrank_mono hle
  have h4 : Module.finrank F ↥(LinearMap.range φ) ≤
      (Matrix.of fun (a b : ι × Fin N) => if a.1 = b.1 then π b.2 a.2 else 0).rank := h3
  omega

/-- The reshuffled identity M = Am + Bt Atᵀ. -/
theorem uri_counting_reshuffle {F : Type*} [Field F] {N k : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι]
    (π : Matrix (Fin N) (Fin N) F) (x l : ι → Fin N → F) (A B : ι → Matrix (Fin N) (Fin k) F)
    (h : ∀ y u, Matrix.vecMulVec (x y) (l u) + A u * (B y)ᵀ = if y = u then π else 0) :
    (Matrix.of fun (a b : ι × Fin N) => if a.1 = b.1 then π b.2 a.2 else 0) =
      Matrix.of (fun (a b : ι × Fin N) => x a.1 b.2 * l b.1 a.2) +
      (Matrix.of fun (a : ι × Fin N) (s : Fin k) => B a.1 a.2 s) *
        (Matrix.of fun (b : ι × Fin N) (s : Fin k) => A b.1 b.2 s)ᵀ := by
  ext ⟨y, j⟩ ⟨u, i⟩
  have e := congrFun (congrFun (h y u) i) j
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply] at e
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hs : (∑ s, B y j s * A u i s) = ∑ s, A u i s * B y j s :=
    Finset.sum_congr rfl (fun s _ => mul_comm _ _)
  rw [hs]
  by_cases hyu : y = u
  · subst hyu
    rw [if_pos rfl] at e
    rw [if_pos rfl]
    exact e.symm
  · rw [if_neg hyu] at e
    rw [if_neg hyu]
    rw [Matrix.zero_apply] at e
    exact e.symm

/-- The rank-one part: rank Am ≤ rank X * rank L. -/
theorem uri_counting_rank_Am {F : Type*} [Field F] {N : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι]
    (x l : ι → Fin N → F) :
    (Matrix.of (fun (a b : ι × Fin N) => x a.1 b.2 * l b.1 a.2)).rank ≤
      (Matrix.of fun y i => x y i).rank * (Matrix.of fun u j => l u j).rank := by
  obtain ⟨U, V, hX⟩ := bianca_exists_sum_vecMulVec_of_rank (Matrix.of fun y i => x y i)
  obtain ⟨U', V', hL⟩ := bianca_exists_sum_vecMulVec_of_rank (Matrix.of fun u j => l u j)
  have hfac : Matrix.of (fun (a b : ι × Fin N) => x a.1 b.2 * l b.1 a.2) =
      (Matrix.of fun (a : ι × Fin N) (c : Fin (Matrix.of fun y i => x y i).rank ×
          Fin (Matrix.of fun u j => l u j).rank) => U c.1 a.1 * V' c.2 a.2) *
      (Matrix.of fun (c : Fin (Matrix.of fun y i => x y i).rank × Fin (Matrix.of fun u j => l u j).rank)
          (b : ι × Fin N) => U' c.2 b.1 * V c.1 b.2) := by
    ext ⟨y, j⟩ ⟨u, i⟩
    have e1 := congrFun (congrFun hX y) i
    have e2 := congrFun (congrFun hL u) j
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply] at e1 e2
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [e1, e2, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => by ring))
  rw [hfac]
  calc _ ≤ _ := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin (Matrix.of fun y i => x y i).rank × Fin (Matrix.of fun u j => l u j).rank) :=
        Matrix.rank_le_card_width _
    _ = _ := by simp

/-- **T463: Ada's counting lemma, basis-free, over any field.** -/
theorem uri_ada_counting_lemma (F : Type*) [Field F] (N k : ℕ) : AdaCountingLemma F N k := by
  intro ι _ _ π x l A B h
  have hM := uri_counting_reshuffle ι π x l A B h
  have hlow := uri_block_copies_rank_le (F := F) ι π
  have hadd := bianca_matrix_rank_add_le (Matrix.of (fun (a b : ι × Fin N) => x a.1 b.2 * l b.1 a.2))
    ((Matrix.of fun (a : ι × Fin N) (s : Fin k) => B a.1 a.2 s) *
      (Matrix.of fun (b : ι × Fin N) (s : Fin k) => A b.1 b.2 s)ᵀ)
  rw [← hM] at hadd
  have hB : ((Matrix.of fun (a : ι × Fin N) (s : Fin k) => B a.1 a.2 s) *
      (Matrix.of fun (b : ι × Fin N) (s : Fin k) => A b.1 b.2 s)ᵀ).rank ≤ k := by
    calc _ ≤ _ := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin k) := Matrix.rank_le_card_width _
      _ = k := by simp
  have hA := uri_counting_rank_Am ι x l
  omega
end

/-! ## unit P_N_add_three_ge_six_and_P6_ge_nine_every_field -/
section
open Matrix

/-- **P(N) ≥ N + 3 for every N ≥ 6, over every field (T454)**: Ada's slice counting route (ada_ge_N_add_three_of_counting)
with Uri's basis-free counting lemma (uri_ada_counting_lemma, T463). -/
theorem ada_ge_N_add_three_ge_six {F : Type*} [Field F] (N : ℕ) (hN : 6 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    N + 3 ≤ B.rank + (biancaRealignF C).rank :=
  ada_ge_N_add_three_of_counting N hN (fun k => uri_ada_counting_lemma F N k) B C h

/-- **P(6) ≥ 9 over every field**: the n = 6 rung of the n + 3 ladder. -/
theorem ada_P6_ge_nine {F : Type*} [Field F] (B C : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) F)
    (h : biancaSwapF F (Fin 6) = B + C) : 9 ≤ B.rank + (biancaRealignF C).rank :=
  ada_ge_N_add_three_ge_six 6 le_rfl B C h
end

/-! ## The results in the notation of SwapSplit.lean -/

namespace SwapSplit

theorem swapMat_eq_biancaSwapF (F : Type*) [Field F] (N : ℕ) : swapMat F N = biancaSwapF F (Fin N) := by
  ext p q
  simp only [swapMat, biancaSwapF, Matrix.of_apply]
  exact if_congr ⟨fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩, fun ⟨h1, h2⟩ => ⟨h2.symm, h1.symm⟩⟩ rfl rfl

theorem realign_eq_biancaRealignF {F : Type*} [Field F] {N : ℕ}
    (C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) : realign C = biancaRealignF C := rfl

/-- P(4) ≥ 7 over every field. -/
theorem swap_split_four_ge_seven {F : Type*} [Field F] (B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F)
    (h : swapMat F 4 = B + C) : 7 ≤ B.rank + (realign C).rank := by
  rw [realign_eq_biancaRealignF]
  exact nadia_P4_ge_seven_any_field B C (by rw [← swapMat_eq_biancaSwapF]; exact h)

/-- P(4) = 7 over every field: the value 7 is attained, and every split needs at least 7. -/
theorem swap_split_four_eq_seven (F : Type*) [Field F] :
    (∃ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C ∧ B.rank + (realign C).rank = 7) ∧
    ∀ B C : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) F,
        swapMat F 4 = B + C → 7 ≤ B.rank + (realign C).rank := by
  refine ⟨?_, fun B C h => swap_split_four_ge_seven B C h⟩
  obtain ⟨B, C, h, hle⟩ := daria_P4_le_seven (F := F)
  have h' : swapMat F 4 = B + C := by rw [swapMat_eq_biancaSwapF]; exact h
  refine ⟨B, C, h', le_antisymm ?_ (swap_split_four_ge_seven B C h')⟩
  rw [realign_eq_biancaRealignF]
  exact hle

/-- P(5) ≥ 8 over every field. -/
theorem swap_split_five_ge_eight {F : Type*} [Field F] (B C : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) F)
    (h : swapMat F 5 = B + C) : 8 ≤ B.rank + (realign C).rank := by
  rw [realign_eq_biancaRealignF]
  exact ada_P5_ge_eight B C (by rw [← swapMat_eq_biancaSwapF]; exact h)

/-- P(6) ≥ 9 over every field. -/
theorem swap_split_six_ge_nine {F : Type*} [Field F] (B C : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) F)
    (h : swapMat F 6 = B + C) : 9 ≤ B.rank + (realign C).rank := by
  rw [realign_eq_biancaRealignF]
  exact ada_P6_ge_nine B C (by rw [← swapMat_eq_biancaSwapF]; exact h)

/-- P(N) ≥ N + 3 for every N ≥ 4, over every field. -/
theorem swap_split_ge_add_three {F : Type*} [Field F] (N : ℕ) (hN : 4 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : N + 3 ≤ B.rank + (realign C).rank := by
  obtain rfl | rfl | h6 : N = 4 ∨ N = 5 ∨ 6 ≤ N := by omega
  · exact swap_split_four_ge_seven B C h
  · exact swap_split_five_ge_eight B C h
  · rw [realign_eq_biancaRealignF]
    exact ada_ge_N_add_three_ge_six N h6 B C (by rw [← swapMat_eq_biancaSwapF]; exact h)

end SwapSplit

#print axioms SwapSplit.swap_split_four_eq_seven
#print axioms SwapSplit.swap_split_five_ge_eight
#print axioms SwapSplit.swap_split_six_ge_nine
#print axioms SwapSplit.swap_split_ge_add_three
