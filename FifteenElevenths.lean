/-
The bound P(N) ≥ 15 N / 11 for N ≥ 5, over every field.

The body of this file is the part of the dependency closure of the library unit
minsum_ge_fifteen_elevenths_N_every_field of an automated multi-agent run that is not already in
SmallValues.lean, concatenated in dependency order (one section per unit). The only change is that two unused
lines `open _root_.Groundwork` are removed; that namespace exists only in the run's own environment. The proof is a
certificate: 189 inequalities between dimensions of sums of column spaces of five slices, each proved for
every slice system, and one arithmetic lemma that combines them. The last section states the result with the
definitions of SwapSplit.lean.
-/
import Mathlib
import SwapSplit
import SmallValues

/-! ## unit T444_iSup_finset_polymatroid_rows -/
section
open Matrix

/-- **T444 FINAL helper (Lena)**: the map S ↦ finrank (⨆ i ∈ S, W i) on finsets is submodular in the form used by the
LP rows of R214: for S ⊆ U, S ⊆ V and T = U ∪ V, f(T) + f(S) ≤ f(U) + f(V). -/
theorem lena_iSup_finset_submod {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    [DecidableEq ι] (W : ι → Submodule F M) (S U V T : Finset ι) (hSU : S ⊆ U) (hSV : S ⊆ V) (hT : T = U ∪ V) :
    Module.finrank F ↥(⨆ i ∈ T, W i) + Module.finrank F ↥(⨆ i ∈ S, W i) ≤
      Module.finrank F ↥(⨆ i ∈ U, W i) + Module.finrank F ↥(⨆ i ∈ V, W i) := by
  subst hT
  rw [Finset.iSup_union]
  have hle : (⨆ i ∈ S, W i) ≤ (⨆ i ∈ U, W i) ⊓ (⨆ i ∈ V, W i) :=
    le_inf (iSup₂_le fun i hi => le_iSup₂_of_le i (hSU hi) le_rfl)
      (iSup₂_le fun i hi => le_iSup₂_of_le i (hSV hi) le_rfl)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (⨆ i ∈ U, W i) (⨆ i ∈ V, W i)
  omega

/-- Monotonicity of S ↦ finrank (⨆ i ∈ S, W i). -/
theorem lena_iSup_finset_mono {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (W : ι → Submodule F M) (S T : Finset ι) (h : S ⊆ T) :
    Module.finrank F ↥(⨆ i ∈ S, W i) ≤ Module.finrank F ↥(⨆ i ∈ T, W i) :=
  Submodule.finrank_mono (iSup₂_le fun i hi => le_iSup₂_of_le i (h hi) le_rfl)

/-- The empty finset gives finrank 0. -/
theorem lena_iSup_finset_empty {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (W : ι → Submodule F M) : Module.finrank F ↥(⨆ i ∈ (∅ : Finset ι), W i) = 0 := by
  simp

/-- Singletons and pairs. -/
theorem lena_iSup_finset_singleton {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M]
    (W : ι → Submodule F M) (a : ι) : (⨆ i ∈ ({a} : Finset ι), W i) = W a := by
  simp

theorem lena_iSup_finset_pair {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M] [DecidableEq ι]
    (W : ι → Submodule F M) (a b : ι) : (⨆ i ∈ ({a, b} : Finset ι), W i) = W a ⊔ W b := by
  rw [Finset.iSup_insert, Finset.iSup_singleton]
end

/-! ## unit T444_R214_integer_polymatroid_fl -/
section
open Matrix

/-- **T444 (Lena)**: the integer-valued polymatroid of ten subspaces, S ↦ finrank (⨆ i ∈ S, W i), as used by the rows of
Gideon's exact certificate for Silas's R214 (index y for A_y, 5 + y for C_y). -/
noncomputable def lenaR214Fl {F M : Type*} [Field F] [AddCommGroup M] [Module F M] (W : Fin 10 → Submodule F M)
    (S : Finset (Fin 10)) : ℤ :=
  (Module.finrank F ↥(⨆ i ∈ S, W i) : ℤ)

theorem lena_fl_submod {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (W : Fin 10 → Submodule F M) (S U V T : Finset (Fin 10)) (hSU : S ⊆ U) (hSV : S ⊆ V) (hT : T = U ∪ V) :
    lenaR214Fl W T + lenaR214Fl W S ≤ lenaR214Fl W U + lenaR214Fl W V := by
  unfold lenaR214Fl
  exact_mod_cast lena_iSup_finset_submod W S U V T hSU hSV hT

theorem lena_fl_mono {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (W : Fin 10 → Submodule F M) (S T : Finset (Fin 10)) (h : S ⊆ T) : lenaR214Fl W S ≤ lenaR214Fl W T := by
  unfold lenaR214Fl
  exact_mod_cast lena_iSup_finset_mono W S T h

theorem lena_fl_empty {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (W : Fin 10 → Submodule F M) : lenaR214Fl W ∅ = 0 := by
  unfold lenaR214Fl
  rw [lena_iSup_finset_empty W]; rfl

theorem lena_fl_single {F M : Type*} [Field F] [AddCommGroup M] [Module F M] (W : Fin 10 → Submodule F M)
    (a : Fin 10) : lenaR214Fl W {a} = (Module.finrank F ↥(W a) : ℤ) := by
  unfold lenaR214Fl
  rw [lena_iSup_finset_singleton W a]

theorem lena_fl_pair {F M : Type*} [Field F] [AddCommGroup M] [Module F M] (W : Fin 10 → Submodule F M)
    (a b : Fin 10) : lenaR214Fl W {a, b} = (Module.finrank F ↥(W a ⊔ W b) : ℤ) := by
  unfold lenaR214Fl
  rw [lena_iSup_finset_pair W a b]
end

/-! ## unit T444_R214_slice_subspaces_W -/
section
open Matrix

/-- **T444 (Lena)**: the ten column spaces of five slices, A_y = col X (s y) at index y and C_y = col P (s y) at 5 + y. -/
noncomputable def lenaR214W {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) : Fin 10 → Submodule F (Fin N → F) :=
  fun i => if h : i.val < 5 then LinearMap.range (X (s ⟨i.val, h⟩)).mulVecLin
    else LinearMap.range (P (s ⟨i.val - 5, by omega⟩)).mulVecLin

theorem lena_W_A {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) (y : Fin 5) (i : Fin 10) (hi : i.val = y.val) :
    lenaR214W X P s i = LinearMap.range (X (s y)).mulVecLin := by
  have h : i.val < 5 := by omega
  have e : (⟨i.val, h⟩ : Fin 5) = y := Fin.ext hi
  simp only [lenaR214W, dif_pos h, e]

theorem lena_W_C {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) (y : Fin 5) (i : Fin 10) (hi : i.val = y.val + 5) :
    lenaR214W X P s i = LinearMap.range (P (s y)).mulVecLin := by
  have h : ¬ i.val < 5 := by omega
  have e : (⟨i.val - 5, by omega⟩ : Fin 5) = y := Fin.ext (by show i.val - 5 = y.val; omega)
  simp only [lenaR214W, dif_neg h, e]

/-- Singleton values: the rank of X (s y), resp. P (s y). -/
theorem lena_fl_A {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) (y : Fin 5) (i : Fin 10) (hi : i.val = y.val) :
    lenaR214Fl (lenaR214W X P s) {i} = ((X (s y)).rank : ℤ) := by
  rw [lena_fl_single, lena_W_A X P s y i hi]; rfl

theorem lena_fl_C {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) (y : Fin 5) (i : Fin 10) (hi : i.val = y.val + 5) :
    lenaR214Fl (lenaR214W X P s) {i} = ((P (s y)).rank : ℤ) := by
  rw [lena_fl_single, lena_W_C X P s y i hi]; rfl

/-- Pair values {A_y, C_u}: finrank (col X (s y) ⊔ col P (s u)). -/
theorem lena_fl_AC {F : Type*} [Field F] {N a b : ℕ} (X : Fin N → Matrix (Fin N) (Fin a) F)
    (P : Fin N → Matrix (Fin N) (Fin b) F) (s : Fin 5 → Fin N) (y u : Fin 5) (i j : Fin 10) (hi : i.val = y.val)
    (hj : j.val = u.val + 5) :
    lenaR214Fl (lenaR214W X P s) {i, j} =
      (Module.finrank F ↥(LinearMap.range (X (s y)).mulVecLin ⊔ LinearMap.range (P (s u)).mulVecLin) : ℤ) := by
  rw [lena_fl_pair, lena_W_A X P s y i hi, lena_W_C X P s u j hj]
end

/-! ## unit minsum_ge_five_quarters_N_every_field -/
section

open Matrix


/-- T347 Lemma 1 (Nadia): per-slice coranks. If X Yᵀ + P Qᵀ = 1 (N × N), then N ≤ rank (Yᵀ X) + rank (Qᵀ P), i.e. the
coranks of Yᵀ X and Qᵀ P add up to at most d = r + k − N. The kernels of Yᵀ X and Qᵀ P embed, by v ↦ (v, −Qᵀ X v) and
u ↦ (−Yᵀ P u, u), into the kernel of [X P] (dimension r + k − N) with trivial intersection. -/
theorem nadia_slice_corank {F : Type*} [Field F] {N r k : ℕ}
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
  -- the two kernel identities
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


/-- Excess triangle (submodularity): dim(A ⊔ C) + dim B ≤ dim(A ⊔ B) + dim(B ⊔ C). -/
theorem nadia_finrank_sup_triangle {F : Type*} [Field F] {N : ℕ} (A B C : Submodule F (Fin N → F)) :
    Module.finrank F ↥(A ⊔ C) + Module.finrank F B ≤ Module.finrank F ↥(A ⊔ B) + Module.finrank F ↥(B ⊔ C) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) (B ⊔ C)
  have h1 : Module.finrank F ↥(A ⊔ C) ≤ Module.finrank F ↥((A ⊔ B) ⊔ (B ⊔ C)) :=
    Submodule.finrank_mono (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
  have h2 : Module.finrank F B ≤ Module.finrank F ↥((A ⊔ B) ⊓ (B ⊔ C)) :=
    Submodule.finrank_mono (le_inf le_sup_right le_sup_left)
  omega

/-- T347 Lemma 2 (Nadia): approximate inclusions between slices a ≠ b, as excess bounds.
(i) dim(col X_a ⊔ col P_b) + rank(Y_bᵀ X_b) ≤ dim col P_b + r; (ii) dim(col P_b ⊔ col X_a) + rank(Q_aᵀ P_a) ≤ dim col X_a + k. -/
theorem nadia_slice_excess {F : Type*} [Field F] {N r k : ℕ}
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
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (X a).mulVecLin) (LinearMap.range (P b).mulVecLin)
    have h3 := nadia_rank_add_rank_le_rank_mul (X a) ((Y b)ᵀ * X b)
    simp only [Fintype.card_fin] at h3
    have h4 : (X a * ((Y b)ᵀ * X b)).rank = Module.finrank F (LinearMap.range (X a * ((Y b)ᵀ * X b)).mulVecLin) := rfl
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
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (P b).mulVecLin) (LinearMap.range (X a).mulVecLin)
    have h3 := nadia_rank_add_rank_le_rank_mul (P b) ((Q a)ᵀ * P a)
    simp only [Fintype.card_fin] at h3
    have h4 : (P b * ((Q a)ᵀ * P a)).rank = Module.finrank F (LinearMap.range (P b * ((Q a)ᵀ * P a)).mulVecLin) := rfl
    have h5 : (P b).rank = Module.finrank F (LinearMap.range (P b).mulVecLin) := rfl
    omega

/-- T347 Lemma 3 (Nadia): the corank three-cycle over distinct slices a, b, c. -/
theorem nadia_slice_three_cycle {F : Type*} [Field F] {N r k : ℕ}
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
  · have E1 := (nadia_slice_excess X Y P Q ho c a (Ne.symm hac)).2
    have E2 := (nadia_slice_excess X Y P Q ho c b (Ne.symm hbc)).1
    have E3 := (nadia_slice_excess X Y P Q ho a b hab).2
    have T1 := nadia_finrank_sup_triangle (LinearMap.range (P a).mulVecLin) (LinearMap.range (X c).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have T2 := nadia_finrank_sup_triangle (LinearMap.range (X c).mulVecLin) (LinearMap.range (P b).mulVecLin)
      (LinearMap.range (X a).mulVecLin)
    have h1 := htop' a
    have h2 := hXr a
    omega
  · have E1 := (nadia_slice_excess X Y P Q ho a c hac).1
    have E2 := (nadia_slice_excess X Y P Q ho b c hbc).2
    have E3 := (nadia_slice_excess X Y P Q ho b a (Ne.symm hab)).1
    have T1 := nadia_finrank_sup_triangle (LinearMap.range (X a).mulVecLin) (LinearMap.range (P c).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have T2 := nadia_finrank_sup_triangle (LinearMap.range (P c).mulVecLin) (LinearMap.range (X b).mulVecLin)
      (LinearMap.range (P a).mulVecLin)
    have h1 := htop a
    have h2 := hPk a
    omega

/-- T347 (Nadia): the slice identities force 5N ≤ 4(r + k) for N ≥ 3 (three rotations of the three-cycle on slices
0, 1, 2 in both orientations, plus the corank lemma on each slice). -/
theorem nadia_slice_five_quarters {F : Type*} [Field F] {N r k : ℕ} (hN : 3 ≤ N)
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) : 5 * N ≤ 4 * (r + k) := by
  set s0 : Fin N := ⟨0, by omega⟩
  set s1 : Fin N := ⟨1, by omega⟩
  set s2 : Fin N := ⟨2, by omega⟩
  have h01 : s0 ≠ s1 := by simp [s0, s1, Fin.ext_iff]
  have h02 : s0 ≠ s2 := by simp [s0, s2, Fin.ext_iff]
  have h12 : s1 ≠ s2 := by simp [s1, s2, Fin.ext_iff]
  have c0 := nadia_slice_corank (X s0) (Y s0) (P s0) (Q s0) (hd s0)
  have c1 := nadia_slice_corank (X s1) (Y s1) (P s1) (Q s1) (hd s1)
  have c2 := nadia_slice_corank (X s2) (Y s2) (P s2) (Q s2) (hd s2)
  have a1 := nadia_slice_three_cycle X Y P Q hd ho s0 s1 s2 h01 h02 h12
  have a2 := nadia_slice_three_cycle X Y P Q hd ho s1 s2 s0 h12 (Ne.symm h01) (Ne.symm h02)
  have a3 := nadia_slice_three_cycle X Y P Q hd ho s2 s0 s1 (Ne.symm h02) (Ne.symm h12) h01
  omega

/-- **T347 (Nadia): minsum(N) ≥ 5N/4 over every field.** If SWAP_N = B + C over a field F and N ≥ 3, then
5N ≤ 4 (rank B + OS(C)). Bianca's slice factorization (copied from minsum_ge_eight_sevenths_N_every_field, with
credit) gives the slice identities; nadia_slice_five_quarters finishes. Improves 8N/7; tight at N = 3. -/
theorem nadia_minsumF_ge_five_quarters {F : Type*} [Field F] (N : ℕ) (hN : 3 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    5 * N ≤ 4 * (B.rank + (biancaRealignF C).rank) := by
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
  exact nadia_slice_five_quarters hN X Y PP QQ hd ho
end

/-! ## unit sprintB_transposed_slice_system_corank_excess -/
section

open Matrix

/-- Sprint B brick (Milo): the transposed slice system (X, Y, P, Q) -> (Y, X, Q, P) satisfies hd again. -/
theorem milo_slice_transpose_hd {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) :
    ∀ y, Y y * (X y)ᵀ + Q y * (P y)ᵀ = 1 := by
  intro y
  have h := congrArg Matrix.transpose (hd y)
  simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one] using h

/-- Sprint B brick (Milo): the transposed slice system satisfies ho again (with the two slice indices swapped). -/
theorem milo_slice_transpose_ho {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) :
    ∀ y u, y ≠ u → Y y * (X u)ᵀ + Q u * (P y)ᵀ = 0 := by
  intro y u hyu
  have h := congrArg Matrix.transpose (ho u y (Ne.symm hyu))
  simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_zero] using h

/-- Sprint B brick (Milo): Nadia's per-slice corank bound on the transposed side. -/
theorem milo_slice_corank_transpose {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) (y : Fin N) :
    N ≤ ((X y)ᵀ * Y y).rank + ((P y)ᵀ * Q y).rank :=
  nadia_slice_corank (Y y) (X y) (Q y) (P y) (milo_slice_transpose_hd X Y P Q hd y)

/-- Sprint B brick (Milo): Nadia's excess bounds (i)/(ii) on the transposed side (col Y, col Q). -/
theorem milo_slice_excess_transpose {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (a b : Fin N) (hab : a ≠ b) :
    Module.finrank F ↥(LinearMap.range (Y a).mulVecLin ⊔ LinearMap.range (Q b).mulVecLin) + ((X b)ᵀ * Y b).rank ≤
        Module.finrank F (LinearMap.range (Q b).mulVecLin) + r ∧
    Module.finrank F ↥(LinearMap.range (Q b).mulVecLin ⊔ LinearMap.range (Y a).mulVecLin) + ((P a)ᵀ * Q a).rank ≤
        Module.finrank F (LinearMap.range (Y a).mulVecLin) + k :=
  nadia_slice_excess Y X Q P (milo_slice_transpose_ho X Y P Q ho) a b hab
end

/-! ## unit fourthirds_E1_slice_col_sums_full -/
section

open Matrix

/-- 4n/3 brick E1 (Milo): in a slice system, col X_y + col P_y is the whole space. -/
theorem milo_slice_col_XP_sup_top {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) (y : Fin N) :
    LinearMap.range (X y).mulVecLin ⊔ LinearMap.range (P y).mulVecLin = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = (X y) *ᵥ ((Y y)ᵀ *ᵥ x) + (P y) *ᵥ ((Q y)ᵀ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hd y, Matrix.one_mulVec]
  rw [hx]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

/-- 4n/3 brick E1 (Milo): finrank (col X_y + col P_y) = N. -/
theorem milo_slice_col_XP_finrank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) (y : Fin N) :
    Module.finrank F ↥(LinearMap.range (X y).mulVecLin ⊔ LinearMap.range (P y).mulVecLin) = N := by
  rw [milo_slice_col_XP_sup_top X Y P Q hd y, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- 4n/3 brick E1 (Milo): finrank (col Y_y + col Q_y) = N (the transposed side). -/
theorem milo_slice_col_YQ_finrank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1) (y : Fin N) :
    Module.finrank F ↥(LinearMap.range (Y y).mulVecLin ⊔ LinearMap.range (Q y).mulVecLin) = N :=
  milo_slice_col_XP_finrank Y X Q P (milo_slice_transpose_hd X Y P Q hd) y
end

/-! ## unit slice_intersection_rank_bound_two_factorizations -/
section
open Matrix

/-- R195's intersection bound (sprint group B, Hugo): if one matrix factors two ways, M = X * Y = P * Q, then
rank M ≤ dim (col X ⊓ col P). In the slice system M = X_y Y_uᵀ = -(P_u Q_yᵀ) (take Q := -Q_yᵀ). Any field. -/
theorem hugo_rank_le_finrank_range_inf {F : Type*} [Field F] {m n p o : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype o] [DecidableEq n] [DecidableEq p] [DecidableEq o]
    (X : Matrix m n F) (Y : Matrix n o F) (P : Matrix m p F) (Q : Matrix p o F) (h : X * Y = P * Q) :
    (X * Y).rank ≤ Module.finrank F
      (LinearMap.range X.mulVecLin ⊓ LinearMap.range P.mulVecLin : Submodule F (m → F)) := by
  have h1 : LinearMap.range (X * Y).mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  have h2 : LinearMap.range (X * Y).mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rw [h, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
  unfold Matrix.rank
  exact Submodule.finrank_mono (le_inf h1 h2)

/-- Row-space twin: with M = X * Y = P * Q, rank M ≤ dim (row Y ⊓ row Q) (columns of Yᵀ and Qᵀ). -/
theorem hugo_rank_le_finrank_range_inf_rows {F : Type*} [Field F] {m n p o : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype o] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq o]
    (X : Matrix m n F) (Y : Matrix n o F) (P : Matrix m p F) (Q : Matrix p o F) (h : X * Y = P * Q) :
    (X * Y).rank ≤ Module.finrank F
      (LinearMap.range Yᵀ.mulVecLin ⊓ LinearMap.range Qᵀ.mulVecLin : Submodule F (o → F)) := by
  have ht : Yᵀ * Xᵀ = Qᵀ * Pᵀ := by rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h]
  have := hugo_rank_le_finrank_range_inf Yᵀ Xᵀ Qᵀ Pᵀ ht
  rwa [← Matrix.transpose_mul, Matrix.rank_transpose] at this

/-- Step-0 witness: X = P = 1, Y = Q = 1 over ℚ (n = 2): rank 1 = 2 ≤ dim(⊤ ⊓ ⊤) = 2. -/
example : ((1 : Matrix (Fin 2) (Fin 2) ℚ) * 1).rank ≤ Module.finrank ℚ
    (LinearMap.range (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVecLin ⊓ LinearMap.range (1 : Matrix (Fin 2) (Fin 2) ℚ).mulVecLin :
      Submodule ℚ (Fin 2 → ℚ)) :=
  hugo_rank_le_finrank_range_inf 1 1 1 1 rfl
end

/-! ## unit R195_slice_sumN_cap_facts -/
section
open Matrix

/-- R195 fact kind [sumN] (Hugo): in a slice system, hd gives range X_y ⊔ range P_y = ⊤. Any field. -/
theorem hugo_slice_sup_eq_top {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F) (hd : X * Yᵀ + P * Qᵀ = 1) :
    LinearMap.range X.mulVecLin ⊔ LinearMap.range P.mulVecLin = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = X *ᵥ (Yᵀ *ᵥ x) + P *ᵥ (Qᵀ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hd, Matrix.one_mulVec]
  rw [hx]
  exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

/-- [sumN] as a dimension: finrank (range X_y ⊔ range P_y) = N. -/
theorem hugo_slice_sup_finrank {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F) (hd : X * Yᵀ + P * Qᵀ = 1) :
    Module.finrank F (LinearMap.range X.mulVecLin ⊔ LinearMap.range P.mulVecLin : Submodule F (Fin N → F)) = N := by
  rw [hugo_slice_sup_eq_top X Y P Q hd, finrank_top, Module.finrank_fin_fun]

/-- [sumN] right side: hd also gives range Y_y ⊔ range Q_y = ⊤ (transpose of hd). -/
theorem hugo_slice_sup_eq_top_right {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Matrix (Fin N) (Fin r) F) (P Q : Matrix (Fin N) (Fin k) F) (hd : X * Yᵀ + P * Qᵀ = 1) :
    LinearMap.range Y.mulVecLin ⊔ LinearMap.range Q.mulVecLin = ⊤ := by
  apply hugo_slice_sup_eq_top Y X Q P
  have h := congrArg Matrix.transpose hd
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.transpose_one] at h
  exact h

/-- R195 fact kind [cap] (Hugo), modular form: if M = X * Y' = P * Q' then
rank M + finrank (range X ⊔ range P) ≤ finrank (range X) + finrank (range P). -/
theorem hugo_cap_modular {F : Type*} [Field F] {m n p o : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype o] [DecidableEq n] [DecidableEq p] [DecidableEq o]
    (X : Matrix m n F) (Y' : Matrix n o F) (P : Matrix m p F) (Q' : Matrix p o F) (h : X * Y' = P * Q') :
    (X * Y').rank + Module.finrank F (LinearMap.range X.mulVecLin ⊔ LinearMap.range P.mulVecLin : Submodule F (m → F)) ≤
      Module.finrank F (LinearMap.range X.mulVecLin) + Module.finrank F (LinearMap.range P.mulVecLin) := by
  have h1 := hugo_rank_le_finrank_range_inf X Y' P Q' h
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range X.mulVecLin) (LinearMap.range P.mulVecLin)
  omega

/-- [cap] in the slice system (left side): for y ≠ u, ho gives M = X_y * (Y_u)ᵀ = P_u * (-(Q_y)ᵀ), so
rank M + finrank (range X_y ⊔ range P_u) ≤ rank X_y + rank P_u. -/
theorem hugo_slice_cap_left {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (y u : Fin N) (hyu : y ≠ u) :
    (X y * (Y u)ᵀ).rank + Module.finrank F (LinearMap.range (X y).mulVecLin ⊔ LinearMap.range (P u).mulVecLin :
      Submodule F (Fin N → F)) ≤ (X y).rank + (P u).rank := by
  have h : X y * (Y u)ᵀ = P u * (-(Q y)ᵀ) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left (ho y u hyu)
  exact hugo_cap_modular (X y) (Y u)ᵀ (P u) (-(Q y)ᵀ) h

/-- [cap] in the slice system (right side): rank M + finrank (range Y_u ⊔ range Q_y) ≤ rank Y_u + rank Q_y. -/
theorem hugo_slice_cap_right {F : Type*} [Field F] {N r k : ℕ}
    (X Y : Fin N → Matrix (Fin N) (Fin r) F) (P Q : Fin N → Matrix (Fin N) (Fin k) F)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (y u : Fin N) (hyu : y ≠ u) :
    (X y * (Y u)ᵀ).rank + Module.finrank F (LinearMap.range (Y u).mulVecLin ⊔ LinearMap.range (Q y).mulVecLin :
      Submodule F (Fin N → F)) ≤ (Y u).rank + (Q y).rank := by
  have h : (Y u) * (X y)ᵀ = (Q y) * (-(P u)ᵀ) := by
    have h0 := congrArg Matrix.transpose (ho y u hyu)
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.transpose_zero] at h0
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left h0
  have hr : (X y * (Y u)ᵀ).rank = (Y u * (X y)ᵀ).rank := by
    rw [← Matrix.rank_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hr]
  exact hugo_cap_modular (Y u) (X y)ᵀ (Q y) (-(P u)ᵀ) h
end

/-! ## unit T444_R214_rank_neg -/
section
open Matrix

/-- **T444 helper (Lena)**: negation does not change the rank of a square matrix over a field. -/
theorem lena_rank_neg {F : Type*} [Field F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : (-M).rank = M.rank := by
  have hu : IsUnit (-1 : Matrix (Fin n) (Fin n) F).det := by
    rw [Matrix.det_neg, Matrix.det_one, mul_one]; exact isUnit_neg_one.pow _
  rw [show -M = M * (-1 : Matrix (Fin n) (Fin n) F) by rw [Matrix.mul_neg, Matrix.mul_one],
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu]
end

/-! ## unit T444_R214_rows_part0 -/
section
open Matrix

/-- T444 (Lena): rows 0..31 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_0 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (-1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 1} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({2, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({2, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({4, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 5, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 5, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 6} : Finset (Fin 10)) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := lena_fl_submod (lenaR214W X P s) ∅ {0} {5} {0, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) ∅ {1} {6} {1, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) ∅ {2} {7} {2, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) ∅ {3} {8} {3, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) ∅ {4} {9} {4, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {0} {0, 6} {0, 7} {0, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {0} {0, 7} {0, 8} {0, 7, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {1} {0, 1} {1, 5} {0, 1, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {0, 1} {0, 1, 4} {0, 1, 9} {0, 1, 4, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {2} {2, 5} {2, 8} {2, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {3} {3, 4} {3, 9} {3, 4, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {3} {3, 6} {3, 7} {3, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {4} {1, 4} {4, 6} {1, 4, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {4} {4, 6} {4, 7} {4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {1, 4} {1, 2, 4} {1, 4, 7} {1, 2, 4, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {1, 4} {1, 4, 5} {1, 4, 8} {1, 4, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {1, 4} {1, 4, 7} {1, 4, 8} {1, 4, 7, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 1, 4} {0, 1, 4, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {1, 2, 4} {1, 2, 4, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {3, 4} {0, 3, 4} {3, 4, 5} {0, 3, 4, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {3, 4} {3, 4, 6} {3, 4, 7} {3, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 3, 4} {0, 3, 4, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {5} {1, 5} {4, 5} {1, 4, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {5} {3, 5} {4, 5} {3, 4, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {5} {3, 5} {5, 8} {3, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 5} {0, 1, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 5} {0, 3, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 5} {0, 5, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 3, 5} {0, 3, 4, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {1, 2, 4, 5} {1, 2, 4, 5, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {6} {3, 6} {4, 6} {3, 4, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {1, 6} {1, 4, 6} (by decide)
    linarith only [a]
end

/-! ## unit T444_R214_rows_part1 -/
section
open Matrix

/-- T444 (Lena): rows 32..63 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_1 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({2, 7, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({2, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({3, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 5, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 7, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 5, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({2, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({5, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 5, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 2, 4, 5, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 5, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 7, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({4, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 4, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({7, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 4, 7, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 7, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 7, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({4, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({4, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({3, 4, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W X P s) ({1, 4, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({0, 1, 4, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({0, 5} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({1, 6} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({2, 7} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({3, 8} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W X P s) ({4, 9} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := lena_fl_mono (lenaR214W X P s) {1, 6} {1, 6, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {7} {1, 7} {4, 7} {1, 4, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {7} {1, 7} {6, 7} {1, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {7} {3, 7} {4, 7} {3, 4, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {2, 7} {1, 2, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {2, 7} {2, 7, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {1, 2, 7} {1, 2, 4, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 3, 4, 7} {0, 3, 4, 6, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {6, 7} {0, 6, 7} {3, 6, 7} {0, 3, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {6, 7} {0, 6, 7} {4, 6, 7} {0, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {0, 6, 7} {0, 3, 6, 7} {0, 4, 6, 7} {0, 3, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {3, 6, 7} {0, 3, 6, 7} {3, 4, 6, 7} {0, 3, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {8} {0, 8} {5, 8} {0, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {8} {1, 8} {4, 8} {1, 4, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {8} {2, 8} {7, 8} {2, 7, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {3, 8} {3, 5, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {0, 1, 4, 8} {0, 1, 4, 7, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {5, 8} {1, 5, 8} {2, 5, 8} {1, 2, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {1, 5, 8} {1, 2, 5, 8} {1, 4, 5, 8} {1, 2, 4, 5, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {7, 8} {0, 7, 8} {4, 7, 8} {0, 4, 7, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {4, 7, 8} {0, 4, 7, 8} {1, 4, 7, 8} {0, 1, 4, 7, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W X P s) {9} {0, 9} {1, 9} {0, 1, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {4, 9} {1, 4, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {4, 9} {3, 4, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W X P s) {1, 4, 9} {0, 1, 4, 9} (by decide)
    linarith only [a]
  · have a := milo_slice_col_XP_finrank X Y P Q hd (s 0)
    have d := lena_fl_AC X P s 0 0 0 5 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_XP_finrank X Y P Q hd (s 1)
    have d := lena_fl_AC X P s 1 1 1 6 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_XP_finrank X Y P Q hd (s 2)
    have d := lena_fl_AC X P s 2 2 2 7 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_XP_finrank X Y P Q hd (s 3)
    have d := lena_fl_AC X P s 3 3 3 8 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_XP_finrank X Y P Q hd (s 4)
    have d := lena_fl_AC X P s 4 4 4 9 rfl rfl
    linarith only [a, d]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0} {0, 1} {0, 6} {0, 1, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0} {0, 6} {0, 7} {0, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
end

/-! ## unit T444_R214_rows_part2 -/
section
open Matrix

/-- T444 (Lena): rows 64..95 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_2 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 5} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 5, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 5, 6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 5, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({5, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 5, 6} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 5, 6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 5, 6} : Finset (Fin 10)) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := lena_fl_submod (lenaR214W Y Q s) {0} {0, 8} {0, 9} {0, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {1} {0, 1} {1, 5} {0, 1, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {1} {1, 8} {1, 9} {1, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0, 1} {0, 1, 2} {0, 1, 7} {0, 1, 2, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {2} {2, 8} {2, 9} {2, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 1, 2} {0, 1, 2, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {3} {0, 3} {3, 5} {0, 3, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {3} {3, 5} {3, 6} {3, 5, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {3} {3, 6} {3, 7} {3, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0, 3} {0, 3, 4} {0, 3, 9} {0, 3, 4, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0, 3} {0, 3, 6} {0, 3, 7} {0, 3, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {4} {0, 4} {4, 5} {0, 4, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {4} {2, 4} {4, 7} {2, 4, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {4} {4, 6} {4, 7} {4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0, 4} {0, 3, 4} {0, 4, 8} {0, 3, 4, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {2, 4} {2, 3, 4} {2, 4, 8} {2, 3, 4, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {2, 4} {2, 4, 5} {2, 4, 6} {2, 4, 5, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 3, 4} {0, 3, 4, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {2, 3, 4} {2, 3, 4, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {5} {1, 5} {5, 6} {1, 5, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {5} {2, 5} {4, 5} {2, 4, 5} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 5} {0, 1, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 5} {0, 3, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 5} {0, 4, 5} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {2, 3, 4, 5} {2, 3, 4, 5, 6} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {6} {0, 6} {3, 6} {0, 3, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {6} {2, 6} {4, 6} {2, 4, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {1, 6} {0, 1, 6} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {1, 6} {1, 5, 6} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {1, 6} {1, 6, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {5, 6} {2, 5, 6} {3, 5, 6} {2, 3, 5, 6} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {2, 5, 6} {2, 3, 5, 6} {2, 4, 5, 6} {2, 3, 4, 5, 6} (by decide) (by decide) (by decide)
    linarith only [a]
end

/-! ## unit T444_R214_rows_part3 -/
section
open Matrix

/-- T444 (Lena): rows 96..127 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_3 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 2, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 2, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 4, 8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 8, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 8, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 4, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 4, 8} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 3, 4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 4, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 4, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 3, 4, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 8, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 2, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 8, 9} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 2, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 1, 2, 8, 9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({0, 5} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({1, 6} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({2, 7} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({3, 8} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (-1) * lenaR214Fl (lenaR214W Y Q s) ({4, 9} : Finset (Fin 10)) ≤ (-1) * (N : ℤ) ∧
      (1) * ((X (s 0) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 0) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := lena_fl_submod (lenaR214W Y Q s) {7} {0, 7} {1, 7} {0, 1, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {7} {0, 7} {3, 7} {0, 3, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {7} {1, 7} {6, 7} {1, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {2, 7} {0, 2, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {2, 7} {2, 4, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 2, 7} {0, 1, 2, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 3, 4, 7} {0, 3, 4, 6, 7} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {6, 7} {0, 6, 7} {3, 6, 7} {0, 3, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {6, 7} {0, 6, 7} {4, 6, 7} {0, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {0, 6, 7} {0, 3, 6, 7} {0, 4, 6, 7} {0, 3, 4, 6, 7} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {8} {0, 8} {4, 8} {0, 4, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {8} {2, 8} {4, 8} {2, 4, 8} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {0, 1, 2, 8} {0, 1, 2, 8, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {3, 8} {3, 4, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {3, 8} {3, 8, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {3, 4, 8} {0, 3, 4, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {3, 4, 8} {2, 3, 4, 8} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {9} {0, 9} {3, 9} {0, 3, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {9} {3, 9} {8, 9} {3, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {4, 9} {3, 4, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_mono (lenaR214W Y Q s) {3, 4, 9} {0, 3, 4, 9} (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {8, 9} {0, 8, 9} {1, 8, 9} {0, 1, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {8, 9} {1, 8, 9} {2, 8, 9} {1, 2, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := lena_fl_submod (lenaR214W Y Q s) {1, 8, 9} {0, 1, 8, 9} {1, 2, 8, 9} {0, 1, 2, 8, 9} (by decide) (by decide) (by decide)
    linarith only [a]
  · have a := milo_slice_col_YQ_finrank X Y P Q hd (s 0)
    have d := lena_fl_AC Y Q s 0 0 0 5 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_YQ_finrank X Y P Q hd (s 1)
    have d := lena_fl_AC Y Q s 1 1 1 6 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_YQ_finrank X Y P Q hd (s 2)
    have d := lena_fl_AC Y Q s 2 2 2 7 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_YQ_finrank X Y P Q hd (s 3)
    have d := lena_fl_AC Y Q s 3 3 3 8 rfl rfl
    linarith only [a, d]
  · have a := milo_slice_col_YQ_finrank X Y P Q hd (s 4)
    have d := lena_fl_AC Y Q s 4 4 4 9 rfl rfl
    linarith only [a, d]
  · have a := hugo_slice_cap_left X Y P Q ho (s 0) (s 1) (hs 0 1 (by decide))
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_C X P s 1 6 rfl
    have d := lena_fl_AC X P s 0 1 0 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 0) (s 1) (hs 0 1 (by decide))
    have b := lena_fl_A Y Q s 1 1 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    have d := lena_fl_AC Y Q s 1 0 1 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 0)) (Y (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_A Y Q s 1 1 rfl
    linarith only [a, b, c]
end

/-! ## unit T444_R214_rows_part4 -/
section
open Matrix

/-- T444 (Lena): rows 128..159 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_4 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (-1) * ((X (s 0) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 0) * (Y (s 2))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 0) * (Y (s 3))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({0, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 0) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 0) * (Y (s 4))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({5} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 2))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 3))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({1, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 1) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 6} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 4))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({1} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (-1) * ((X (s 1) * (Y (s 4))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({6} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 2) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 2) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (-1) * ((X (s 2) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({2, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 7} : Finset (Fin 10)) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 1)) (Q (s 0))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 0) * (Y (s 1))ᵀ).rank = (P (s 1) * (Q (s 0))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 0 1 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 1 6 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 0) (s 2) (hs 0 2 (by decide))
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_C X P s 2 7 rfl
    have d := lena_fl_AC X P s 0 2 0 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 0) (s 2) (hs 0 2 (by decide))
    have b := lena_fl_A Y Q s 2 2 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    have d := lena_fl_AC Y Q s 2 0 2 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 0)) (Y (s 2))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_A Y Q s 2 2 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 0) (s 3) (hs 0 3 (by decide))
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_C X P s 3 8 rfl
    have d := lena_fl_AC X P s 0 3 0 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 0) (s 3) (hs 0 3 (by decide))
    have b := lena_fl_A Y Q s 3 3 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    have d := lena_fl_AC Y Q s 3 0 3 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 0)) (Y (s 3))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_A Y Q s 3 3 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 0) (s 4) (hs 0 4 (by decide))
    have b := lena_fl_A X P s 0 0 rfl
    have c := lena_fl_C X P s 4 9 rfl
    have d := lena_fl_AC X P s 0 4 0 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 0) (s 4) (hs 0 4 (by decide))
    have b := lena_fl_A Y Q s 4 4 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    have d := lena_fl_AC Y Q s 4 0 4 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 4)) (Q (s 0))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 0) * (Y (s 4))ᵀ).rank = (P (s 4) * (Q (s 0))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 0 4 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 4 9 rfl
    have c := lena_fl_C Y Q s 0 5 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 1) (s 0) (hs 1 0 (by decide))
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_C X P s 0 5 rfl
    have d := lena_fl_AC X P s 1 0 1 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 1) (s 0) (hs 1 0 (by decide))
    have b := lena_fl_A Y Q s 0 0 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    have d := lena_fl_AC Y Q s 0 1 0 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 1)) (Y (s 0))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_A Y Q s 0 0 rfl
    linarith only [a, b, c]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 0)) (Q (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 1) * (Y (s 0))ᵀ).rank = (P (s 0) * (Q (s 1))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 1 0 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 0 5 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 1) (s 2) (hs 1 2 (by decide))
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_C X P s 2 7 rfl
    have d := lena_fl_AC X P s 1 2 1 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 1) (s 2) (hs 1 2 (by decide))
    have b := lena_fl_A Y Q s 2 2 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    have d := lena_fl_AC Y Q s 2 1 2 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 2)) (Q (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 1) * (Y (s 2))ᵀ).rank = (P (s 2) * (Q (s 1))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 1 2 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 2 7 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 1) (s 3) (hs 1 3 (by decide))
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_C X P s 3 8 rfl
    have d := lena_fl_AC X P s 1 3 1 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 1) (s 3) (hs 1 3 (by decide))
    have b := lena_fl_A Y Q s 3 3 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    have d := lena_fl_AC Y Q s 3 1 3 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 1)) (Y (s 3))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_A Y Q s 3 3 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 1) (s 4) (hs 1 4 (by decide))
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_C X P s 4 9 rfl
    have d := lena_fl_AC X P s 1 4 1 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 1) (s 4) (hs 1 4 (by decide))
    have b := lena_fl_A Y Q s 4 4 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    have d := lena_fl_AC Y Q s 4 1 4 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 1)) (Y (s 4))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 1 1 rfl
    have c := lena_fl_A Y Q s 4 4 rfl
    linarith only [a, b, c]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 4)) (Q (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 1) * (Y (s 4))ᵀ).rank = (P (s 4) * (Q (s 1))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 1 4 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 4 9 rfl
    have c := lena_fl_C Y Q s 1 6 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 2) (s 0) (hs 2 0 (by decide))
    have b := lena_fl_A X P s 2 2 rfl
    have c := lena_fl_C X P s 0 5 rfl
    have d := lena_fl_AC X P s 2 0 2 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 2) (s 0) (hs 2 0 (by decide))
    have b := lena_fl_A Y Q s 0 0 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    have d := lena_fl_AC Y Q s 0 2 0 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 0)) (Q (s 2))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 2) * (Y (s 0))ᵀ).rank = (P (s 0) * (Q (s 2))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 2 0 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 0 5 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_right X Y P Q ho (s 2) (s 1) (hs 2 1 (by decide))
    have b := lena_fl_A Y Q s 1 1 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    have d := lena_fl_AC Y Q s 1 2 1 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 2)) (Y (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 2 2 rfl
    have c := lena_fl_A Y Q s 1 1 rfl
    linarith only [a, b, c]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 1)) (Q (s 2))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 2) * (Y (s 1))ᵀ).rank = (P (s 1) * (Q (s 2))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 2 1 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 1 6 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 2) (s 3) (hs 2 3 (by decide))
    have b := lena_fl_A X P s 2 2 rfl
    have c := lena_fl_C X P s 3 8 rfl
    have d := lena_fl_AC X P s 2 3 2 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 2) (s 3) (hs 2 3 (by decide))
    have b := lena_fl_A Y Q s 3 3 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    have d := lena_fl_AC Y Q s 3 2 3 7 rfl rfl
    linarith only [a, b, c, d]
end

/-! ## unit T444_R214_rows_part5 -/
section
open Matrix

/-- T444 (Lena): rows 160..188 of Gideon's exact R214 certificate, in the exact hypothesis form of greta_R214_core,
for the slice system at slices s 0..s 4 (generated by work/Lena/t444/gen_split.py). -/
theorem lena_R214_rows_5 {F : Type*} [Field F] {N r k : ℕ} (X Y : Fin N → Matrix (Fin N) (Fin r) F)
    (P Q : Fin N → Matrix (Fin N) (Fin k) F) (hd : ∀ y, X y * (Y y)ᵀ + P y * (Q y)ᵀ = 1)
    (ho : ∀ y u, y ≠ u → X y * (Y u)ᵀ + P u * (Q y)ᵀ = 0) (s : Fin 5 → Fin N) (hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u) :
      (-1) * ((X (s 2) * (Y (s 3))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (-1) * ((X (s 2) * (Y (s 3))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 2) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 2) * (Y (s 4))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({2} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 3) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 3) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 3) * (Y (s 2))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({3, 9} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 3) * (Y (s 4))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 3) * (Y (s 4))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({8} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 5} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 0))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 4) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({0} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (-1) * ((X (s 4) * (Y (s 0))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({5} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({6} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 6} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 1))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 4) * (Y (s 1))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({1} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({7} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 7} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 2))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 4) * (Y (s 2))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({2} : Finset (Fin 10)) + (-1) * (r : ℤ) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W X P s) ({4} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W X P s) ({4, 8} : Finset (Fin 10)) ≤ 0 ∧
      (1) * ((X (s 4) * (Y (s 3))ᵀ).rank : ℤ) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({3} : Finset (Fin 10)) + (-1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({3, 9} : Finset (Fin 10)) ≤ 0 ∧
      (-1) * ((X (s 4) * (Y (s 3))ᵀ).rank : ℤ) + (1) * lenaR214Fl (lenaR214W X P s) ({8} : Finset (Fin 10)) + (1) * lenaR214Fl (lenaR214W Y Q s) ({9} : Finset (Fin 10)) + (-1) * (k : ℤ) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 2)) (Y (s 3))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 2 2 rfl
    have c := lena_fl_A Y Q s 3 3 rfl
    linarith only [a, b, c]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 3)) (Q (s 2))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 2) * (Y (s 3))ᵀ).rank = (P (s 3) * (Q (s 2))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 2 3 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 3 8 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_right X Y P Q ho (s 2) (s 4) (hs 2 4 (by decide))
    have b := lena_fl_A Y Q s 4 4 rfl
    have c := lena_fl_C Y Q s 2 7 rfl
    have d := lena_fl_AC Y Q s 4 2 4 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 2)) (Y (s 4))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 2 2 rfl
    have c := lena_fl_A Y Q s 4 4 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 3) (s 0) (hs 3 0 (by decide))
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_C X P s 0 5 rfl
    have d := lena_fl_AC X P s 3 0 3 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 3) (s 0) (hs 3 0 (by decide))
    have b := lena_fl_A Y Q s 0 0 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    have d := lena_fl_AC Y Q s 0 3 0 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 3)) (Y (s 0))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_A Y Q s 0 0 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 3) (s 1) (hs 3 1 (by decide))
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_C X P s 1 6 rfl
    have d := lena_fl_AC X P s 3 1 3 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 3) (s 1) (hs 3 1 (by decide))
    have b := lena_fl_A Y Q s 1 1 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    have d := lena_fl_AC Y Q s 1 3 1 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 3)) (Y (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_A Y Q s 1 1 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 3) (s 2) (hs 3 2 (by decide))
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_C X P s 2 7 rfl
    have d := lena_fl_AC X P s 3 2 3 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 3) (s 2) (hs 3 2 (by decide))
    have b := lena_fl_A Y Q s 2 2 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    have d := lena_fl_AC Y Q s 2 3 2 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 2)) (Q (s 3))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 3) * (Y (s 2))ᵀ).rank = (P (s 2) * (Q (s 3))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 3 2 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 2 7 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 3) (s 4) (hs 3 4 (by decide))
    have b := lena_fl_A X P s 3 3 rfl
    have c := lena_fl_C X P s 4 9 rfl
    have d := lena_fl_AC X P s 3 4 3 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 3) (s 4) (hs 3 4 (by decide))
    have b := lena_fl_A Y Q s 4 4 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    have d := lena_fl_AC Y Q s 4 3 4 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 4)) (Q (s 3))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 3) * (Y (s 4))ᵀ).rank = (P (s 4) * (Q (s 3))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 3 4 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 4 9 rfl
    have c := lena_fl_C Y Q s 3 8 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 4) (s 0) (hs 4 0 (by decide))
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_C X P s 0 5 rfl
    have d := lena_fl_AC X P s 4 0 4 5 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 4) (s 0) (hs 4 0 (by decide))
    have b := lena_fl_A Y Q s 0 0 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    have d := lena_fl_AC Y Q s 0 4 0 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 4)) (Y (s 0))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_A Y Q s 0 0 rfl
    linarith only [a, b, c]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 0)) (Q (s 4))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 4) * (Y (s 0))ᵀ).rank = (P (s 0) * (Q (s 4))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 4 0 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 0 5 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    linarith only [a, b, c, e]
  · have a := hugo_slice_cap_left X Y P Q ho (s 4) (s 1) (hs 4 1 (by decide))
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_C X P s 1 6 rfl
    have d := lena_fl_AC X P s 4 1 4 6 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 4) (s 1) (hs 4 1 (by decide))
    have b := lena_fl_A Y Q s 1 1 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    have d := lena_fl_AC Y Q s 1 4 1 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 4)) (Y (s 1))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_A Y Q s 1 1 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 4) (s 2) (hs 4 2 (by decide))
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_C X P s 2 7 rfl
    have d := lena_fl_AC X P s 4 2 4 7 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 4) (s 2) (hs 4 2 (by decide))
    have b := lena_fl_A Y Q s 2 2 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    have d := lena_fl_AC Y Q s 2 4 2 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (X (s 4)) (Y (s 2))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_A Y Q s 2 2 rfl
    linarith only [a, b, c]
  · have a := hugo_slice_cap_left X Y P Q ho (s 4) (s 3) (hs 4 3 (by decide))
    have b := lena_fl_A X P s 4 4 rfl
    have c := lena_fl_C X P s 3 8 rfl
    have d := lena_fl_AC X P s 4 3 4 8 rfl rfl
    linarith only [a, b, c, d]
  · have a := hugo_slice_cap_right X Y P Q ho (s 4) (s 3) (hs 4 3 (by decide))
    have b := lena_fl_A Y Q s 3 3 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    have d := lena_fl_AC Y Q s 3 4 3 9 rfl rfl
    linarith only [a, b, c, d]
  · have a := nadia_rank_add_rank_le_rank_mul (P (s 3)) (Q (s 4))ᵀ
    rw [Fintype.card_fin, Matrix.rank_transpose] at a
    have e : (X (s 4) * (Y (s 3))ᵀ).rank = (P (s 3) * (Q (s 4))ᵀ).rank := by rw [eq_neg_of_add_eq_zero_left (ho _ _ (hs 4 3 (by decide))), lena_rank_neg]
    have b := lena_fl_C X P s 3 8 rfl
    have c := lena_fl_C Y Q s 4 9 rfl
    linarith only [a, b, c, e]
end

/-! ## unit R214_core_fifteen_N_le_eleven_r_plus_k -/
section
/-! T465, the R214 arithmetic core (Greta). The 189 rows of the exact L = 5 dual certificate of Silas's R214 (weights:
Gideon, work/Gideon/r214_exact_certificate.txt, common denominator 13035; independent check Greta,
work/Greta/sprintC/r214_exact_weights.txt) imply 15 N <= 11 (r + k). Statement: Lena's T444 interface
(shared/R214_core_statement_interface.lean): fl, gr are the span-rank functions of the left {A_y = y, C_y = 5 + y} and the
right generators, m the pair ranks, all as integers; no matrices. The weighted sum of h0..h188 is
-(r + k) + (7/11) fl(empty) <= -15N/11, so h189 : 0 <= fl(empty) (the LP's x >= 0; in T444 fl(empty) = 0) is the one extra
hypothesis. Proof: 10-row chunk sums with integer weights 13035 mu_i, then a binary tree of exact pairwise sums. -/
theorem greta_R214_core (fl gr : Finset (Fin 10) → ℤ) (m : Fin 5 → Fin 5 → ℤ) (r k N : ℤ)
    (h0 : (-1) * fl ({0} : Finset (Fin 10)) + (-1) * fl ({5} : Finset (Fin 10)) + (1) * fl ({0, 5} : Finset (Fin 10)) + (1) * fl (∅ : Finset (Fin 10)) ≤ 0)
    (h1 : (-1) * fl ({1} : Finset (Fin 10)) + (-1) * fl ({6} : Finset (Fin 10)) + (1) * fl ({1, 6} : Finset (Fin 10)) + (1) * fl (∅ : Finset (Fin 10)) ≤ 0)
    (h2 : (-1) * fl ({2} : Finset (Fin 10)) + (-1) * fl ({7} : Finset (Fin 10)) + (1) * fl ({2, 7} : Finset (Fin 10)) + (1) * fl (∅ : Finset (Fin 10)) ≤ 0)
    (h3 : (-1) * fl ({3} : Finset (Fin 10)) + (-1) * fl ({8} : Finset (Fin 10)) + (1) * fl ({3, 8} : Finset (Fin 10)) + (1) * fl (∅ : Finset (Fin 10)) ≤ 0)
    (h4 : (-1) * fl ({4} : Finset (Fin 10)) + (-1) * fl ({9} : Finset (Fin 10)) + (1) * fl ({4, 9} : Finset (Fin 10)) + (1) * fl (∅ : Finset (Fin 10)) ≤ 0)
    (h5 : (-1) * fl ({0, 6} : Finset (Fin 10)) + (-1) * fl ({0, 7} : Finset (Fin 10)) + (1) * fl ({0, 6, 7} : Finset (Fin 10)) + (1) * fl ({0} : Finset (Fin 10)) ≤ 0)
    (h6 : (-1) * fl ({0, 7} : Finset (Fin 10)) + (-1) * fl ({0, 8} : Finset (Fin 10)) + (1) * fl ({0, 7, 8} : Finset (Fin 10)) + (1) * fl ({0} : Finset (Fin 10)) ≤ 0)
    (h7 : (-1) * fl ({0, 1} : Finset (Fin 10)) + (-1) * fl ({1, 5} : Finset (Fin 10)) + (1) * fl ({0, 1, 5} : Finset (Fin 10)) + (1) * fl ({1} : Finset (Fin 10)) ≤ 0)
    (h8 : (-1) * fl ({0, 1, 4} : Finset (Fin 10)) + (-1) * fl ({0, 1, 9} : Finset (Fin 10)) + (1) * fl ({0, 1, 4, 9} : Finset (Fin 10)) + (1) * fl ({0, 1} : Finset (Fin 10)) ≤ 0)
    (h9 : (-1) * fl ({2, 5} : Finset (Fin 10)) + (-1) * fl ({2, 8} : Finset (Fin 10)) + (1) * fl ({2, 5, 8} : Finset (Fin 10)) + (1) * fl ({2} : Finset (Fin 10)) ≤ 0)
    (h10 : (-1) * fl ({3, 4} : Finset (Fin 10)) + (-1) * fl ({3, 9} : Finset (Fin 10)) + (1) * fl ({3, 4, 9} : Finset (Fin 10)) + (1) * fl ({3} : Finset (Fin 10)) ≤ 0)
    (h11 : (-1) * fl ({3, 6} : Finset (Fin 10)) + (-1) * fl ({3, 7} : Finset (Fin 10)) + (1) * fl ({3, 6, 7} : Finset (Fin 10)) + (1) * fl ({3} : Finset (Fin 10)) ≤ 0)
    (h12 : (-1) * fl ({1, 4} : Finset (Fin 10)) + (-1) * fl ({4, 6} : Finset (Fin 10)) + (1) * fl ({1, 4, 6} : Finset (Fin 10)) + (1) * fl ({4} : Finset (Fin 10)) ≤ 0)
    (h13 : (-1) * fl ({4, 6} : Finset (Fin 10)) + (-1) * fl ({4, 7} : Finset (Fin 10)) + (1) * fl ({4, 6, 7} : Finset (Fin 10)) + (1) * fl ({4} : Finset (Fin 10)) ≤ 0)
    (h14 : (-1) * fl ({1, 2, 4} : Finset (Fin 10)) + (-1) * fl ({1, 4, 7} : Finset (Fin 10)) + (1) * fl ({1, 2, 4, 7} : Finset (Fin 10)) + (1) * fl ({1, 4} : Finset (Fin 10)) ≤ 0)
    (h15 : (-1) * fl ({1, 4, 5} : Finset (Fin 10)) + (-1) * fl ({1, 4, 8} : Finset (Fin 10)) + (1) * fl ({1, 4, 5, 8} : Finset (Fin 10)) + (1) * fl ({1, 4} : Finset (Fin 10)) ≤ 0)
    (h16 : (-1) * fl ({1, 4, 7} : Finset (Fin 10)) + (-1) * fl ({1, 4, 8} : Finset (Fin 10)) + (1) * fl ({1, 4, 7, 8} : Finset (Fin 10)) + (1) * fl ({1, 4} : Finset (Fin 10)) ≤ 0)
    (h17 : (1) * fl ({0, 1, 4} : Finset (Fin 10)) + (-1) * fl ({0, 1, 4, 8} : Finset (Fin 10)) ≤ 0)
    (h18 : (1) * fl ({1, 2, 4} : Finset (Fin 10)) + (-1) * fl ({1, 2, 4, 5} : Finset (Fin 10)) ≤ 0)
    (h19 : (-1) * fl ({0, 3, 4} : Finset (Fin 10)) + (-1) * fl ({3, 4, 5} : Finset (Fin 10)) + (1) * fl ({0, 3, 4, 5} : Finset (Fin 10)) + (1) * fl ({3, 4} : Finset (Fin 10)) ≤ 0)
    (h20 : (-1) * fl ({3, 4, 6} : Finset (Fin 10)) + (-1) * fl ({3, 4, 7} : Finset (Fin 10)) + (1) * fl ({3, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({3, 4} : Finset (Fin 10)) ≤ 0)
    (h21 : (1) * fl ({0, 3, 4} : Finset (Fin 10)) + (-1) * fl ({0, 3, 4, 7} : Finset (Fin 10)) ≤ 0)
    (h22 : (-1) * fl ({1, 5} : Finset (Fin 10)) + (-1) * fl ({4, 5} : Finset (Fin 10)) + (1) * fl ({1, 4, 5} : Finset (Fin 10)) + (1) * fl ({5} : Finset (Fin 10)) ≤ 0)
    (h23 : (-1) * fl ({3, 5} : Finset (Fin 10)) + (-1) * fl ({4, 5} : Finset (Fin 10)) + (1) * fl ({3, 4, 5} : Finset (Fin 10)) + (1) * fl ({5} : Finset (Fin 10)) ≤ 0)
    (h24 : (-1) * fl ({3, 5} : Finset (Fin 10)) + (-1) * fl ({5, 8} : Finset (Fin 10)) + (1) * fl ({3, 5, 8} : Finset (Fin 10)) + (1) * fl ({5} : Finset (Fin 10)) ≤ 0)
    (h25 : (1) * fl ({0, 5} : Finset (Fin 10)) + (-1) * fl ({0, 1, 5} : Finset (Fin 10)) ≤ 0)
    (h26 : (1) * fl ({0, 5} : Finset (Fin 10)) + (-1) * fl ({0, 3, 5} : Finset (Fin 10)) ≤ 0)
    (h27 : (1) * fl ({0, 5} : Finset (Fin 10)) + (-1) * fl ({0, 5, 8} : Finset (Fin 10)) ≤ 0)
    (h28 : (1) * fl ({0, 3, 5} : Finset (Fin 10)) + (-1) * fl ({0, 3, 4, 5} : Finset (Fin 10)) ≤ 0)
    (h29 : (1) * fl ({1, 2, 4, 5} : Finset (Fin 10)) + (-1) * fl ({1, 2, 4, 5, 8} : Finset (Fin 10)) ≤ 0)
    (h30 : (-1) * fl ({3, 6} : Finset (Fin 10)) + (-1) * fl ({4, 6} : Finset (Fin 10)) + (1) * fl ({3, 4, 6} : Finset (Fin 10)) + (1) * fl ({6} : Finset (Fin 10)) ≤ 0)
    (h31 : (1) * fl ({1, 6} : Finset (Fin 10)) + (-1) * fl ({1, 4, 6} : Finset (Fin 10)) ≤ 0)
    (h32 : (1) * fl ({1, 6} : Finset (Fin 10)) + (-1) * fl ({1, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h33 : (-1) * fl ({1, 7} : Finset (Fin 10)) + (-1) * fl ({4, 7} : Finset (Fin 10)) + (1) * fl ({1, 4, 7} : Finset (Fin 10)) + (1) * fl ({7} : Finset (Fin 10)) ≤ 0)
    (h34 : (-1) * fl ({1, 7} : Finset (Fin 10)) + (-1) * fl ({6, 7} : Finset (Fin 10)) + (1) * fl ({1, 6, 7} : Finset (Fin 10)) + (1) * fl ({7} : Finset (Fin 10)) ≤ 0)
    (h35 : (-1) * fl ({3, 7} : Finset (Fin 10)) + (-1) * fl ({4, 7} : Finset (Fin 10)) + (1) * fl ({3, 4, 7} : Finset (Fin 10)) + (1) * fl ({7} : Finset (Fin 10)) ≤ 0)
    (h36 : (1) * fl ({2, 7} : Finset (Fin 10)) + (-1) * fl ({1, 2, 7} : Finset (Fin 10)) ≤ 0)
    (h37 : (1) * fl ({2, 7} : Finset (Fin 10)) + (-1) * fl ({2, 7, 8} : Finset (Fin 10)) ≤ 0)
    (h38 : (1) * fl ({1, 2, 7} : Finset (Fin 10)) + (-1) * fl ({1, 2, 4, 7} : Finset (Fin 10)) ≤ 0)
    (h39 : (1) * fl ({0, 3, 4, 7} : Finset (Fin 10)) + (-1) * fl ({0, 3, 4, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h40 : (-1) * fl ({0, 6, 7} : Finset (Fin 10)) + (-1) * fl ({3, 6, 7} : Finset (Fin 10)) + (1) * fl ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * fl ({6, 7} : Finset (Fin 10)) ≤ 0)
    (h41 : (-1) * fl ({0, 6, 7} : Finset (Fin 10)) + (-1) * fl ({4, 6, 7} : Finset (Fin 10)) + (1) * fl ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({6, 7} : Finset (Fin 10)) ≤ 0)
    (h42 : (-1) * fl ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * fl ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({0, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h43 : (-1) * fl ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * fl ({3, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * fl ({3, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h44 : (-1) * fl ({0, 8} : Finset (Fin 10)) + (-1) * fl ({5, 8} : Finset (Fin 10)) + (1) * fl ({0, 5, 8} : Finset (Fin 10)) + (1) * fl ({8} : Finset (Fin 10)) ≤ 0)
    (h45 : (-1) * fl ({1, 8} : Finset (Fin 10)) + (-1) * fl ({4, 8} : Finset (Fin 10)) + (1) * fl ({1, 4, 8} : Finset (Fin 10)) + (1) * fl ({8} : Finset (Fin 10)) ≤ 0)
    (h46 : (-1) * fl ({2, 8} : Finset (Fin 10)) + (-1) * fl ({7, 8} : Finset (Fin 10)) + (1) * fl ({2, 7, 8} : Finset (Fin 10)) + (1) * fl ({8} : Finset (Fin 10)) ≤ 0)
    (h47 : (1) * fl ({3, 8} : Finset (Fin 10)) + (-1) * fl ({3, 5, 8} : Finset (Fin 10)) ≤ 0)
    (h48 : (1) * fl ({0, 1, 4, 8} : Finset (Fin 10)) + (-1) * fl ({0, 1, 4, 7, 8} : Finset (Fin 10)) ≤ 0)
    (h49 : (-1) * fl ({1, 5, 8} : Finset (Fin 10)) + (-1) * fl ({2, 5, 8} : Finset (Fin 10)) + (1) * fl ({1, 2, 5, 8} : Finset (Fin 10)) + (1) * fl ({5, 8} : Finset (Fin 10)) ≤ 0)
    (h50 : (-1) * fl ({1, 2, 5, 8} : Finset (Fin 10)) + (-1) * fl ({1, 4, 5, 8} : Finset (Fin 10)) + (1) * fl ({1, 2, 4, 5, 8} : Finset (Fin 10)) + (1) * fl ({1, 5, 8} : Finset (Fin 10)) ≤ 0)
    (h51 : (-1) * fl ({0, 7, 8} : Finset (Fin 10)) + (-1) * fl ({4, 7, 8} : Finset (Fin 10)) + (1) * fl ({0, 4, 7, 8} : Finset (Fin 10)) + (1) * fl ({7, 8} : Finset (Fin 10)) ≤ 0)
    (h52 : (-1) * fl ({0, 4, 7, 8} : Finset (Fin 10)) + (-1) * fl ({1, 4, 7, 8} : Finset (Fin 10)) + (1) * fl ({0, 1, 4, 7, 8} : Finset (Fin 10)) + (1) * fl ({4, 7, 8} : Finset (Fin 10)) ≤ 0)
    (h53 : (-1) * fl ({0, 9} : Finset (Fin 10)) + (-1) * fl ({1, 9} : Finset (Fin 10)) + (1) * fl ({0, 1, 9} : Finset (Fin 10)) + (1) * fl ({9} : Finset (Fin 10)) ≤ 0)
    (h54 : (1) * fl ({4, 9} : Finset (Fin 10)) + (-1) * fl ({1, 4, 9} : Finset (Fin 10)) ≤ 0)
    (h55 : (1) * fl ({4, 9} : Finset (Fin 10)) + (-1) * fl ({3, 4, 9} : Finset (Fin 10)) ≤ 0)
    (h56 : (1) * fl ({1, 4, 9} : Finset (Fin 10)) + (-1) * fl ({0, 1, 4, 9} : Finset (Fin 10)) ≤ 0)
    (h57 : (-1) * fl ({0, 5} : Finset (Fin 10)) ≤ (-1) * N)
    (h58 : (-1) * fl ({1, 6} : Finset (Fin 10)) ≤ (-1) * N)
    (h59 : (-1) * fl ({2, 7} : Finset (Fin 10)) ≤ (-1) * N)
    (h60 : (-1) * fl ({3, 8} : Finset (Fin 10)) ≤ (-1) * N)
    (h61 : (-1) * fl ({4, 9} : Finset (Fin 10)) ≤ (-1) * N)
    (h62 : (-1) * gr ({0, 1} : Finset (Fin 10)) + (-1) * gr ({0, 6} : Finset (Fin 10)) + (1) * gr ({0, 1, 6} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) ≤ 0)
    (h63 : (-1) * gr ({0, 6} : Finset (Fin 10)) + (-1) * gr ({0, 7} : Finset (Fin 10)) + (1) * gr ({0, 6, 7} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) ≤ 0)
    (h64 : (-1) * gr ({0, 8} : Finset (Fin 10)) + (-1) * gr ({0, 9} : Finset (Fin 10)) + (1) * gr ({0, 8, 9} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) ≤ 0)
    (h65 : (-1) * gr ({0, 1} : Finset (Fin 10)) + (-1) * gr ({1, 5} : Finset (Fin 10)) + (1) * gr ({0, 1, 5} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) ≤ 0)
    (h66 : (-1) * gr ({1, 8} : Finset (Fin 10)) + (-1) * gr ({1, 9} : Finset (Fin 10)) + (1) * gr ({1, 8, 9} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) ≤ 0)
    (h67 : (-1) * gr ({0, 1, 2} : Finset (Fin 10)) + (-1) * gr ({0, 1, 7} : Finset (Fin 10)) + (1) * gr ({0, 1, 2, 7} : Finset (Fin 10)) + (1) * gr ({0, 1} : Finset (Fin 10)) ≤ 0)
    (h68 : (-1) * gr ({2, 8} : Finset (Fin 10)) + (-1) * gr ({2, 9} : Finset (Fin 10)) + (1) * gr ({2, 8, 9} : Finset (Fin 10)) + (1) * gr ({2} : Finset (Fin 10)) ≤ 0)
    (h69 : (1) * gr ({0, 1, 2} : Finset (Fin 10)) + (-1) * gr ({0, 1, 2, 8} : Finset (Fin 10)) ≤ 0)
    (h70 : (-1) * gr ({0, 3} : Finset (Fin 10)) + (-1) * gr ({3, 5} : Finset (Fin 10)) + (1) * gr ({0, 3, 5} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) ≤ 0)
    (h71 : (-1) * gr ({3, 5} : Finset (Fin 10)) + (-1) * gr ({3, 6} : Finset (Fin 10)) + (1) * gr ({3, 5, 6} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) ≤ 0)
    (h72 : (-1) * gr ({3, 6} : Finset (Fin 10)) + (-1) * gr ({3, 7} : Finset (Fin 10)) + (1) * gr ({3, 6, 7} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) ≤ 0)
    (h73 : (-1) * gr ({0, 3, 4} : Finset (Fin 10)) + (-1) * gr ({0, 3, 9} : Finset (Fin 10)) + (1) * gr ({0, 3, 4, 9} : Finset (Fin 10)) + (1) * gr ({0, 3} : Finset (Fin 10)) ≤ 0)
    (h74 : (-1) * gr ({0, 3, 6} : Finset (Fin 10)) + (-1) * gr ({0, 3, 7} : Finset (Fin 10)) + (1) * gr ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * gr ({0, 3} : Finset (Fin 10)) ≤ 0)
    (h75 : (-1) * gr ({0, 4} : Finset (Fin 10)) + (-1) * gr ({4, 5} : Finset (Fin 10)) + (1) * gr ({0, 4, 5} : Finset (Fin 10)) + (1) * gr ({4} : Finset (Fin 10)) ≤ 0)
    (h76 : (-1) * gr ({2, 4} : Finset (Fin 10)) + (-1) * gr ({4, 7} : Finset (Fin 10)) + (1) * gr ({2, 4, 7} : Finset (Fin 10)) + (1) * gr ({4} : Finset (Fin 10)) ≤ 0)
    (h77 : (-1) * gr ({4, 6} : Finset (Fin 10)) + (-1) * gr ({4, 7} : Finset (Fin 10)) + (1) * gr ({4, 6, 7} : Finset (Fin 10)) + (1) * gr ({4} : Finset (Fin 10)) ≤ 0)
    (h78 : (-1) * gr ({0, 3, 4} : Finset (Fin 10)) + (-1) * gr ({0, 4, 8} : Finset (Fin 10)) + (1) * gr ({0, 3, 4, 8} : Finset (Fin 10)) + (1) * gr ({0, 4} : Finset (Fin 10)) ≤ 0)
    (h79 : (-1) * gr ({2, 3, 4} : Finset (Fin 10)) + (-1) * gr ({2, 4, 8} : Finset (Fin 10)) + (1) * gr ({2, 3, 4, 8} : Finset (Fin 10)) + (1) * gr ({2, 4} : Finset (Fin 10)) ≤ 0)
    (h80 : (-1) * gr ({2, 4, 5} : Finset (Fin 10)) + (-1) * gr ({2, 4, 6} : Finset (Fin 10)) + (1) * gr ({2, 4, 5, 6} : Finset (Fin 10)) + (1) * gr ({2, 4} : Finset (Fin 10)) ≤ 0)
    (h81 : (1) * gr ({0, 3, 4} : Finset (Fin 10)) + (-1) * gr ({0, 3, 4, 7} : Finset (Fin 10)) ≤ 0)
    (h82 : (1) * gr ({2, 3, 4} : Finset (Fin 10)) + (-1) * gr ({2, 3, 4, 5} : Finset (Fin 10)) ≤ 0)
    (h83 : (-1) * gr ({1, 5} : Finset (Fin 10)) + (-1) * gr ({5, 6} : Finset (Fin 10)) + (1) * gr ({1, 5, 6} : Finset (Fin 10)) + (1) * gr ({5} : Finset (Fin 10)) ≤ 0)
    (h84 : (-1) * gr ({2, 5} : Finset (Fin 10)) + (-1) * gr ({4, 5} : Finset (Fin 10)) + (1) * gr ({2, 4, 5} : Finset (Fin 10)) + (1) * gr ({5} : Finset (Fin 10)) ≤ 0)
    (h85 : (1) * gr ({0, 5} : Finset (Fin 10)) + (-1) * gr ({0, 1, 5} : Finset (Fin 10)) ≤ 0)
    (h86 : (1) * gr ({0, 5} : Finset (Fin 10)) + (-1) * gr ({0, 3, 5} : Finset (Fin 10)) ≤ 0)
    (h87 : (1) * gr ({0, 5} : Finset (Fin 10)) + (-1) * gr ({0, 4, 5} : Finset (Fin 10)) ≤ 0)
    (h88 : (1) * gr ({2, 3, 4, 5} : Finset (Fin 10)) + (-1) * gr ({2, 3, 4, 5, 6} : Finset (Fin 10)) ≤ 0)
    (h89 : (-1) * gr ({0, 6} : Finset (Fin 10)) + (-1) * gr ({3, 6} : Finset (Fin 10)) + (1) * gr ({0, 3, 6} : Finset (Fin 10)) + (1) * gr ({6} : Finset (Fin 10)) ≤ 0)
    (h90 : (-1) * gr ({2, 6} : Finset (Fin 10)) + (-1) * gr ({4, 6} : Finset (Fin 10)) + (1) * gr ({2, 4, 6} : Finset (Fin 10)) + (1) * gr ({6} : Finset (Fin 10)) ≤ 0)
    (h91 : (1) * gr ({1, 6} : Finset (Fin 10)) + (-1) * gr ({0, 1, 6} : Finset (Fin 10)) ≤ 0)
    (h92 : (1) * gr ({1, 6} : Finset (Fin 10)) + (-1) * gr ({1, 5, 6} : Finset (Fin 10)) ≤ 0)
    (h93 : (1) * gr ({1, 6} : Finset (Fin 10)) + (-1) * gr ({1, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h94 : (-1) * gr ({2, 5, 6} : Finset (Fin 10)) + (-1) * gr ({3, 5, 6} : Finset (Fin 10)) + (1) * gr ({2, 3, 5, 6} : Finset (Fin 10)) + (1) * gr ({5, 6} : Finset (Fin 10)) ≤ 0)
    (h95 : (-1) * gr ({2, 3, 5, 6} : Finset (Fin 10)) + (-1) * gr ({2, 4, 5, 6} : Finset (Fin 10)) + (1) * gr ({2, 3, 4, 5, 6} : Finset (Fin 10)) + (1) * gr ({2, 5, 6} : Finset (Fin 10)) ≤ 0)
    (h96 : (-1) * gr ({0, 7} : Finset (Fin 10)) + (-1) * gr ({1, 7} : Finset (Fin 10)) + (1) * gr ({0, 1, 7} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) ≤ 0)
    (h97 : (-1) * gr ({0, 7} : Finset (Fin 10)) + (-1) * gr ({3, 7} : Finset (Fin 10)) + (1) * gr ({0, 3, 7} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) ≤ 0)
    (h98 : (-1) * gr ({1, 7} : Finset (Fin 10)) + (-1) * gr ({6, 7} : Finset (Fin 10)) + (1) * gr ({1, 6, 7} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) ≤ 0)
    (h99 : (1) * gr ({2, 7} : Finset (Fin 10)) + (-1) * gr ({0, 2, 7} : Finset (Fin 10)) ≤ 0)
    (h100 : (1) * gr ({2, 7} : Finset (Fin 10)) + (-1) * gr ({2, 4, 7} : Finset (Fin 10)) ≤ 0)
    (h101 : (1) * gr ({0, 2, 7} : Finset (Fin 10)) + (-1) * gr ({0, 1, 2, 7} : Finset (Fin 10)) ≤ 0)
    (h102 : (1) * gr ({0, 3, 4, 7} : Finset (Fin 10)) + (-1) * gr ({0, 3, 4, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h103 : (-1) * gr ({0, 6, 7} : Finset (Fin 10)) + (-1) * gr ({3, 6, 7} : Finset (Fin 10)) + (1) * gr ({0, 3, 6, 7} : Finset (Fin 10)) + (1) * gr ({6, 7} : Finset (Fin 10)) ≤ 0)
    (h104 : (-1) * gr ({0, 6, 7} : Finset (Fin 10)) + (-1) * gr ({4, 6, 7} : Finset (Fin 10)) + (1) * gr ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * gr ({6, 7} : Finset (Fin 10)) ≤ 0)
    (h105 : (-1) * gr ({0, 3, 6, 7} : Finset (Fin 10)) + (-1) * gr ({0, 4, 6, 7} : Finset (Fin 10)) + (1) * gr ({0, 3, 4, 6, 7} : Finset (Fin 10)) + (1) * gr ({0, 6, 7} : Finset (Fin 10)) ≤ 0)
    (h106 : (-1) * gr ({0, 8} : Finset (Fin 10)) + (-1) * gr ({4, 8} : Finset (Fin 10)) + (1) * gr ({0, 4, 8} : Finset (Fin 10)) + (1) * gr ({8} : Finset (Fin 10)) ≤ 0)
    (h107 : (-1) * gr ({2, 8} : Finset (Fin 10)) + (-1) * gr ({4, 8} : Finset (Fin 10)) + (1) * gr ({2, 4, 8} : Finset (Fin 10)) + (1) * gr ({8} : Finset (Fin 10)) ≤ 0)
    (h108 : (1) * gr ({0, 1, 2, 8} : Finset (Fin 10)) + (-1) * gr ({0, 1, 2, 8, 9} : Finset (Fin 10)) ≤ 0)
    (h109 : (1) * gr ({3, 8} : Finset (Fin 10)) + (-1) * gr ({3, 4, 8} : Finset (Fin 10)) ≤ 0)
    (h110 : (1) * gr ({3, 8} : Finset (Fin 10)) + (-1) * gr ({3, 8, 9} : Finset (Fin 10)) ≤ 0)
    (h111 : (1) * gr ({3, 4, 8} : Finset (Fin 10)) + (-1) * gr ({0, 3, 4, 8} : Finset (Fin 10)) ≤ 0)
    (h112 : (1) * gr ({3, 4, 8} : Finset (Fin 10)) + (-1) * gr ({2, 3, 4, 8} : Finset (Fin 10)) ≤ 0)
    (h113 : (-1) * gr ({0, 9} : Finset (Fin 10)) + (-1) * gr ({3, 9} : Finset (Fin 10)) + (1) * gr ({0, 3, 9} : Finset (Fin 10)) + (1) * gr ({9} : Finset (Fin 10)) ≤ 0)
    (h114 : (-1) * gr ({3, 9} : Finset (Fin 10)) + (-1) * gr ({8, 9} : Finset (Fin 10)) + (1) * gr ({3, 8, 9} : Finset (Fin 10)) + (1) * gr ({9} : Finset (Fin 10)) ≤ 0)
    (h115 : (1) * gr ({4, 9} : Finset (Fin 10)) + (-1) * gr ({3, 4, 9} : Finset (Fin 10)) ≤ 0)
    (h116 : (1) * gr ({3, 4, 9} : Finset (Fin 10)) + (-1) * gr ({0, 3, 4, 9} : Finset (Fin 10)) ≤ 0)
    (h117 : (-1) * gr ({0, 8, 9} : Finset (Fin 10)) + (-1) * gr ({1, 8, 9} : Finset (Fin 10)) + (1) * gr ({0, 1, 8, 9} : Finset (Fin 10)) + (1) * gr ({8, 9} : Finset (Fin 10)) ≤ 0)
    (h118 : (-1) * gr ({1, 8, 9} : Finset (Fin 10)) + (-1) * gr ({2, 8, 9} : Finset (Fin 10)) + (1) * gr ({1, 2, 8, 9} : Finset (Fin 10)) + (1) * gr ({8, 9} : Finset (Fin 10)) ≤ 0)
    (h119 : (-1) * gr ({0, 1, 8, 9} : Finset (Fin 10)) + (-1) * gr ({1, 2, 8, 9} : Finset (Fin 10)) + (1) * gr ({0, 1, 2, 8, 9} : Finset (Fin 10)) + (1) * gr ({1, 8, 9} : Finset (Fin 10)) ≤ 0)
    (h120 : (-1) * gr ({0, 5} : Finset (Fin 10)) ≤ (-1) * N)
    (h121 : (-1) * gr ({1, 6} : Finset (Fin 10)) ≤ (-1) * N)
    (h122 : (-1) * gr ({2, 7} : Finset (Fin 10)) ≤ (-1) * N)
    (h123 : (-1) * gr ({3, 8} : Finset (Fin 10)) ≤ (-1) * N)
    (h124 : (-1) * gr ({4, 9} : Finset (Fin 10)) ≤ (-1) * N)
    (h125 : (1) * m 0 1 + (-1) * fl ({0} : Finset (Fin 10)) + (-1) * fl ({6} : Finset (Fin 10)) + (1) * fl ({0, 6} : Finset (Fin 10)) ≤ 0)
    (h126 : (1) * m 0 1 + (-1) * gr ({1} : Finset (Fin 10)) + (-1) * gr ({5} : Finset (Fin 10)) + (1) * gr ({1, 5} : Finset (Fin 10)) ≤ 0)
    (h127 : (-1) * m 0 1 + (1) * fl ({0} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h128 : (-1) * m 0 1 + (1) * fl ({6} : Finset (Fin 10)) + (1) * gr ({5} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h129 : (1) * m 0 2 + (-1) * fl ({0} : Finset (Fin 10)) + (-1) * fl ({7} : Finset (Fin 10)) + (1) * fl ({0, 7} : Finset (Fin 10)) ≤ 0)
    (h130 : (1) * m 0 2 + (-1) * gr ({2} : Finset (Fin 10)) + (-1) * gr ({5} : Finset (Fin 10)) + (1) * gr ({2, 5} : Finset (Fin 10)) ≤ 0)
    (h131 : (-1) * m 0 2 + (1) * fl ({0} : Finset (Fin 10)) + (1) * gr ({2} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h132 : (1) * m 0 3 + (-1) * fl ({0} : Finset (Fin 10)) + (-1) * fl ({8} : Finset (Fin 10)) + (1) * fl ({0, 8} : Finset (Fin 10)) ≤ 0)
    (h133 : (1) * m 0 3 + (-1) * gr ({3} : Finset (Fin 10)) + (-1) * gr ({5} : Finset (Fin 10)) + (1) * gr ({3, 5} : Finset (Fin 10)) ≤ 0)
    (h134 : (-1) * m 0 3 + (1) * fl ({0} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h135 : (1) * m 0 4 + (-1) * fl ({0} : Finset (Fin 10)) + (-1) * fl ({9} : Finset (Fin 10)) + (1) * fl ({0, 9} : Finset (Fin 10)) ≤ 0)
    (h136 : (1) * m 0 4 + (-1) * gr ({4} : Finset (Fin 10)) + (-1) * gr ({5} : Finset (Fin 10)) + (1) * gr ({4, 5} : Finset (Fin 10)) ≤ 0)
    (h137 : (-1) * m 0 4 + (1) * fl ({9} : Finset (Fin 10)) + (1) * gr ({5} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h138 : (1) * m 1 0 + (-1) * fl ({1} : Finset (Fin 10)) + (-1) * fl ({5} : Finset (Fin 10)) + (1) * fl ({1, 5} : Finset (Fin 10)) ≤ 0)
    (h139 : (1) * m 1 0 + (-1) * gr ({0} : Finset (Fin 10)) + (-1) * gr ({6} : Finset (Fin 10)) + (1) * gr ({0, 6} : Finset (Fin 10)) ≤ 0)
    (h140 : (-1) * m 1 0 + (1) * fl ({1} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h141 : (-1) * m 1 0 + (1) * fl ({5} : Finset (Fin 10)) + (1) * gr ({6} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h142 : (1) * m 1 2 + (-1) * fl ({1} : Finset (Fin 10)) + (-1) * fl ({7} : Finset (Fin 10)) + (1) * fl ({1, 7} : Finset (Fin 10)) ≤ 0)
    (h143 : (1) * m 1 2 + (-1) * gr ({2} : Finset (Fin 10)) + (-1) * gr ({6} : Finset (Fin 10)) + (1) * gr ({2, 6} : Finset (Fin 10)) ≤ 0)
    (h144 : (-1) * m 1 2 + (1) * fl ({7} : Finset (Fin 10)) + (1) * gr ({6} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h145 : (1) * m 1 3 + (-1) * fl ({1} : Finset (Fin 10)) + (-1) * fl ({8} : Finset (Fin 10)) + (1) * fl ({1, 8} : Finset (Fin 10)) ≤ 0)
    (h146 : (1) * m 1 3 + (-1) * gr ({3} : Finset (Fin 10)) + (-1) * gr ({6} : Finset (Fin 10)) + (1) * gr ({3, 6} : Finset (Fin 10)) ≤ 0)
    (h147 : (-1) * m 1 3 + (1) * fl ({1} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h148 : (1) * m 1 4 + (-1) * fl ({1} : Finset (Fin 10)) + (-1) * fl ({9} : Finset (Fin 10)) + (1) * fl ({1, 9} : Finset (Fin 10)) ≤ 0)
    (h149 : (1) * m 1 4 + (-1) * gr ({4} : Finset (Fin 10)) + (-1) * gr ({6} : Finset (Fin 10)) + (1) * gr ({4, 6} : Finset (Fin 10)) ≤ 0)
    (h150 : (-1) * m 1 4 + (1) * fl ({1} : Finset (Fin 10)) + (1) * gr ({4} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h151 : (-1) * m 1 4 + (1) * fl ({9} : Finset (Fin 10)) + (1) * gr ({6} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h152 : (1) * m 2 0 + (-1) * fl ({2} : Finset (Fin 10)) + (-1) * fl ({5} : Finset (Fin 10)) + (1) * fl ({2, 5} : Finset (Fin 10)) ≤ 0)
    (h153 : (1) * m 2 0 + (-1) * gr ({0} : Finset (Fin 10)) + (-1) * gr ({7} : Finset (Fin 10)) + (1) * gr ({0, 7} : Finset (Fin 10)) ≤ 0)
    (h154 : (-1) * m 2 0 + (1) * fl ({5} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h155 : (1) * m 2 1 + (-1) * gr ({1} : Finset (Fin 10)) + (-1) * gr ({7} : Finset (Fin 10)) + (1) * gr ({1, 7} : Finset (Fin 10)) ≤ 0)
    (h156 : (-1) * m 2 1 + (1) * fl ({2} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h157 : (-1) * m 2 1 + (1) * fl ({6} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h158 : (1) * m 2 3 + (-1) * fl ({2} : Finset (Fin 10)) + (-1) * fl ({8} : Finset (Fin 10)) + (1) * fl ({2, 8} : Finset (Fin 10)) ≤ 0)
    (h159 : (1) * m 2 3 + (-1) * gr ({3} : Finset (Fin 10)) + (-1) * gr ({7} : Finset (Fin 10)) + (1) * gr ({3, 7} : Finset (Fin 10)) ≤ 0)
    (h160 : (-1) * m 2 3 + (1) * fl ({2} : Finset (Fin 10)) + (1) * gr ({3} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h161 : (-1) * m 2 3 + (1) * fl ({8} : Finset (Fin 10)) + (1) * gr ({7} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h162 : (1) * m 2 4 + (-1) * gr ({4} : Finset (Fin 10)) + (-1) * gr ({7} : Finset (Fin 10)) + (1) * gr ({4, 7} : Finset (Fin 10)) ≤ 0)
    (h163 : (-1) * m 2 4 + (1) * fl ({2} : Finset (Fin 10)) + (1) * gr ({4} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h164 : (1) * m 3 0 + (-1) * fl ({3} : Finset (Fin 10)) + (-1) * fl ({5} : Finset (Fin 10)) + (1) * fl ({3, 5} : Finset (Fin 10)) ≤ 0)
    (h165 : (1) * m 3 0 + (-1) * gr ({0} : Finset (Fin 10)) + (-1) * gr ({8} : Finset (Fin 10)) + (1) * gr ({0, 8} : Finset (Fin 10)) ≤ 0)
    (h166 : (-1) * m 3 0 + (1) * fl ({3} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h167 : (1) * m 3 1 + (-1) * fl ({3} : Finset (Fin 10)) + (-1) * fl ({6} : Finset (Fin 10)) + (1) * fl ({3, 6} : Finset (Fin 10)) ≤ 0)
    (h168 : (1) * m 3 1 + (-1) * gr ({1} : Finset (Fin 10)) + (-1) * gr ({8} : Finset (Fin 10)) + (1) * gr ({1, 8} : Finset (Fin 10)) ≤ 0)
    (h169 : (-1) * m 3 1 + (1) * fl ({3} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h170 : (1) * m 3 2 + (-1) * fl ({3} : Finset (Fin 10)) + (-1) * fl ({7} : Finset (Fin 10)) + (1) * fl ({3, 7} : Finset (Fin 10)) ≤ 0)
    (h171 : (1) * m 3 2 + (-1) * gr ({2} : Finset (Fin 10)) + (-1) * gr ({8} : Finset (Fin 10)) + (1) * gr ({2, 8} : Finset (Fin 10)) ≤ 0)
    (h172 : (-1) * m 3 2 + (1) * fl ({7} : Finset (Fin 10)) + (1) * gr ({8} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h173 : (1) * m 3 4 + (-1) * fl ({3} : Finset (Fin 10)) + (-1) * fl ({9} : Finset (Fin 10)) + (1) * fl ({3, 9} : Finset (Fin 10)) ≤ 0)
    (h174 : (1) * m 3 4 + (-1) * gr ({4} : Finset (Fin 10)) + (-1) * gr ({8} : Finset (Fin 10)) + (1) * gr ({4, 8} : Finset (Fin 10)) ≤ 0)
    (h175 : (-1) * m 3 4 + (1) * fl ({9} : Finset (Fin 10)) + (1) * gr ({8} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h176 : (1) * m 4 0 + (-1) * fl ({4} : Finset (Fin 10)) + (-1) * fl ({5} : Finset (Fin 10)) + (1) * fl ({4, 5} : Finset (Fin 10)) ≤ 0)
    (h177 : (1) * m 4 0 + (-1) * gr ({0} : Finset (Fin 10)) + (-1) * gr ({9} : Finset (Fin 10)) + (1) * gr ({0, 9} : Finset (Fin 10)) ≤ 0)
    (h178 : (-1) * m 4 0 + (1) * fl ({4} : Finset (Fin 10)) + (1) * gr ({0} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h179 : (-1) * m 4 0 + (1) * fl ({5} : Finset (Fin 10)) + (1) * gr ({9} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h180 : (1) * m 4 1 + (-1) * fl ({4} : Finset (Fin 10)) + (-1) * fl ({6} : Finset (Fin 10)) + (1) * fl ({4, 6} : Finset (Fin 10)) ≤ 0)
    (h181 : (1) * m 4 1 + (-1) * gr ({1} : Finset (Fin 10)) + (-1) * gr ({9} : Finset (Fin 10)) + (1) * gr ({1, 9} : Finset (Fin 10)) ≤ 0)
    (h182 : (-1) * m 4 1 + (1) * fl ({4} : Finset (Fin 10)) + (1) * gr ({1} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h183 : (1) * m 4 2 + (-1) * fl ({4} : Finset (Fin 10)) + (-1) * fl ({7} : Finset (Fin 10)) + (1) * fl ({4, 7} : Finset (Fin 10)) ≤ 0)
    (h184 : (1) * m 4 2 + (-1) * gr ({2} : Finset (Fin 10)) + (-1) * gr ({9} : Finset (Fin 10)) + (1) * gr ({2, 9} : Finset (Fin 10)) ≤ 0)
    (h185 : (-1) * m 4 2 + (1) * fl ({4} : Finset (Fin 10)) + (1) * gr ({2} : Finset (Fin 10)) + (-1) * r ≤ 0)
    (h186 : (1) * m 4 3 + (-1) * fl ({4} : Finset (Fin 10)) + (-1) * fl ({8} : Finset (Fin 10)) + (1) * fl ({4, 8} : Finset (Fin 10)) ≤ 0)
    (h187 : (1) * m 4 3 + (-1) * gr ({3} : Finset (Fin 10)) + (-1) * gr ({9} : Finset (Fin 10)) + (1) * gr ({3, 9} : Finset (Fin 10)) ≤ 0)
    (h188 : (-1) * m 4 3 + (1) * fl ({8} : Finset (Fin 10)) + (1) * gr ({9} : Finset (Fin 10)) + (-1) * k ≤ 0)
    (h189 : 0 ≤ fl (∅ : Finset (Fin 10))) :
    15 * N ≤ 11 * (r + k) := by
  have c0 : 186 * fl {0, 1, 4, 9} + (-186) * fl {0, 1, 4} + 186 * fl {0, 1, 5} + (-186) * fl {0, 1, 9} + 1736 * fl {0, 5} + 366 * fl {0, 6, 7} + (-366) * fl {0, 6} + 186 * fl {0, 7, 8} + (-552) * fl {0, 7} + (-186) * fl {0, 8} + (-1184) * fl {0} + (-186) * fl {1, 5} + 1055 * fl {1, 6} + (-869) * fl {1} + 80 * fl {2, 5, 8} + (-80) * fl {2, 5} + 1685 * fl {2, 7} + (-80) * fl {2, 8} + (-1605) * fl {2} + 1657 * fl {3, 8} + (-1657) * fl {3} + 2162 * fl {4, 9} + (-2162) * fl {4} + (-1736) * fl {5} + (-1055) * fl {6} + (-1685) * fl {7} + (-1657) * fl {8} + (-2162) * fl {9} + 8295 * fl ∅ ≤ 0 := by linarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have c1 : (-186) * fl {0, 1, 4, 8} + 186 * fl {0, 1, 4} + 366 * fl {0, 3, 4, 5} + (-366) * fl {0, 3, 4} + (-80) * fl {1, 2, 4, 5} + 80 * fl {1, 2, 4, 7} + 80 * fl {1, 4, 5, 8} + (-80) * fl {1, 4, 5} + 346 * fl {1, 4, 6} + 186 * fl {1, 4, 7, 8} + (-266) * fl {1, 4, 7} + (-266) * fl {1, 4, 8} + (-366) * fl {3, 4, 5} + 416 * fl {3, 4, 9} + (-50) * fl {3, 4} + 316 * fl {3, 6, 7} + (-316) * fl {3, 6} + (-316) * fl {3, 7} + (-416) * fl {3, 9} + 732 * fl {3} + 316 * fl {4, 6, 7} + (-662) * fl {4, 6} + (-316) * fl {4, 7} + 662 * fl {4} ≤ 0 := by linarith only [h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
  have c2 : (-186) * fl {0, 1, 5} + (-366) * fl {0, 3, 4, 5} + (-366) * fl {0, 3, 4, 7} + 366 * fl {0, 3, 4} + (-28) * fl {0, 5, 8} + 580 * fl {0, 5} + (-80) * fl {1, 2, 4, 5, 8} + 80 * fl {1, 2, 4, 5} + 80 * fl {1, 4, 5} + (-80) * fl {1, 5} + 366 * fl {3, 4, 5} + 50 * fl {3, 4, 6, 7} + (-50) * fl {3, 4, 6} + (-50) * fl {3, 4, 7} + 50 * fl {3, 4} + 52 * fl {3, 5, 8} + (-418) * fl {3, 5} + (-446) * fl {4, 5} + (-52) * fl {5, 8} + 498 * fl {5} ≤ 0 := by linarith only [h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
  have c3 : (-366) * fl {0, 3, 4, 6, 7} + 366 * fl {0, 3, 4, 7} + (-80) * fl {1, 2, 4, 7} + (-346) * fl {1, 4, 6} + 266 * fl {1, 4, 7} + 1028 * fl {1, 6} + (-948) * fl {1, 7} + (-186) * fl {2, 7, 8} + 266 * fl {2, 7} + 50 * fl {3, 4, 6} + 50 * fl {3, 4, 7} + (-50) * fl {3, 6} + (-50) * fl {3, 7} + (-50) * fl {4, 6} + (-316) * fl {4, 7} + (-682) * fl {6, 7} + 50 * fl {6} + 998 * fl {7} ≤ 0 := by linarith only [h30, h31, h32, h33, h34, h35, h36, h37, h38, h39]
  have c4 : (-186) * fl {0, 1, 4, 7, 8} + 186 * fl {0, 1, 4, 8} + 366 * fl {0, 3, 4, 6, 7} + 28 * fl {0, 5, 8} + (-366) * fl {0, 6, 7} + (-28) * fl {0, 8} + 80 * fl {1, 2, 5, 8} + 266 * fl {1, 4, 8} + (-80) * fl {1, 5, 8} + (-266) * fl {1, 8} + (-80) * fl {2, 5, 8} + 186 * fl {2, 7, 8} + (-186) * fl {2, 8} + (-50) * fl {3, 4, 6, 7} + (-52) * fl {3, 5, 8} + (-316) * fl {3, 6, 7} + 52 * fl {3, 8} + (-316) * fl {4, 6, 7} + (-266) * fl {4, 8} + 52 * fl {5, 8} + 682 * fl {6, 7} + (-186) * fl {7, 8} + 480 * fl {8} ≤ 0 := by linarith only [h40, h41, h42, h43, h44, h45, h46, h47, h48, h49]
  have c5 : 6350 * N + 186 * fl {0, 1, 4, 7, 8} + (-186) * fl {0, 1, 4, 9} + 186 * fl {0, 1, 9} + (-2316) * fl {0, 5} + (-186) * fl {0, 7, 8} + (-186) * fl {0, 9} + 80 * fl {1, 2, 4, 5, 8} + (-80) * fl {1, 2, 5, 8} + (-80) * fl {1, 4, 5, 8} + (-186) * fl {1, 4, 7, 8} + 80 * fl {1, 5, 8} + (-2083) * fl {1, 6} + (-186) * fl {1, 9} + (-1951) * fl {2, 7} + (-416) * fl {3, 4, 9} + 602 * fl {4, 9} + 186 * fl {7, 8} + 186 * fl {9} ≤ 0 := by linarith only [h50, h51, h52, h53, h54, h55, h56, h57, h58, h59]
  have c6 : 4473 * N + (-1709) * fl {3, 8} + (-2764) * fl {4, 9} + 687 * gr {0, 1, 2, 7} + (-687) * gr {0, 1, 2, 8} + 318 * gr {0, 1, 5} + 369 * gr {0, 1, 6} + (-687) * gr {0, 1, 7} + 182 * gr {0, 6, 7} + (-551) * gr {0, 6} + (-182) * gr {0, 7} + 687 * gr {0, 8, 9} + (-687) * gr {0, 8} + (-687) * gr {0, 9} + 1238 * gr {0} + (-318) * gr {1, 5} + 687 * gr {1, 8, 9} + (-687) * gr {1, 8} + (-687) * gr {1, 9} + 1005 * gr {1} + 687 * gr {2, 8, 9} + (-687) * gr {2, 8} + (-687) * gr {2, 9} + 687 * gr {2} ≤ 0 := by linarith only [h60, h61, h62, h63, h64, h65, h66, h67, h68, h69]
  have c7 : 333 * gr {0, 3, 4, 8} + 126 * gr {0, 3, 4, 9} + (-459) * gr {0, 3, 4} + 403 * gr {0, 3, 5} + 277 * gr {0, 3, 6, 7} + (-277) * gr {0, 3, 6} + (-277) * gr {0, 3, 7} + (-126) * gr {0, 3, 9} + 333 * gr {0, 4, 5} + (-333) * gr {0, 4, 8} + 592 * gr {2, 3, 4, 8} + (-592) * gr {2, 3, 4} + 1184 * gr {2, 4, 7} + (-592) * gr {2, 4, 8} + (-592) * gr {2, 4} + 592 * gr {3, 5, 6} + (-995) * gr {3, 5} + 182 * gr {3, 6, 7} + (-774) * gr {3, 6} + (-182) * gr {3, 7} + 1177 * gr {3} + (-333) * gr {4, 5} + 459 * gr {4, 6, 7} + (-459) * gr {4, 6} + (-1643) * gr {4, 7} + 1976 * gr {4} ≤ 0 := by linarith only [h70, h71, h72, h73, h74, h75, h76, h77, h78, h79]
  have c8 : (-318) * gr {0, 1, 5} + (-459) * gr {0, 3, 4, 7} + 459 * gr {0, 3, 4} + (-403) * gr {0, 3, 5} + 277 * gr {0, 3, 6} + (-333) * gr {0, 4, 5} + 1054 * gr {0, 5} + (-277) * gr {0, 6} + 592 * gr {1, 5, 6} + (-592) * gr {1, 5} + (-592) * gr {2, 3, 4, 5, 6} + 592 * gr {2, 3, 4} + 592 * gr {2, 4, 5, 6} + (-592) * gr {2, 4, 6} + 592 * gr {2, 4} + (-592) * gr {2, 5} + (-277) * gr {3, 6} + (-592) * gr {4, 5} + (-592) * gr {5, 6} + 1184 * gr {5} + 277 * gr {6} ≤ 0 := by linarith only [h80, h81, h82, h83, h84, h85, h86, h87, h88, h89]
  have c9 : (-369) * gr {0, 1, 6} + 687 * gr {0, 1, 7} + (-687) * gr {0, 2, 7} + 277 * gr {0, 3, 7} + (-964) * gr {0, 7} + (-592) * gr {1, 5, 6} + 1602 * gr {1, 6} + (-1328) * gr {1, 7} + 592 * gr {2, 3, 4, 5, 6} + (-592) * gr {2, 4, 5, 6} + 592 * gr {2, 4, 6} + (-592) * gr {2, 6} + 687 * gr {2, 7} + (-592) * gr {3, 5, 6} + (-277) * gr {3, 7} + (-592) * gr {4, 6} + 592 * gr {5, 6} + (-641) * gr {6, 7} + 592 * gr {6} + 1605 * gr {7} ≤ 0 := by linarith only [h90, h91, h92, h93, h94, h95, h96, h97, h98, h99]
  have c10 : (-687) * gr {0, 1, 2, 7} + (-687) * gr {0, 1, 2, 8, 9} + 687 * gr {0, 1, 2, 8} + 687 * gr {0, 2, 7} + 459 * gr {0, 3, 4, 7} + (-277) * gr {0, 3, 6, 7} + 333 * gr {0, 4, 8} + (-182) * gr {0, 6, 7} + (-333) * gr {0, 8} + (-1184) * gr {2, 4, 7} + 592 * gr {2, 4, 8} + 1184 * gr {2, 7} + (-592) * gr {2, 8} + (-925) * gr {3, 4, 8} + (-182) * gr {3, 6, 7} + 925 * gr {3, 8} + (-459) * gr {4, 6, 7} + (-925) * gr {4, 8} + 641 * gr {6, 7} + 925 * gr {8} ≤ 0 := by linarith only [h100, h101, h102, h103, h104, h105, h106, h107, h108, h109]
  have c11 : 687 * gr {0, 1, 2, 8, 9} + (-333) * gr {0, 3, 4, 8} + (-126) * gr {0, 3, 4, 9} + 126 * gr {0, 3, 9} + (-687) * gr {0, 8, 9} + (-126) * gr {0, 9} + (-687) * gr {1, 8, 9} + (-592) * gr {2, 3, 4, 8} + (-687) * gr {2, 8, 9} + 925 * gr {3, 4, 8} + 1374 * gr {3, 8} + (-1500) * gr {3, 9} + 126 * gr {4, 9} + 1500 * gr {9} ≤ 0 := by linarith only [h110, h111, h112, h113, h114, h115, h116, h117, h118, h119]
  have c12 : 6952 * N + 366 * fl {0, 6} + 552 * fl {0, 7} + (-769) * fl {0} + 761 * fl {6} + (-552) * fl {7} + (-1054) * gr {0, 5} + 910 * gr {1, 5} + (-1602) * gr {1, 6} + (-761) * gr {1} + (-1871) * gr {2, 7} + (-2299) * gr {3, 8} + (-126) * gr {4, 9} + 217 * gr {5} + (-1127) * k + 552 * m 0 2 + (-149) * r ≤ 0 := by linarith only [h120, h121, h122, h123, h124, h125, h126, h127, h128, h129]
  have c13 : 214 * fl {0, 8} + 186 * fl {0, 9} + 1953 * fl {0} + 266 * fl {1, 5} + (-266) * fl {1} + (-266) * fl {5} + (-214) * fl {8} + 925 * fl {9} + 828 * gr {0, 6} + (-828) * gr {0} + 592 * gr {2, 5} + 552 * gr {2} + 995 * gr {3, 5} + 214 * gr {3} + 925 * gr {4, 5} + (-925) * gr {4} + (-1401) * gr {5} + (-828) * gr {6} + (-1111) * k + (-552) * m 0 2 + 1094 * m 1 0 + (-2353) * r ≤ 0 := by linarith only [h130, h131, h132, h133, h134, h135, h136, h137, h138, h139]
  have c14 : 948 * fl {1, 7} + 266 * fl {1, 8} + 186 * fl {1, 9} + 210 * fl {1} + 801 * fl {5} + 592 * fl {7} + (-266) * fl {8} + (-186) * fl {9} + 293 * gr {0} + 592 * gr {2, 6} + (-592) * gr {2} + 1051 * gr {3, 6} + 266 * gr {3} + 1051 * gr {4, 6} + (-1051) * gr {4} + (-353) * gr {6} + (-2341) * k + (-1094) * m 1 0 + 1237 * m 1 4 + (-1610) * r ≤ 0 := by linarith only [h140, h141, h142, h143, h144, h145, h146, h147, h148, h149]
  have c15 : 925 * fl {1} + 80 * fl {2, 5} + 266 * fl {2, 8} + (-340) * fl {2} + 1146 * fl {5} + 1322 * fl {6} + (-266) * fl {8} + 312 * fl {9} + 1146 * gr {0, 7} + (-1146) * gr {0} + 1328 * gr {1, 7} + (-1322) * gr {1} + 459 * gr {3, 7} + (-459) * gr {3} + 925 * gr {4} + 312 * gr {6} + (-385) * gr {7} + (-2860) * k + (-1237) * m 1 4 + 725 * m 2 3 + (-931) * r ≤ 0 := by linarith only [h150, h151, h152, h153, h154, h155, h156, h157, h158, h159]
  have c16 : 1945 * fl {2} + 418 * fl {3, 5} + 366 * fl {3, 6} + 1707 * fl {3} + (-418) * fl {5} + (-366) * fl {6} + 423 * fl {8} + 1020 * gr {0, 8} + 418 * gr {0} + 687 * gr {1, 8} + 366 * gr {1} + 302 * gr {3} + 1643 * gr {4, 7} + (-1220) * gr {7} + (-1707) * gr {8} + (-423) * k + (-725) * m 2 3 + (-4436) * r ≤ 0 := by linarith only [h160, h161, h162, h163, h164, h165, h166, h167, h168, h169]
  have c17 : 366 * fl {3, 7} + 416 * fl {3, 9} + (-782) * fl {3} + 446 * fl {4, 5} + 392 * fl {4} + (-25) * fl {5} + 1279 * fl {7} + 925 * fl {9} + 813 * gr {0, 9} + 25 * gr {0} + 1279 * gr {2, 8} + (-1279) * gr {2} + 925 * gr {4, 8} + (-925) * gr {4} + 782 * gr {8} + (-392) * gr {9} + (-3407) * k + (-838) * r ≤ 0 := by linarith only [h170, h171, h172, h173, h174, h175, h176, h177, h178, h179]
  have c18 : 712 * fl {4, 6} + 632 * fl {4, 7} + 266 * fl {4, 8} + 1108 * fl {4} + (-712) * fl {6} + (-632) * fl {7} + 1500 * fl {8} + 687 * gr {1, 9} + 712 * gr {1} + 687 * gr {2, 9} + 632 * gr {2} + 1500 * gr {3, 9} + (-1500) * gr {3} + (-1108) * gr {9} + (-1766) * k + (-2718) * r ≤ 0 := by linarith only [h180, h181, h182, h183, h184, h185, h186, h187, h188]
  have t0_0 : (-186) * fl {0, 1, 4, 8} + 186 * fl {0, 1, 4, 9} + 186 * fl {0, 1, 5} + (-186) * fl {0, 1, 9} + 366 * fl {0, 3, 4, 5} + (-366) * fl {0, 3, 4} + 1736 * fl {0, 5} + 366 * fl {0, 6, 7} + (-366) * fl {0, 6} + 186 * fl {0, 7, 8} + (-552) * fl {0, 7} + (-186) * fl {0, 8} + (-1184) * fl {0} + (-80) * fl {1, 2, 4, 5} + 80 * fl {1, 2, 4, 7} + 80 * fl {1, 4, 5, 8} + (-80) * fl {1, 4, 5} + 346 * fl {1, 4, 6} + 186 * fl {1, 4, 7, 8} + (-266) * fl {1, 4, 7} + (-266) * fl {1, 4, 8} + (-186) * fl {1, 5} + 1055 * fl {1, 6} + (-869) * fl {1} + 80 * fl {2, 5, 8} + (-80) * fl {2, 5} + 1685 * fl {2, 7} + (-80) * fl {2, 8} + (-1605) * fl {2} + (-366) * fl {3, 4, 5} + 416 * fl {3, 4, 9} + (-50) * fl {3, 4} + 316 * fl {3, 6, 7} + (-316) * fl {3, 6} + (-316) * fl {3, 7} + 1657 * fl {3, 8} + (-416) * fl {3, 9} + (-925) * fl {3} + 316 * fl {4, 6, 7} + (-662) * fl {4, 6} + (-316) * fl {4, 7} + 2162 * fl {4, 9} + (-1500) * fl {4} + (-1736) * fl {5} + (-1055) * fl {6} + (-1685) * fl {7} + (-1657) * fl {8} + (-2162) * fl {9} + 8295 * fl ∅ ≤ 0 := by linarith only [c0, c1]
  have t0_1 : (-186) * fl {0, 1, 5} + (-366) * fl {0, 3, 4, 5} + (-366) * fl {0, 3, 4, 6, 7} + 366 * fl {0, 3, 4} + (-28) * fl {0, 5, 8} + 580 * fl {0, 5} + (-80) * fl {1, 2, 4, 5, 8} + 80 * fl {1, 2, 4, 5} + (-80) * fl {1, 2, 4, 7} + 80 * fl {1, 4, 5} + (-346) * fl {1, 4, 6} + 266 * fl {1, 4, 7} + (-80) * fl {1, 5} + 1028 * fl {1, 6} + (-948) * fl {1, 7} + (-186) * fl {2, 7, 8} + 266 * fl {2, 7} + 366 * fl {3, 4, 5} + 50 * fl {3, 4, 6, 7} + 50 * fl {3, 4} + 52 * fl {3, 5, 8} + (-418) * fl {3, 5} + (-50) * fl {3, 6} + (-50) * fl {3, 7} + (-446) * fl {4, 5} + (-50) * fl {4, 6} + (-316) * fl {4, 7} + (-52) * fl {5, 8} + 498 * fl {5} + (-682) * fl {6, 7} + 50 * fl {6} + 998 * fl {7} ≤ 0 := by linarith only [c2, c3]
  have t0_2 : 6350 * N + 186 * fl {0, 1, 4, 8} + (-186) * fl {0, 1, 4, 9} + 186 * fl {0, 1, 9} + 366 * fl {0, 3, 4, 6, 7} + 28 * fl {0, 5, 8} + (-2316) * fl {0, 5} + (-366) * fl {0, 6, 7} + (-186) * fl {0, 7, 8} + (-28) * fl {0, 8} + (-186) * fl {0, 9} + 80 * fl {1, 2, 4, 5, 8} + (-80) * fl {1, 4, 5, 8} + (-186) * fl {1, 4, 7, 8} + 266 * fl {1, 4, 8} + (-2083) * fl {1, 6} + (-266) * fl {1, 8} + (-186) * fl {1, 9} + (-80) * fl {2, 5, 8} + 186 * fl {2, 7, 8} + (-1951) * fl {2, 7} + (-186) * fl {2, 8} + (-50) * fl {3, 4, 6, 7} + (-416) * fl {3, 4, 9} + (-52) * fl {3, 5, 8} + (-316) * fl {3, 6, 7} + 52 * fl {3, 8} + (-316) * fl {4, 6, 7} + (-266) * fl {4, 8} + 602 * fl {4, 9} + 52 * fl {5, 8} + 682 * fl {6, 7} + 480 * fl {8} + 186 * fl {9} ≤ 0 := by linarith only [c4, c5]
  have t0_3 : 4473 * N + (-1709) * fl {3, 8} + (-2764) * fl {4, 9} + 687 * gr {0, 1, 2, 7} + (-687) * gr {0, 1, 2, 8} + 318 * gr {0, 1, 5} + 369 * gr {0, 1, 6} + (-687) * gr {0, 1, 7} + 333 * gr {0, 3, 4, 8} + 126 * gr {0, 3, 4, 9} + (-459) * gr {0, 3, 4} + 403 * gr {0, 3, 5} + 277 * gr {0, 3, 6, 7} + (-277) * gr {0, 3, 6} + (-277) * gr {0, 3, 7} + (-126) * gr {0, 3, 9} + 333 * gr {0, 4, 5} + (-333) * gr {0, 4, 8} + 182 * gr {0, 6, 7} + (-551) * gr {0, 6} + (-182) * gr {0, 7} + 687 * gr {0, 8, 9} + (-687) * gr {0, 8} + (-687) * gr {0, 9} + 1238 * gr {0} + (-318) * gr {1, 5} + 687 * gr {1, 8, 9} + (-687) * gr {1, 8} + (-687) * gr {1, 9} + 1005 * gr {1} + 592 * gr {2, 3, 4, 8} + (-592) * gr {2, 3, 4} + 1184 * gr {2, 4, 7} + (-592) * gr {2, 4, 8} + (-592) * gr {2, 4} + 687 * gr {2, 8, 9} + (-687) * gr {2, 8} + (-687) * gr {2, 9} + 687 * gr {2} + 592 * gr {3, 5, 6} + (-995) * gr {3, 5} + 182 * gr {3, 6, 7} + (-774) * gr {3, 6} + (-182) * gr {3, 7} + 1177 * gr {3} + (-333) * gr {4, 5} + 459 * gr {4, 6, 7} + (-459) * gr {4, 6} + (-1643) * gr {4, 7} + 1976 * gr {4} ≤ 0 := by linarith only [c6, c7]
  have t0_4 : (-318) * gr {0, 1, 5} + (-369) * gr {0, 1, 6} + 687 * gr {0, 1, 7} + (-687) * gr {0, 2, 7} + (-459) * gr {0, 3, 4, 7} + 459 * gr {0, 3, 4} + (-403) * gr {0, 3, 5} + 277 * gr {0, 3, 6} + 277 * gr {0, 3, 7} + (-333) * gr {0, 4, 5} + 1054 * gr {0, 5} + (-277) * gr {0, 6} + (-964) * gr {0, 7} + (-592) * gr {1, 5} + 1602 * gr {1, 6} + (-1328) * gr {1, 7} + 592 * gr {2, 3, 4} + 592 * gr {2, 4} + (-592) * gr {2, 5} + (-592) * gr {2, 6} + 687 * gr {2, 7} + (-592) * gr {3, 5, 6} + (-277) * gr {3, 6} + (-277) * gr {3, 7} + (-592) * gr {4, 5} + (-592) * gr {4, 6} + 1184 * gr {5} + (-641) * gr {6, 7} + 869 * gr {6} + 1605 * gr {7} ≤ 0 := by linarith only [c8, c9]
  have t0_5 : (-687) * gr {0, 1, 2, 7} + 687 * gr {0, 1, 2, 8} + 687 * gr {0, 2, 7} + 459 * gr {0, 3, 4, 7} + (-333) * gr {0, 3, 4, 8} + (-126) * gr {0, 3, 4, 9} + (-277) * gr {0, 3, 6, 7} + 126 * gr {0, 3, 9} + 333 * gr {0, 4, 8} + (-182) * gr {0, 6, 7} + (-687) * gr {0, 8, 9} + (-333) * gr {0, 8} + (-126) * gr {0, 9} + (-687) * gr {1, 8, 9} + (-592) * gr {2, 3, 4, 8} + (-1184) * gr {2, 4, 7} + 592 * gr {2, 4, 8} + 1184 * gr {2, 7} + (-687) * gr {2, 8, 9} + (-592) * gr {2, 8} + (-182) * gr {3, 6, 7} + 2299 * gr {3, 8} + (-1500) * gr {3, 9} + (-459) * gr {4, 6, 7} + (-925) * gr {4, 8} + 126 * gr {4, 9} + 641 * gr {6, 7} + 925 * gr {8} + 1500 * gr {9} ≤ 0 := by linarith only [c10, c11]
  have t0_6 : 6952 * N + 366 * fl {0, 6} + 552 * fl {0, 7} + 214 * fl {0, 8} + 186 * fl {0, 9} + 1184 * fl {0} + 266 * fl {1, 5} + (-266) * fl {1} + (-266) * fl {5} + 761 * fl {6} + (-552) * fl {7} + (-214) * fl {8} + 925 * fl {9} + (-1054) * gr {0, 5} + 828 * gr {0, 6} + (-828) * gr {0} + 910 * gr {1, 5} + (-1602) * gr {1, 6} + (-761) * gr {1} + 592 * gr {2, 5} + (-1871) * gr {2, 7} + 552 * gr {2} + 995 * gr {3, 5} + (-2299) * gr {3, 8} + 214 * gr {3} + 925 * gr {4, 5} + (-126) * gr {4, 9} + (-925) * gr {4} + (-1184) * gr {5} + (-828) * gr {6} + (-2238) * k + 1094 * m 1 0 + (-2502) * r ≤ 0 := by linarith only [c12, c13]
  have t0_7 : 948 * fl {1, 7} + 266 * fl {1, 8} + 186 * fl {1, 9} + 1135 * fl {1} + 80 * fl {2, 5} + 266 * fl {2, 8} + (-340) * fl {2} + 1947 * fl {5} + 1322 * fl {6} + 592 * fl {7} + (-532) * fl {8} + 126 * fl {9} + 1146 * gr {0, 7} + (-853) * gr {0} + 1328 * gr {1, 7} + (-1322) * gr {1} + 592 * gr {2, 6} + (-592) * gr {2} + 1051 * gr {3, 6} + 459 * gr {3, 7} + (-193) * gr {3} + 1051 * gr {4, 6} + (-126) * gr {4} + (-41) * gr {6} + (-385) * gr {7} + (-5201) * k + (-1094) * m 1 0 + 725 * m 2 3 + (-2541) * r ≤ 0 := by linarith only [c14, c15]
  have t0_8 : 1945 * fl {2} + 418 * fl {3, 5} + 366 * fl {3, 6} + 366 * fl {3, 7} + 416 * fl {3, 9} + 925 * fl {3} + 446 * fl {4, 5} + 392 * fl {4} + (-443) * fl {5} + (-366) * fl {6} + 1279 * fl {7} + 423 * fl {8} + 925 * fl {9} + 1020 * gr {0, 8} + 813 * gr {0, 9} + 443 * gr {0} + 687 * gr {1, 8} + 366 * gr {1} + 1279 * gr {2, 8} + (-1279) * gr {2} + 302 * gr {3} + 1643 * gr {4, 7} + 925 * gr {4, 8} + (-925) * gr {4} + (-1220) * gr {7} + (-925) * gr {8} + (-392) * gr {9} + (-3830) * k + (-725) * m 2 3 + (-5274) * r ≤ 0 := by linarith only [c16, c17]
  have t1_0 : (-186) * fl {0, 1, 4, 8} + 186 * fl {0, 1, 4, 9} + (-186) * fl {0, 1, 9} + (-366) * fl {0, 3, 4, 6, 7} + (-28) * fl {0, 5, 8} + 2316 * fl {0, 5} + 366 * fl {0, 6, 7} + (-366) * fl {0, 6} + 186 * fl {0, 7, 8} + (-552) * fl {0, 7} + (-186) * fl {0, 8} + (-1184) * fl {0} + (-80) * fl {1, 2, 4, 5, 8} + 80 * fl {1, 4, 5, 8} + 186 * fl {1, 4, 7, 8} + (-266) * fl {1, 4, 8} + (-266) * fl {1, 5} + 2083 * fl {1, 6} + (-948) * fl {1, 7} + (-869) * fl {1} + 80 * fl {2, 5, 8} + (-80) * fl {2, 5} + (-186) * fl {2, 7, 8} + 1951 * fl {2, 7} + (-80) * fl {2, 8} + (-1605) * fl {2} + 50 * fl {3, 4, 6, 7} + 416 * fl {3, 4, 9} + 52 * fl {3, 5, 8} + (-418) * fl {3, 5} + 316 * fl {3, 6, 7} + (-366) * fl {3, 6} + (-366) * fl {3, 7} + 1657 * fl {3, 8} + (-416) * fl {3, 9} + (-925) * fl {3} + (-446) * fl {4, 5} + 316 * fl {4, 6, 7} + (-712) * fl {4, 6} + (-632) * fl {4, 7} + 2162 * fl {4, 9} + (-1500) * fl {4} + (-52) * fl {5, 8} + (-1238) * fl {5} + (-682) * fl {6, 7} + (-1005) * fl {6} + (-687) * fl {7} + (-1657) * fl {8} + (-2162) * fl {9} + 8295 * fl ∅ ≤ 0 := by linarith only [t0_0, t0_1]
  have t1_1 : 10823 * N + 186 * fl {0, 1, 4, 8} + (-186) * fl {0, 1, 4, 9} + 186 * fl {0, 1, 9} + 366 * fl {0, 3, 4, 6, 7} + 28 * fl {0, 5, 8} + (-2316) * fl {0, 5} + (-366) * fl {0, 6, 7} + (-186) * fl {0, 7, 8} + (-28) * fl {0, 8} + (-186) * fl {0, 9} + 80 * fl {1, 2, 4, 5, 8} + (-80) * fl {1, 4, 5, 8} + (-186) * fl {1, 4, 7, 8} + 266 * fl {1, 4, 8} + (-2083) * fl {1, 6} + (-266) * fl {1, 8} + (-186) * fl {1, 9} + (-80) * fl {2, 5, 8} + 186 * fl {2, 7, 8} + (-1951) * fl {2, 7} + (-186) * fl {2, 8} + (-50) * fl {3, 4, 6, 7} + (-416) * fl {3, 4, 9} + (-52) * fl {3, 5, 8} + (-316) * fl {3, 6, 7} + (-1657) * fl {3, 8} + (-316) * fl {4, 6, 7} + (-266) * fl {4, 8} + (-2162) * fl {4, 9} + 52 * fl {5, 8} + 682 * fl {6, 7} + 480 * fl {8} + 186 * fl {9} + 687 * gr {0, 1, 2, 7} + (-687) * gr {0, 1, 2, 8} + 318 * gr {0, 1, 5} + 369 * gr {0, 1, 6} + (-687) * gr {0, 1, 7} + 333 * gr {0, 3, 4, 8} + 126 * gr {0, 3, 4, 9} + (-459) * gr {0, 3, 4} + 403 * gr {0, 3, 5} + 277 * gr {0, 3, 6, 7} + (-277) * gr {0, 3, 6} + (-277) * gr {0, 3, 7} + (-126) * gr {0, 3, 9} + 333 * gr {0, 4, 5} + (-333) * gr {0, 4, 8} + 182 * gr {0, 6, 7} + (-551) * gr {0, 6} + (-182) * gr {0, 7} + 687 * gr {0, 8, 9} + (-687) * gr {0, 8} + (-687) * gr {0, 9} + 1238 * gr {0} + (-318) * gr {1, 5} + 687 * gr {1, 8, 9} + (-687) * gr {1, 8} + (-687) * gr {1, 9} + 1005 * gr {1} + 592 * gr {2, 3, 4, 8} + (-592) * gr {2, 3, 4} + 1184 * gr {2, 4, 7} + (-592) * gr {2, 4, 8} + (-592) * gr {2, 4} + 687 * gr {2, 8, 9} + (-687) * gr {2, 8} + (-687) * gr {2, 9} + 687 * gr {2} + 592 * gr {3, 5, 6} + (-995) * gr {3, 5} + 182 * gr {3, 6, 7} + (-774) * gr {3, 6} + (-182) * gr {3, 7} + 1177 * gr {3} + (-333) * gr {4, 5} + 459 * gr {4, 6, 7} + (-459) * gr {4, 6} + (-1643) * gr {4, 7} + 1976 * gr {4} ≤ 0 := by linarith only [t0_2, t0_3]
  have t1_2 : (-687) * gr {0, 1, 2, 7} + 687 * gr {0, 1, 2, 8} + (-318) * gr {0, 1, 5} + (-369) * gr {0, 1, 6} + 687 * gr {0, 1, 7} + (-333) * gr {0, 3, 4, 8} + (-126) * gr {0, 3, 4, 9} + 459 * gr {0, 3, 4} + (-403) * gr {0, 3, 5} + (-277) * gr {0, 3, 6, 7} + 277 * gr {0, 3, 6} + 277 * gr {0, 3, 7} + 126 * gr {0, 3, 9} + (-333) * gr {0, 4, 5} + 333 * gr {0, 4, 8} + 1054 * gr {0, 5} + (-182) * gr {0, 6, 7} + (-277) * gr {0, 6} + (-964) * gr {0, 7} + (-687) * gr {0, 8, 9} + (-333) * gr {0, 8} + (-126) * gr {0, 9} + (-592) * gr {1, 5} + 1602 * gr {1, 6} + (-1328) * gr {1, 7} + (-687) * gr {1, 8, 9} + (-592) * gr {2, 3, 4, 8} + 592 * gr {2, 3, 4} + (-1184) * gr {2, 4, 7} + 592 * gr {2, 4, 8} + 592 * gr {2, 4} + (-592) * gr {2, 5} + (-592) * gr {2, 6} + 1871 * gr {2, 7} + (-687) * gr {2, 8, 9} + (-592) * gr {2, 8} + (-592) * gr {3, 5, 6} + (-182) * gr {3, 6, 7} + (-277) * gr {3, 6} + (-277) * gr {3, 7} + 2299 * gr {3, 8} + (-1500) * gr {3, 9} + (-592) * gr {4, 5} + (-459) * gr {4, 6, 7} + (-592) * gr {4, 6} + (-925) * gr {4, 8} + 126 * gr {4, 9} + 1184 * gr {5} + 869 * gr {6} + 1605 * gr {7} + 925 * gr {8} + 1500 * gr {9} ≤ 0 := by linarith only [t0_4, t0_5]
  have t1_3 : 6952 * N + 366 * fl {0, 6} + 552 * fl {0, 7} + 214 * fl {0, 8} + 186 * fl {0, 9} + 1184 * fl {0} + 266 * fl {1, 5} + 948 * fl {1, 7} + 266 * fl {1, 8} + 186 * fl {1, 9} + 869 * fl {1} + 80 * fl {2, 5} + 266 * fl {2, 8} + (-340) * fl {2} + 1681 * fl {5} + 2083 * fl {6} + 40 * fl {7} + (-746) * fl {8} + 1051 * fl {9} + (-1054) * gr {0, 5} + 828 * gr {0, 6} + 1146 * gr {0, 7} + (-1681) * gr {0} + 910 * gr {1, 5} + (-1602) * gr {1, 6} + 1328 * gr {1, 7} + (-2083) * gr {1} + 592 * gr {2, 5} + 592 * gr {2, 6} + (-1871) * gr {2, 7} + (-40) * gr {2} + 995 * gr {3, 5} + 1051 * gr {3, 6} + 459 * gr {3, 7} + (-2299) * gr {3, 8} + 21 * gr {3} + 925 * gr {4, 5} + 1051 * gr {4, 6} + (-126) * gr {4, 9} + (-1051) * gr {4} + (-1184) * gr {5} + (-869) * gr {6} + (-385) * gr {7} + (-7439) * k + 725 * m 2 3 + (-5043) * r ≤ 0 := by linarith only [t0_6, t0_7]
  have t1_4 : 1945 * fl {2} + 418 * fl {3, 5} + 366 * fl {3, 6} + 366 * fl {3, 7} + 416 * fl {3, 9} + 925 * fl {3} + 446 * fl {4, 5} + 712 * fl {4, 6} + 632 * fl {4, 7} + 266 * fl {4, 8} + 1500 * fl {4} + (-443) * fl {5} + (-1078) * fl {6} + 647 * fl {7} + 1923 * fl {8} + 925 * fl {9} + 1020 * gr {0, 8} + 813 * gr {0, 9} + 443 * gr {0} + 687 * gr {1, 8} + 687 * gr {1, 9} + 1078 * gr {1} + 1279 * gr {2, 8} + 687 * gr {2, 9} + (-647) * gr {2} + 1500 * gr {3, 9} + (-1198) * gr {3} + 1643 * gr {4, 7} + 925 * gr {4, 8} + (-925) * gr {4} + (-1220) * gr {7} + (-925) * gr {8} + (-1500) * gr {9} + (-5596) * k + (-725) * m 2 3 + (-7992) * r ≤ 0 := by linarith only [t0_8, c18]
  have t2_0 : 10823 * N + (-366) * fl {0, 6} + (-552) * fl {0, 7} + (-214) * fl {0, 8} + (-186) * fl {0, 9} + (-1184) * fl {0} + (-266) * fl {1, 5} + (-948) * fl {1, 7} + (-266) * fl {1, 8} + (-186) * fl {1, 9} + (-869) * fl {1} + (-80) * fl {2, 5} + (-266) * fl {2, 8} + (-1605) * fl {2} + (-418) * fl {3, 5} + (-366) * fl {3, 6} + (-366) * fl {3, 7} + (-416) * fl {3, 9} + (-925) * fl {3} + (-446) * fl {4, 5} + (-712) * fl {4, 6} + (-632) * fl {4, 7} + (-266) * fl {4, 8} + (-1500) * fl {4} + (-1238) * fl {5} + (-1005) * fl {6} + (-687) * fl {7} + (-1177) * fl {8} + (-1976) * fl {9} + 8295 * fl ∅ + 687 * gr {0, 1, 2, 7} + (-687) * gr {0, 1, 2, 8} + 318 * gr {0, 1, 5} + 369 * gr {0, 1, 6} + (-687) * gr {0, 1, 7} + 333 * gr {0, 3, 4, 8} + 126 * gr {0, 3, 4, 9} + (-459) * gr {0, 3, 4} + 403 * gr {0, 3, 5} + 277 * gr {0, 3, 6, 7} + (-277) * gr {0, 3, 6} + (-277) * gr {0, 3, 7} + (-126) * gr {0, 3, 9} + 333 * gr {0, 4, 5} + (-333) * gr {0, 4, 8} + 182 * gr {0, 6, 7} + (-551) * gr {0, 6} + (-182) * gr {0, 7} + 687 * gr {0, 8, 9} + (-687) * gr {0, 8} + (-687) * gr {0, 9} + 1238 * gr {0} + (-318) * gr {1, 5} + 687 * gr {1, 8, 9} + (-687) * gr {1, 8} + (-687) * gr {1, 9} + 1005 * gr {1} + 592 * gr {2, 3, 4, 8} + (-592) * gr {2, 3, 4} + 1184 * gr {2, 4, 7} + (-592) * gr {2, 4, 8} + (-592) * gr {2, 4} + 687 * gr {2, 8, 9} + (-687) * gr {2, 8} + (-687) * gr {2, 9} + 687 * gr {2} + 592 * gr {3, 5, 6} + (-995) * gr {3, 5} + 182 * gr {3, 6, 7} + (-774) * gr {3, 6} + (-182) * gr {3, 7} + 1177 * gr {3} + (-333) * gr {4, 5} + 459 * gr {4, 6, 7} + (-459) * gr {4, 6} + (-1643) * gr {4, 7} + 1976 * gr {4} ≤ 0 := by linarith only [t1_0, t1_1]
  have t2_1 : 6952 * N + 366 * fl {0, 6} + 552 * fl {0, 7} + 214 * fl {0, 8} + 186 * fl {0, 9} + 1184 * fl {0} + 266 * fl {1, 5} + 948 * fl {1, 7} + 266 * fl {1, 8} + 186 * fl {1, 9} + 869 * fl {1} + 80 * fl {2, 5} + 266 * fl {2, 8} + (-340) * fl {2} + 1681 * fl {5} + 2083 * fl {6} + 40 * fl {7} + (-746) * fl {8} + 1051 * fl {9} + (-687) * gr {0, 1, 2, 7} + 687 * gr {0, 1, 2, 8} + (-318) * gr {0, 1, 5} + (-369) * gr {0, 1, 6} + 687 * gr {0, 1, 7} + (-333) * gr {0, 3, 4, 8} + (-126) * gr {0, 3, 4, 9} + 459 * gr {0, 3, 4} + (-403) * gr {0, 3, 5} + (-277) * gr {0, 3, 6, 7} + 277 * gr {0, 3, 6} + 277 * gr {0, 3, 7} + 126 * gr {0, 3, 9} + (-333) * gr {0, 4, 5} + 333 * gr {0, 4, 8} + (-182) * gr {0, 6, 7} + 551 * gr {0, 6} + 182 * gr {0, 7} + (-687) * gr {0, 8, 9} + (-333) * gr {0, 8} + (-126) * gr {0, 9} + (-1681) * gr {0} + 318 * gr {1, 5} + (-687) * gr {1, 8, 9} + (-2083) * gr {1} + (-592) * gr {2, 3, 4, 8} + 592 * gr {2, 3, 4} + (-1184) * gr {2, 4, 7} + 592 * gr {2, 4, 8} + 592 * gr {2, 4} + (-687) * gr {2, 8, 9} + (-592) * gr {2, 8} + (-40) * gr {2} + (-592) * gr {3, 5, 6} + 995 * gr {3, 5} + (-182) * gr {3, 6, 7} + 774 * gr {3, 6} + 182 * gr {3, 7} + (-1500) * gr {3, 9} + 21 * gr {3} + 333 * gr {4, 5} + (-459) * gr {4, 6, 7} + 459 * gr {4, 6} + (-925) * gr {4, 8} + (-1051) * gr {4} + 1220 * gr {7} + 925 * gr {8} + 1500 * gr {9} + (-7439) * k + 725 * m 2 3 + (-5043) * r ≤ 0 := by linarith only [t1_2, t1_3]
  have t3_0 : 17775 * N + (-1945) * fl {2} + (-418) * fl {3, 5} + (-366) * fl {3, 6} + (-366) * fl {3, 7} + (-416) * fl {3, 9} + (-925) * fl {3} + (-446) * fl {4, 5} + (-712) * fl {4, 6} + (-632) * fl {4, 7} + (-266) * fl {4, 8} + (-1500) * fl {4} + 443 * fl {5} + 1078 * fl {6} + (-647) * fl {7} + (-1923) * fl {8} + (-925) * fl {9} + 8295 * fl ∅ + (-1020) * gr {0, 8} + (-813) * gr {0, 9} + (-443) * gr {0} + (-687) * gr {1, 8} + (-687) * gr {1, 9} + (-1078) * gr {1} + (-1279) * gr {2, 8} + (-687) * gr {2, 9} + 647 * gr {2} + (-1500) * gr {3, 9} + 1198 * gr {3} + (-1643) * gr {4, 7} + (-925) * gr {4, 8} + 925 * gr {4} + 1220 * gr {7} + 925 * gr {8} + 1500 * gr {9} + (-7439) * k + 725 * m 2 3 + (-5043) * r ≤ 0 := by linarith only [t2_0, t2_1]
  have t4_0 : 17775 * N + 8295 * fl ∅ + (-13035) * k + (-13035) * r ≤ 0 := by linarith only [t3_0, t1_4]
  linarith only [t4_0, h189]
end

/-! ## unit minsum_ge_fifteen_elevenths_N_every_field -/
section
open Matrix

/-- **T444 (Lena): P(n) >= 15n/11 for every n >= 5, over EVERY field.** Every exact split SWAP_N = B + C has
15 N <= 11 (rank B + OS C). The constant 15/11 is Silas's R214 (5-slice LP); exact certificates by Gideon and Greta.
Proof: Daria's slice bridge at slices 0..4, the 189 certificate rows from verified units (T444_R214_rows_part0..5),
and Greta's arithmetic core greta_R214_core. -/
theorem lena_minsumF_ge_fifteen_elevenths {F : Type*} [Field F] (N : ℕ) (hN : 5 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F) (h : biancaSwapF F (Fin N) = B + C) :
    15 * N ≤ 11 * (B.rank + (biancaRealignF C).rank) := by
  classical
  obtain ⟨X, Y, P, Q, hd, ho⟩ := slice_system_of_split B C h
  let s : Fin 5 → Fin N := fun y => ⟨y.val, by omega⟩
  have hs : ∀ y u : Fin 5, y ≠ u → s y ≠ s u := fun y u hyu e => hyu (Fin.ext (by
    have h' := congrArg Fin.val e
    simpa [s] using h'))
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := lena_R214_rows_0 X Y P Q hd ho s hs
  obtain ⟨h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63⟩ := lena_R214_rows_1 X Y P Q hd ho s hs
  obtain ⟨h64, h65, h66, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90, h91, h92, h93, h94, h95⟩ := lena_R214_rows_2 X Y P Q hd ho s hs
  obtain ⟨h96, h97, h98, h99, h100, h101, h102, h103, h104, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, h115, h116, h117, h118, h119, h120, h121, h122, h123, h124, h125, h126, h127⟩ := lena_R214_rows_3 X Y P Q hd ho s hs
  obtain ⟨h128, h129, h130, h131, h132, h133, h134, h135, h136, h137, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, h153, h154, h155, h156, h157, h158, h159⟩ := lena_R214_rows_4 X Y P Q hd ho s hs
  obtain ⟨h160, h161, h162, h163, h164, h165, h166, h167, h168, h169, h170, h171, h172, h173, h174, h175, h176, h177, h178, h179, h180, h181, h182, h183, h184, h185, h186, h187, h188⟩ := lena_R214_rows_5 X Y P Q hd ho s hs
  have h189 : 0 ≤ lenaR214Fl (lenaR214W X P s) (∅ : Finset (Fin 10)) := by rw [lena_fl_empty]
  have hcore := greta_R214_core (lenaR214Fl (lenaR214W X P s)) (lenaR214Fl (lenaR214W Y Q s))
    (fun y u => ((X (s y) * (Y (s u))ᵀ).rank : ℤ)) (B.rank : ℤ) ((biancaRealignF C).rank : ℤ) (N : ℤ)
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86 h87 h88 h89 h90 h91 h92 h93 h94 h95 h96 h97 h98 h99 h100 h101 h102 h103 h104 h105 h106 h107 h108 h109 h110 h111 h112 h113 h114 h115 h116 h117 h118 h119 h120 h121 h122 h123 h124 h125 h126 h127 h128 h129 h130 h131 h132 h133 h134 h135 h136 h137 h138 h139 h140 h141 h142 h143 h144 h145 h146 h147 h148 h149 h150 h151 h152 h153 h154 h155 h156 h157 h158 h159 h160 h161 h162 h163 h164 h165 h166 h167 h168 h169 h170 h171 h172 h173 h174 h175 h176 h177 h178 h179 h180 h181 h182 h183 h184 h185 h186 h187 h188 h189
  exact_mod_cast hcore
end

/-! ## The result in the notation of SwapSplit.lean -/

namespace SwapSplit

/-- P(N) ≥ 15 N / 11 for every N ≥ 5, over every field. -/
theorem swap_split_ge_fifteen_elevenths {F : Type*} [Field F] (N : ℕ) (hN : 5 ≤ N)
    (B C : Matrix (Fin N × Fin N) (Fin N × Fin N) F)
    (h : swapMat F N = B + C) : 15 * N ≤ 11 * (B.rank + (realign C).rank) := by
  rw [realign_eq_biancaRealignF]
  exact lena_minsumF_ge_fifteen_elevenths N hN B C (by rw [← swapMat_eq_biancaSwapF]; exact h)

end SwapSplit

#print axioms SwapSplit.swap_split_ge_fifteen_elevenths
