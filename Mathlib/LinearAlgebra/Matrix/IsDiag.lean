/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Data.Matrix.Kronecker

#align_import linear_algebra.matrix.is_diag from "leanprover-community/mathlib"@"55e2dfde0cff928ce5c70926a3f2c7dee3e2dd99"

/-!
# Diagonal matrices

This file contains the definition and basic results about diagonal matrices.

## Main results

- `Matrix.IsDiag`: a proposition that states a given square matrix `A` is diagonal.

## Tags

diag, diagonal, matrix
-/


namespace Matrix

variable {α β R n m : Type*}

open Function

open Matrix Kronecker

/-- `A.IsDiag` means square matrix `A` is a diagonal matrix. -/
def IsDiag [Zero α] (A : Matrix n n α) : Prop :=
  Pairwise fun i j => A i j = 0
#align matrix.is_diag Matrix.IsDiag

@[simp]
lemma isDiag_diagonal [Zero α] [DecidableEq n] (d : n → α) : (diagonal d).IsDiag := fun _ _ =>
  Matrix.diagonal_apply_ne _
#align matrix.is_diag_diagonal Matrix.isDiag_diagonal

/-- Diagonal matrices are generated by the `Matrix.diagonal` of their `Matrix.diag`. -/
theorem IsDiag.diagonal_diag [Zero α] [DecidableEq n] {A : Matrix n n α} (h : A.IsDiag) :
    diagonal (diag A) = A :=
  ext fun i j => by
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [diagonal_apply_eq, diag]
    · rw [diagonal_apply_ne _ hij, h hij]
#align matrix.is_diag.diagonal_diag Matrix.IsDiag.diagonal_diag

/-- `Matrix.IsDiag.diagonal_diag` as an iff. -/
theorem isDiag_iff_diagonal_diag [Zero α] [DecidableEq n] (A : Matrix n n α) :
    A.IsDiag ↔ diagonal (diag A) = A :=
  ⟨IsDiag.diagonal_diag, fun hd => hd ▸ isDiag_diagonal (diag A)⟩
#align matrix.is_diag_iff_diagonal_diag Matrix.isDiag_iff_diagonal_diag

/-- Every matrix indexed by a subsingleton is diagonal. -/
theorem isDiag_of_subsingleton [Zero α] [Subsingleton n] (A : Matrix n n α) : A.IsDiag :=
  fun i j h => (h <| Subsingleton.elim i j).elim
#align matrix.is_diag_of_subsingleton Matrix.isDiag_of_subsingleton

/-- Every zero matrix is diagonal. -/
@[simp]
theorem isDiag_zero [Zero α] : (0 : Matrix n n α).IsDiag := fun _ _ _ => rfl
#align matrix.is_diag_zero Matrix.isDiag_zero

/-- Every identity matrix is diagonal. -/
@[simp]
theorem isDiag_one [DecidableEq n] [Zero α] [One α] : (1 : Matrix n n α).IsDiag := fun _ _ =>
  one_apply_ne
#align matrix.is_diag_one Matrix.isDiag_one

lemma IsDiag.map [Zero α] [Zero β] {A : Matrix n n α} (ha : A.IsDiag) {f : α → β} (hf : f 0 = 0) :
    (A.map f).IsDiag := by
  intro i j h
  simp [ha h, hf]
#align matrix.is_diag.map Matrix.IsDiag.map

lemma IsDiag.neg [AddGroup α] {A : Matrix n n α} (ha : A.IsDiag) : (-A).IsDiag := by
  intro i j h
  simp [ha h]
#align matrix.is_diag.neg Matrix.IsDiag.neg

@[simp]
lemma isDiag_neg_iff [AddGroup α] {A : Matrix n n α} : (-A).IsDiag ↔ A.IsDiag :=
  ⟨fun ha _ _ h => neg_eq_zero.1 (ha h), IsDiag.neg⟩
#align matrix.is_diag_neg_iff Matrix.isDiag_neg_iff

lemma IsDiag.add [AddZeroClass α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A + B).IsDiag := by
  intro i j h
  simp [ha h, hb h]
#align matrix.is_diag.add Matrix.IsDiag.add

lemma IsDiag.sub [AddGroup α] {A B : Matrix n n α} (ha : A.IsDiag) (hb : B.IsDiag) :
    (A - B).IsDiag := by
  intro i j h
  simp [ha h, hb h]
#align matrix.is_diag.sub Matrix.IsDiag.sub

lemma IsDiag.smul [Monoid R] [AddMonoid α] [DistribMulAction R α] (k : R) {A : Matrix n n α}
    (ha : A.IsDiag) : (k • A).IsDiag := by
  intro i j h
  simp [ha h]
#align matrix.is_diag.smul Matrix.IsDiag.smul

@[simp]
lemma isDiag_smul_one (n) [Semiring α] [DecidableEq n] (k : α) :
    (k • (1 : Matrix n n α)).IsDiag :=
  isDiag_one.smul k
#align matrix.is_diag_smul_one Matrix.isDiag_smul_one

lemma IsDiag.transpose [Zero α] {A : Matrix n n α} (ha : A.IsDiag) : Aᵀ.IsDiag := fun _ _ h =>
  ha h.symm
#align matrix.is_diag.transpose Matrix.IsDiag.transpose

@[simp]
lemma isDiag_transpose_iff [Zero α] {A : Matrix n n α} : Aᵀ.IsDiag ↔ A.IsDiag :=
  ⟨IsDiag.transpose, IsDiag.transpose⟩
#align matrix.is_diag_transpose_iff Matrix.isDiag_transpose_iff

lemma IsDiag.conjTranspose [Semiring α] [StarRing α] {A : Matrix n n α} (ha : A.IsDiag) :
    Aᴴ.IsDiag :=
  ha.transpose.map (star_zero _)
#align matrix.is_diag.conj_transpose Matrix.IsDiag.conjTranspose

@[simp]
lemma isDiag_conjTranspose_iff [Semiring α] [StarRing α] {A : Matrix n n α} :
    Aᴴ.IsDiag ↔ A.IsDiag :=
  ⟨fun ha => by
    convert ha.conjTranspose
    simp, IsDiag.conjTranspose⟩
#align matrix.is_diag_conj_transpose_iff Matrix.isDiag_conjTranspose_iff

lemma IsDiag.submatrix [Zero α] {A : Matrix n n α} (ha : A.IsDiag) {f : m → n}
    (hf : Injective f) : (A.submatrix f f).IsDiag := fun _ _ h => ha (hf.ne h)
#align matrix.is_diag.submatrix Matrix.IsDiag.submatrix

/-- `(A ⊗ B).IsDiag` if both `A` and `B` are diagonal. -/
theorem IsDiag.kronecker [MulZeroClass α] {A : Matrix m m α} {B : Matrix n n α} (hA : A.IsDiag)
    (hB : B.IsDiag) : (A ⊗ₖ B).IsDiag := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.inj_iff, Ne, not_and_or] at h
  cases' h with hac hbd
  · simp [hA hac]
  · simp [hB hbd]
#align matrix.is_diag.kronecker Matrix.IsDiag.kronecker

lemma IsDiag.isSymm [Zero α] {A : Matrix n n α} (h : A.IsDiag) : A.IsSymm := by
  ext i j
  by_cases g : i = j; · rw [g, transpose_apply]
  simp [h g, h (Ne.symm g)]
#align matrix.is_diag.is_symm Matrix.IsDiag.isSymm

/-- The block matrix `A.fromBlocks 0 0 D` is diagonal if `A` and `D` are diagonal. -/
theorem IsDiag.fromBlocks [Zero α] {A : Matrix m m α} {D : Matrix n n α} (ha : A.IsDiag)
    (hd : D.IsDiag) : (A.fromBlocks 0 0 D).IsDiag := by
  rintro (i | i) (j | j) hij
  · exact ha (ne_of_apply_ne _ hij)
  · rfl
  · rfl
  · exact hd (ne_of_apply_ne _ hij)
#align matrix.is_diag.from_blocks Matrix.IsDiag.fromBlocks

/-- This is the `iff` version of `Matrix.IsDiag.fromBlocks`. -/
theorem isDiag_fromBlocks_iff [Zero α] {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} : (A.fromBlocks B C D).IsDiag ↔ A.IsDiag ∧ B = 0 ∧ C = 0 ∧ D.IsDiag := by
  constructor
  · intro h
    refine' ⟨fun i j hij => _, ext fun i j => _, ext fun i j => _, fun i j hij => _⟩
    · exact h (Sum.inl_injective.ne hij)
    · exact h Sum.inl_ne_inr
    · exact h Sum.inr_ne_inl
    · exact h (Sum.inr_injective.ne hij)
  · rintro ⟨ha, hb, hc, hd⟩
    convert IsDiag.fromBlocks ha hd
#align matrix.is_diag_from_blocks_iff Matrix.isDiag_fromBlocks_iff

/-- A symmetric block matrix `A.fromBlocks B C D` is diagonal
    if `A` and `D` are diagonal and `B` is `0`. -/
theorem IsDiag.fromBlocks_of_isSymm [Zero α] {A : Matrix m m α} {C : Matrix n m α}
    {D : Matrix n n α} (h : (A.fromBlocks 0 C D).IsSymm) (ha : A.IsDiag) (hd : D.IsDiag) :
    (A.fromBlocks 0 C D).IsDiag := by
  rw [← (isSymm_fromBlocks_iff.1 h).2.1]
  exact ha.fromBlocks hd
#align matrix.is_diag.from_blocks_of_is_symm Matrix.IsDiag.fromBlocks_of_isSymm

lemma mul_transpose_self_isDiag_iff_hasOrthogonalRows [Fintype n] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (A * Aᵀ).IsDiag ↔ A.HasOrthogonalRows :=
  Iff.rfl
#align matrix.mul_transpose_self_is_diag_iff_has_orthogonal_rows Matrix.mul_transpose_self_isDiag_iff_hasOrthogonalRows

lemma transpose_mul_self_isDiag_iff_hasOrthogonalCols [Fintype m] [Mul α] [AddCommMonoid α]
    {A : Matrix m n α} : (Aᵀ * A).IsDiag ↔ A.HasOrthogonalCols :=
  Iff.rfl
#align matrix.transpose_mul_self_is_diag_iff_has_orthogonal_cols Matrix.transpose_mul_self_isDiag_iff_hasOrthogonalCols

end Matrix
