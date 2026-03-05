import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.MotzkinTransposition

/-
Proving Stiemke's Lemma via reduction to Motzkin Transposition.
-/

open Matrix

namespace FarkasLemma

variable {F : Type*} [Field F] [LinearOrder F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

-- Primal Stiemke certificate: a strictly positive vector in the kernel of `A`.
def StiemkePrimal {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 < x j) ∧ A.mulVec x = 0

-- Dual Stiemke certificate: a nonnegative nonzero vector of the form `yᵀA`.
def StiemkeDual {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  ∃ y : m → F, (0 ≤ (vecMul y A) ∧ 0 ≠ (vecMul y A))

/-!
## Reduction to Motzkin

For a Stiemke instance `A : Matrix m (Fin n) F`, define the transformed
Motzkin data:

- strict block: `-I` on `Fin n` so `(-I)x < 0` means `x > 0`
- weak block: empty (`Fin 0`)
- equality block: `A` with RHS `0`
- strict and equality RHS are `0`
- weak RHS is vacuous
-/

-- Strict block `-I`: enforces positivity after rewriting `(-I)x < 0` as `x > 0`.
def steimMotzA {n : ℕ} (_A : Matrix m (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => if i = j then (-1 : F) else 0

-- Weak block is empty, so there are no weak inequalities in this reduction.
def steimMotzB {n : ℕ} (_A : Matrix m (Fin n) F) : Matrix (Fin 0) (Fin n) F :=
  fun i _ => Fin.elim0 i

-- Equality block is exactly `A`, preserving kernel constraints.
def steimMotzC {n : ℕ} (A : Matrix m (Fin n) F) : Matrix m (Fin n) F := A

-- Strict RHS is zero so strict constraints are `(-I)x < 0`.
def steimMotza {n : ℕ} (_A : Matrix m (Fin n) F) : Fin n → F := fun _ => 0

-- Weak RHS is vacuous because the weak index type is empty.
def steimMotzb {n : ℕ} (_A : Matrix m (Fin n) F) : Fin 0 → F :=
  fun i => Fin.elim0 i

-- Equality RHS is zero, encoding `Ax = 0`.
def steimMotzc {n : ℕ} (_A : Matrix m (Fin n) F) : m → F := fun _ => 0

-- Pack the transformed Motzkin data as a single map from a Stiemke instance.
def motz_to_steim {n : ℕ} (A : Matrix m (Fin n) F) :
  Matrix (Fin n) (Fin n) F × Matrix (Fin 0) (Fin n) F × Matrix m (Fin n) F ×
  (Fin n → F) × (Fin 0 → F) × (m → F) :=
  (steimMotzA A, steimMotzB A, steimMotzC A, steimMotza A, steimMotzb A, steimMotzc A)

-- Shorthand for the Motzkin primal system induced by a Stiemke instance.
def StiemkeMotzkinPrimal {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  MotzkinPrimal (steimMotzA A) (steimMotzB A) (steimMotzC A)
    (steimMotza A) (steimMotzb A) (steimMotzc A)

-- Shorthand for the Motzkin dual system induced by a Stiemke instance.
def StiemkeMotzkinDual {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  MotzkinDual (steimMotzA A) (steimMotzB A) (steimMotzC A)
    (steimMotza A) (steimMotzb A) (steimMotzc A)

omit [Fintype m] in
/-- Converts a Stiemke primal witness (`x > 0` and `Ax = 0`) into the
Motzkin primal witness for the transformed instance. -/
lemma stiemke_primal_to_motzkin_primal {n : ℕ} [IsStrictOrderedRing F]
  (A : Matrix m (Fin n) F)
    (hP : StiemkePrimal A) :
    StiemkeMotzkinPrimal A := by
  rcases hP with ⟨x, hx_pos, hAx_zero⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    have hneg : -x i < (0 : F) := by
      exact neg_lt_zero.mpr (hx_pos i)
    simpa [steimMotza, steimMotzA, Matrix.mulVec, dotProduct] using hneg
  · intro i
    exact Fin.elim0 i
  · simpa [steimMotzC, steimMotzc] using hAx_zero

omit [Fintype m] in
/-- Converts a Motzkin primal witness of the transformed instance back into a
Stiemke primal witness (`x > 0` and `Ax = 0`). -/
lemma motzkin_primal_to_stiemke_primal {n : ℕ} [IsStrictOrderedRing F]
  (A : Matrix m (Fin n) F)
    (hP : StiemkeMotzkinPrimal A) :
    StiemkePrimal A := by
  rcases hP with ⟨x, hstrict, _hweak, hEq⟩
  refine ⟨x, ?_, ?_⟩
  · intro j
    have hneg : -x j < (0 : F) := by
      simpa [steimMotza, steimMotzA, Matrix.mulVec, dotProduct] using hstrict j
    simpa using (neg_lt_neg hneg)
  · simpa [steimMotzC, steimMotzc] using hEq

/-- Converts a Stiemke dual witness (`vecMul y A` nonnegative and nonzero)
into the Motzkin dual witness for the transformed instance. -/
lemma stiemke_dual_to_motzkin_dual {n : ℕ} (A : Matrix m (Fin n) F)
    (hD : StiemkeDual A) :
    StiemkeMotzkinDual A := by
  rcases hD with ⟨v, hv_nonneg, hv_ne⟩
  let y0 : F := 0
  let y : Fin n → F := vecMul v A
  let u : Fin 0 → F := fun i => Fin.elim0 i
  refine ⟨y0, y, u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [y0]
  · simpa [y] using hv_nonneg
  · intro i
    exact Fin.elim0 i
  · right
    simpa [y] using hv_ne.symm
  · ext j
    have hyj : (vecMul y (steimMotzA A)) j = -y j := by
      simp [steimMotzA, Matrix.vecMul, dotProduct]
    have huj : (vecMul u (steimMotzB A)) j = 0 := by
      simp [u, steimMotzB, Matrix.vecMul, dotProduct]
    calc
      (vecMul y (steimMotzA A) + vecMul u (steimMotzB A) + vecMul v (steimMotzC A)) j
          = (vecMul y (steimMotzA A)) j + (vecMul u (steimMotzB A)) j + (vecMul v A) j := by
            simp [steimMotzC]
      _ = -y j + 0 + (vecMul v A) j := by rw [hyj, huj]
      _ = 0 := by simp [y]
  · simp [y0, y, u, steimMotza, steimMotzb, steimMotzc, dotProduct]

/-- Converts a Motzkin dual witness of the transformed instance back into a
Stiemke dual witness. -/
lemma motzkin_dual_to_stiemke_dual {n : ℕ} (A : Matrix m (Fin n) F)
    (hD : StiemkeMotzkinDual A) :
    StiemkeDual A := by
  rcases hD with ⟨y0, y, u, v, hy0_nn, hy_nn, _hu_nn, hnontriv, hmat, hscalar⟩
  have hy0_zero : y0 = 0 := by
    simpa [steimMotza, steimMotzb, steimMotzc, dotProduct] using hscalar
  have hy_ne : y ≠ 0 := by
    cases hnontriv with
    | inl hy0_ne => exact (False.elim (hy0_ne hy0_zero))
    | inr hy_ne => exact hy_ne
  have hy_eq : vecMul v A = y := by
    ext j
    have hmat_j : (vecMul y (steimMotzA A) + vecMul u (steimMotzB A) + vecMul v A) j = 0 := by
      simpa using congr_fun hmat j
    have hyi : (vecMul y (steimMotzA A)) j = -y j := by
      simp [steimMotzA, Matrix.vecMul, dotProduct]
    have hui : (vecMul u (steimMotzB A)) j = 0 := by
      simp [steimMotzB, Matrix.vecMul, dotProduct]
    have hsum : -y j + (vecMul v A) j = 0 := by
      simpa [hyi, hui, add_assoc, add_comm, add_left_comm] using hmat_j
    have hsum' : (vecMul v A) j + (-y j) = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have htmp : (vecMul v A) j = -(-y j) := eq_neg_of_add_eq_zero_left hsum'
    simpa using htmp
  refine ⟨v, ?_, ?_⟩
  · intro j
    rw [hy_eq]
    exact hy_nn j
  · intro hv_zero
    apply hy_ne
    have : y = 0 := by simpa [hy_eq] using hv_zero.symm
    exact this

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

/-- Stiemke primal and dual certificates cannot hold simultaneously, obtained
from Motzkin exclusivity under the reduction. -/
theorem stiemke_exclusive {n : ℕ} [IsStrictOrderedRing F] (A : Matrix m (Fin n) F) :
    ¬(StiemkePrimal A ∧ StiemkeDual A) := by
  intro h
  rcases h with ⟨hP, hD⟩
  have hPm : StiemkeMotzkinPrimal A := stiemke_primal_to_motzkin_primal A hP
  have hDm : StiemkeMotzkinDual A := stiemke_dual_to_motzkin_dual A hD
  exact motzkin_exclusive
    (A := steimMotzA A) (B := steimMotzB A) (C := steimMotzC A)
    (a := steimMotza A) (b := steimMotzb A) (c := steimMotzc A)
    ⟨hPm, hDm⟩

/-- Every Stiemke instance has either a primal certificate or a dual
certificate, obtained from Motzkin exhaustiveness under the reduction. -/
theorem stiemke_exhaustive {n : ℕ} [IsStrictOrderedRing F] (A : Matrix m (Fin n) F) :
  StiemkePrimal A ∨ StiemkeDual A := by
  have hM : StiemkeMotzkinPrimal A ∨ StiemkeMotzkinDual A :=
    motzkin_exhaustive
      (A := steimMotzA A) (B := steimMotzB A) (C := steimMotzC A)
      (a := steimMotza A) (b := steimMotzb A) (c := steimMotzc A)
  cases hM with
  | inl hP =>
      exact Or.inl (motzkin_primal_to_stiemke_primal A hP)
  | inr hD =>
      exact Or.inr (motzkin_dual_to_stiemke_dual A hD)

end FarkasLemma
