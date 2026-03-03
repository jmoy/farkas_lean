import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.FourierMotzkin

open Matrix

namespace FarkasLemma

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def A1Primal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, A.mulVec x ≤  b

def A1Dual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0)

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

theorem A1Exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
    ¬(A1Primal A b ∧ A1Dual A b) := by
  rintro ⟨⟨x, hAx⟩, ⟨y, hy, hyA, hyb⟩⟩
  have hyb_nonneg : 0 ≤ y ⬝ᵥ b := by
    have hdot_le : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ b := by
      simpa using dotProduct_le_dotProduct_of_nonneg_left hAx hy
    have hdot_eq : y ⬝ᵥ (A *ᵥ x) = 0 := by
      calc
        y ⬝ᵥ (A *ᵥ x) = (y ᵥ* A) ⬝ᵥ x := by
          simpa using Matrix.dotProduct_mulVec y A x
        _ = 0 := by simp [hyA]
    have hzero : 0 ≤ y ⬝ᵥ (A *ᵥ x) := by
      simp [hdot_eq]
    exact le_trans hzero hdot_le
  linarith

private theorem liftDual_of_fourierMotzkin {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F) (b : m → F) (M : Matrix κ m F)
    (hM_last : ∀ i, (M * A) i (Fin.last n) = 0)
    (hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j)
  (y' : κ → F)
  (hy'_nonneg : ∀ j, 0 ≤ y' j)
  (hy'_Ared : y' ᵥ* (M * (A.submatrix id Fin.castSucc)) = 0)
  (hy'_bred : y' ⬝ᵥ M.mulVec b < 0) :
  let y : m → F := M.transpose.mulVec y'
  (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0) := by
  have hy_nonneg : ∀ j, 0 ≤ (M.transpose.mulVec y') j := by
    intro j
    simpa [Matrix.mulVec] using dotProduct_nonneg_of_nonneg (hMt_nonneg j) hy'_nonneg
  have hy'_Acast : y' ᵥ* ((M * A).submatrix id Fin.castSucc) = 0 := by
    have hAred_eq : M * (A.submatrix id Fin.castSucc) = (M * A).submatrix id Fin.castSucc := by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA : y' ᵥ* (M * A) = 0 := by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul, dotProduct, hM_last]
    · intro k
      simpa [Matrix.vecMul, dotProduct] using congr_fun hy'_Acast k
  have hyA : (M.transpose.mulVec y') ᵥ* A = 0 := by
    calc
      (M.transpose.mulVec y') ᵥ* A = (y' ᵥ* M) ᵥ* A := by
        rw [Matrix.mulVec_transpose]
      _ = y' ᵥ* (M * A) := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := hy'_MA
  have hyb : (M.transpose.mulVec y') ⬝ᵥ b < 0 := by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b = (y' ᵥ* M) ⬝ᵥ b := by
        rw [Matrix.mulVec_transpose]
      _ = y' ⬝ᵥ M.mulVec b := by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0 := hy'_bred
  simpa using
    (show (∀ j, 0 ≤ (M.transpose.mulVec y') j) ∧
        ((M.transpose.mulVec y') ᵥ* A = 0) ∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg, hyA, hyb⟩)

/-!
## Farkas' Lemma
-/

theorem A1Exhaust {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
    A1Primal A b ∨ A1Dual A b := by
  induction n generalizing m b with
  | zero =>
      by_cases hb : 0 ≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi : ∃ i : m, b i < 0 := by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i, lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i, hbi⟩
        classical
        let y : m → F := fun j => if j = i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i <;> simp [y, hji]
        · ext j
          exact j.elim0
        · have hyb : y ⬝ᵥ b = b i := by
            simp [y, dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP : A1Primal A b
      · exact Or.inl hP
      · right
        rcases Fourier_Motzkin A b with ⟨κ, _, M, hM_nonneg, hM_last, hFM⟩
        let Ared : Matrix κ (Fin n) F := M * (A.submatrix id Fin.castSucc)
        let bred : κ → F := M.mulVec b
        have hFM' : A1Primal A b ↔ A1Primal (m := κ) Ared bred := by
          simpa [A1Primal, Ared, bred] using hFM
        have hred_noPrimal : ¬ A1Primal (m := κ) Ared bred := by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust : A1Primal (m := κ) Ared bred ∨ A1Dual (m := κ) Ared bred :=
          ih (m := κ) (A := Ared) (b := bred)
        have hred_dual : A1Dual (m := κ) Ared bred := by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y', hy'_nonneg, hy'_Ared, hy'_bred⟩
        have hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j := by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift : A1Dual A b := by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared, bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift
end FarkasLemma
