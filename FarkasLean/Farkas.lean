import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.Alt1

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

def InCone {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b

def HasDualCert {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ (vecMul y A) j) ∧ y ⬝ᵥ b < 0

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

theorem not_inCone_and_hasDualCert {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
    ¬(InCone A b ∧ HasDualCert A b) := by
  rintro ⟨⟨x, hx_nonneg, rfl⟩, y, hyA_nonneg, hyb_neg⟩
  have h_assoc : y ⬝ᵥ (A.mulVec x) = (vecMul y A) ⬝ᵥ x :=
    dotProduct_mulVec y A x
  have h_nonneg : 0 ≤ (vecMul y A) ⬝ᵥ x :=
    dotProduct_nonneg_of_nonneg hyA_nonneg hx_nonneg
  linarith [h_assoc, h_nonneg, hyb_neg]

/-!
## Farkas' Lemma
-/

theorem farkas {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
    InCone A b ∨ HasDualCert A b := by
  classical
  let C : Matrix (m ⊕ m ⊕ Fin n) (Fin n) F := fun i j =>
    match i with
    | Sum.inl i₁ => A i₁ j
    | Sum.inr (Sum.inl i₂) => -A i₂ j
    | Sum.inr (Sum.inr k) => if k = j then (-1 : F) else 0
  let d : (m ⊕ m ⊕ Fin n) → F := fun i =>
    match i with
    | Sum.inl i₁ => b i₁
    | Sum.inr (Sum.inl i₂) => -b i₂
    | Sum.inr (Sum.inr _) => 0
  have hAlt : A1Primal (m := m ⊕ m ⊕ Fin n) C d ∨ A1Dual (m := m ⊕ m ⊕ Fin n) C d :=
    A1Exhaust (m := m ⊕ m ⊕ Fin n) C d
  rcases hAlt with hPrimal | hDual
  · left
    rcases hPrimal with ⟨x, hx_le⟩
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj := hx_le (Sum.inr (Sum.inr j))
      have hj' : -x j ≤ (0 : F) := by
        simpa [A1Primal, C, d, Matrix.mulVec, dotProduct] using hj
      linarith
    · ext i
      have hi₁ := hx_le (Sum.inl i)
      have hi₂ := hx_le (Sum.inr (Sum.inl i))
      have hle : A.mulVec x i ≤ b i := by
        simpa [A1Primal, C, d] using hi₁
      have hge_neg : -(A.mulVec x i) ≤ -b i := by
        simpa [A1Primal, C, d, Matrix.mulVec, dotProduct] using hi₂
      have hge : b i ≤ A.mulVec x i := by
        linarith
      exact le_antisymm hle hge
  · right
    rcases hDual with ⟨w, hw_nonneg, hwC_zero, hwd_neg⟩
    let y₁ : m → F := fun i => w (Sum.inl i)
    let y₂ : m → F := fun i => w (Sum.inr (Sum.inl i))
    let y : m → F := y₁ - y₂
    refine ⟨y, ?_, ?_⟩
    · intro j
      have hcol0 : (w ᵥ* C) j = 0 := by simpa using congr_fun hwC_zero j
      have hcol : (vecMul y A) j = w (Sum.inr (Sum.inr j)) := by
        have hsplit :
            (w ᵥ* C) j = (vecMul y₁ A) j - (vecMul y₂ A) j - w (Sum.inr (Sum.inr j)) := by
          simp [C, y₁, y₂, Matrix.vecMul, dotProduct]
          ring
        have hy_split : (vecMul y A) j = (vecMul y₁ A) j - (vecMul y₂ A) j := by
          simp [y, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
        linarith [hcol0, hsplit, hy_split]
      have hj_nonneg : 0 ≤ w (Sum.inr (Sum.inr j)) := hw_nonneg (Sum.inr (Sum.inr j))
      simpa [hcol] using hj_nonneg
    · have hwd : w ⬝ᵥ d = y ⬝ᵥ b := by
        calc
          w ⬝ᵥ d = y₁ ⬝ᵥ b - y₂ ⬝ᵥ b := by
            simp [d, y₁, y₂, dotProduct]
            ring
          _ = y ⬝ᵥ b := by
            simp [y, dotProduct, Finset.sum_sub_distrib, sub_mul]
      rw [hwd] at hwd_neg
      exact hwd_neg

end FarkasLemma
