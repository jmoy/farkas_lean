import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.Alt1

/-
Proving Stiemke's Lemma Based on the theorem of the alternative in
Alt1.Lean
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

def StiemkePrimal {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 < x j) ∧ A.mulVec x = 0

def StiemkeDual {n : ℕ} (A : Matrix m (Fin n) F) : Prop :=
  ∃ y : m → F, (0 ≤ (vecMul y A) ∧ 0 ≠ (vecMul y A))

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

theorem stiemke_exclusive {n : ℕ} [IsStrictOrderedRing F] (A : Matrix m (Fin n) F) :
    ¬(StiemkePrimal A ∧ StiemkeDual A) := by
  rintro ⟨⟨x, hx_pos, ha_zero⟩, y, hyA_nonneg, hyA_ne_zero⟩
  have hzero : (vecMul y A) ⬝ᵥ x = 0 := by
    simpa [ha_zero] using (Matrix.dotProduct_mulVec y A x).symm
  have hsum_zero : ∑ j : Fin n, (vecMul y A) j * x j = 0 := by
    simpa [dotProduct] using hzero
  have hterm_nonneg : ∀ j : Fin n, 0 ≤ (vecMul y A) j * x j :=
    fun j => mul_nonneg (hyA_nonneg j) (le_of_lt (hx_pos j))
  have hterm_eq_zero : ∀ j : Fin n, (vecMul y A) j * x j = 0 := fun j =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm_nonneg i)).mp hsum_zero j (by simp)
  have hvec_zero : vecMul y A = 0 := by
    ext j
    exact (mul_eq_zero.mp (hterm_eq_zero j)).resolve_right (ne_of_gt (hx_pos j))
  exact hyA_ne_zero hvec_zero.symm

theorem stiemke_exhaustive {n : ℕ} [IsStrictOrderedRing F] (A : Matrix m (Fin n) F) :
  StiemkePrimal A ∨ StiemkeDual A := by
  let C : Matrix (m ⊕ m ⊕ Fin n) (Fin n) F := fun i j =>
    match i with
    | Sum.inl i₁ => A i₁ j
    | Sum.inr (Sum.inl i₂) => - (A i₂ j)
    | Sum.inr (Sum.inr k) => if k = j then (-1 : F) else 0
  let d : (m ⊕ m ⊕ Fin n) → F := fun i =>
    match i with
    | Sum.inl i₁ => 0
    | Sum.inr (Sum.inl i₂) => 0
    | Sum.inr (Sum.inr _) => -1
  cases A1Exhaust C d with
  | inl hAltPrimal =>
      obtain ⟨x, hCx⟩ := hAltPrimal
      -- By the primal certificate A x <= 0, Ax >= 0 so Ax=0
      -- Also by the primal certificate x >= 1 so x > 0
      left
      refine ⟨x, ?_, ?_⟩
      · intro j
        have hx_ge_one : (1 : F) ≤ x j := by
          have hrow := hCx (Sum.inr (Sum.inr j))
          -- row j in the third block is `-x j ≤ -1`
          have hneg : -x j ≤ (-1 : F) := by
            simpa [C, d, Matrix.mulVec, dotProduct] using hrow
          simpa using hneg
        linarith
      · have h₁ : A.mulVec x ≤ 0 := fun i => by
          simpa [C, d, Matrix.mulVec, dotProduct] using hCx (Sum.inl i)
        have h₂ : ∀ i, 0 ≤ (A.mulVec x) i := fun i => neg_nonpos.mp <| by
          simpa [C, d, Matrix.mulVec, dotProduct] using hCx (Sum.inr (Sum.inl i))
        ext i
        exact le_antisymm (h₁ i) (h₂ i)
  | inr hAltDual =>
      obtain ⟨w, hw_nonneg, hwC_zero, hwd_neg⟩ := hAltDual
      -- By the dual certificate w ≥ 0, w ᵥ* C = 0, and w ⬝ᵥ d < 0
      -- Splitting w into blocks gives y A = w₃ ≥ 0, with w₃ ≠ 0 since w ⬝ᵥ d < 0
      let y₁ : m → F := fun i => w (Sum.inl i)
      let y₂ : m → F := fun i => w (Sum.inr (Sum.inl i))
      let y : m → F := y₁ - y₂
      right
      refine ⟨y, ?_, ?_⟩
      · intro j
        have hcol0 : (w ᵥ* C) j = 0 := by simpa using congr_fun hwC_zero j
        have hsplit :
            (w ᵥ* C) j = (vecMul y A) j - w (Sum.inr (Sum.inr j)) := by
          simp [C, y, y₁, y₂, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
          ring
        have h_eq : (vecMul y A) j = w (Sum.inr (Sum.inr j)) := by linarith [hcol0, hsplit]
        rw [h_eq]
        exact hw_nonneg (Sum.inr (Sum.inr j))
      · intro hzero
        have hw3_zero : ∀ j, w (Sum.inr (Sum.inr j)) = 0 := fun j => by
          have hcol0 : (w ᵥ* C) j = 0 := by simpa using congr_fun hwC_zero j
          have hy_j : (vecMul y A) j = 0 := by simpa using congr_fun hzero.symm j
          have hsplit :
              (w ᵥ* C) j = (vecMul y A) j - w (Sum.inr (Sum.inr j)) := by
            simp [C, y, y₁, y₂, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
            ring
          linarith [hcol0, hy_j, hsplit]
        have hwd_zero : w ⬝ᵥ d = 0 := by simp [d, dotProduct, hw3_zero]
        linarith [hwd_neg, hwd_zero]

end FarkasLemma
