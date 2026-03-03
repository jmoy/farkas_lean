import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open Matrix

namespace FarkasLemma

lemma mulVec_lastCases_split
    {m : Type*} {F : Type*} [Semiring F] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F)
    (xₙ : F)
    (x' : Fin n → F)
    (i : m) :
    A.mulVec (Fin.lastCases xₙ x') i
      = (A.submatrix id Fin.castSucc i ⬝ᵥ x') + A i (Fin.last n) * xₙ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

lemma dotProduct_mul_right
  {F : Type*} [CommSemiring F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c) ⬝ᵥ x) = (a ⬝ᵥ x) * c := by
  calc
    ((fun j : Fin n => a j * c) ⬝ᵥ x)
        = ∑ j : Fin n, (a j * c) * x j := by simp [dotProduct]
    _ = ∑ j : Fin n, (a j * x j) * c := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Fin n, a j * x j) * c := by
          rw [← Finset.sum_mul]
    _ = (a ⬝ᵥ x) * c := by simp [dotProduct]

lemma dotProduct_scaled_inv_mul
    {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F)
    (hc : c ≠ 0) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c = a ⬝ᵥ x := by
  calc
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) * c
        = ((a ⬝ᵥ x) * c⁻¹) * c := by
            rw [dotProduct_mul_right]
    _ = a ⬝ᵥ x := by
          field_simp [hc]

lemma dotProduct_mul_inv
  {F : Type*} [Field F] {n : ℕ}
    (a x : Fin n → F)
    (c : F) :
    ((fun j : Fin n => a j * c⁻¹) ⬝ᵥ x) = (a ⬝ᵥ x) * c⁻¹ := by
  simpa using dotProduct_mul_right a x c⁻¹

lemma split_add_mul_inv
    {F : Type*} [Field F]
    (u x c : F)
    (hc : c ≠ 0) :
    ((u + c * x) * c⁻¹) = u * c⁻¹ + x := by
  calc
    ((u + c * x) * c⁻¹)
        = u * c⁻¹ + (c * x) * c⁻¹ := by ring
    _ = u * c⁻¹ + x := by
          have hx : (c * x) * c⁻¹ = x := by
            calc
              (c * x) * c⁻¹ = x * (c * c⁻¹) := by ring
              _ = x := by simp [mul_inv_cancel₀ hc]
          simp [hx]

lemma mul_inv_cancel_right
    {F : Type*} [Field F]
    (a c : F)
    (hc : c ≠ 0) :
    (a * c⁻¹) * c = a := by
  calc
    (a * c⁻¹) * c = a * (c⁻¹ * c) := by ring
    _ = a := by simp [inv_mul_cancel₀ hc]

lemma upper_bound_from_linear_pos
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : 0 < c)
    (hlin : u + c * x ≤ b) :
    x + u * c⁻¹ ≤ b * c⁻¹ := by
  have hscaled : (u + c * x) * c⁻¹ ≤ b * c⁻¹ :=
    mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr (le_of_lt hc))
  calc
    x + u * c⁻¹ = u * c⁻¹ + x := by ring
    _ = (u + c * x) * c⁻¹ := by
          symm
          exact split_add_mul_inv u x c (ne_of_gt hc)
    _ ≤ b * c⁻¹ := hscaled

lemma lower_bound_from_linear_neg
  {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c : F)
    (hc : c < 0)
    (hlin : u + c * x ≤ b) :
    b * c⁻¹ ≤ x + u * c⁻¹ := by
  have hscaled : b * c⁻¹ ≤ (u + c * x) * c⁻¹ :=
    mul_le_mul_of_nonpos_right hlin (inv_nonpos.mpr (le_of_lt hc))
  calc
    b * c⁻¹ ≤ (u + c * x) * c⁻¹ := hscaled
    _ = u * c⁻¹ + x := split_add_mul_inv u x c (ne_of_lt hc)
    _ = x + u * c⁻¹ := by ring

end FarkasLemma
