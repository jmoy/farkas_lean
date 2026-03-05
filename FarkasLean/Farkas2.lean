import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.Farkas1

/-
Proving Farkas Lemma Based on the theorem of the alternative in
Farkas1.Lean
-/

open Matrix

namespace FarkasLemma2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m : Type*} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def InCone2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b

def HasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ (vecMul y A) j) ∧ y ⬝ᵥ b < 0

/-!
## Mutual Exclusivity
Matrix associativity makes this trivial compared to manual sums.
-/

/-!
## Reduction to Farkas1
-/

-- Matrix part of the reduction to `Farkas1`.
def farkas2RedA {n : ℕ} (A : Matrix m (Fin n) F) : Matrix (m ⊕ m ⊕ Fin n) (Fin n) F :=
  fun i j =>
    match i with
    | Sum.inl i₁ => A i₁ j
    | Sum.inr (Sum.inl i₂) => -A i₂ j
    | Sum.inr (Sum.inr k) => if k = j then (-1 : F) else 0

-- RHS part of the reduction to `Farkas1`.
def farkas2Redd {n : ℕ} (b : m → F) : (m ⊕ m ⊕ Fin n) → F :=
  fun i =>
    match i with
    | Sum.inl i₁ => b i₁
    | Sum.inr (Sum.inl i₂) => -b i₂
    | Sum.inr (Sum.inr _) => 0

-- Packed transformed data.
def farkas2_to_farkas1 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Matrix (m ⊕ m ⊕ Fin n) (Fin n) F × ((m ⊕ m ⊕ Fin n) → F) :=
  (farkas2RedA A, farkas2Redd b)

-- Shorthand for the reduced `Farkas1` primal system.
def Farkas2ReducedPrimal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Primal (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

-- Shorthand for the reduced `Farkas1` dual system.
def Farkas2ReducedDual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  FarkasLemma.Farkas1Dual (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)

/-!
## Mapping lemmas
-/

-- Converts a reduced `Farkas1` primal witness into an `InCone2` witness.
omit [Fintype m] in
lemma farkas1_primal_to_inCone2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hP : Farkas2ReducedPrimal A b) :
    InCone2 A b := by
  rcases hP with ⟨x, hx_le⟩
  refine ⟨x, ?_, ?_⟩
  · intro j
    have hj := hx_le (Sum.inr (Sum.inr j))
    have hj' : -x j ≤ (0 : F) := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hj
    linarith
  · ext i
    have hi₁ := hx_le (Sum.inl i)
    have hi₂ := hx_le (Sum.inr (Sum.inl i))
    have hle : A.mulVec x i ≤ b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd] using hi₁
    have hge_neg : -(A.mulVec x i) ≤ -b i := by
      simpa [Farkas2ReducedPrimal, farkas2RedA, farkas2Redd, Matrix.mulVec, dotProduct] using hi₂
    have hge : b i ≤ A.mulVec x i := by
      linarith
    exact le_antisymm hle hge

-- Converts a reduced `Farkas1` dual witness into a `HasDualCert2` witness.
lemma farkas1_dual_to_hasDualCert2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F)
    (hD : Farkas2ReducedDual A b) :
    HasDualCert2 A b := by
  rcases hD with ⟨w, hw_nonneg, hwC_zero, hwd_neg⟩
  let y₁ : m → F := fun i => w (Sum.inl i)
  let y₂ : m → F := fun i => w (Sum.inr (Sum.inl i))
  let y : m → F := y₁ - y₂
  refine ⟨y, ?_, ?_⟩
  · intro j
    have hcol0 : (w ᵥ* farkas2RedA A) j = 0 := by simpa using congr_fun hwC_zero j
    have hcol : (vecMul y A) j = w (Sum.inr (Sum.inr j)) := by
      have hsplit :
          (w ᵥ* farkas2RedA A) j =
            (vecMul y₁ A) j - (vecMul y₂ A) j - w (Sum.inr (Sum.inr j)) := by
        simp [farkas2RedA, y₁, y₂, Matrix.vecMul, dotProduct]
        ring
      have hy_split : (vecMul y A) j = (vecMul y₁ A) j - (vecMul y₂ A) j := by
        simp [y, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
      linarith [hcol0, hsplit, hy_split]
    have hj_nonneg : 0 ≤ w (Sum.inr (Sum.inr j)) := hw_nonneg (Sum.inr (Sum.inr j))
    simpa [hcol] using hj_nonneg
  · have hwd : w ⬝ᵥ farkas2Redd b = y ⬝ᵥ b := by
      calc
        w ⬝ᵥ farkas2Redd b = y₁ ⬝ᵥ b - y₂ ⬝ᵥ b := by
          simp [farkas2Redd, y₁, y₂, dotProduct]
          ring
        _ = y ⬝ᵥ b := by
          simp [y, dotProduct, Finset.sum_sub_distrib, sub_mul]
    rw [hwd] at hwd_neg
    exact hwd_neg

/-!
## Farkas' Lemma
-/

theorem farkas2_exhaustive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b := by
  have hAlt : Farkas2ReducedPrimal A b ∨ Farkas2ReducedDual A b :=
    FarkasLemma.Farkas1Exhaust (m := m ⊕ m ⊕ Fin n) (farkas2RedA A) (farkas2Redd b)
  cases hAlt with
  | inl hP =>
      exact Or.inl (farkas1_primal_to_inCone2 A b hP)
  | inr hD =>
      exact Or.inr (farkas1_dual_to_hasDualCert2 A b hD)

theorem farkas2_exclusive {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  ¬(InCone2 A b ∧ HasDualCert2 A b) := by
  rintro ⟨⟨x, hx_nonneg, rfl⟩, y, hyA_nonneg, hyb_neg⟩
  have h_assoc : y ⬝ᵥ (A.mulVec x) = (vecMul y A) ⬝ᵥ x :=
    dotProduct_mulVec y A x
  have h_nonneg : 0 ≤ (vecMul y A) ⬝ᵥ x :=
    dotProduct_nonneg_of_nonneg hyA_nonneg hx_nonneg
  linarith [h_assoc, h_nonneg, hyb_neg]

theorem farkas2 {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  InCone2 A b ∨ HasDualCert2 A b :=
  farkas2_exhaustive A b

end FarkasLemma2
