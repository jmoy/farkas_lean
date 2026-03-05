import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import FarkasLean.Alt1

/-
Motzkin Transposition Theorem (Inhomogeneous Form)

Given three block matrices and RHS vectors:
  A : Matrix p (Fin n) F   — strict inequality block
  B : Matrix q (Fin n) F   — weak inequality block
  C : Matrix r (Fin n) F   — equality block
  a : p → F                — strict RHS
  b : q → F                — weak RHS
  c : r → F                — equality RHS

Exactly one of the following systems has a solution:

  Primal: ∃ x, Ax < a ∧ Bx ≤ b ∧ Cx = c
  Dual:   ∃ y0, y, u, v,
            y0 ≥ 0 ∧ y ≥ 0 ∧ u ≥ 0 ∧ (y0 ≠ 0 ∨ y ≠ 0) ∧
            yᵀA + uᵀB + vᵀC = 0 ∧ y⋅a + u⋅b + v⋅c + y0 = 0

We prove this by reduction to the Alt1 theorem.
-/

open Matrix

namespace FarkasLemma

variable {F : Type*} [Field F] [LinearOrder F]
variable {p q r : Type*} [Fintype p] [Fintype q] [Fintype r]

/-!
## Definitions

`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (yᵀA).

In `MotzkinPrimal`, the strict block is interpreted entrywise as
`∀ i, A.mulVec x i < a i`.

In `MotzkinDual`, `(y0 ≠ 0 ∨ y ≠ 0)` encodes `(y0, y) ≠ 0`.
-/

def MotzkinPrimal {n : ℕ} (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F)
    (C : Matrix r (Fin n) F) (a : p → F) (b : q → F) (c : r → F) : Prop :=
  ∃ x : Fin n → F, (∀ i, A.mulVec x i < a i) ∧ B.mulVec x ≤ b ∧ C.mulVec x = c

def MotzkinDual {n : ℕ} (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F)
    (C : Matrix r (Fin n) F) (a : p → F) (b : q → F) (c : r → F) : Prop :=
  ∃ (y0 : F) (y : p → F) (u : q → F) (v : r → F),
    0 ≤ y0 ∧ 0 ≤ y ∧ 0 ≤ u ∧ (y0 ≠ 0 ∨ y ≠ 0) ∧
    vecMul y A + vecMul u B + vecMul v C = 0 ∧
    y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c + y0 = 0

/-!
## Mutual Exclusivity

If x witnesses Primal and (y0, y, u, v) witnesses Dual, then
the matrix identity implies

  y⋅(Ax) + u⋅(Bx) + v⋅(Cx) = 0,

while primal feasibility gives bounds against

  y⋅a + u⋅b + v⋅c.

Combining these with `y0 ≥ 0` and

  y⋅a + u⋅b + v⋅c + y0 = 0

forces a contradiction in both nontriviality cases (`y0 ≠ 0` or `y ≠ 0`).
-/

theorem motzkin_exclusive {n : ℕ} [IsStrictOrderedRing F]
  (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F) (C : Matrix r (Fin n) F)
  (a : p → F) (b : q → F) (c : r → F) :
  ¬(MotzkinPrimal A B C a b c ∧ MotzkinDual A B C a b c) := by
  rintro ⟨⟨x, hAx_lt, hBx_le, hCx_eq⟩,
    y0, y, u, v, hy0_nn, hy_nn, hu_nn, hnontriv, hmat, hscalar⟩
  have hzero : (vecMul y A + vecMul u B + vecMul v C) ⬝ᵥ x = 0 := by
    simp [hmat]
  have hsum : y ⬝ᵥ (A *ᵥ x) + u ⬝ᵥ (B *ᵥ x) + v ⬝ᵥ (C *ᵥ x) = 0 := by
    have hy : (vecMul y A) ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by
      simpa using (Matrix.dotProduct_mulVec y A x).symm
    have hu : (vecMul u B) ⬝ᵥ x = u ⬝ᵥ (B *ᵥ x) := by
      simpa using (Matrix.dotProduct_mulVec u B x).symm
    have hv : (vecMul v C) ⬝ᵥ x = v ⬝ᵥ (C *ᵥ x) := by
      simpa using (Matrix.dotProduct_mulVec v C x).symm
    have hsplit :
        (vecMul y A + vecMul u B + vecMul v C) ⬝ᵥ x
          = (vecMul y A) ⬝ᵥ x + (vecMul u B) ⬝ᵥ x + (vecMul v C) ⬝ᵥ x := by
      simp [dotProduct, Finset.sum_add_distrib, add_mul, add_assoc]
    calc
      y ⬝ᵥ (A *ᵥ x) + u ⬝ᵥ (B *ᵥ x) + v ⬝ᵥ (C *ᵥ x)
          = (vecMul y A + vecMul u B + vecMul v C) ⬝ᵥ x := by
              linarith [hy, hu, hv, hsplit]
      _ = 0 := hzero
  have hsum' : y ⬝ᵥ (A *ᵥ x) + u ⬝ᵥ (B *ᵥ x) + v ⬝ᵥ c = 0 := by
    simpa [hCx_eq] using hsum
  have hu_le : u ⬝ᵥ (B *ᵥ x) ≤ u ⬝ᵥ b := by
    simpa using dotProduct_le_dotProduct_of_nonneg_left hBx_le hu_nn
  have hAx_le : A *ᵥ x ≤ a := fun i => le_of_lt (hAx_lt i)
  have hy_le : y ⬝ᵥ (A *ᵥ x) ≤ y ⬝ᵥ a := by
    simpa using dotProduct_le_dotProduct_of_nonneg_left hAx_le hy_nn
  have h_rhs_nonneg : 0 ≤ y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c := by
    have hbound :
        y ⬝ᵥ (A *ᵥ x) + u ⬝ᵥ (B *ᵥ x) + v ⬝ᵥ c
          ≤ y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c := by
      linarith
    linarith [hsum', hbound]
  have h_rhs_nonpos : y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c ≤ 0 := by
    linarith [hscalar, hy0_nn]
  have h_rhs_eq : y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c = -y0 := by
    linarith [hscalar]
  cases hnontriv with
  | inl hy0_ne =>
      have hy0_zero : y0 = 0 := by linarith [h_rhs_nonneg, h_rhs_eq, hy0_nn]
      exact hy0_ne hy0_zero
  | inr hy_ne =>
      have hy_pos_exists : ∃ i : p, 0 < y i := by
        by_contra hnone
        apply hy_ne
        ext i
        have hy_not_pos : ¬ 0 < y i := by
          exact (not_exists.mp hnone) i
        exact le_antisymm (le_of_not_gt hy_not_pos) (hy_nn i)
      have hdiff_pos :
          0 < ∑ i : p, y i * (a i - (A *ᵥ x) i) := by
        have hnonneg : ∀ i : p, 0 ≤ y i * (a i - (A *ᵥ x) i) := by
          intro i
          exact mul_nonneg (hy_nn i) (sub_nonneg.mpr (le_of_lt (hAx_lt i)))
        rcases hy_pos_exists with ⟨i0, hyi0_pos⟩
        have hterm_pos : 0 < y i0 * (a i0 - (A *ᵥ x) i0) := by
          exact mul_pos hyi0_pos (sub_pos.mpr (hAx_lt i0))
        exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨i0, by simp, hterm_pos⟩
      have hy_strict : y ⬝ᵥ (A *ᵥ x) < y ⬝ᵥ a := by
        have hdiff :
            y ⬝ᵥ a - y ⬝ᵥ (A *ᵥ x)
              = ∑ i : p, y i * (a i - (A *ᵥ x) i) := by
          calc
            y ⬝ᵥ a - y ⬝ᵥ (A *ᵥ x)
                = (∑ i : p, y i * a i) + ∑ i : p, -(y i * (A *ᵥ x) i) := by
                    simp [dotProduct, sub_eq_add_neg, Finset.sum_neg_distrib]
            _ = ∑ i : p, (y i * a i + -(y i * (A *ᵥ x) i)) := by
                  simp [Finset.sum_add_distrib]
            _ = ∑ i : p, y i * (a i - (A *ᵥ x) i) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  ring
        linarith [hdiff_pos, hdiff]
      have h_rhs_pos : 0 < y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c := by
        have hstrict :
            y ⬝ᵥ (A *ᵥ x) + u ⬝ᵥ (B *ᵥ x) + v ⬝ᵥ c
              < y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c := by
          linarith [hy_strict, hu_le]
        linarith [hsum', hstrict]
      linarith [h_rhs_pos, h_rhs_nonpos]

/-!
## Exhaustiveness

We homogenize the system by introducing a variable t and a slack variable s,
then apply A1Exhaust to the augmented homogeneous system.

Variables: z = (x, t, s) : Fin (n+2) → F, where
  x = fun k => z (Fin.castSucc (Fin.castSucc k))   (the original n variables)
  t = z (Fin.castSucc (Fin.last n))                 (homogenization variable)
  s = z (Fin.last (n + 1))                          (slack variable)

The augmented matrix E : Matrix (p ⊕ q ⊕ r ⊕ r ⊕ Unit ⊕ Unit) (Fin (n+2)) F is:
  p rows (A-block):   [A | -a | 1]   encodes (Ax)ᵢ - aᵢ·t + s ≤ 0
  q rows (B-block):   [B | -b | 0]   encodes (Bx)ᵢ - bᵢ·t     ≤ 0
  r rows (C+-block):  [C | -c | 0]   encodes (Cx)ᵢ - cᵢ·t     ≤ 0
  r rows (C−-block):  [-C| c  | 0]   encodes -(Cx)ᵢ + cᵢ·t   ≤ 0  (so Cx = tc)
  Unit row (t-bound): [0 | -1 | 1]   encodes -t + s ≤ 0          (so t ≥ s ≥ 1 > 0)
  Unit row (s-bound): [0 |  0 | -1]  encodes -s ≤ -1             (so s ≥ 1)

RHS d is all zeros except d(s-bound) = -1.

Primal recovery: from Ez ≤ d, get s ≥ 1, t ≥ s > 0, then set x' = x/t.
  (Ax')ᵢ + s/t ≤ aᵢ, so (Ax')ᵢ < aᵢ  (since s,t > 0)
  (Bx')ᵢ ≤ bᵢ,  Cx' = c.

Dual recovery: from w ≥ 0, wᵀE = 0, w⬝d < 0, extract y0, y, u, v.
-/

theorem motzkin_exhaustive {n : ℕ} [IsStrictOrderedRing F]
  (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F) (C : Matrix r (Fin n) F)
  (a : p → F) (b : q → F) (c : r → F) :
  MotzkinPrimal A B C a b c ∨ MotzkinDual A B C a b c := by
  -- Build the augmented matrix and RHS (homogenized with t and slack s)
  let E : Matrix (p ⊕ q ⊕ r ⊕ r ⊕ Unit ⊕ Unit) (Fin (n + 2)) F := fun i j =>
    match i with
    | Sum.inl i_p =>
        Fin.lastCases 1 (fun j' => Fin.lastCases (-(a i_p)) (A i_p) j') j
    | Sum.inr (Sum.inl i_q) =>
        Fin.lastCases 0 (fun j' => Fin.lastCases (-(b i_q)) (B i_q) j') j
    | Sum.inr (Sum.inr (Sum.inl i_r)) =>
        Fin.lastCases 0 (fun j' => Fin.lastCases (-(c i_r)) (C i_r) j') j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i_r))) =>
        Fin.lastCases 0 (fun j' => Fin.lastCases (c i_r) (fun k => -C i_r k) j') j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) =>
        Fin.lastCases 1 (fun j' => Fin.lastCases (-1 : F) (fun _ => 0) j') j
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) =>
        Fin.lastCases (-1 : F) (fun _ => 0) j
  let d : (p ⊕ q ⊕ r ⊕ r ⊕ Unit ⊕ Unit) → F := fun i =>
    match i with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) => 0
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) => -1
  cases A1Exhaust E d with
  | inl hAltPrimal =>
    obtain ⟨z, hEz⟩ := hAltPrimal
    left
    let x : Fin n → F := fun k => z (Fin.castSucc (Fin.castSucc k))
    let t : F := z (Fin.castSucc (Fin.last n))
    let s : F := z (Fin.last (n + 1))
    -- Row extraction lemmas
    have hA_row : ∀ i, (A.mulVec x) i - a i * t + s ≤ 0 := by
      intro i
      simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using
        hEz (Sum.inl i)
    have hB_row : ∀ i, (B.mulVec x) i - b i * t ≤ 0 := by
      intro i
      simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using
        hEz (Sum.inr (Sum.inl i))
    have hCp_row : ∀ i, (C.mulVec x) i - c i * t ≤ 0 := by
      intro i
      simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using
        hEz (Sum.inr (Sum.inr (Sum.inl i)))
    have hCm_row : ∀ i, -(C.mulVec x) i + c i * t ≤ 0 := by
      intro i
      simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using
        hEz (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
    have ht_row : -t + s ≤ 0 := by
      simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_comm, mul_left_comm, mul_assoc] using
        hEz (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
    have hs_row : (1 : F) ≤ s := by
      have hs_bound : -s ≤ (-1 : F) := by
        simpa [E, d, x, t, s, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
          mul_comm, mul_left_comm, mul_assoc] using
          hEz (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
      linarith
    -- Derived positivity
    have hs_pos : (0 : F) < s := by linarith
    have ht_pos : (0 : F) < t := by linarith
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    -- Cx = c * t
    have hCx_eq : ∀ i, (C.mulVec x) i = c i * t := fun i => by
      linarith [hCp_row i, hCm_row i]
    -- mulVec linearity: M.mulVec (t⁻¹ • v) i = t⁻¹ * (M.mulVec v) i
    have hA_smul : ∀ i, (A.mulVec (t⁻¹ • x)) i = t⁻¹ * (A.mulVec x) i := by
      intro i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.mul_sum,
        mul_assoc, mul_comm]
    have hB_smul : ∀ i, (B.mulVec (t⁻¹ • x)) i = t⁻¹ * (B.mulVec x) i := by
      intro i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.mul_sum,
        mul_assoc, mul_comm]
    have hC_smul : ∀ i, (C.mulVec (t⁻¹ • x)) i = t⁻¹ * (C.mulVec x) i := by
      intro i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, Finset.mul_sum,
        mul_assoc, mul_comm]
    -- Dehomogenized solution
    let x' : Fin n → F := t⁻¹ • x
    refine ⟨x', ?_, ?_, ?_⟩
    · -- ∀ i, (A.mulVec x') i < a i
      intro i
      have h1 : (A.mulVec x) i ≤ a i * t - s := by linarith [hA_row i]
      have h2 : t⁻¹ * (A.mulVec x) i ≤ t⁻¹ * (a i * t - s) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr ht_pos))
      have h3 : t⁻¹ * (a i * t - s) = a i - t⁻¹ * s := by
        field_simp
      have h4 : (0 : F) < t⁻¹ * s := mul_pos (inv_pos.mpr ht_pos) hs_pos
      linarith [hA_smul i]
    · -- B.mulVec x' ≤ b
      intro i
      have h1 : (B.mulVec x) i ≤ b i * t := by linarith [hB_row i]
      have h2 : t⁻¹ * (B.mulVec x) i ≤ t⁻¹ * (b i * t) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr ht_pos))
      have h3 : t⁻¹ * (b i * t) = b i := by field_simp
      linarith [hB_smul i]
    · -- C.mulVec x' = c
      ext i
      have h1 : (C.mulVec x') i = t⁻¹ * (C.mulVec x) i := hC_smul i
      have h2 : (C.mulVec x) i = c i * t := hCx_eq i
      rw [h1, h2]; field_simp
  | inr hAltDual =>
    obtain ⟨w, hw_nonneg, hwE_zero, hwd_neg⟩ := hAltDual
    right
    -- Split w into six blocks
    let y   : p → F := fun i_p => w (Sum.inl i_p)
    let u   : q → F := fun i_q => w (Sum.inr (Sum.inl i_q))
    let wCp : r → F := fun i_r => w (Sum.inr (Sum.inr (Sum.inl i_r)))
    let wCm : r → F := fun i_r => w (Sum.inr (Sum.inr (Sum.inr (Sum.inl i_r))))
    let y0  : F     := w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
    let ws  : F     := w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))
    let v   : r → F := wCp - wCm
    -- Sublemmas from w ⬝ᵥ d < 0
    have hws_pos : (0 : F) < ws := by
      have hwd : w ⬝ᵥ d = -ws := by
        simp [d, ws, dotProduct]
      linarith [hwd_neg, hwd]
    -- Sublemmas from w ᵥ* E = 0
    -- x-columns (castSucc ∘ castSucc k): vecMul y A + vecMul u B + vecMul v C = 0
    have hx_col : vecMul y A + vecMul u B + vecMul v C = 0 := by
      ext j
      have hcol : (w ᵥ* E) (Fin.castSucc (Fin.castSucc j)) = 0 := by
        simpa using congr_fun hwE_zero (Fin.castSucc (Fin.castSucc j))
      have hsplit :
          (w ᵥ* E) (Fin.castSucc (Fin.castSucc j)) =
            (vecMul y A) j + (vecMul u B) j + (vecMul wCp C) j - (vecMul wCm C) j := by
        simp [E, y, u, wCp, wCm, Matrix.vecMul, dotProduct]
        ring
      have hvsplit : (vecMul v C) j = (vecMul wCp C) j - (vecMul wCm C) j := by
        simp [v, Matrix.vecMul, dotProduct, Finset.sum_sub_distrib, sub_mul]
      have hgoal_j : (vecMul y A + vecMul u B + vecMul v C) j = 0 := by
        calc
          (vecMul y A + vecMul u B + vecMul v C) j
              = (vecMul y A) j + (vecMul u B) j + (vecMul v C) j := by
                  simp [add_assoc]
          _ = (vecMul y A) j + (vecMul u B) j + ((vecMul wCp C) j - (vecMul wCm C) j) := by
                rw [hvsplit]
          _ = 0 := by linarith [hcol, hsplit]
      simpa using hgoal_j
    -- t-column (castSucc (last n)): y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c + y0 = 0
    have ht_col : y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c + y0 = 0 := by
      have hcol : (w ᵥ* E) (Fin.castSucc (Fin.last n)) = 0 := by
        simpa using congr_fun hwE_zero (Fin.castSucc (Fin.last n))
      have hsplit :
          (w ᵥ* E) (Fin.castSucc (Fin.last n)) =
            -(y ⬝ᵥ a) - (u ⬝ᵥ b) - (wCp ⬝ᵥ c) + (wCm ⬝ᵥ c) - y0 := by
        simp [E, y, u, wCp, wCm, y0, Matrix.vecMul, dotProduct]
        ring
      have hvdot : v ⬝ᵥ c = wCp ⬝ᵥ c - wCm ⬝ᵥ c := by
        simp [v, dotProduct, Finset.sum_sub_distrib, sub_mul]
      linarith [hcol, hsplit, hvdot]
    -- s-column (last (n+1)): (∑ i, y i) + y0 = ws
    have hs_col : (∑ i, y i) + y0 = ws := by
      have hcol : (w ᵥ* E) (Fin.last (n + 1)) = 0 := by
        simpa using congr_fun hwE_zero (Fin.last (n + 1))
      have hsplit : (w ᵥ* E) (Fin.last (n + 1)) = (∑ i : p, y i) + y0 - ws := by
        simp [E, y, y0, ws, Matrix.vecMul, dotProduct]
        ring
      linarith [hcol, hsplit]
    -- Nontriviality: (∑ i, y i) + y0 = ws > 0, all nonneg, so y0 ≠ 0 ∨ y ≠ 0
    have hne : y0 ≠ 0 ∨ y ≠ 0 := by
      by_contra hnot
      have hy0_zero : y0 = 0 := by
        by_contra hy0_ne
        exact hnot (Or.inl hy0_ne)
      have hy_zero : y = 0 := by
        by_contra hy_ne
        exact hnot (Or.inr hy_ne)
      have hsum_zero : (∑ i : p, y i) = 0 := by
        simp [hy_zero]
      have hws_zero : ws = 0 := by
        linarith [hs_col, hy0_zero, hsum_zero]
      exact (ne_of_gt hws_pos) hws_zero
    refine ⟨y0, y, u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 ≤ y0
      exact hw_nonneg (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
    · -- 0 ≤ y
      intro i; exact hw_nonneg (Sum.inl i)
    · -- 0 ≤ u
      intro i; exact hw_nonneg (Sum.inr (Sum.inl i))
    · -- y0 ≠ 0 ∨ y ≠ 0
      exact hne
    · -- vecMul y A + vecMul u B + vecMul v C = 0
      exact hx_col
    · -- y ⬝ᵥ a + u ⬝ᵥ b + v ⬝ᵥ c + y0 = 0
      exact ht_col

end FarkasLemma
