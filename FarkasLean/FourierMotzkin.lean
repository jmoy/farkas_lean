import FarkasLean.AlgebraHelpers

namespace FarkasLemma

-- A helper lemma first

-- Given finite index sets of lower and upper bounds in a lattice, if every lower bound
-- is below every upper bound, then there exists an element lying between all lowers
-- and all uppers.
--
-- If one side is empty, the witness is chosen from the nonempty side via `sup'`/`inf'`;
-- if both are empty, a witness is provided by `h_nonempty`.
private lemma finite_bounds_witness
    {ι : Type*} [Finite ι]
    {κ : Type*} [Finite κ]
    {F : Type*} [Lattice F]
    (h_nonempty : Nonempty F)
    (lhss : ι → F)
    (rhss : κ → F)
    (h : ∀ i j, lhss i ≤ rhss j) :
    ∃ x : F, ((∀ i, lhss i ≤ x) ∧ (∀ j, x ≤ rhss j)) := by
  haveI:= Fintype.ofFinite ι
  haveI:= Fintype.ofFinite κ
  by_cases hi: Nonempty ι
  · -- lhss is nonempty, use sup over it
    exact ⟨ Finset.univ.sup' Finset.univ_nonempty lhss,
            fun i => Finset.univ.le_sup' lhss (Finset.mem_univ i),
            fun j => Finset.sup'_le _ _ (fun i _ => h i j) ⟩
  · by_cases hj: Nonempty κ
    · -- rhss is nonempty, use inf over it
      exact ⟨ Finset.univ.inf' Finset.univ_nonempty rhss,
              fun i => False.elim (hi ⟨i⟩),
              fun j => Finset.univ.inf'_le _ (Finset.mem_univ j) ⟩
    · -- both are empty, any element will do
      obtain ⟨x⟩ := h_nonempty
      exact ⟨x,fun i => False.elim (hi ⟨i⟩),
               fun j => False.elim (hj ⟨j⟩)⟩

/--
`Fourier_Motzkin` performs one-step Fourier–Motzkin elimination on the last variable
of a finite linear system `A.mulVec x ≤ b`.

It constructs a finite index type `κ` and a nonnegative matrix `M` such that:
* the last column is eliminated: `(M * A) i (Fin.last n) = 0`,
* feasibility is preserved and reflected:
  the original system in `n+1` variables is feasible iff the projected system
  `(M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b` is feasible in `n` variables.

This is the standard elimination step used in proofs of Farkas-type results.
-/
theorem Fourier_Motzkin
  {m : Type u}
  {F : Type v}
  [Fintype m]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {n : ℕ}
  (A : Matrix m (Fin (n + 1)) F)
  (b : m → F) :
  ∃ κ : Type u, ∃ _ : Fintype κ, ∃ M : Matrix κ m F,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      ((∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b) := by
  /-

  ----------------------------------------------
  PART 1. Definitions and setup.
  ----------------------------------------------

  -/
  -- For notational convenience split A into last column and other columns
  let Aₙ : m → F := fun i => A i (Fin.last n)
  let A₀ : Matrix m (Fin n) F := A.submatrix id Fin.castSucc
  -- Partition rows by the sign of the eliminated variable coefficient.
  let posRow : Finset m := Finset.univ.filter (fun i => 0 < Aₙ i)
  let negRow : Finset m := Finset.univ.filter (fun i => Aₙ i < 0)
  let zeroRow : Finset m := Finset.univ.filter (fun i => Aₙ i = 0)
  -- New row index type after elimination:
  -- * `inl (iPos, iNeg)` for combined inequalities from positive/negative rows,
  -- * `inr iZero` for rows already independent of the eliminated variable.
  let κ : Type _ := ((↥posRow × ↥negRow) ⊕ ↥zeroRow)
  -- Normalized coefficient/bound functions used to isolate `xₙ`.
  let posCoeffs : posRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let posb : posRow -> F := fun i => b i * (Aₙ i)⁻¹
  let negCoeffs : negRow -> Fin n -> F := fun i j => A₀ i j * (Aₙ i)⁻¹
  let negb : negRow -> F := fun i => b i * (Aₙ i)⁻¹
  let zeroCoeffs : zeroRow -> Fin n -> F := fun i j => A₀ i j
  let zerob : zeroRow -> F := fun i => b i
  -- Eliminated system `(A', b')` in `n` variables.
  let A' : Matrix κ (Fin n) F := fun i j => match i with
    | Sum.inl (iPos, iNeg) => posCoeffs iPos j - negCoeffs iNeg j
    | Sum.inr iZero => zeroCoeffs iZero j
  let b' : κ -> F := fun i => match i with
    | Sum.inl (iPos, iNeg) => posb iPos - negb iNeg
    | Sum.inr iZero => zerob iZero
  /-

  ----------------------------------------------
  PART 2. Forward direction.
  ----------------------------------------------
  Every solution of the original system projects to
  a solution of the eliminated system.


  -/
  have hlft: ∀ x : Fin (n + 1) → F,
        A.mulVec x ≤ b → ∃ x' : Fin n → F, A'.mulVec x' ≤ b' := by
    intro x hx
    -- Just dropping the last coordinate is going to be enough
    -- But the value of the last coordinate will have work to do.
    let x' : Fin n → F := fun j => x (Fin.castSucc j)
    let xₙ := x (Fin.last n)
    use x'
    intro i
    match i with
    | Sum.inl (iPos, iNeg) =>
      -- We have to satisfy a combined inequality arising from a positive
      -- and a negative row.
      -- Strategy: use the eliminated coordinate `xₙ` itself as a witness.
      -- From the positive row we derive an upper bound on `xₙ`, and from the
      -- negative row a lower bound on `xₙ`; combining these yields the reduced
      -- inequality for the `(iPos, iNeg)` row.
      --
      -- Now the real work begins. We will use xₙ to chain two inequalities
      -- Derive the upper-bound inequality for xₙ from the positive row.
      have h₁ : xₙ ≤ posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        have hpos : 0 < Aₙ iPos := (Finset.mem_filter.mp iPos.property).2
        have hrow_pos := hx iPos
        have hpos_ne : Aₙ iPos ≠ 0 := ne_of_gt hpos
        have hlin_pos :
            (A₀ iPos ⬝ᵥ x') + Aₙ iPos * xₙ ≤ b iPos := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_pos
        have hdot_pos :
            (posCoeffs iPos) ⬝ᵥ x' = (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by
          simpa [posCoeffs] using dotProduct_mul_inv (A₀ iPos) x' (Aₙ iPos)
        have hbound_pos : xₙ + (posCoeffs iPos) ⬝ᵥ x' ≤ posb iPos := by
          calc
            xₙ + (posCoeffs iPos) ⬝ᵥ x'
                = xₙ + (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹ := by rw [hdot_pos]
            _ ≤ b iPos * (Aₙ iPos)⁻¹ :=
              upper_bound_from_linear_pos
                (A₀ iPos ⬝ᵥ x') xₙ (b iPos) (Aₙ iPos) hpos hlin_pos
            _ = posb iPos := by simp [posb]
        simpa [le_sub_iff_add_le] using hbound_pos
      -- Derive the lower-bound inequality for xₙ from the negative row.
      have h₂ : negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤ xₙ := by
        have hneg : Aₙ iNeg < 0 := (Finset.mem_filter.mp iNeg.property).2
        have hrow_neg := hx iNeg
        have hneg_ne : Aₙ iNeg ≠ 0 := ne_of_lt hneg
        have hlin_neg :
            (A₀ iNeg ⬝ᵥ x') + Aₙ iNeg * xₙ ≤ b iNeg := by
          simpa [Matrix.mulVec, dotProduct, x', xₙ, Aₙ, Fin.sum_univ_castSucc,
            add_assoc, add_left_comm, add_comm, A₀] using hrow_neg
        have hdot_neg :
            (negCoeffs iNeg) ⬝ᵥ x' = (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ := by
          simpa [negCoeffs] using dotProduct_mul_inv (A₀ iNeg) x' (Aₙ iNeg)
        have hbound_neg : negb iNeg ≤ xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by
          calc
            negb iNeg = b iNeg * (Aₙ iNeg)⁻¹ := by simp [negb]
            _ ≤ xₙ + (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹ :=
              lower_bound_from_linear_neg
                (A₀ iNeg ⬝ᵥ x') xₙ (b iNeg) (Aₙ iNeg) hneg hlin_neg
            _ = xₙ + (negCoeffs iNeg) ⬝ᵥ x' := by rw [hdot_neg]
        simpa [sub_le_iff_le_add] using hbound_neg
      -- Combine the upper and lower bounds to get the eliminated inequality.
      have h_combined : (posCoeffs iPos) ⬝ᵥ x' - negCoeffs iNeg ⬝ᵥ x'
                          ≤ posb iPos - negb iNeg := by
        linarith [h₁, h₂]
      simpa [A', b', Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using h_combined
    --
    | Sum.inr iZero =>
      -- A zero row is easy, the reduced inequality is the same as the original
      simp only [A', b', Matrix.mulVec,zeroCoeffs, zerob]
      have hzero : Aₙ iZero = 0 := (Finset.mem_filter.mp iZero.property).2
      have hzero' : A iZero (Fin.last n) = 0 := by simpa [Aₙ] using hzero
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hzero'] using hx iZero
  /-

  ----------------------------------------------
  PART 3. Backward direction.
  ----------------------------------------------

  From an eliminated solution, reconstruct a witness
  for the eliminated coordinate and then lift back to the original system.



  -/
  have hright : ∀ x' : Fin n → F,
        A'.mulVec x' ≤ b' → ∃ x : Fin (n + 1) → F, A.mulVec x ≤ b := by
    intro x' hsol
    -- Candidate lower/upper bounds for the eliminated variable.
    let valpos : posRow → F := fun i => posb i - (posCoeffs i) ⬝ᵥ x'
    let valneg : negRow → F := fun i => negb i - (negCoeffs i) ⬝ᵥ x'
    -- Pairwise compatibility of lower and upper bounds follows from `hsol`.
    have hbounds : ∀ iNeg iPos, valneg iNeg ≤ valpos iPos := by
      intro iNeg iPos
      have := hsol (Sum.inl (iPos, iNeg))
      dsimp [A', b'] at this
      have hlin :
          (posCoeffs iPos) ⬝ᵥ x' - (negCoeffs iNeg) ⬝ᵥ x' ≤ posb iPos - negb iNeg := by
        simpa [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib] using this
      have hbound :
          negb iNeg - (negCoeffs iNeg) ⬝ᵥ x' ≤
        posb iPos - (posCoeffs iPos) ⬝ᵥ x' := by
        linarith [hlin]
      simpa [valpos, valneg] using hbound
    -- Choose `xₙ` between all lower and upper bounds.
    obtain ⟨xₙ, h_xₙn, h_xₙp⟩ := finite_bounds_witness ⟨0⟩ valneg valpos hbounds
    -- Reassemble the full vector from `xₙ` and `x'`.
    let x : Fin (n + 1) → F := Fin.lastCases xₙ x'
    -- We need to show that this will work
    refine ⟨x, fun i => ?_⟩
    by_cases hlast : Aₙ i = 0
    -- The zero row is the easy case
    · let iZero : zeroRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlast⟩⟩
      have hlast' : A i (Fin.last n) = 0 := by simpa [Aₙ] using hlast
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hlast', x, A', b', zeroCoeffs, zerob]
        using hsol (Sum.inr iZero)
    · cases lt_or_gt_of_ne hlast with
      | inl hneg =>
      -- Negative row
        let iNeg : negRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hneg⟩⟩
        have hiNeg : (iNeg : m) = i := rfl
        have h := h_xₙn iNeg
        dsimp [valneg] at h
        rw [sub_le_iff_le_add] at h
        rw [add_comm] at h
        have h_scaled := mul_le_mul_of_nonpos_right h (le_of_lt hneg)
        have h_scaled' : (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg ≤ negb iNeg * Aₙ iNeg := by
          simpa [hiNeg, add_comm] using h_scaled
        have hdot_neg : A₀ i ⬝ᵥ x' = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iNeg ⬝ᵥ x' := by simp [hiNeg]
            _ = ((fun j : Fin n => A₀ iNeg j * (Aₙ iNeg)⁻¹) ⬝ᵥ x') * Aₙ iNeg := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iNeg) x' (Aₙ iNeg) (ne_of_lt hneg)
            _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg + xₙ * Aₙ iNeg := by
                rw [hdot_neg]
                simp [Aₙ, hiNeg, mul_comm]
          _ = (xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg := by ring
          _ ≤ negb iNeg * Aₙ iNeg := h_scaled'
          _ = b i := by
                calc
                  negb iNeg * Aₙ iNeg
                      = (b iNeg * (Aₙ iNeg)⁻¹) * Aₙ iNeg := by simp [negb]
                  _ = b iNeg := by
                    simpa using mul_inv_cancel_right (b iNeg) (Aₙ iNeg) (ne_of_lt hneg)
                  _ = b i := by simp [hiNeg]
      | inr hpos =>
      -- Positive row
        let iPos : posRow := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpos⟩⟩
        have hiPos : (iPos : m) = i := rfl
        have h := h_xₙp iPos
        dsimp [valpos] at h
        rw [le_sub_iff_add_le, add_comm] at h
        have h_scaled := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        have h_scaled' : ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos ≤ posb iPos * Aₙ iPos := by
          simpa [hiPos] using h_scaled
        have hdot_pos : A₀ i ⬝ᵥ x' = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by
          calc
            A₀ i ⬝ᵥ x' = A₀ iPos ⬝ᵥ x' := by simp [hiPos]
            _ = ((fun j : Fin n => A₀ iPos j * (Aₙ iPos)⁻¹) ⬝ᵥ x') * Aₙ iPos := by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iPos) x' (Aₙ iPos) hpos.ne'
            _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos := by rfl
        calc
          A.mulVec x i
              = (A₀ i ⬝ᵥ x') + Aₙ i * xₙ := by
                  simpa [x, A₀, Aₙ] using mulVec_lastCases_split A xₙ x' i
          _ = ((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos + xₙ * Aₙ iPos := by
                rw [hdot_pos]
                simp [Aₙ, hiPos, mul_comm]
          _ = ((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos := by ring
          _ ≤ posb iPos * Aₙ iPos := h_scaled'
          _ = b i := by
                calc
                  posb iPos * Aₙ iPos
                      = (b iPos * (Aₙ iPos)⁻¹) * Aₙ iPos := by simp [posb]
                  _ = b iPos := by
                    simpa using mul_inv_cancel_right (b iPos) (Aₙ iPos) hpos.ne'
                  _ = b i := by simp [hiPos]
  /-

  ----------------------------------------------
  PART 4. Assembling the products
  ----------------------------------------------

  The difficult mathematical work has been done.
  Now we have to assemble the products into the form required by
  the statement of the theorem.

  -/
  classical
  -- Build a nonnegative combination matrix `M` realizing the elimination:
  -- rows for `(iPos,iNeg)` combine one positive and one negative row,
  -- zero rows are copied.
  let M : Matrix κ m F := fun i j =>
    match i with
    | Sum.inl (iPos, iNeg) =>
      (if (j : m) = (iPos : m) then (Aₙ iPos)⁻¹ else 0) +
      (if (j : m) = (iNeg : m) then -(Aₙ iNeg)⁻¹ else 0)
    | Sum.inr iZero =>
        if (j : m) = (iZero : m) then 1 else 0
  -- Identify abstract eliminated data `(A', b')` with matrix expressions via `M`.
  have hA'_eq : A' = M * A₀ := by
    ext i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mul_apply]
      simp [A', M, posCoeffs, negCoeffs, A₀, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      simp [A', M, Matrix.mul_apply, zeroCoeffs, A₀]
  have hb'_eq : b' = M.mulVec b := by
    ext i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, posb, negb, add_mul, Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mulVec, dotProduct]
      simp [b', M, zerob]
  -- `M` is entrywise nonnegative.
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      refine add_nonneg ?_ ?_
      · by_cases h : (j : m) = (iPos : m)
        · simpa [M, h] using inv_nonneg.mpr (le_of_lt (Finset.mem_filter.mp iPos.property).2)
        · simp [h]
      · by_cases h : (j : m) = (iNeg : m)
        · simpa [M, h]
            using neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt (Finset.mem_filter.mp iNeg.property).2))
        · simp [h]
    | inr iZero =>
      by_cases h0 : (j : m) = (iZero : m)
      · simp [M, h0]
      · simp [M, h0]
  -- Multiplying by `M` eliminates the last column exactly.
  have hM_last_zero : ∀ i, (M * A) i (Fin.last n) = 0 := by
    intro i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos, iNeg⟩
      have hposnz : Aₙ iPos ≠ 0 := ne_of_gt (Finset.mem_filter.mp iPos.property).2
      have hnegnz : Aₙ iNeg ≠ 0 := ne_of_lt (Finset.mem_filter.mp iNeg.property).2
      rw [Matrix.mul_apply]
      simp [M, Aₙ, hposnz, hnegnz, add_mul, Finset.sum_add_distrib]
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [M, Aₙ, (Finset.mem_filter.mp iZero.property).2]
  -- Main equivalence rewritten in terms of `M`.
  have h_equiv_M :
      (∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * A₀).mulVec x' ≤ M.mulVec b := by
    constructor
    · rintro ⟨x, hx⟩
      rcases hlft x hx with ⟨x', hElim⟩
      refine ⟨x', ?_⟩
      simpa only [hA'_eq, hb'_eq] using hElim
    · rintro ⟨x', hxElim⟩
      have hA'ineq : A'.mulVec x' ≤ b' := by
        simpa only [hA'_eq, hb'_eq] using hxElim
      exact hright x' hA'ineq
  -- Package all existential witnesses and side conditions.
  exact ⟨κ, inferInstance, M, hM_nonneg, hM_last_zero, by simpa [A₀] using h_equiv_M⟩
end FarkasLemma
