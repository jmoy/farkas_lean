# Farkas Lean

A Lean 4 / Mathlib formalization of several classical **theorems of the alternative** in linear programming, all proved via **Fourier–Motzkin elimination**.

The proof is complete — no `sorry` anywhere in the codebase.

## What is proved

Four theorems of the alternative are formalized, each asserting that exactly one of two systems — a *primal* and a *dual* — has a solution.  Mutual exclusivity and exhaustiveness are proved separately for each.

### 1. Farkas' Lemma, Form 1 (`FarkasLean.Farkas1`)

For a matrix `A : Matrix m (Fin n) F` and vector `b : m → F`, exactly one of
the following holds:

> **Primal** (`Farkas1Primal`): The system `Ax ≤ b` is feasible.
> $$\exists\, x,\quad A x \le b$$

> **Dual** (`Farkas1Dual`): There exists a nonnegative dual certificate.
> $$\exists\, y \ge 0,\quad y^T A = 0 \;\wedge\; y^T b < 0$$

```lean
theorem Farkas1Exclusive (A : Matrix m (Fin n) F) (b : m → F) :
    ¬(Farkas1Primal A b ∧ Farkas1Dual A b)

theorem Farkas1Exhaust (A : Matrix m (Fin n) F) (b : m → F) :
    Farkas1Primal A b ∨ Farkas1Dual A b
```

This is the core result; everything else reduces to it.

---

### 2. Farkas' Lemma, Form 2 — Cone Membership (`FarkasLean.Farkas2`)

For a matrix `A : Matrix m (Fin n) F` and vector `b : m → F`, exactly one of
the following holds:

> **Primal** (`InCone2`): `b` lies in the conic hull of the columns of `A`.
> $$\exists\, x \ge 0,\quad A x = b$$

> **Dual** (`HasDualCert2`): There is a separating dual certificate.
> $$\exists\, y,\quad y^T A \ge 0 \;\wedge\; y^T b < 0$$

```lean
theorem farkas2_exclusive (A : Matrix m (Fin n) F) (b : m → F) :
    ¬(InCone2 A b ∧ HasDualCert2 A b)

theorem farkas2_exhaustive (A : Matrix m (Fin n) F) (b : m → F) :
    InCone2 A b ∨ HasDualCert2 A b
```

---

### 3. Motzkin Transposition Theorem (`FarkasLean.MotzkinTransposition`)

For matrices `A : Matrix p (Fin n) F`, `B : Matrix q (Fin n) F`,
`C : Matrix r (Fin n) F` with corresponding RHS vectors `a`, `b`, `c`,
exactly one of the following holds:

> **Primal** (`MotzkinPrimal`): The mixed system with strict, weak, and
> equality constraints is feasible.
> $$\exists\, x,\quad Ax < a \;\wedge\; Bx \le b \;\wedge\; Cx = c$$

> **Dual** (`MotzkinDual`): There exist multipliers `y0 ≥ 0`, `y ≥ 0`,
> `u ≥ 0`, `v` (unrestricted), with `(y0, y) ≠ 0`, satisfying
> $$y^T A + u^T B + v^T C = 0 \;\wedge\; y \cdot a + u \cdot b + v \cdot c + y_0 = 0$$

```lean
theorem motzkin_exclusive
    (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F)
    (C : Matrix r (Fin n) F) (a : p → F) (b : q → F) (c : r → F) :
    ¬(MotzkinPrimal A B C a b c ∧ MotzkinDual A B C a b c)

theorem motzkin_exhaustive
    (A : Matrix p (Fin n) F) (B : Matrix q (Fin n) F)
    (C : Matrix r (Fin n) F) (a : p → F) (b : q → F) (c : r → F) :
    MotzkinPrimal A B C a b c ∨ MotzkinDual A B C a b c
```

---

### 4. Stiemke's Lemma (`FarkasLean.Stiemke`)

For a matrix `A : Matrix m (Fin n) F`, exactly one of the following holds:

> **Primal** (`StiemkePrimal`): There is a strictly positive vector in the
> kernel of `A`.
> $$\exists\, x \gg 0,\quad A x = 0$$

> **Dual** (`StiemkeDual`): There is a nonneg nonzero covector in the image
> of `Aᵀ`.
> $$\exists\, y,\quad y^T A \ge 0 \;\wedge\; y^T A \ne 0$$

```lean
theorem stiemke_exclusive (A : Matrix m (Fin n) F) :
    ¬(StiemkePrimal A ∧ StiemkeDual A)

theorem stiemke_exhaustive (A : Matrix m (Fin n) F) :
    StiemkePrimal A ∨ StiemkeDual A
```

---

## Proof strategy: Fourier–Motzkin elimination

The entire development rests on a single algorithmic step.

### The Fourier–Motzkin step (`FarkasLean.FourierMotzkin`)

```lean
theorem Fourier_Motzkin
    [Fintype m] [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : ℕ} (A : Matrix m (Fin (n + 1)) F) (b : m → F) :
    ∃ κ : Type _, ∃ _ : Fintype κ, ∃ M : Matrix κ m F,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      ((∃ x : Fin (n + 1) → F, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b)
```

Given a system `Ax ≤ b` in `n+1` variables, the theorem produces a
finite type `κ`, a nonneg row-combination matrix `M`, and an equivalence
between the original system and the projected system `(MA)x' ≤ Mb` in `n`
variables, with the last column of `MA` equal to zero.

**The construction.**  Rows of `A` are partitioned by the sign of the
coefficient of the last variable `xₙ`:
- *Positive rows* (`Aᵢₙ > 0`): each gives an upper bound
  `xₙ ≤ (bᵢ − Aᵢ₀ₙ₋₁ · x') / Aᵢₙ`.
- *Negative rows* (`Aᵢₙ < 0`): each gives a lower bound.
- *Zero rows* (`Aᵢₙ = 0`): already independent of `xₙ`.

The projected system has one row for every positive–negative pair (encoding
the constraint that the upper bound of that pair exceeds the lower bound),
plus one row for each zero row.  The matrix `M` records the scaling
coefficients `1/Aᵢₙ` and `-1/Aᵢₙ`.  Backward feasibility uses
`finite_bounds_witness`, a small lemma that finds an element lying between
any finite family of lower and upper bounds in a lattice, provided all lowers
are ≤ all uppers.

### Farkas' Lemma Form 1 by induction (`FarkasLean.Farkas1`)

`Farkas1Exhaust` is proved by induction on the number of columns `n`:

- **Base case `n = 0`**: `Ax ≤ b` trivially holds with `x = 0` iff `b ≥ 0`;
  otherwise a unit dual certificate witnessing the violated component exists.
- **Inductive step**: Apply `Fourier_Motzkin` to project to `n` variables.
  Either the projected system is primal feasible (lift back) or by the IH it
  has a dual certificate; the latter is then lifted to the original system
  using the nonneg matrix `M`.

### Farkas' Lemma Form 2 (`FarkasLean.Farkas2`)

Reduces to Form 1 by constructing an augmented system over the index type
`m ⊕ m ⊕ Fin n` that encodes the constraints `Ax ≤ b`, `-Ax ≤ -b` (together
forcing `Ax = b`) and `-Iₙx ≤ 0` (forcing `x ≥ 0`).  Witnesses are mapped
back and forth.

### Motzkin Transposition (`FarkasLean.MotzkinTransposition`)

Reduces to Form 1 by *homogenization*: a new variable `t` replaces the RHS,
and a slack variable `s` records infeasibility.  The augmented system in
`n + 2` variables has the form `A'x' ≤ 0`, and the Farkas dual certificate
there is unpackaged to produce the Motzkin dual multipliers.

### Stiemke's Lemma (`FarkasLean.Stiemke`)

Reduces to the Motzkin theorem by setting:
- strict block: `-I` (so `(-I)x < 0` ⟺ `x > 0`),
- weak block: empty,
- equality block: `A` with RHS `0`.

---

## Dependency graph

```
FourierMotzkin
      │
      ▼
   Farkas1  ◄─────────────────────┐
      │                           │
      ├──────────────┐            │
      ▼              ▼            │
   Farkas2   MotzkinTransposition─┘
                     │
                     ▼
                  Stiemke
```

---

## Comparison with Mathlib

Mathlib 4 already contains `Mathlib.LinearAlgebra.Farkas`, which proves
Farkas' lemma using **topological separation** (the Hahn–Banach theorem or
geometric form of separation in locally convex spaces).  That approach works
naturally over `ℝ` (or any `RCLike` field) but invokes real-analysis
machinery.

This development takes a different route:

| Aspect | This project | Mathlib |
|---|---|---|
| **Proof technique** | Fourier–Motzkin elimination (algorithmic/combinatorial) | Topological separation / Hahn–Banach |
| **Field** | Any `[Field F] [LinearOrder F] [IsStrictOrderedRing F]` | Primarily `ℝ` / `RCLike` |
| **Decidability** | Constructive where possible | Classical |
| **Scope** | Farkas (two forms), Motzkin, Stiemke | Mainly one form of Farkas |
| **Method** | Strong induction on number of variables | Functional-analytic |

Working over an arbitrary ordered field (which includes `ℚ`, `ℝ`, any
ordered number field, or any finite field extension with a compatible order)
makes the results purely algebraic and gives them a wider range of
applicability, e.g. to rational LP, exact arithmetic, or computer-algebra
settings.

---

## Building

The project uses [Mathlib v4.28.0](https://github.com/leanprover-community/mathlib4).

```bash
lake exe cache get   # download prebuilt Mathlib cache
lake build           # build the project
```

---

## Module overview

| File | Contents |
|---|---|
| `FarkasLean/AlgebraHelpers.lean` | Auxiliary lemmas on dot products, scalar inverses, and bound extraction from linear inequalities |
| `FarkasLean/FourierMotzkin.lean` | `Fourier_Motzkin`: one-step variable elimination with nonneg combination matrix |
| `FarkasLean/Farkas1.lean` | `Farkas1Exclusive`, `Farkas1Exhaust`: Farkas' lemma for `Ax ≤ b` |
| `FarkasLean/Farkas2.lean` | `farkas2_exclusive`, `farkas2_exhaustive`: cone-membership form of Farkas |
| `FarkasLean/MotzkinTransposition.lean` | `motzkin_exclusive`, `motzkin_exhaustive`: Motzkin's theorem for mixed constraint systems |
| `FarkasLean/Stiemke.lean` | `stiemke_exclusive`, `stiemke_exhaustive`: Stiemke's lemma for strictly positive kernel vectors |

---

https://jyotirmoy.net
jyotirmoy@jyotirmoy.net

