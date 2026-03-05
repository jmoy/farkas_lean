# Farkas Lean

A Lean 4 / Mathlib formalization of several classical **theorems of the alternative** about linear inequalities,proved via **Fourier–Motzkin elimination**.


## What is proved

Four theorems of the alternative are formalized, each asserting that exactly one of two systems — a *primal* and a *dual* — has a solution.  Mutual exclusivity and exhaustiveness are proved separately for each.

### 1. Farkas' Lemma, Form 1 (`FarkasLean.Farkas1`)

For a matrix `A : Matrix m (Fin n) F` and vector `b : m → F`, exactly one of
the following holds:

> **Primal** (`Farkas1Primal`): The system `Ax ≤ b` is feasible.
> $$\exists\, x,\quad A x \le b$$

> **Dual** (`Farkas1Dual`): There exists a nonnegative dual certificate.
> $$\exists\, y \ge 0,\quad y^T A = 0 \;\wedge\; y^T b < 0$$

This is the core result; everything else reduces to it.

---

### 2. Farkas' Lemma, Form 2 — Cone Membership (`FarkasLean.Farkas2`)

For a matrix `A : Matrix m (Fin n) F` and vector `b : m → F`, exactly one of
the following holds:

> **Primal** (`InCone2`): `b` lies in the conic hull of the columns of `A`.
> $$\exists\, x \ge 0,\quad A x = b$$

> **Dual** (`HasDualCert2`): There is a separating dual certificate.
> $$\exists\, y,\quad y^T A \ge 0 \;\wedge\; y^T b < 0$$

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

---

### 4. Stiemke's Lemma (`FarkasLean.Stiemke`)

For a matrix `A : Matrix m (Fin n) F`, exactly one of the following holds:

> **Primal** (`StiemkePrimal`): There is a strictly positive vector in the
> kernel of `A`.
> $$\exists\, x \gg 0,\quad A x = 0$$

> **Dual** (`StiemkeDual`): There is a nonneg nonzero covector in the image
> of `Aᵀ`.
> $$\exists\, y,\quad y^T A \ge 0 \;\wedge\; y^T A \ne 0$$

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


### Farkas' Lemma Form 1 by induction (`FarkasLean.Farkas1`)

`Farkas1Exhaust` is proved by induction on the number of columns `n` using Fourier-Motzkin elimination for the reduction.

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
machinery. This development takes a different route
Working over an arbitrary ordered field (thus applying for eg. to `ℚ`) we provide a purely algebraic, inductive, proof.

---

Author: Jyotirmoy Bhattacharya
https://jyotirmoy.net
jyotirmoy@jyotirmoy.net

I wrote this to teach myself Lean. 

While the high-level data and proof structures were chosen by me, the smaller lemmas were all proved by Claude 4.6 Sonnet/Opus and GPT-5.3-codex and for these lemmas I've not tried to optimize the proofs. So this may not be the best example to learn lean from.

