/-
  ApproxToffoli.BlockDecomp
  A-qubit block decomposition of 8×8 matrices.

  CCX is block-diagonal in the A-qubit basis:
    CCX = P₀_A ⊗ I_BC + P₁_A ⊗ CNOT_BC

  This gives: |Tr(M† CCX)|² = |Tr(block00 M) + Tr(CNOT_BC_4 · block11 M)|²
-/

import ApproxToffoli.Defs
import ApproxToffoli.Gates
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open Matrix Complex

noncomputable section

/-! ## 4×4 block extraction -/

/-- Upper-left 4×4 block (A=0,A=0) of an 8×8 matrix -/
def block00 (M : Mat8) : Mat4 :=
  Matrix.of fun i j => M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- Lower-right 4×4 block (A=1,A=1) of an 8×8 matrix -/
def block11 (M : Mat8) : Mat4 :=
  Matrix.of fun i j => M ⟨i.val + 4, by omega⟩ ⟨j.val + 4, by omega⟩

/-- Upper-right 4×4 block (A=0,A=1) of an 8×8 matrix.
    Captures A=0 row and A=1 column entries — needed for the matrix-product
    block formula `block00(M·X) = block00 M · block00 X + block01 M · block10 X`. -/
def block01 (M : Mat8) : Mat4 :=
  Matrix.of fun i j => M ⟨i.val, by omega⟩ ⟨j.val + 4, by omega⟩

/-- Lower-left 4×4 block (A=1,A=0) of an 8×8 matrix. -/
def block10 (M : Mat8) : Mat4 :=
  Matrix.of fun i j => M ⟨i.val + 4, by omega⟩ ⟨j.val, by omega⟩

/-! ## Block decomposition under conjugate transpose -/

lemma block00_conjTranspose (M : Mat8) :
    block00 M.conjTranspose = (block00 M).conjTranspose := by
  ext i j
  simp [block00, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma block11_conjTranspose (M : Mat8) :
    block11 M.conjTranspose = (block11 M).conjTranspose := by
  ext i j
  simp [block11, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma block01_conjTranspose (M : Mat8) :
    block01 M.conjTranspose = (block10 M).conjTranspose := by
  ext i j
  simp [block01, block10, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma block10_conjTranspose (M : Mat8) :
    block10 M.conjTranspose = (block01 M).conjTranspose := by
  ext i j
  simp [block01, block10, Matrix.conjTranspose_apply, Matrix.of_apply]

/-! ## Block decomposition of the identity Mat8 -/

lemma block00_one : block00 (1 : Mat8) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block00, Matrix.of_apply, Matrix.one_apply]

lemma block11_one : block11 (1 : Mat8) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block11, Matrix.of_apply, Matrix.one_apply]

lemma block01_one : block01 (1 : Mat8) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block01, Matrix.of_apply, Matrix.one_apply]

lemma block10_one : block10 (1 : Mat8) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block10, Matrix.of_apply, Matrix.one_apply]

/-! ## 2×2 sub-block extraction from a 4×4 matrix (along its first qubit)

For a Mat4 V interpreted as a 2-qubit gate with high-order bit indexing the
first qubit (e.g., V indexed by i = 2*a + b, where a is the first qubit),
these extract the four 2×2 sub-blocks. Used to express the A-block decomposition
of `embedAB(V)` and `embedAC(U)` in terms of V's / U's first-qubit blocks. -/

/-- Top-left 2×2 sub-block of a Mat4 V: rows {0,1}, cols {0,1}. -/
def blockA_00 (V : Mat4) : Mat2 :=
  Matrix.of fun i j => V ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- Bottom-right 2×2 sub-block of a Mat4 V: rows {2,3}, cols {2,3}. -/
def blockA_11 (V : Mat4) : Mat2 :=
  Matrix.of fun i j => V ⟨i.val + 2, by omega⟩ ⟨j.val + 2, by omega⟩

/-- Top-right 2×2 sub-block of a Mat4 V: rows {0,1}, cols {2,3}. -/
def blockA_01 (V : Mat4) : Mat2 :=
  Matrix.of fun i j => V ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩

/-- Bottom-left 2×2 sub-block of a Mat4 V: rows {2,3}, cols {0,1}. -/
def blockA_10 (V : Mat4) : Mat2 :=
  Matrix.of fun i j => V ⟨i.val + 2, by omega⟩ ⟨j.val, by omega⟩

/-! ## Linearity of block extraction -/

/-- block00 distributes over addition. -/
lemma block00_add (M N : Mat8) :
    block00 (M + N) = block00 M + block00 N := by
  ext i j
  simp [block00, Matrix.of_apply, Matrix.add_apply]

/-- block11 distributes over addition. -/
lemma block11_add (M N : Mat8) :
    block11 (M + N) = block11 M + block11 N := by
  ext i j
  simp [block11, Matrix.of_apply, Matrix.add_apply]

/-- block01 distributes over addition. -/
lemma block01_add (M N : Mat8) :
    block01 (M + N) = block01 M + block01 N := by
  ext i j
  simp [block01, Matrix.of_apply, Matrix.add_apply]

/-- block10 distributes over addition. -/
lemma block10_add (M N : Mat8) :
    block10 (M + N) = block10 M + block10 N := by
  ext i j
  simp [block10, Matrix.of_apply, Matrix.add_apply]

/-! ## General matrix-product block formula

For any 8×8 matrices M, X, the diagonal blocks of M·X decompose as:
  block00(M·X) = block00 M · block00 X + block01 M · block10 X
  block11(M·X) = block10 M · block01 X + block11 M · block11 X
This follows from splitting the 8-term sum `(M·X)[i,j] = ∑_{k:Fin 8} M[i,k]·X[k,j]`
into the lower 4 terms (matching block00 · block00) and upper 4 terms (matching
block01 · block10). -/

/-- Helper: the entries of `M*X` at A=0 row, A=0 column expressed as
    sum of products via Fin.sum_univ_eight (Fin 8 literal indexing). -/
private lemma block00_mul_entry (M X : Mat8) (i j : Fin 4) :
    block00 (M * X) i j =
      M ⟨i.val, by omega⟩ 0 * X 0 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 1 * X 1 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 2 * X 2 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 3 * X 3 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 4 * X 4 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 5 * X 5 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 6 * X 6 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 7 * X 7 ⟨j.val, by omega⟩ := by
  simp [block00, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]

/-- Helper: `(block00 M * block00 X) i j` expressed in canonical Fin 8 literal form. -/
private lemma block00_block00_entry (M X : Mat8) (i j : Fin 4) :
    (block00 M * block00 X) i j =
      M ⟨i.val, by omega⟩ 0 * X 0 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 1 * X 1 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 2 * X 2 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 3 * X 3 ⟨j.val, by omega⟩ := by
  simp [block00, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- Helper: `(block01 M * block10 X) i j` expressed in canonical Fin 8 literal form
    (indices 4..7 from the upper-block sum). -/
private lemma block01_block10_entry (M X : Mat8) (i j : Fin 4) :
    (block01 M * block10 X) i j =
      M ⟨i.val, by omega⟩ 4 * X 4 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 5 * X 5 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 6 * X 6 ⟨j.val, by omega⟩ +
      M ⟨i.val, by omega⟩ 7 * X 7 ⟨j.val, by omega⟩ := by
  simp [block01, block10, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Diagonal block product formula**: block00 of M·X involves blocks 00,01 of M and 00,10 of X.
    `block00(M·X) = block00 M · block00 X + block01 M · block10 X` -/
theorem block00_mul (M X : Mat8) :
    block00 (M * X) = block00 M * block00 X + block01 M * block10 X := by
  ext i j
  rw [block00_mul_entry, Matrix.add_apply, block00_block00_entry, block01_block10_entry]
  ring

/-- Helper: the entries of `M*X` at A=1 row, A=1 column expressed as
    sum of products via Fin.sum_univ_eight (Fin 8 literal indexing). -/
private lemma block11_mul_entry (M X : Mat8) (i j : Fin 4) :
    block11 (M * X) i j =
      M ⟨i.val + 4, by omega⟩ 0 * X 0 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 1 * X 1 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 2 * X 2 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 3 * X 3 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 4 * X 4 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 5 * X 5 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 6 * X 6 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 7 * X 7 ⟨j.val + 4, by omega⟩ := by
  simp [block11, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]

/-- Helper: `(block10 M * block01 X) i j` in canonical Fin 8 literal form (indices 0..3). -/
private lemma block10_block01_entry (M X : Mat8) (i j : Fin 4) :
    (block10 M * block01 X) i j =
      M ⟨i.val + 4, by omega⟩ 0 * X 0 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 1 * X 1 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 2 * X 2 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 3 * X 3 ⟨j.val + 4, by omega⟩ := by
  simp [block10, block01, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- Helper: `(block11 M * block11 X) i j` in canonical Fin 8 literal form (indices 4..7). -/
private lemma block11_block11_entry (M X : Mat8) (i j : Fin 4) :
    (block11 M * block11 X) i j =
      M ⟨i.val + 4, by omega⟩ 4 * X 4 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 5 * X 5 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 6 * X 6 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 7 * X 7 ⟨j.val + 4, by omega⟩ := by
  simp [block11, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Diagonal block product formula**: block11 of M·X involves blocks 10,11 of M and 01,11 of X.
    `block11(M·X) = block10 M · block01 X + block11 M · block11 X` -/
theorem block11_mul (M X : Mat8) :
    block11 (M * X) = block10 M * block01 X + block11 M * block11 X := by
  ext i j
  rw [block11_mul_entry, Matrix.add_apply, block10_block01_entry, block11_block11_entry]
  ring

/-! ## Off-diagonal block product formulas -/

/-- Helper: entries of `M*X` at A=0 row, A=1 column (block01 indexing). -/
private lemma block01_mul_entry (M X : Mat8) (i j : Fin 4) :
    block01 (M * X) i j =
      M ⟨i.val, by omega⟩ 0 * X 0 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 1 * X 1 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 2 * X 2 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 3 * X 3 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 4 * X 4 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 5 * X 5 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 6 * X 6 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 7 * X 7 ⟨j.val + 4, by omega⟩ := by
  simp [block01, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]

/-- Helper: `(block00 M * block01 X) i j` (lower 4 terms). -/
private lemma block00_block01_entry (M X : Mat8) (i j : Fin 4) :
    (block00 M * block01 X) i j =
      M ⟨i.val, by omega⟩ 0 * X 0 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 1 * X 1 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 2 * X 2 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 3 * X 3 ⟨j.val + 4, by omega⟩ := by
  simp [block00, block01, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- Helper: `(block01 M * block11 X) i j` (upper 4 terms). -/
private lemma block01_block11_entry (M X : Mat8) (i j : Fin 4) :
    (block01 M * block11 X) i j =
      M ⟨i.val, by omega⟩ 4 * X 4 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 5 * X 5 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 6 * X 6 ⟨j.val + 4, by omega⟩ +
      M ⟨i.val, by omega⟩ 7 * X 7 ⟨j.val + 4, by omega⟩ := by
  simp [block01, block11, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Off-diagonal block product formula**: block01 of M·X.
    `block01(M·X) = block00 M · block01 X + block01 M · block11 X` -/
theorem block01_mul (M X : Mat8) :
    block01 (M * X) = block00 M * block01 X + block01 M * block11 X := by
  ext i j
  rw [block01_mul_entry, Matrix.add_apply, block00_block01_entry, block01_block11_entry]
  ring

/-- Helper: entries of `M*X` at A=1 row, A=0 column (block10 indexing). -/
private lemma block10_mul_entry (M X : Mat8) (i j : Fin 4) :
    block10 (M * X) i j =
      M ⟨i.val + 4, by omega⟩ 0 * X 0 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 1 * X 1 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 2 * X 2 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 3 * X 3 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 4 * X 4 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 5 * X 5 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 6 * X 6 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 7 * X 7 ⟨j.val, by omega⟩ := by
  simp [block10, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]

/-- Helper: `(block10 M * block00 X) i j` (lower 4 terms). -/
private lemma block10_block00_entry (M X : Mat8) (i j : Fin 4) :
    (block10 M * block00 X) i j =
      M ⟨i.val + 4, by omega⟩ 0 * X 0 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 1 * X 1 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 2 * X 2 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 3 * X 3 ⟨j.val, by omega⟩ := by
  simp [block10, block00, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- Helper: `(block11 M * block10 X) i j` (upper 4 terms). -/
private lemma block11_block10_entry (M X : Mat8) (i j : Fin 4) :
    (block11 M * block10 X) i j =
      M ⟨i.val + 4, by omega⟩ 4 * X 4 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 5 * X 5 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 6 * X 6 ⟨j.val, by omega⟩ +
      M ⟨i.val + 4, by omega⟩ 7 * X 7 ⟨j.val, by omega⟩ := by
  simp [block11, block10, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]

/-- **Off-diagonal block product formula**: block10 of M·X.
    `block10(M·X) = block10 M · block00 X + block11 M · block10 X` -/
theorem block10_mul (M X : Mat8) :
    block10 (M * X) = block10 M * block00 X + block11 M * block10 X := by
  ext i j
  rw [block10_mul_entry, Matrix.add_apply, block10_block00_entry, block11_block10_entry]
  ring

/-! ## CNOT on qubits B,C (4×4) -/

/-- CNOT gate on qubits B,C as a 4×4 matrix.
    This is the A=1 block of CCX.
    Index encoding: i = 2*b + c for (b,c) ∈ Fin 2 × Fin 2. -/
def CNOT_BC_4 : Mat4 :=
  Matrix.of fun i j =>
    let b1 := i.val / 2
    let c1 := i.val % 2
    let b2 := j.val / 2
    let c2 := j.val % 2
    if b1 = b2 then
      if b1 = 1 then
        pauliX ⟨c1, by omega⟩ ⟨c2, by omega⟩
      else
        if c1 = c2 then 1 else 0
    else 0

/-! ## NormSq block decomposition -/

set_option maxHeartbeats 12800000 in
-- Iter 755: Heartbeats raised for `normSq_trace_block_decomp`'s
-- 64-leaf fin_cases over the trace expansion to combine 8×8 blocks.
/-- **NormSq block decomposition**: |Tr(M† CCX)|² = |Tr(block00 M) + Tr(CNOT_BC_4 · block11 M)|²

    This decomposes the squared trace overlap with CCX using the A-qubit block structure.
    CCX = P₀_A ⊗ I_BC + P₁_A ⊗ CNOT_BC, so the A=0 block contributes Tr(block00 M)
    and the A=1 block contributes Tr(CNOT_BC_4 · block11 M). -/
theorem normSq_trace_block_decomp (M : Mat8) :
    Complex.normSq (Matrix.trace (M.conjTranspose * CCX)) =
    Complex.normSq (Matrix.trace (block00 M) + Matrix.trace (CNOT_BC_4 * block11 M)) := by
  -- Strategy: show both arguments to normSq differ only by conjugation
  -- Tr(M†CCX) = conj(Tr(block00 M) + Tr(CNOT_BC_4 · block11 M))
  -- So normSq(Tr(M†CCX)) = normSq(conj(z)) = normSq(z)
  suffices h : Matrix.trace (M.conjTranspose * CCX) =
      starRingEnd ℂ (Matrix.trace (block00 M) + Matrix.trace (CNOT_BC_4 * block11 M)) by
    rw [h, Complex.normSq_conj]
  -- Expand trace of M†CCX: Σ_i Σ_j conj(M_{ji}) * CCX_{ji}
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Fin.sum_univ_eight]
  -- Expand CCX entries
  simp only [CCX, Matrix.of_apply, decode3, pauliX]
  -- Evaluate Fin comparisons
  norm_num
  -- LHS is now a sum of starRingEnd ℂ (M i j) terms with numeric coefficients
  -- Expand RHS: block00, block11, CNOT_BC_4, trace
  simp only [block00, block11, CNOT_BC_4, Matrix.of_apply, pauliX]
  simp only [Fin.sum_univ_four]
  norm_num
  -- Both sides are equal up to Fin 8 literal vs constructor representation.
  -- (n : Fin 8) and ⟨n, proof⟩ are propositionally equal via Fin.ext.
  -- Use convert to allow Fin.ext + omega on mismatched indices.
  -- Goal: two sums of (starRingEnd ℂ) (M i j) are equal
  -- They differ only in Fin 8 representation: literal vs constructor
  -- Rewrite Fin literals to constructor form using Fin.ext
  simp only [show (2 : Fin 8) = ⟨2, by omega⟩ from Fin.ext (by norm_num),
             show (3 : Fin 8) = ⟨3, by omega⟩ from Fin.ext (by norm_num),
             show (4 : Fin 8) = ⟨4, by omega⟩ from Fin.ext (by norm_num),
             show (5 : Fin 8) = ⟨5, by omega⟩ from Fin.ext (by norm_num),
             show (6 : Fin 8) = ⟨6, by omega⟩ from Fin.ext (by norm_num),
             show (7 : Fin 8) = ⟨7, by omega⟩ from Fin.ext (by norm_num)]
  -- Only associativity of + differs
  abel

/-- **Cauchy-Schwarz bound on block decomposition**: For any 8×8 matrix M,
    |Tr(M† CCX)|² ≤ 2·(|Tr(block00 M)|² + |Tr(CNOT_BC_4 · block11 M)|²).

    This is the standard parallelogram bound |a+b|² ≤ 2(|a|² + |b|²) applied
    to the block decomposition. Useful primitive for proofs that bound the two
    block traces separately (e.g., via cnot_trace_bound on each block). -/
theorem trace_block_decomp_cauchy_schwarz (M : Mat8) :
    Complex.normSq (Matrix.trace (M.conjTranspose * CCX)) ≤
    2 * (Complex.normSq (Matrix.trace (block00 M)) +
         Complex.normSq (Matrix.trace (CNOT_BC_4 * block11 M))) := by
  rw [normSq_trace_block_decomp]
  set a := Matrix.trace (block00 M)
  set b := Matrix.trace (CNOT_BC_4 * block11 M)
  -- Parallelogram identity: |a+b|² + |a-b|² = 2(|a|² + |b|²)
  have h_par : Complex.normSq (a + b) + Complex.normSq (a - b) =
      2 * Complex.normSq a + 2 * Complex.normSq b := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im]; ring
  nlinarith [Complex.normSq_nonneg (a - b)]

/-- Trace of a Mat2 diagonal: `tr(Diag(a, b)) = a + b`. -/
lemma trace_diagonal_Fin2 (a b : ℂ) :
    (Matrix.diagonal ![a, b] : Mat2).trace = a + b := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Trace of a Mat4 diagonal: `tr(Diag(a,b,c,d)) = a + b + c + d`. -/
lemma trace_diagonal_Fin4 (a b c d : ℂ) :
    (Matrix.diagonal ![a, b, c, d] : Mat4).trace = a + b + c + d := by
  rw [Matrix.trace_diagonal, Fin.sum_univ_four]
  have e2 : (![a, b, c, d] : Fin 4 → ℂ) 2 = c := rfl
  have e3 : (![a, b, c, d] : Fin 4 → ℂ) 3 = d := rfl
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, e2, e3]


/-- The trace of the Mat2 identity is 2. -/
lemma Mat2_trace_one : Matrix.trace (1 : Mat2) = 2 := by
  simp [Matrix.trace_one]

/-- The trace of the Mat4 identity is 4. -/
lemma Mat4_trace_one : Matrix.trace (1 : Mat4) = 4 := by
  simp [Matrix.trace_one]

/-- The trace of the Mat8 identity is 8. -/
lemma Mat8_trace_one : Matrix.trace (1 : Mat8) = 8 := by
  simp [Matrix.trace_one]

/-- block00 of zero is zero. -/
lemma block00_zero : block00 (0 : Mat8) = 0 := by
  ext i j; simp [block00, Matrix.of_apply, Matrix.zero_apply]

/-- block11 of zero is zero. -/
lemma block11_zero : block11 (0 : Mat8) = 0 := by
  ext i j; simp [block11, Matrix.of_apply, Matrix.zero_apply]

/-- The trace of a Mat8 decomposes as the sum of traces of its diagonal
    A-blocks: `trace M = trace (block00 M) + trace (block11 M)`. -/
theorem trace_eq_block00_add_block11 (M : Mat8) :
    M.trace = (block00 M).trace + (block11 M).trace := by
  simp [Matrix.trace, Matrix.diag, block00, block11, Matrix.of_apply,
        Fin.sum_univ_eight, Fin.sum_univ_four]
  ring

/-- For a Mat8 unitary M that is block-diagonal in qubit A
    (block01 M = block10 M = 0), the diagonal blocks block00 M and
    block11 M are themselves unitary Mat4. Extracted from PY24 A.24
    proof scaffold. -/
theorem block_diag_A_blocks_unitary {M : Mat8}
    (hM : M.conjTranspose * M = 1)
    (h01 : block01 M = 0) (h10 : block10 M = 0) :
    (block00 M).conjTranspose * block00 M = 1 ∧
    (block11 M).conjTranspose * block11 M = 1 := by
  refine ⟨?_, ?_⟩
  · have h := congrArg block00 hM
    rw [block00_one] at h
    rw [block00_mul, block00_conjTranspose, block01_conjTranspose,
        h10, Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero] at h
    exact h
  · have h := congrArg block11 hM
    rw [block11_one] at h
    rw [block11_mul, block10_conjTranspose, block11_conjTranspose,
        h01, Matrix.conjTranspose_zero, Matrix.zero_mul, zero_add] at h
    exact h

/-- Two Mat8 matrices that are both block-diagonal in qubit A (block01 = block10 = 0)
    are equal iff their diagonal blocks (block00, block11) are equal. Useful for
    reconstructing a Mat8 from its diagonal blocks when the off-diagonals are known
    zero, e.g., when the matrix commutes with Z_A. -/
theorem mat8_eq_of_blocks_off_diag_zero {M N : Mat8}
    (h00 : block00 M = block00 N) (h11 : block11 M = block11 N)
    (h01_M : block01 M = 0) (h10_M : block10 M = 0)
    (h01_N : block01 N = 0) (h10_N : block10 N = 0) :
    M = N := by
  ext i j
  by_cases hi : i.val < 4
  · by_cases hj : j.val < 4
    · -- Case (i < 4, j < 4): both indices in upper-left block → use h00.
      have h := congrFun (congrFun h00 ⟨i.val, hi⟩) ⟨j.val, hj⟩
      simp only [block00, Matrix.of_apply] at h
      exact h
    · -- Case (i < 4, j ≥ 4): upper-right off-diagonal → both zero via block01.
      push_neg at hj
      have hM := congrFun (congrFun h01_M ⟨i.val, hi⟩) ⟨j.val - 4, by omega⟩
      have hN := congrFun (congrFun h01_N ⟨i.val, hi⟩) ⟨j.val - 4, by omega⟩
      simp only [block01, Matrix.of_apply, Matrix.zero_apply] at hM hN
      have hj_eq : j.val - 4 + 4 = j.val := by omega
      rw [show ((⟨i.val, by omega⟩ : Fin 8)) = i from Fin.ext rfl] at hM hN
      rw [show ((⟨j.val - 4 + 4, by omega⟩ : Fin 8)) = j from Fin.ext (by omega)] at hM hN
      rw [hM, hN]
  · push_neg at hi
    by_cases hj : j.val < 4
    · -- Case (i ≥ 4, j < 4): lower-left off-diagonal → both zero via block10.
      have hM := congrFun (congrFun h10_M ⟨i.val - 4, by omega⟩) ⟨j.val, hj⟩
      have hN := congrFun (congrFun h10_N ⟨i.val - 4, by omega⟩) ⟨j.val, hj⟩
      simp only [block10, Matrix.of_apply, Matrix.zero_apply] at hM hN
      rw [show ((⟨i.val - 4 + 4, by omega⟩ : Fin 8)) = i from
            Fin.ext (Nat.sub_add_cancel hi)] at hM hN
      rw [show ((⟨j.val, by omega⟩ : Fin 8)) = j from Fin.ext rfl] at hM hN
      rw [hM, hN]
    · -- Case (i ≥ 4, j ≥ 4): both indices in lower-right block → use h11.
      push_neg at hj
      have h := congrFun (congrFun h11 ⟨i.val - 4, by omega⟩) ⟨j.val - 4, by omega⟩
      simp only [block11, Matrix.of_apply] at h
      rw [show ((⟨i.val - 4 + 4, by omega⟩ : Fin 8)) = i from
            Fin.ext (Nat.sub_add_cancel hi)] at h
      rw [show ((⟨j.val - 4 + 4, by omega⟩ : Fin 8)) = j from
            Fin.ext (Nat.sub_add_cancel hj)] at h
      exact h

/-- Construct a Mat8 from two Mat4 blocks A (top-left) and B (bottom-right),
    with zero off-diagonal blocks. The result is a block-diagonal matrix in
    qubit A. Useful for reconstructing a block-diagonal Mat8 from its diagonal
    blocks. -/
def Mat8.ofBlockDiag (A B : Mat4) : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then A ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else 0
    else
      if _hj : j.val < 4 then 0
      else B ⟨i.val - 4, by omega⟩ ⟨j.val - 4, by omega⟩

lemma block00_ofBlockDiag (A B : Mat4) :
    block00 (Mat8.ofBlockDiag A B) = A := by
  ext i j
  simp only [block00, Mat8.ofBlockDiag, Matrix.of_apply, dif_pos i.isLt, dif_pos j.isLt]

lemma block11_ofBlockDiag (A B : Mat4) :
    block11 (Mat8.ofBlockDiag A B) = B := by
  ext i j
  have hi : ¬ (i.val + 4 < 4) := by omega
  have hj : ¬ (j.val + 4 < 4) := by omega
  simp only [block11, Mat8.ofBlockDiag, Matrix.of_apply, dif_neg hi, dif_neg hj]
  congr 1

lemma block01_ofBlockDiag (A B : Mat4) :
    block01 (Mat8.ofBlockDiag A B) = 0 := by
  ext i j
  have hi : i.val < 4 := i.isLt
  have hj : ¬ (j.val + 4 < 4) := by omega
  simp only [block01, Mat8.ofBlockDiag, Matrix.of_apply, dif_pos hi, dif_neg hj,
             Matrix.zero_apply]

lemma block10_ofBlockDiag (A B : Mat4) :
    block10 (Mat8.ofBlockDiag A B) = 0 := by
  ext i j
  have hi : ¬ (i.val + 4 < 4) := by omega
  have hj : j.val < 4 := j.isLt
  simp only [block10, Mat8.ofBlockDiag, Matrix.of_apply, dif_neg hi, dif_pos hj,
             Matrix.zero_apply]

end
