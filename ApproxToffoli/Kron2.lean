/-
  ApproxToffoli.Kron2
  Two-qubit tensor product infrastructure (4×4 from two 2×2 matrices).
  Used for the compose case where one qubit factors out.
-/

import ApproxToffoli.Defs
import ApproxToffoli.BlockDecomp
import ApproxToffoli.CNOTTrace
import ApproxToffoli.Helpers

open Matrix Complex

noncomputable section

/-! ## Two-qubit tensor product -/

/-- Tensor product of two 2×2 matrices, producing a 4×4 matrix.
    (B ⊗ C)_{(b₁c₁),(b₂c₂)} = B_{b₁b₂} · C_{c₁c₂}
    Index encoding: i = 2*b + c. -/
def kron2 (B C : Mat2) : Mat4 :=
  Matrix.of fun i j =>
    B ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
    C ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩

/-! ## kron2 multiplicativity -/

set_option maxHeartbeats 800000 in
-- Heartbeat bump: kron2 multiplication needs 16-case fin_cases × fin_cases
-- on Fin 4 × Fin 4 with Matrix.mul_apply + Fin.sum_univ_four expansion;
-- exceeds default budget.
/-- Tensor product is multiplicative: (A⊗B)(C⊗D) = (AC)⊗(BD) -/
lemma kron2_mul (A B C D : Mat2) :
    kron2 A B * kron2 C D = kron2 (A * C) (B * D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [kron2, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.isValue, Fin.sum_univ_two] <;>
    norm_num <;>
    ring

/-! ## kron2 zero helpers -/

/-- Tensor with zero on the left is zero. -/
lemma kron2_zero_left (X : Mat2) : kron2 (0 : Mat2) X = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.zero_apply, Matrix.of_apply]

/-- Tensor with zero on the right is zero. -/
lemma kron2_zero_right (X : Mat2) : kron2 X (0 : Mat2) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.zero_apply, Matrix.of_apply]

/-- Backward direction of `kron2 X Y = 0 ↔ X = 0 ∨ Y = 0`. The forward
    direction requires more involved Fin index manipulation; deferred. -/
lemma kron2_eq_zero_of_factor_zero (X Y : Mat2) :
    X = 0 ∨ Y = 0 → kron2 X Y = 0 := by
  rintro (rfl | rfl)
  · exact kron2_zero_left _
  · exact kron2_zero_right _

/-! ## kron2 trace -/

/-- Trace of tensor product is product of traces -/
lemma trace_kron2 (B C : Mat2) :
    Matrix.trace (kron2 B C) = (B 0 0 + B 1 1) * (C 0 0 + C 1 1) := by
  simp [Matrix.trace, Matrix.diag, kron2, Matrix.of_apply, Fin.sum_univ_four]
  ring

/-- Trace of tensor product expressed as product of `Matrix.trace`s.
    `tr(B ⊗ C) = tr(B) · tr(C)`. Convenient form for compositional reasoning. -/
lemma trace_kron2_eq_mul (B C : Mat2) :
    Matrix.trace (kron2 B C) = B.trace * C.trace := by
  rw [trace_kron2]
  show (B 0 0 + B 1 1) * (C 0 0 + C 1 1) = B.trace * C.trace
  unfold Matrix.trace Matrix.diag
  rw [Fin.sum_univ_two, Fin.sum_univ_two]

/-- Trace of CNOT_BC_4 * kron2(B,C) -/
lemma trace_cnot_kron2 (B C : Mat2) :
    Matrix.trace (CNOT_BC_4 * kron2 B C) =
    B 0 0 * (C 0 0 + C 1 1) + B 1 1 * (C 0 1 + C 1 0) := by
  rw [trace_cnot_mul]
  simp [kron2, Matrix.of_apply]
  ring

/-! ## kron2 conjTranspose -/

lemma kron2_conjTranspose (B C : Mat2) :
    (kron2 B C).conjTranspose = kron2 B.conjTranspose C.conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.of_apply, Matrix.conjTranspose_apply, star_mul']

/-- The conjTranspose-mul of two kron2 tensors is a single kron2 of factor products:
    `(P₀ ⊗ Q₀)† · (P₁ ⊗ Q₁) = (P₀† · P₁) ⊗ (Q₀† · Q₁)`. Used in the BC-AC-AB-BC
    chain to combine block_kk M = kron2 P_k Q_k (k = 0, 1) into a single tensor. -/
lemma kron2_conjTranspose_mul_kron2 (P₀ P₁ Q₀ Q₁ : Mat2) :
    (kron2 P₀ Q₀).conjTranspose * (kron2 P₁ Q₁) =
      kron2 (P₀.conjTranspose * P₁) (Q₀.conjTranspose * Q₁) := by
  rw [kron2_conjTranspose, kron2_mul]

/-! ## Unitarity -/

/-- kron2 of unitaries is unitary -/
lemma isUnitary4_kron2 {B C : Mat2} (hB : IsUnitary2 B) (hC : IsUnitary2 C) :
    IsUnitary4 (kron2 B C) := by
  unfold IsUnitary4
  rw [kron2_conjTranspose, kron2_mul]
  unfold IsUnitary2 at hB hC
  rw [hB, hC]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kron2, Matrix.of_apply, Matrix.one_apply]

/-- Product of 4×4 unitaries is unitary -/
lemma isUnitary4_mul {A B : Mat4} (hA : IsUnitary4 A) (hB : IsUnitary4 B) :
    IsUnitary4 (A * B) := by
  unfold IsUnitary4 at *
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A.conjTranspose, hA,
      Matrix.one_mul, hB]

/-- Conjugate transpose of a 4×4 unitary is unitary -/
lemma isUnitary4_conjTranspose {V : Mat4} (hV : IsUnitary4 V) :
    IsUnitary4 V.conjTranspose := by
  unfold IsUnitary4 at *
  rw [Matrix.conjTranspose_conjTranspose]
  exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hV

/-- 2×2 identity matrix is unitary -/
lemma isUnitary2_one : IsUnitary2 (1 : Mat2) := by
  unfold IsUnitary2
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

/-- 4×4 identity matrix is unitary -/
lemma isUnitary4_one : IsUnitary4 (1 : Mat4) := by
  unfold IsUnitary4
  rw [Matrix.conjTranspose_one, Matrix.one_mul]

/-- CNOT_BC_4 is unitary -/
lemma cnot_bc_4_unitary : IsUnitary4 CNOT_BC_4 := by
  unfold IsUnitary4
  have : CNOT_BC_4.conjTranspose = CNOT_BC_4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CNOT_BC_4, Matrix.of_apply, Matrix.conjTranspose_apply, pauliX]
  rw [this, cnot_bc_4_sq]

/-! ## CNOT_BC_4 as kron2 -/

/-- CNOT_BC_4 = kron2 proj0 I₂ + kron2 proj1 pauliX -/
lemma cnot_bc_4_eq_kron2 :
    CNOT_BC_4 = kron2 proj0 I₂ + kron2 proj1 pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT_BC_4, kron2, proj0, proj1, I₂, pauliX, Matrix.of_apply, Matrix.add_apply]

/-! ## kron2 additivity for traces -/

/-- Trace of sum of kron2s -/
lemma trace_kron2_add (A B C D : Mat2) :
    Matrix.trace (kron2 A B + kron2 C D) =
    Matrix.trace (kron2 A B) + Matrix.trace (kron2 C D) :=
  Matrix.trace_add _ _

/-- Trace of CNOT times sum of kron2s -/
lemma trace_cnot_kron2_add (A B C D : Mat2) :
    Matrix.trace (CNOT_BC_4 * (kron2 A B + kron2 C D)) =
    Matrix.trace (CNOT_BC_4 * kron2 A B) + Matrix.trace (CNOT_BC_4 * kron2 C D) := by
  rw [mul_add, Matrix.trace_add]

/-! ## A-block decomposition of kron3 (bridge to kron2)

The A=0 and A=1 blocks of `kron3 A B C` factor cleanly:
  block00 (kron3 A B C) = A₀₀ · kron2 B C  (entrywise)
  block11 (kron3 A B C) = A₁₁ · kron2 B C  (entrywise)
This is the structural bridge between 8×8 kron3 and 4×4 kron2 used to
extract A-block trace quantities. -/

/-- A=0 block of kron3 factors as A₀₀ scalar times kron2(B,C). -/
lemma block00_kron3_apply (A B C : Mat2) (i j : Fin 4) :
    block00 (kron3 A B C) i j = A 0 0 * kron2 B C i j := by
  fin_cases i <;> fin_cases j <;>
    (simp [block00, kron3, kron2, Matrix.of_apply, decode3]; ring)

/-- A=1 block of kron3 factors as A₁₁ scalar times kron2(B,C). -/
lemma block11_kron3_apply (A B C : Mat2) (i j : Fin 4) :
    block11 (kron3 A B C) i j = A 1 1 * kron2 B C i j := by
  fin_cases i <;> fin_cases j <;>
    (simp [block11, kron3, kron2, Matrix.of_apply, decode3]; ring)

/-- A=0 block of kron3 as a matrix equality with scalar action. -/
lemma block00_kron3 (A B C : Mat2) :
    block00 (kron3 A B C) = A 0 0 • kron2 B C := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, block00_kron3_apply]

/-- A=1 block of kron3 as a matrix equality with scalar action. -/
lemma block11_kron3 (A B C : Mat2) :
    block11 (kron3 A B C) = A 1 1 • kron2 B C := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, block11_kron3_apply]

/-- When the A-component is identity, both diagonal blocks equal kron2 B C. -/
lemma block00_kron3_I (B C : Mat2) :
    block00 (kron3 I₂ B C) = kron2 B C := by
  rw [block00_kron3]
  show (I₂ : Mat2) 0 0 • kron2 B C = kron2 B C
  unfold I₂
  rw [Matrix.one_apply_eq, one_smul]

/-- When the A-component is identity, both diagonal blocks equal kron2 B C. -/
lemma block11_kron3_I (B C : Mat2) :
    block11 (kron3 I₂ B C) = kron2 B C := by
  rw [block11_kron3]
  show (I₂ : Mat2) 1 1 • kron2 B C = kron2 B C
  unfold I₂
  rw [Matrix.one_apply_eq, one_smul]

/-! ## CX_BC · kron3 decomposition

CX_BC = kron3 I₂ proj0 I₂ + kron3 I₂ proj1 pauliX, so:
  CX_BC · kron3(uA, uB, uC) = kron3(uA, proj0·uB, uC) + kron3(uA, proj1·uB, pauliX·uC)
This factors with the A-component uA preserved across both terms; the B,C
components reflect the CNOT_BC structure. Used for analyzing the CX_BC
compose case via block decomposition. -/

/-- Algebraic identity: CX_BC absorbed into a kron3 layer is a sum of two kron3's
    with shared A-component and CNOT-twisted B,C-components. -/
lemma cx_bc_mul_kron3 (uA uB uC : Mat2) :
    CX_BC * kron3 uA uB uC =
    kron3 uA (proj0 * uB) uC + kron3 uA (proj1 * uB) (pauliX * uC) := by
  unfold CX_BC
  rw [add_mul, kron3_mul, kron3_mul]
  simp [I₂, one_mul]

/-- A=0 block of `CX_BC · kron3 uA uB uC` factors as `uA₀₀ • (CNOT · kron2 uB uC)`.
    This is the closed-form expression for the upper-left block of the CX_BC compose form. -/
lemma block00_cx_bc_mul_kron3 (uA uB uC : Mat2) :
    block00 (CX_BC * kron3 uA uB uC) = uA 0 0 • (CNOT_BC_4 * kron2 uB uC) := by
  rw [cx_bc_mul_kron3, block00_add, block00_kron3, block00_kron3, ← smul_add]
  congr 1
  rw [cnot_bc_4_eq_kron2, add_mul, kron2_mul, kron2_mul]
  simp [I₂]

/-- A=1 block of `CX_BC · kron3 uA uB uC` factors as `uA₁₁ • (CNOT · kron2 uB uC)`. -/
lemma block11_cx_bc_mul_kron3 (uA uB uC : Mat2) :
    block11 (CX_BC * kron3 uA uB uC) = uA 1 1 • (CNOT_BC_4 * kron2 uB uC) := by
  rw [cx_bc_mul_kron3, block11_add, block11_kron3, block11_kron3, ← smul_add]
  congr 1
  rw [cnot_bc_4_eq_kron2, add_mul, kron2_mul, kron2_mul]
  simp [I₂]

/-! ## Block structure of CX_BC

Since CX_BC = kron3 I₂ proj0 I₂ + kron3 I₂ proj1 pauliX has I₂ as its A-factor,
it is A-block-diagonal: block00 CX_BC = block11 CX_BC = CNOT_BC_4 and the
off-diagonal blocks vanish. -/

-- Flexible linter disabled (iter 158): the `simp [I₂, Matrix.one_apply_eq]`
-- below needs flexible simp to evaluate the I₂ entries; `simp only`-based
-- refactor would require fragile explicit args. Stable as-is.
set_option linter.flexible false in
/-- A=0 diagonal block of CX_BC equals CNOT_BC_4. -/
lemma block00_cx_bc : block00 CX_BC = CNOT_BC_4 := by
  unfold CX_BC
  rw [block00_add, block00_kron3, block00_kron3]
  simp [I₂, Matrix.one_apply_eq]
  exact cnot_bc_4_eq_kron2.symm

set_option linter.flexible false in
/-- A=1 diagonal block of CX_BC equals CNOT_BC_4. -/
lemma block11_cx_bc : block11 CX_BC = CNOT_BC_4 := by
  unfold CX_BC
  rw [block11_add, block11_kron3, block11_kron3]
  simp [I₂, Matrix.one_apply_eq]
  exact cnot_bc_4_eq_kron2.symm

/-- Right-identity tensor on the left commutes with `kron2`:
    `kron2 X 1 · kron2 1 Y = kron2 X Y`. -/
lemma kron2_X_one_mul_kron2_one_Y (X Y : Mat2) :
    kron2 X (1 : Mat2) * kron2 (1 : Mat2) Y = kron2 X Y := by
  rw [kron2_mul, mul_one, one_mul]

/-- Right-identity tensor on the right commutes with `kron2`:
    `kron2 1 Y · kron2 X 1 = kron2 X Y`. -/
lemma kron2_one_Y_mul_kron2_X_one (X Y : Mat2) :
    kron2 (1 : Mat2) Y * kron2 X (1 : Mat2) = kron2 X Y := by
  rw [kron2_mul, mul_one, one_mul]

/-- Negation pulls out of kron2's left factor. -/
lemma kron2_neg_left (A B : Mat2) : kron2 (-A) B = -kron2 A B := by
  ext i j
  simp [kron2, Matrix.of_apply, Matrix.neg_apply]

/-- Negation pulls out of kron2's right factor. -/
lemma kron2_neg_right (A B : Mat2) : kron2 A (-B) = -kron2 A B := by
  ext i j
  simp [kron2, Matrix.of_apply, Matrix.neg_apply]

/-- Linearity of kron2 in the left factor: `kron2 (A + A') C = kron2 A C + kron2 A' C`. -/
lemma kron2_add_left (A A' C : Mat2) :
    kron2 (A + A') C = kron2 A C + kron2 A' C := by
  ext i j
  simp [kron2, Matrix.of_apply, Matrix.add_apply]
  ring

/-- Linearity of kron2 in the right factor: `kron2 A (C + C') = kron2 A C + kron2 A C'`. -/
lemma kron2_add_right (A C C' : Mat2) :
    kron2 A (C + C') = kron2 A C + kron2 A C' := by
  ext i j
  simp [kron2, Matrix.of_apply, Matrix.add_apply]
  ring

/-- Scalar multiplication compatibility with kron2 in the left factor. -/
lemma kron2_smul_left (s : ℂ) (B C : Mat2) :
    kron2 (s • B) C = s • kron2 B C := by
  ext i j
  simp [kron2, Matrix.of_apply, smul_eq_mul]
  ring

/-- Scalar multiplication compatibility with kron2 in the right factor. -/
lemma kron2_smul_right (s : ℂ) (B C : Mat2) :
    kron2 B (s • C) = s • kron2 B C := by
  ext i j
  simp [kron2, Matrix.of_apply, smul_eq_mul]
  ring

/-- Expansion of `(kron2 A B + kron2 C D)† · (kron2 A B + kron2 C D)` as a
    4-term `kron2` sum of dagger products. Useful for tensor-rank analysis
    where a 2-term tensor sum's unitarity gives 4 cross-product constraints. -/
lemma kron2_sum_dagger_mul_kron2_sum (A B C D : Mat2) :
    (kron2 A B + kron2 C D).conjTranspose * (kron2 A B + kron2 C D) =
    kron2 (A.conjTranspose * A) (B.conjTranspose * B) +
    kron2 (A.conjTranspose * C) (B.conjTranspose * D) +
    kron2 (C.conjTranspose * A) (D.conjTranspose * B) +
    kron2 (C.conjTranspose * C) (D.conjTranspose * D) := by
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      kron2_conjTranspose_mul_kron2, kron2_conjTranspose_mul_kron2,
      kron2_conjTranspose_mul_kron2, kron2_conjTranspose_mul_kron2]
  abel

end
