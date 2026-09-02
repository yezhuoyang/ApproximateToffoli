/-
  ApproxToffoli.HP.SixGate
  Construction: CCZ can be implemented with 6 neighbor gates.

  Following Huang & Palsberg (2026), Section 3 Example 3.1 and Lemma D.5:
  CCZ = embedBC(SWAP) · embedAB(CS†) · embedBC(SWAP·CS†) ·
        embedAB(CNOT) · embedBC(CS) · embedAB(CNOT)

  This proves NeighborCircuit 6 CCZ_diag.toMatrix.
-/

import ApproxToffoli.HP.FiveToFour

open Matrix Complex

noncomputable section

/-! ## Gate definitions -/

/-- Standard 2-qubit CNOT as a permutation matrix: 0→0, 1→1, 2→3, 3→2. -/
def CNOT_4_std : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- Controlled-S gate: CS = Diag(1, 1, 1, i). -/
def CS_4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => Complex.I | _, _ => 0

/-- Controlled-S†: CS† = Diag(1, 1, 1, -i). -/
def CS_dag_4 : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => -Complex.I | _, _ => 0

/-- SWAP · CS†: the composite gate used in the decomposition.
    = [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,-i]] -/
private def SWAP_CS_dag : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 2 => 1 | 2, 1 => 1 | 3, 3 => -Complex.I | _, _ => 0

/-- Local copy of the 2-qubit SWAP, defined with explicit match for simp reduction. -/
private def SWAP_4_local : Mat4 :=
  Matrix.of fun (i j : Fin 4) =>
    match i, j with
    | 0, 0 => (1 : ℂ) | 1, 2 => 1 | 2, 1 => 1 | 3, 3 => 1 | _, _ => 0

/-- SWAP_4_local equals the imported SWAP_4 -/
private theorem swap4_local_eq : SWAP_4_local = SWAP_4 := by
  ext i j
  unfold SWAP_4_local SWAP_4
  simp only [Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> rfl

-- SWAP_4 * CS_dag_4 = SWAP_CS_dag, 4×4 matrix product entry-by-entry
set_option maxHeartbeats 800000 in
private theorem swap4_mul_cs_dag : SWAP_4 * CS_dag_4 = SWAP_CS_dag := by
  rw [← swap4_local_eq]
  ext i j
  simp only [SWAP_4_local, CS_dag_4, SWAP_CS_dag,
             Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-! ## The 6-gate matrix identity

  We prove:
  embedBC(SWAP_4) · embedAB(CS†) · embedBC(SWAP_CS_dag) ·
  embedAB(CNOT) · embedBC(CS) · embedAB(CNOT) = CCZ_diag.toMatrix

  Split into halves to manage heartbeats.
-/

/-- Right half: embedAB(CNOT) · embedBC(CS) · embedAB(CNOT) -/
private def sixGateRight : Mat8 :=
  embedAB CNOT_4_std * embedBC CS_4 * embedAB CNOT_4_std

set_option maxHeartbeats 8000000 in
-- 3-fold product of 8×8 matrices, entry-by-entry
private theorem sixGateRight_eq :
    sixGateRight =
      Matrix.of fun (i j : Fin 8) =>
        match i, j with
        | 0, 0 => (1 : ℂ) | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => Complex.I
        | 4, 4 => 1 | 5, 5 => Complex.I | 6, 6 => 1 | 7, 7 => 1
        | _, _ => 0 := by
  unfold sixGateRight
  ext i j
  simp only [embedAB, embedBC, CNOT_4_std, CS_4,
             Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-- Left half uses SWAP_4_local for simp compatibility -/
private def sixGateLeft : Mat8 :=
  embedBC SWAP_4_local * embedAB CS_dag_4 * embedBC SWAP_CS_dag

set_option maxHeartbeats 8000000 in
-- Full product: left · right = CCZ
private theorem sixGate_product_eq :
    sixGateLeft * sixGateRight = CCZ_diag.toMatrix := by
  rw [sixGateRight_eq]
  unfold sixGateLeft
  ext i j
  simp only [embedAB, embedBC, SWAP_4_local, CS_dag_4, SWAP_CS_dag,
             DiagGate3.toMatrix, Matrix.diagonal_apply,
             ccz_d_0, ccz_d_1, ccz_d_2, ccz_d_3,
             ccz_d_4, ccz_d_5, ccz_d_6, ccz_d_7,
             Matrix.mul_apply, Matrix.of_apply,
             Fin.sum_univ_eight]
  fin_cases i <;> fin_cases j <;>
  · simp <;> ring

/-- The 6-gate product (using imported SWAP_4) equals CCZ -/
theorem ccz_eq_six_gates :
    embedBC SWAP_4 * embedAB CS_dag_4 * embedBC (SWAP_4 * CS_dag_4) *
    embedAB CNOT_4_std * embedBC CS_4 * embedAB CNOT_4_std = CCZ_diag.toMatrix := by
  -- Replace SWAP_4 with local version and pre-computed product
  rw [swap4_mul_cs_dag]
  conv_lhs => rw [show embedBC SWAP_4 = embedBC SWAP_4_local from by rw [swap4_local_eq]]
  -- Now LHS is sixGateLeft * sixGateRight (after re-association)
  have h : sixGateLeft * sixGateRight = CCZ_diag.toMatrix := sixGate_product_eq
  unfold sixGateLeft sixGateRight at h
  simp only [mul_assoc] at h ⊢
  exact h

/-! ## NeighborCircuit 6 for CCZ -/

/-- Intermediate: the 6-gate product using local SWAP equals CCZ -/
private theorem ccz_eq_local :
    embedBC SWAP_4_local * embedAB CS_dag_4 * embedBC SWAP_CS_dag *
    embedAB CNOT_4_std * embedBC CS_4 * embedAB CNOT_4_std = CCZ_diag.toMatrix := by
  have h := sixGate_product_eq
  unfold sixGateLeft sixGateRight at h
  simp only [mul_assoc] at h ⊢
  exact h

/-! ## Unitarity of the six construction gates (iter 1043) -/

set_option maxHeartbeats 800000 in
private theorem isUnitary4_SWAP_4_local : IsUnitary4 SWAP_4_local := by
  unfold IsUnitary4 SWAP_4_local
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
private theorem isUnitary4_CS_dag_4 : IsUnitary4 CS_dag_4 := by
  unfold IsUnitary4 CS_dag_4
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
private theorem isUnitary4_SWAP_CS_dag : IsUnitary4 SWAP_CS_dag := by
  unfold IsUnitary4 SWAP_CS_dag
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
theorem isUnitary4_CNOT_4_std : IsUnitary4 CNOT_4_std := by
  unfold IsUnitary4 CNOT_4_std
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

set_option maxHeartbeats 800000 in
theorem isUnitary4_CS_4 : IsUnitary4 CS_4 := by
  unfold IsUnitary4 CS_4
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
             Fin.sum_univ_four, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- CCZ is implementable with exactly 6 neighbor gates, all of them UNITARY.
    Same construction as `ccz_six_neighbor`, typed over
    `UnitaryNeighborCircuit` so it feeds the unitary S₄/S₅ chain. -/
theorem ccz_six_unitaryNeighbor : UnitaryNeighborCircuit 6 CCZ_diag.toMatrix := by
  rw [← ccz_eq_local]
  have h : UnitaryNeighborCircuit 6
    ((((((singleQubitLayer I₂ I₂ I₂ *
      embedBC SWAP_4_local * singleQubitLayer I₂ I₂ I₂) *
      embedAB CS_dag_4 * singleQubitLayer I₂ I₂ I₂) *
      embedBC SWAP_CS_dag * singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_4_std * singleQubitLayer I₂ I₂ I₂) *
      embedBC CS_4 * singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_4_std * singleQubitLayer I₂ I₂ I₂) :=
    .compose_AB CNOT_4_std isUnitary4_CNOT_4_std I₂ I₂ I₂
      isUnitary2_one isUnitary2_one isUnitary2_one
      (.compose_BC CS_4 isUnitary4_CS_4 I₂ I₂ I₂
        isUnitary2_one isUnitary2_one isUnitary2_one
        (.compose_AB CNOT_4_std isUnitary4_CNOT_4_std I₂ I₂ I₂
          isUnitary2_one isUnitary2_one isUnitary2_one
          (.compose_BC SWAP_CS_dag isUnitary4_SWAP_CS_dag I₂ I₂ I₂
            isUnitary2_one isUnitary2_one isUnitary2_one
            (.compose_AB CS_dag_4 isUnitary4_CS_dag_4 I₂ I₂ I₂
              isUnitary2_one isUnitary2_one isUnitary2_one
              (.compose_BC SWAP_4_local isUnitary4_SWAP_4_local I₂ I₂ I₂
                isUnitary2_one isUnitary2_one isUnitary2_one
                (.product I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one))))))
  simp only [singleQubitLayer_one, mul_one, one_mul] at h
  exact h

/-- CCZ can be implemented with exactly 6 neighbor gates.
    Construction from Huang & Palsberg (2026), Section 3. -/
theorem ccz_six_neighbor : NeighborCircuit 6 CCZ_diag.toMatrix := by
  -- Rewrite goal from CCZ to the 6-gate product
  rw [← ccz_eq_local]
  -- Construct NeighborCircuit term with identity product layers
  have h : NeighborCircuit 6
    ((((((singleQubitLayer I₂ I₂ I₂ *
      embedBC SWAP_4_local * singleQubitLayer I₂ I₂ I₂) *
      embedAB CS_dag_4 * singleQubitLayer I₂ I₂ I₂) *
      embedBC SWAP_CS_dag * singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_4_std * singleQubitLayer I₂ I₂ I₂) *
      embedBC CS_4 * singleQubitLayer I₂ I₂ I₂) *
      embedAB CNOT_4_std * singleQubitLayer I₂ I₂ I₂) :=
    .compose_AB CNOT_4_std I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
      (.compose_BC CS_4 I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
        (.compose_AB CNOT_4_std I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
          (.compose_BC SWAP_CS_dag I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
            (.compose_AB CS_dag_4 I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
              (.compose_BC SWAP_4_local I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one
                (.product I₂ I₂ I₂ isUnitary2_one isUnitary2_one isUnitary2_one))))))
  simp only [singleQubitLayer_one, mul_one, one_mul] at h
  exact h

end
