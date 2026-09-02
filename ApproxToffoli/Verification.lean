/-
  Verification lemmas to validate the correctness of the formalization.

  1. Positive tests: circuits with AB/BC connections are AchievableCircuit
  2. Negative tests: AC CX gates are NOT AllowedCX
  3. Matrix entry correctness checks
-/

import ApproxToffoli.Basic

open Matrix Complex Real

noncomputable section

set_option linter.style.longLine false

/-! ## Identity is unitary -/

lemma I2_unitary : IsUnitary2 I₂ := by
  unfold IsUnitary2 I₂
  simp [conjTranspose_one]

/-! ## 1. Positive Tests: AB/BC circuits are achievable -/

/-- The identity circuit (0 CX gates) is achievable with any budget -/
lemma identity_achievable (n : ℕ) :
    AchievableCircuit n (kron3 I₂ I₂ I₂) := by
  induction n with
  | zero => exact AchievableCircuit.single_layer I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary
  | succ n ih => exact AchievableCircuit.weaken ih

/-- A single CX_AB gate is achievable with budget 1 -/
lemma cx_ab_achievable :
    AchievableCircuit 1
      (kron3 I₂ I₂ I₂ * CX_AB * singleQubitLayer I₂ I₂ I₂) :=
  AchievableCircuit.compose I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary
    (Or.inl rfl)
    (AchievableCircuit.single_layer I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary)

/-- A single CX_BC gate is achievable with budget 1 -/
lemma cx_bc_achievable :
    AchievableCircuit 1
      (kron3 I₂ I₂ I₂ * CX_BC * singleQubitLayer I₂ I₂ I₂) :=
  AchievableCircuit.compose I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary
    (Or.inr (Or.inr (Or.inl rfl)))
    (AchievableCircuit.single_layer I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary)

/-- An AB-BC sequence (2 CX gates) is achievable with budget 2 -/
lemma ab_bc_achievable :
    AchievableCircuit 2
      ((kron3 I₂ I₂ I₂ * CX_AB * singleQubitLayer I₂ I₂ I₂)
        * CX_BC * singleQubitLayer I₂ I₂ I₂) :=
  AchievableCircuit.compose I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary
    (Or.inr (Or.inr (Or.inl rfl)))
    cx_ab_achievable

/-- Any AchievableCircuit n is also AchievableCircuit (n+k) -/
lemma achievable_weaken_add {n k : ℕ} {U : Mat8}
    (h : AchievableCircuit n U) :
    AchievableCircuit (n + k) U := by
  induction k with
  | zero => exact h
  | succ k ih => exact AchievableCircuit.weaken ih

/-- An AB-BC-AB circuit (3 CX gates) is achievable with budget 5 -/
lemma ab_bc_ab_achievable_5 :
    AchievableCircuit 5
      (((kron3 I₂ I₂ I₂ * CX_AB * singleQubitLayer I₂ I₂ I₂)
        * CX_BC * singleQubitLayer I₂ I₂ I₂)
        * CX_AB * singleQubitLayer I₂ I₂ I₂) := by
  apply achievable_weaken_add (n := 3) (k := 2)
  exact AchievableCircuit.compose I₂ I₂ I₂ I2_unitary I2_unitary I2_unitary
    (Or.inl rfl)
    ab_bc_achievable

/-! ## 2. Negative Tests: AC connections are NOT allowed -/

/-- CNOT gate with A as control, C as target (B = identity) -/
def CX_AC : Mat8 :=
  kron3 proj0 I₂ I₂ + kron3 proj1 I₂ pauliX

/-- CNOT gate with C as control, A as target (B = identity) -/
def CX_CA : Mat8 :=
  kron3 I₂ I₂ proj0 + kron3 pauliX I₂ proj1

/-- Helper to extract a matrix entry from an equality -/
private lemma mat8_entry_eq {A B : Mat8} (h : A = B)
    (i j : Fin 8) : A i j = B i j :=
  congr_fun (congr_fun h i) j

/-- CX_AC is NOT an allowed gate -/
theorem cx_ac_not_allowed : ¬ AllowedCX CX_AC := by
  unfold AllowedCX
  push_neg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> {
    have := mat8_entry_eq h ⟨5, by omega⟩ ⟨4, by omega⟩
    simp [CX_AC, CX_AB, CX_BA, CX_BC, CX_CB, kron3, decode3,
          proj0, proj1, pauliX, I₂, Matrix.of_apply,
          Matrix.add_apply, Matrix.one_apply] at this
  }

/-- CX_CA is NOT an allowed gate -/
theorem cx_ca_not_allowed : ¬ AllowedCX CX_CA := by
  unfold AllowedCX
  push_neg
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> {
    have := mat8_entry_eq h ⟨5, by omega⟩ ⟨1, by omega⟩
    simp [CX_CA, CX_AB, CX_BA, CX_BC, CX_CB, kron3, decode3,
          proj0, proj1, pauliX, I₂, Matrix.of_apply,
          Matrix.add_apply, Matrix.one_apply] at this
  }

/-! ## 3. Gate correctness: verify specific matrix entries -/

lemma ccx_flips_110_to_111 :
    CCX ⟨7, by omega⟩ ⟨6, by omega⟩ = 1 := by
  simp [CCX, decode3, pauliX, Matrix.of_apply, Fin.ext_iff]

lemma ccx_flips_111_to_110 :
    CCX ⟨6, by omega⟩ ⟨7, by omega⟩ = 1 := by
  simp [CCX, decode3, pauliX, Matrix.of_apply, Fin.ext_iff]

lemma ccx_preserves_000 :
    CCX ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
  simp [CCX, decode3, pauliX, Matrix.of_apply, Fin.ext_iff]

lemma ccx_preserves_100 :
    CCX ⟨4, by omega⟩ ⟨4, by omega⟩ = 1 := by
  simp [CCX, decode3, pauliX, Matrix.of_apply, Fin.ext_iff]

lemma ccx_110_not_preserved :
    CCX ⟨6, by omega⟩ ⟨6, by omega⟩ = 0 := by
  simp [CCX, decode3, pauliX, Matrix.of_apply, Fin.ext_iff]

lemma cx_ab_flips :
    CX_AB ⟨6, by omega⟩ ⟨4, by omega⟩ = 1 := by
  simp [CX_AB, kron3, decode3, proj0, proj1, pauliX, I₂,
        Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

lemma cx_bc_flips :
    CX_BC ⟨3, by omega⟩ ⟨2, by omega⟩ = 1 := by
  simp [CX_BC, kron3, decode3, proj0, proj1, pauliX, I₂,
        Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]

/-! ## 4. HS distance basic properties -/

lemma hs_distance_def' (U V : Mat8) :
    hsDistance U V = Real.sqrt (1 - hsFidelity U V) := rfl

lemma hs_fidelity_def' (U V : Mat8) :
    hsFidelity U V =
      Complex.normSq (Matrix.trace (U.conjTranspose * V)) / 64 :=
  rfl

end
