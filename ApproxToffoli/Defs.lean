/-
  ApproxToffoli.Defs
  Core type aliases and single-qubit gate definitions.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix Complex

noncomputable section

/-! ## Matrix type aliases -/

/-- 2×2 complex matrix (single qubit) -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- 4×4 complex matrix (two qubits) -/
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- 8×8 complex matrix (three qubits) -/
abbrev Mat8 := Matrix (Fin 8) (Fin 8) ℂ

/-! ## Single-qubit gates -/

/-- 2×2 identity -/
def I₂ : Mat2 := 1

/-- Pauli X gate -/
def pauliX : Mat2 := Matrix.of !![0, 1; 1, 0]

/-- Pauli Z gate -/
def pauliZ : Mat2 := Matrix.of !![1, 0; 0, -1]

/-! ## Single-qubit gate properties -/

/-- Pauli Z squares to identity: Z² = I -/
theorem pauliZ_sq : pauliZ * pauliZ = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [pauliZ, I₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli X squares to identity: X² = I -/
theorem pauliX_sq : pauliX * pauliX = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [pauliX, I₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Projector |0⟩⟨0| -/
def proj0 : Mat2 := Matrix.of !![1, 0; 0, 0]

/-- Projector |1⟩⟨1| -/
def proj1 : Mat2 := Matrix.of !![0, 0; 0, 1]

/-! ## Projector algebra -/

theorem proj0_sq : proj0 * proj0 = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj1_sq : proj1 * proj1 = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj0_mul_proj1 : proj0 * proj1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj1_mul_proj0 : proj1 * proj0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]

theorem proj0_add_proj1 : proj0 + proj1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, proj1, Matrix.add_apply]

theorem proj0_conjTranspose : proj0.conjTranspose = proj0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj0, Matrix.conjTranspose_apply]

theorem proj1_conjTranspose : proj1.conjTranspose = proj1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [proj1, Matrix.conjTranspose_apply]

end
