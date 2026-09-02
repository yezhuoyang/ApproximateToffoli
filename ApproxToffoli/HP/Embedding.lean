/-
  ApproxToffoli.HP.Embedding
  Embedding 2-qubit gates into 3-qubit space and the SWAP gate.

  Key definitions:
  - embedAB: embed a 4×4 gate on qubits A,B (identity on C)
  - embedBC: embed a 4×4 gate on qubits B,C (identity on A)
  - SWAP_BC: swap qubits B and C
  - NeighborCircuit: inductive type for circuits with k neighbor gates

  Reference: Huang & Palsberg (2026), Section 2.
-/

import ApproxToffoli.TensorProduct
import ApproxToffoli.HP.Defs
import ApproxToffoli.Kron2

open Matrix Complex

noncomputable section

/-! ## Embedding 2-qubit gates into 3-qubit space

Using the binary encoding i = 4a + 2b + c:
- embedAB(V): acts as V on the AB subspace (indices ⌊i/2⌋), identity on C (index i mod 2)
- embedBC(V): acts as V on the BC subspace (indices i mod 4), identity on A (index ⌊i/4⌋)
-/

/-- Embed a 4×4 gate V on qubits A,B with identity on qubit C.
    (V ⊗ I₂)_{i,j} = V_{⌊i/2⌋, ⌊j/2⌋} · δ_{i mod 2, j mod 2} -/
def embedAB (V : Mat4) : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if i.val % 2 = j.val % 2 then
      V ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩
    else 0

/-- Embed a 4×4 gate V on qubits B,C with identity on qubit A.
    (I₂ ⊗ V)_{i,j} = δ_{⌊i/4⌋, ⌊j/4⌋} · V_{i mod 4, j mod 4} -/
def embedBC (V : Mat4) : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if i.val / 4 = j.val / 4 then
      V ⟨i.val % 4, by omega⟩ ⟨j.val % 4, by omega⟩
    else 0

/-! ## Embedding preserves identity -/

set_option maxHeartbeats 1600000 in
-- Brute-force over 64 Fin 8 × Fin 8 cases (default heartbeat budget exceeded).
theorem embedAB_one : embedAB 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedAB, Matrix.of_apply, Matrix.one_apply]

set_option maxHeartbeats 1600000 in
-- Brute-force over 64 Fin 8 × Fin 8 cases (default heartbeat budget exceeded).
theorem embedBC_one : embedBC 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedBC, Matrix.of_apply, Matrix.one_apply]

/-! ## SWAP gate on qubits B and C

SWAP_BC |a,b,c⟩ = |a,c,b⟩
Permutation on Fin 8: fixes 0,3,4,7 and swaps 1↔2, 5↔6.
-/

/-- The SWAP permutation on BC qubits: maps index (a,b,c) to (a,c,b) -/
def swap_bc_perm : Fin 8 → Fin 8
  | 0 => 0  -- (0,0,0) → (0,0,0)
  | 1 => 2  -- (0,0,1) → (0,1,0)
  | 2 => 1  -- (0,1,0) → (0,0,1)
  | 3 => 3  -- (0,1,1) → (0,1,1)
  | 4 => 4  -- (1,0,0) → (1,0,0)
  | 5 => 6  -- (1,0,1) → (1,1,0)
  | 6 => 5  -- (1,1,0) → (1,0,1)
  | 7 => 7  -- (1,1,1) → (1,1,1)

/-- SWAP gate on qubits B,C: a permutation matrix -/
def SWAP_BC : Mat8 :=
  Matrix.of fun (i j : Fin 8) =>
    if swap_bc_perm i = j then 1 else 0

/-- SWAP_BC is an involution: SWAP_BC * SWAP_BC = I -/
theorem SWAP_BC_sq : SWAP_BC * SWAP_BC = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  · simp [SWAP_BC, swap_bc_perm, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_eight]

/-- SWAP_BC is self-adjoint: SWAP_BC† = SWAP_BC -/
theorem SWAP_BC_conjTranspose : SWAP_BC.conjTranspose = SWAP_BC := by
  ext i j; fin_cases i <;> fin_cases j <;>
  · simp [SWAP_BC, swap_bc_perm, Matrix.conjTranspose_apply, Matrix.of_apply, star_one, star_zero]

/-! ## Neighbor circuit: implementation with k general 2-qubit neighbor gates

A 3-qubit unitary U is implementable with k neighbor gates if it can be
written as a product of k embedded 2-qubit gates (on AB or BC pairs),
possibly with single-qubit gates absorbed.

We define this inductively, matching the paper's circuit model.
-/

/-- A 3-qubit unitary implementable with at most k general 2-qubit neighbor gates.
    Single-qubit gates (product layers) are free and don't count toward k.

    This matches the circuit model in Huang & Palsberg:
    - Base: any product of single-qubit gates (0 neighbor gates)
    - Compose: append one 2-qubit gate on AB or BC -/
inductive NeighborCircuit : ℕ → Mat8 → Prop where
  | product (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      NeighborCircuit 0 (singleQubitLayer uA uB uC)
  | weaken {n : ℕ} {U : Mat8} :
      NeighborCircuit n U → NeighborCircuit (n + 1) U
  | compose_AB {n : ℕ} {rest : Mat8} (V : Mat4) (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      NeighborCircuit n rest →
      NeighborCircuit (n + 1) (rest * embedAB V * singleQubitLayer uA uB uC)
  | compose_BC {n : ℕ} {rest : Mat8} (V : Mat4) (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      NeighborCircuit n rest →
      NeighborCircuit (n + 1) (rest * embedBC V * singleQubitLayer uA uB uC)

/-- Like `NeighborCircuit` but with each `compose_*` constructor's inner gate
    `V : Mat4` carrying an `IsUnitary4 V` proof. This is the genuinely-physical
    class of 3-qubit circuits with arbitrary 2-qubit unitary neighbor gates.
    Forgetful map: see `neighborCircuit_of_unitaryNeighbor` in FiveToFour.lean. -/
inductive UnitaryNeighborCircuit : ℕ → Mat8 → Prop where
  | product (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryNeighborCircuit 0 (singleQubitLayer uA uB uC)
  | weaken {n : ℕ} {U : Mat8} :
      UnitaryNeighborCircuit n U → UnitaryNeighborCircuit (n + 1) U
  | compose_AB {n : ℕ} {rest : Mat8} (V : Mat4) (hV : IsUnitary4 V)
      (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryNeighborCircuit n rest →
      UnitaryNeighborCircuit (n + 1)
        (rest * embedAB V * singleQubitLayer uA uB uC)
  | compose_BC {n : ℕ} {rest : Mat8} (V : Mat4) (hV : IsUnitary4 V)
      (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      UnitaryNeighborCircuit n rest →
      UnitaryNeighborCircuit (n + 1)
        (rest * embedBC V * singleQubitLayer uA uB uC)

end
