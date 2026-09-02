/-
  ApproxToffoli.Gates
  Two-qubit CX gates on three qubits and the Toffoli (CCX) gate.
-/

import ApproxToffoli.TensorProduct

open Matrix Complex

noncomputable section

/-! ## Two-qubit CX gates on three qubits

Each CX gate acts on a pair of adjacent qubits (AB or BC)
and is identity on the third qubit.  There is NO direct AC connection.
-/

/-- CNOT: A controls B (C = id) -/
def CX_AB : Mat8 :=
  kron3 proj0 I₂ I₂ + kron3 proj1 pauliX I₂

/-- CNOT: B controls A (C = id) -/
def CX_BA : Mat8 :=
  kron3 I₂ proj0 I₂ + kron3 pauliX proj1 I₂

/-- CNOT: B controls C (A = id) -/
def CX_BC : Mat8 :=
  kron3 I₂ proj0 I₂ + kron3 I₂ proj1 pauliX

/-- CNOT: C controls B (A = id) -/
def CX_CB : Mat8 :=
  kron3 I₂ I₂ proj0 + kron3 I₂ pauliX proj1

/-! ## The Toffoli (CCX) gate -/

/-- The Toffoli gate: flips qubit C iff both A and B are |1⟩.
    Equivalently CCX = |0⟩⟨0|_A ⊗ I_{BC}  +  |1⟩⟨1|_A ⊗ CNOT_{BC}. -/
def CCX : Mat8 :=
  Matrix.of fun i j =>
    let (a1, b1, c1) := decode3 i
    let (a2, b2, c2) := decode3 j
    if a1 = a2 ∧ b1 = b2 then
      if a1.val = 1 ∧ b1.val = 1 then
        pauliX c1 c2          -- X on C in the |11⟩_AB subspace
      else
        if c1 = c2 then 1 else 0  -- identity on C otherwise
    else 0

end
