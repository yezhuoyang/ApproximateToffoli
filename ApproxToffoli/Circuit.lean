/-
  ApproxToffoli.Circuit
  Definition of allowed circuit structure:
  at most n CX gates with only AB/BC connections,
  interleaved with arbitrary single-qubit unitary layers.
-/

import ApproxToffoli.Gates

open Matrix Complex

noncomputable section

/-! ## Unitarity predicate -/

/-- A 2×2 matrix is unitary: U† U = I -/
def IsUnitary2 (U : Mat2) : Prop := U.conjTranspose * U = 1

/-! ## Single-qubit product layer -/

/-- Unitaries on each qubit (tensor product) -/
def singleQubitLayer (uA uB uC : Mat2) : Mat8 := kron3 uA uB uC

/-! ## Allowed two-qubit gates -/

/-- The permitted two-qubit gates: CNOT on a neighbouring pair, in either direction.
    No A–C coupling (`Verification.cx_ac_not_allowed`, `cx_ca_not_allowed`).

    **SCOPE — literal CNOTs, not controlled-unitaries.** The source preprint
    (`ApproxToffoli.pdf`, §4 Eq. 6) poses the problem over the arbitrary controlled
    unitary `CU3(α,β,γ) = I⊗|0⟩⟨0| + U3(α,β,γ)⊗|1⟩⟨1|`, of which CNOT is the single
    point `α = π, β = γ = 0`. So `approxToffoli_lower_bound` quantifies over a strictly
    SMALLER circuit class than the preprint does, and does not formally imply the
    preprint's lower bound. The attaining witness (`Attainment.lean`) is a CNOT circuit
    and hence lies in both classes, so the UPPER bound does transfer.

    Adversarial optimisation over arbitrary two-qubit AB/BC unitaries — a superset of
    CU3 — also returns `8cos(π/8)` (to 2e-14), so the constant is believed unchanged for
    the wider class; that is numerics, not proof. Generalising is not plumbing: a CU3
    crossing conjugates to `I⊗diag(1,e^{iφ})` rather than `I⊗Z`, so `P` and `Q` in
    `CutBound` stop being rank-2 REFLECTIONS and Lemma T1 would have to be redone. -/
def AllowedCX (G : Mat8) : Prop :=
  G = CX_AB ∨ G = CX_BA ∨ G = CX_BC ∨ G = CX_CB

/-! ## Achievable circuits -/

/-- A circuit using at most `n` CX gates (AB or BC only)
    and unlimited single-qubit unitary gates.

    Built inductively:
    • Base: any single-qubit product layer (0 CX gates).
    • Weaken: a circuit with n CX gates is also valid with n+1.
    • Compose: append one CX gate plus a single-qubit layer,
      consuming one unit of CX budget.

    Single-qubit gates must be unitary (U†U = I) to ensure the
    overall circuit is unitary, which is needed for the HS distance
    bound to be well-defined. -/
inductive AchievableCircuit : ℕ → Mat8 → Prop where
  | single_layer (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      AchievableCircuit 0 (singleQubitLayer uA uB uC)
  | weaken {n : ℕ} {U : Mat8} :
      AchievableCircuit n U → AchievableCircuit (n + 1) U
  | compose {n : ℕ} {CX_gate rest : Mat8} (uA uB uC : Mat2)
      (hA : IsUnitary2 uA) (hB : IsUnitary2 uB) (hC : IsUnitary2 uC) :
      AllowedCX CX_gate →
      AchievableCircuit n rest →
      AchievableCircuit (n + 1)
        (rest * CX_gate * singleQubitLayer uA uB uC)

end
