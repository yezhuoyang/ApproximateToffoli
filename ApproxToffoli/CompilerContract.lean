import ApproxToffoli.CurveMain

/-!
# A certified local approximation selector

This module packages the four existing three-qubit witnesses as a finite rewrite library.
`select` chooses the cheapest library entry whose ideal process distance fits the supplied
budget. `select_correct` proves its layout legality, its error bound, and its minimum cost
among these four entries.

The selector is a mathematical specification over real numbers, not extracted executable
code. The contract does not verify a Python implementation, arbitrary-width composition,
routing, or a physical noise model. In particular, minimum cost among the library entries
does not resolve the open optimal-distance cases at CNOT budgets six and seven.
-/

noncomputable section

namespace CompilerContract

/-- The four certified implementations of one Toffoli gate on the line A-B-C. -/
inductive Candidate where
  | identity
  | two
  | four
  | exact
  deriving DecidableEq

/-- Number of neighboring CNOT gates charged by the library. -/
def cost : Candidate → ℕ
  | .identity => 0
  | .two => 2
  | .four => 4
  | .exact => 8

/-- The ideal matrix denoted by a library entry. -/
def matrix : Candidate → Mat8
  | .identity => Curve.witness0
  | .two => Curve.witness2
  | .four => Curve.witness4
  | .exact => Curve.witness8

/-- Exact local process distance to the Toffoli gate. -/
def error : Candidate → ℝ
  | .identity => Real.sqrt 7 / 4
  | .two => Real.sqrt 6 / 4
  | .four => Real.sin (Real.pi / 8)
  | .exact => 0

/-- Every library entry is legal at its stated CNOT cost on the three-qubit line. -/
theorem candidate_legal (c : Candidate) : AchievableCircuit (cost c) (matrix c) := by
  cases c with
  | identity => exact Curve.witness0_achievable
  | two => exact Curve.witness2_achievable
  | four => exact Curve.witness4_achievable
  | exact => exact Curve.witness8_achievable

/-- The library's error metadata agrees exactly with the matrix semantics. -/
theorem candidate_error (c : Candidate) : hsDistance (matrix c) CCX = error c := by
  cases c with
  | identity => exact Curve.witness0_distance
  | two => exact Curve.witness2_distance
  | four => exact Curve.witness4_distance
  | exact => exact Curve.witness8_distance

/-- Choose the first feasible entry, in increasing CNOT-cost order. -/
def select (budget : ℝ) : Candidate := by
  classical
  exact if error .identity ≤ budget then .identity
    else if error .two ≤ budget then .two
    else if error .four ≤ budget then .four
    else .exact

/-- A nonnegative error budget always admits the exact fallback. -/
theorem select_feasible (budget : ℝ) (hbudget : 0 ≤ budget) :
    error (select budget) ≤ budget := by
  classical
  unfold select
  split_ifs with h0 h2 h4
  · exact h0
  · exact h2
  · exact h4
  · exact hbudget

/-- Selection minimizes cost among the four certified library entries. -/
theorem select_minimal (budget : ℝ) (c : Candidate) (hc : error c ≤ budget) :
    cost (select budget) ≤ cost c := by
  classical
  unfold select
  split_ifs with h0 h2 h4 <;> cases c <;> simp_all [cost]

/-- The local compiler contract: layout legality, bounded ideal error, and library optimality. -/
theorem select_correct (budget : ℝ) (hbudget : 0 ≤ budget) :
    AchievableCircuit (cost (select budget)) (matrix (select budget)) ∧
    hsDistance (matrix (select budget)) CCX ≤ budget ∧
    ∀ c : Candidate, hsDistance (matrix c) CCX ≤ budget →
      cost (select budget) ≤ cost c := by
  refine ⟨candidate_legal _, ?_, ?_⟩
  · rw [candidate_error]
    exact select_feasible budget hbudget
  · intro c hc
    rw [candidate_error] at hc
    exact select_minimal budget c hc

end CompilerContract

end
