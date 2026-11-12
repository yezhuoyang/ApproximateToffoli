/-
T-gate accounting for circuits on a line: the MODEL and the GOAL (definitions only).

A one-qubit gate is "Clifford+T with at most n T gates" if, up to a global phase, it
is a product of H, S and T gates containing at most n T gates (`TCost`).  The
one-qubit gates of a circuit are split into such gates, with `t` T gates in total,
and `r` further phase gates `P(φ)` of arbitrary angle, called rotations (`TR`).
CNOTs are Clifford and cost nothing here.

The resource estimate of the paper charges `3 * log2 (r / ε)` T gates to each of the
`r` rotations (`tEstimate`).  That price per rotation is taken from the literature
and is NOT proved here; what is proved is the pair of counts `(t, r)`.

Goal (`ExactLineTGoal`): the exact line circuit can be chosen with at most
`66 (N-1)` CNOTs, at most `36 (N-1)` T gates and at most `4N - 1` rotations.
-/
import Mathlib
import ApproxToffoli.Line.Model

namespace Line

open Matrix

/-- The S gate `P(π/2)`. -/
noncomputable def sGate : Matrix Bool Bool ℂ := pGate (Real.pi / 2)

/-- The T gate `P(π/4)`. -/
noncomputable def tGate : Matrix Bool Bool ℂ := pGate (Real.pi / 4)

/-- `TCost g n`: up to a global phase, `g` is a product of H, S and T gates that
contains at most `n` T gates. -/
inductive TCost : Matrix Bool Bool ℂ → ℕ → Prop where
  | one : TCost 1 0
  | h : TCost hGate 0
  | s : TCost sGate 0
  | t : TCost tGate 1
  | mul {g g' : Matrix Bool Bool ℂ} {m n : ℕ} :
      TCost g m → TCost g' n → TCost (g * g') (m + n)
  | phase {g : Matrix Bool Bool ℂ} {m : ℕ} (c : ℂ) (hc : star c * c = 1) :
      TCost g m → TCost (c • g) m

/-- `TR c t r`: the one-qubit gates of the circuit `c` can be split into Clifford+T
gates containing `t` T gates in total, and `r` further phase gates `P(φ)` of
arbitrary angle (the rotations).  CNOTs are free. -/
inductive TR {N : ℕ} : List (Gate N) → ℕ → ℕ → Prop where
  | nil : TR [] 0 0
  | cx {c : List (Gate N)} {t r : ℕ} (a b : Fin N)
      (adj : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
      TR c t r → TR (Gate.cx a b adj :: c) t r
  | exact {c : List (Gate N)} {t r : ℕ} (q : Fin N) {g : Matrix Bool Bool ℂ} {m : ℕ} :
      TCost g m → TR c t r → TR (Gate.one q g :: c) (t + m) r
  | rot {c : List (Gate N)} {t r : ℕ} (q : Fin N) (φ : ℝ) :
      TR c t r → TR (Gate.one q (pGate φ) :: c) t (r + 1)

/-- The resource estimate: `t` T gates plus `3 * log2 (r / ε)` for each of the `r`
rotations, when the rotations together may deviate by `ε`. -/
noncomputable def tEstimate (t r : ℕ) (ε : ℝ) : ℝ :=
  if r = 0 then (t : ℝ) else (t : ℝ) + 3 * (r : ℝ) * Real.logb 2 ((r : ℝ) / ε)

/-- **Exact synthesis on a line with CNOT, T and rotation counts.**  For every
`N ≥ 4` there is a circuit of adjacent CNOTs and unitary one-qubit gates that equals
the conditional exactly, has at most `66 (N-1)` CNOTs, and whose one-qubit gates
split into Clifford+T gates with at most `36 (N-1)` T gates and at most `4N - 1`
rotations. -/
def ExactLineTGoal : Prop :=
  ∀ N : ℕ, (hN : 4 ≤ N) →
    ∃ c : List (Gate N),
      UnitaryGates c ∧ cnots c ≤ 66 * (N - 1) ∧
      circMat c = condMat (⟨0, by omega⟩ : Fin N) ∧
      ∃ t r : ℕ, TR c t r ∧ t ≤ 36 * (N - 1) ∧ r ≤ 4 * N - 1

end Line
