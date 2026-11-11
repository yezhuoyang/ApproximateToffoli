/-
Circuits on a line of `N` qubits, and the statement of the exact-synthesis theorem.

This file fixes the MODEL and the GOAL.  It contains definitions only (plus a few
immediate facts); the constructions and proofs live in the other files of
`ApproxToffoli/Line/`.

Model.
* A basis state of `N` qubits is a function `Fin N → Bool`; qubit `q` holds bit `x q`.
* A gate is either a CNOT between NEIGHBOURING qubits (the adjacency is part of the
  gate, so every circuit of this type respects the line), or an arbitrary one-qubit
  matrix on one qubit.
* A circuit is a list of gates, executed from the head of the list.
* The cost of a circuit is its number of CNOTs.

Goal (`ExactLineGoal bound`): for every `N ≥ 4` there is a circuit whose one-qubit
gates are unitary, whose matrix is exactly the conditional with target qubit `0`
(flip qubit `0` iff all other qubits are one), and which has at most `bound N` CNOTs.
The paper's theorem is `ExactLineGoal (fun N => 66 * (N - 1))`.
-/
import Mathlib
import ApproxToffoli.ExactLine

namespace Line

open Matrix

/-- Basis states of `N` qubits. -/
abbrev St (N : ℕ) := Fin N → Bool

variable {N : ℕ}

/-- A gate on a line of `N` qubits: a CNOT between neighbours, or a one-qubit gate. -/
inductive Gate (N : ℕ) where
  /-- CNOT with control `c` and target `t`, which must be neighbours on the line. -/
  | cx (c t : Fin N) (adj : c.val + 1 = t.val ∨ t.val + 1 = c.val) : Gate N
  /-- The one-qubit matrix `g` applied to qubit `q`. -/
  | one (q : Fin N) (g : Matrix Bool Bool ℂ) : Gate N

/-- The action of a CNOT on basis states: flip bit `t` when bit `c` is set. -/
def cxFun (c t : Fin N) (x : St N) : St N :=
  Function.update x t (xor (x t) (x c))

theorem cxFun_involutive (c t : Fin N) (h : c ≠ t) : Function.Involutive (cxFun c t) := by
  intro x
  funext r
  unfold cxFun
  by_cases hr : r = t
  · subst hr
    simp [Function.update_of_ne h]
  · simp [Function.update_of_ne hr]

/-- The basis permutation of a CNOT. -/
def cxPerm (c t : Fin N) (h : c ≠ t) : Equiv.Perm (St N) :=
  (cxFun_involutive c t h).toPerm _

theorem adj_ne {c t : Fin N} (adj : c.val + 1 = t.val ∨ t.val + 1 = c.val) : c ≠ t := by
  intro h
  subst h
  omega

/-- The matrix of a one-qubit gate `g` on qubit `q`: it acts on bit `q` and leaves
all other bits unchanged. -/
def oneMat (q : Fin N) (g : Matrix Bool Bool ℂ) : Matrix (St N) (St N) ℂ :=
  Matrix.of fun y x => if (∀ r, r ≠ q → y r = x r) then g (y q) (x q) else 0

/-- The matrix of a gate.  Entry `(y, x)` is the amplitude of basis state `y` in the
image of basis state `x`. -/
def Gate.mat : Gate N → Matrix (St N) (St N) ℂ
  | .cx c t adj => ExactLine.mono (cxPerm c t (adj_ne adj)) (fun _ => 1)
  | .one q g => oneMat q g

/-- The matrix of a circuit.  The head of the list is executed first. -/
noncomputable def circMat : List (Gate N) → Matrix (St N) (St N) ℂ
  | [] => 1
  | g :: c => circMat c * g.mat

/-- The number of CNOTs of a circuit. -/
def cnots : List (Gate N) → ℕ
  | [] => 0
  | .cx _ _ _ :: c => cnots c + 1
  | .one _ _ :: c => cnots c

/-- Every one-qubit gate of the circuit is unitary. -/
def UnitaryGates (c : List (Gate N)) : Prop :=
  ∀ g ∈ c, ∀ q m, g = Gate.one q m → m ∈ Matrix.unitaryGroup Bool ℂ

theorem circMat_append (c d : List (Gate N)) : circMat (c ++ d) = circMat d * circMat c := by
  induction c with
  | nil => simp [circMat]
  | cons g c ih => simp [circMat, ih, Matrix.mul_assoc]

theorem cnots_append (c d : List (Gate N)) : cnots (c ++ d) = cnots c + cnots d := by
  induction c with
  | nil => simp [cnots]
  | cons g c ih =>
    cases g with
    | cx c' t adj => simp [cnots, ih]; omega
    | one q m => simp [cnots, ih]

/-! ### The target: the conditional -/

/-- `allOthers t x`: every qubit other than `t` holds a one. -/
def allOthers (t : Fin N) (x : St N) : Bool := decide (∀ r, r ≠ t → x r = true)

/-- The action of the conditional with target qubit `t` on basis states. -/
def condFun (t : Fin N) (x : St N) : St N :=
  Function.update x t (xor (x t) (allOthers t x))

theorem allOthers_update (t : Fin N) (x : St N) (b : Bool) :
    allOthers t (Function.update x t b) = allOthers t x := by
  unfold allOthers
  congr 1
  apply propext
  constructor
  · intro h r hr
    have := h r hr
    rwa [Function.update_of_ne hr] at this
  · intro h r hr
    rw [Function.update_of_ne hr]
    exact h r hr

theorem condFun_involutive (t : Fin N) : Function.Involutive (condFun t) := by
  intro x
  funext r
  unfold condFun
  rw [allOthers_update]
  by_cases hr : r = t
  · subst hr
    simp
  · simp [Function.update_of_ne hr]

/-- The basis permutation of the conditional with target qubit `t`. -/
def condPerm (t : Fin N) : Equiv.Perm (St N) := (condFun_involutive t).toPerm _

/-- The conditional (multi-controlled X) with target qubit `t`: the permutation
matrix that flips qubit `t` exactly when all other qubits are one. -/
def condMat (t : Fin N) : Matrix (St N) (St N) ℂ :=
  ExactLine.mono (condPerm t) (fun _ => 1)

/-- The conditional sign `T_N`: minus one on the all-ones basis state. -/
def signMat (N : ℕ) : Matrix (St N) (St N) ℂ :=
  Matrix.diagonal fun x => if (∀ r, x r = true) then -1 else 1

/-! ### One-qubit gates used by the constructions -/

/-- The Hadamard gate. -/
noncomputable def hGate : Matrix Bool Bool ℂ :=
  Matrix.of fun y x => if y && x then -(1 / (Real.sqrt 2 : ℂ)) else 1 / (Real.sqrt 2 : ℂ)

/-- The phase gate `P(t) = diag(1, e^{it})`. -/
noncomputable def pGate (t : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then ExactLine.e t else 1

/-- The NOT gate. -/
def xGate : Matrix Bool Bool ℂ :=
  Matrix.of fun y x => if y = !x then 1 else 0

/-! ### The goal -/

/-- **Exact synthesis on a line with at most `bound N` CNOTs.**  For every `N ≥ 4`
there is a circuit of adjacent CNOTs and unitary one-qubit gates, with at most
`bound N` CNOTs, whose matrix is exactly the conditional with target qubit `0`. -/
def ExactLineGoal (bound : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, (hN : 4 ≤ N) →
    ∃ c : List (Gate N),
      UnitaryGates c ∧ cnots c ≤ bound N ∧ circMat c = condMat (⟨0, by omega⟩ : Fin N)

end Line
