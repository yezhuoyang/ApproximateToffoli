/-
Circuits on `N` qubits in which a CNOT may act on ANY pair of distinct qubits.

This is the model for constructions that assume no layout constraint (for instance
the scheme of Huang and Palsberg, PLDI 2024).  It contains definitions only, plus a
few immediate facts.  Basis states, the matrix of a CNOT and of a one-qubit gate,
and the conditional are the ones of `ApproxToffoli/Line/Model.lean`; the only
difference is that a CNOT carries a proof that its two qubits are DISTINCT instead
of a proof that they are neighbours.  Every circuit on a line is a circuit here
(`ofLine`), with the same matrix, the same number of CNOTs and the same T counts.
-/
import Mathlib
import ApproxToffoli.Line.Model
import ApproxToffoli.Line.TModel

namespace Free

open Matrix Line

variable {N : ℕ}

/-- A gate on `N` qubits with no layout constraint: a CNOT on two distinct qubits,
or a one-qubit gate. -/
inductive Gate (N : ℕ) where
  /-- CNOT with control `c` and target `t`, any two distinct qubits. -/
  | cx (c t : Fin N) (h : c ≠ t) : Gate N
  /-- The one-qubit matrix `g` applied to qubit `q`. -/
  | one (q : Fin N) (g : Matrix Bool Bool ℂ) : Gate N

/-- The matrix of a gate. -/
def Gate.mat : Gate N → Matrix (St N) (St N) ℂ
  | .cx c t h => ExactLine.mono (cxPerm c t h) (fun _ => 1)
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
    | cx c' t h => simp [cnots, ih]; omega
    | one q m => simp [cnots, ih]

/-! ### T-gate accounting (same rules as on a line) -/

/-- `TR c t r`: the one-qubit gates of the circuit `c` can be split into Clifford+T
gates containing `t` T gates in total, and `r` further phase gates `P(φ)` of
arbitrary angle (the rotations).  CNOTs are free. -/
inductive TR {N : ℕ} : List (Gate N) → ℕ → ℕ → Prop where
  | nil : TR [] 0 0
  | cx {c : List (Gate N)} {t r : ℕ} (a b : Fin N) (h : a ≠ b) :
      TR c t r → TR (Gate.cx a b h :: c) t r
  | exact {c : List (Gate N)} {t r : ℕ} (q : Fin N) {g : Matrix Bool Bool ℂ} {m : ℕ} :
      TCost g m → TR c t r → TR (Gate.one q g :: c) (t + m) r
  | rot {c : List (Gate N)} {t r : ℕ} (q : Fin N) (φ : ℝ) :
      TR c t r → TR (Gate.one q (pGate φ) :: c) t (r + 1)

/-! ### Circuits on a line are circuits here -/

/-- A gate on a line, seen as a gate with no layout constraint. -/
def ofLineGate : Line.Gate N → Gate N
  | .cx c t adj => .cx c t (adj_ne adj)
  | .one q g => .one q g

/-- A circuit on a line, seen as a circuit with no layout constraint. -/
def ofLine (c : List (Line.Gate N)) : List (Gate N) := c.map ofLineGate

theorem ofLineGate_mat (g : Line.Gate N) : (ofLineGate g).mat = g.mat := by
  cases g <;> rfl

theorem circMat_ofLine (c : List (Line.Gate N)) : circMat (ofLine c) = Line.circMat c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    change circMat (ofLine c) * (ofLineGate g).mat = Line.circMat c * g.mat
    rw [ih, ofLineGate_mat]

theorem cnots_ofLine (c : List (Line.Gate N)) : cnots (ofLine c) = Line.cnots c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g with
    | cx a b adj => change cnots (ofLine c) + 1 = Line.cnots c + 1; rw [ih]
    | one q m => exact ih

theorem unitaryGates_ofLine {c : List (Line.Gate N)} (h : Line.UnitaryGates c) :
    UnitaryGates (ofLine c) := by
  intro g hg q m hgm
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  cases g' with
  | cx a b adj => cases hgm
  | one q' m' =>
    cases hgm
    exact h _ hg' q m rfl

theorem tr_ofLine {c : List (Line.Gate N)} {t r : ℕ} (h : Line.TR c t r) :
    TR (ofLine c) t r := by
  induction h with
  | nil => exact TR.nil
  | cx a b adj _ ih => exact TR.cx a b (adj_ne adj) ih
  | exact q hg _ ih => exact TR.exact q hg ih
  | rot q φ _ ih => exact TR.rot q φ ih

end Free
