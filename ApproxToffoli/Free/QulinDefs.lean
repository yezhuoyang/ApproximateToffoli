/-
The scheme "Qulin" of Huang and Palsberg, "Compiling Conditional Quantum Gates without
Using Helper Qubits" (PLDI 2024), main variant (their Section 4), for the conditional
`C^{N-1}(X)`: the CIRCUIT and the GOAL (definitions only).

The gate lists follow the paper (Fig. 5, 6, 7, 8; Eq. (2), (3), (4), (6)).  Where the
paper prints only a gate count, the list is the one of the authors' public code; the
resulting circuit has exactly the paper's CNOT counts.  The full specification, with
the source of every block, is `notes/hp24_spec.md`; an executable reference with the
same block structure is `PLDI2027LNNCond/tools/hp24_reference.py` in the paper
repository.

Layout.  Qubit `N-1` is the target.  With `k = N / 2` (rounded down) the register is
qubits `0 .. 2k-2` (qubit 0 is the low bit); for odd `N` qubit `N-2` is one more control.
CNOTs may act on any two qubits (`Free.Gate`).

Goal (`QulinGoal`): for every `N ≥ 6` the circuit `qulin N` equals the conditional
exactly, has exactly `124N - 214` (even `N`) or `132N - 358` (odd `N`) CNOTs, and its
one-qubit gates are `100N - 170` T gates and `6N - 15` rotations (even `N`), or
`100N - 276` T gates and `14N - 35` rotations (odd `N`).
-/
import Mathlib
import ApproxToffoli.Free.Model
import ApproxToffoli.Line.Cells2

namespace Qulin

open Matrix Free
open Line (St hGate pGate xGate ryGate condMat)

variable {N : ℕ}

/-! ### Small pieces -/

/-- CNOT with control `c` and target `t`.  (The empty circuit if `c = t`, which never
happens in the circuits below.) -/
def cx (c t : Fin N) : List (Gate N) := if h : c ≠ t then [Gate.cx c t h] else []

/-- The circuits `f 0, f 1, ..., f (m-1)`, in this order. -/
def forUp (m : ℕ) (f : ℕ → List (Gate N)) : List (Gate N) := (List.range m).flatMap f

/-- The Toffoli gate (controls `a`, `b`, target `t`): 6 CNOTs, 7 T gates, 2 Hadamards. -/
noncomputable def ccx (a b t : Fin N) : List (Gate N) :=
  [Gate.one t hGate] ++ cx b t ++ [Gate.one t (pGate (-(Real.pi / 4)))] ++ cx a t ++
  [Gate.one t (pGate (Real.pi / 4))] ++ cx b t ++ [Gate.one t (pGate (-(Real.pi / 4)))] ++
  cx a t ++
  [Gate.one b (pGate (Real.pi / 4)), Gate.one t (pGate (Real.pi / 4)), Gate.one t hGate] ++
  cx a b ++ [Gate.one a (pGate (Real.pi / 4)), Gate.one b (pGate (-(Real.pi / 4)))] ++ cx a b

/-- The controlled phase `diag(1,1,1,e^{iθ})` on `c`, `t` (paper Eq. (3)). -/
noncomputable def cphase (θ : ℝ) (c t : Fin N) : List (Gate N) :=
  [Gate.one c (pGate (θ / 2)), Gate.one t (pGate (θ / 2))] ++ cx c t ++
  [Gate.one t (pGate (-(θ / 2)))] ++ cx c t

/-- The doubly controlled phase: `e^{iθ}` when `c0`, `c1`, `t` are all one (paper Eq. (4)). -/
noncomputable def ccphase (θ : ℝ) (c0 c1 t : Fin N) : List (Gate N) :=
  cx c0 t ++ [Gate.one t (pGate (-(θ / 4)))] ++ cx c1 t ++ [Gate.one t (pGate (θ / 4))] ++
  cx c0 t ++ [Gate.one t (pGate (-(θ / 4)))] ++ cx c1 t ++ [Gate.one t (pGate (θ / 4))] ++
  cphase (θ / 2) c0 c1

/-! ### `C^k(X)` with `k - 2` borrowed qubits (paper Eq. (2)) -/

/-- First half of the relative-phase Toffoli on `u`, `v`, target `s`. -/
noncomputable def ryA (u v s : Fin N) : List (Gate N) :=
  [Gate.one s (ryGate (-(Real.pi / 4)))] ++ cx v s ++ [Gate.one s (ryGate (-(Real.pi / 4)))] ++
  cx u s

/-- The inverse of `ryA`. -/
noncomputable def ryAinv (u v s : Fin N) : List (Gate N) :=
  cx u s ++ [Gate.one s (ryGate (Real.pi / 4))] ++ cx v s ++ [Gate.one s (ryGate (Real.pi / 4))]

/-- The relative-phase Toffoli on `u`, `v`, target `s`: 3 CNOTs. -/
noncomputable def marg (u v s : Fin N) : List (Gate N) :=
  ryA u v s ++ [Gate.one s (ryGate (Real.pi / 4))] ++ cx v s ++
  [Gate.one s (ryGate (Real.pi / 4))]

/-- The chain of relative-phase Toffolis: level `j` writes into the borrowed qubit `a j`
and is controlled by `a (j-1)` and `c (j+1)`; level `0` is controlled by `c 0`, `c 1`. -/
noncomputable def wChain (c a : ℕ → Fin N) : ℕ → List (Gate N)
  | 0 => marg (c 0) (c 1) (a 0)
  | j + 1 =>
    ryA (a j) (c (j + 2)) (a (j + 1)) ++ wChain c a j ++ ryAinv (a j) (c (j + 2)) (a (j + 1))

/-- Half of the multi-controlled gate. -/
noncomputable def mcxHalf (k : ℕ) (c a : ℕ → Fin N) (t : Fin N) : List (Gate N) :=
  ccx (a (k - 3)) (c (k - 1)) t ++ wChain c a (k - 3)

/-- `C^k(X)` (`k ≥ 3`) with controls `c 0 .. c (k-1)`, target `t`, and borrowed qubits
`a 0 .. a (k-3)`. -/
noncomputable def mcx (k : ℕ) (c a : ℕ → Fin N) (t : Fin N) : List (Gate N) :=
  mcxHalf k c a t ++ mcxHalf k c a t

/-! ### The increment with as many borrowed qubits as register qubits (paper Eq. (6)) -/

/-- Carry step: `c ^= a ; b ^= a ; a ^= b c`. -/
noncomputable def ux (a b c : Fin N) : List (Gate N) := cx a c ++ cx a b ++ ccx b c a

/-- Undo the carry, restore `b`, leave the sum bit in `c`. -/
noncomputable def uz (a b c : Fin N) : List (Gate N) := ccx b c a ++ cx a b ++ cx b c

/-- The adder from position `i` on, with `r` carry steps still to do. -/
noncomputable def addFrom (g0 : Fin N) (g q : ℕ → Fin N) : ℕ → ℕ → List (Gate N)
  | 0, i => cx g0 (q i)
  | r + 1, i =>
    ux g0 (g (i + 1)) (q i) ++ addFrom g0 g q r (i + 1) ++ uz g0 (g (i + 1)) (q i)

/-- The adder `q ← q + G + g 0` on the `m`-qubit register `q`, where `G` is the number
held by `g 1 .. g (m-1)`; the carry travels on the qubit `g 0`. -/
noncomputable def addPass (m : ℕ) (q g : ℕ → Fin N) : List (Gate N) :=
  addFrom (g 0) g q (m - 1) 0

/-- Complement the register `q` when `g 0` is zero. -/
def fanX (m : ℕ) (q g : ℕ → Fin N) : List (Gate N) :=
  [Gate.one (g 0) xGate] ++ forUp m (fun i => cx (g 0) (q i)) ++ [Gate.one (g 0) xGate]

/-- Complement `g 1 .. g (m-1)`. -/
def notG (m : ℕ) (g : ℕ → Fin N) : List (Gate N) :=
  forUp (m - 1) (fun i => [Gate.one (g (i + 1)) xGate])

/-- The increment on the register `q 0 .. q (m-1)` with borrowed qubits `g 0 .. g (m-1)`. -/
noncomputable def incB (m : ℕ) (q g : ℕ → Fin N) : List (Gate N) :=
  fanX m q g ++ addPass m q g ++ notG m g ++ addPass m q g ++ notG m g ++
  [Gate.one (q (m - 1)) xGate] ++ fanX m q g

/-! ### The increment with one borrowed qubit (paper Fig. 6) and the decrement (Fig. 5) -/

/-- The register `h, ys 0, ys 1, ...` (`h` is the low bit). -/
def consReg (h : Fin N) (ys : ℕ → Fin N) : ℕ → Fin N
  | 0 => h
  | i + 1 => ys i

/-- The register `ys 0, ..., ys (m-1), h`. -/
def snocReg (ys : ℕ → Fin N) (m : ℕ) (h : Fin N) : ℕ → Fin N :=
  fun i => if i < m then ys i else h

/-- The high half of a register whose low half has `k` qubits. -/
def hi (k : ℕ) (reg : ℕ → Fin N) : ℕ → Fin N := fun i => reg (k + i)

/-- The fan of CNOTs from `h` to the `k - 1` qubits of the high half. -/
def fanH (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : List (Gate N) :=
  forUp (k - 1) (fun i => cx h (hi k reg i))

/-- The increment on the register `reg 0 .. reg (2k-2)` with ONE borrowed qubit `h`. -/
noncomputable def inc (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : List (Gate N) :=
  incB k (consReg h (hi k reg)) reg ++ [Gate.one h xGate] ++ fanH k reg h ++
  mcx k reg (hi k reg) h ++
  incB k (consReg h (hi k reg)) reg ++ [Gate.one h xGate] ++
  mcx k reg (hi k reg) h ++ fanH k reg h ++
  incB k reg (snocReg (hi k reg) (k - 1) h)

/-- NOT on every qubit of the register `reg 0 .. reg (r-1)`. -/
def flips (r : ℕ) (reg : ℕ → Fin N) : List (Gate N) :=
  forUp r (fun i => [Gate.one (reg i) xGate])

/-- The decrement on the register `reg 0 .. reg (2k-2)` with one borrowed qubit `h`. -/
noncomputable def dec (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : List (Gate N) :=
  flips (2 * k - 1) reg ++ inc k reg h ++ flips (2 * k - 1) reg

/-! ### The whole circuit (paper Fig. 7 for even `N`, Fig. 8 for odd `N`) -/

/-- Qubit number `i` (reduced modulo `N`; all indices used below are smaller than `N`). -/
def qb (N : ℕ) (hN : 0 < N) (i : ℕ) : Fin N := ⟨i % N, Nat.mod_lt _ hN⟩

/-- The width of the register: `2 (N / 2) - 1`. -/
def regW (N : ℕ) : ℕ := 2 * (N / 2) - 1

/-- The smallest root angle. -/
noncomputable def θ0 (N : ℕ) : ℝ := Real.pi / 2 ^ (regW N - 1)

/-- The phase `e^{iθ}` on the target, controlled by register qubit `c` (and, for odd `N`,
by the extra control `N - 2`). -/
noncomputable def root (N : ℕ) (hN : 0 < N) (θ : ℝ) (c : Fin N) : List (Gate N) :=
  if N % 2 = 0 then cphase θ c (qb N hN (N - 1))
  else ccphase θ c (qb N hN (N - 2)) (qb N hN (N - 1))

/-- The roots controlled by register qubits `1, 2, ...`, with sign `s`. -/
noncomputable def roots (N : ℕ) (hN : 0 < N) (s : ℝ) : List (Gate N) :=
  forUp (regW N - 1) (fun j => root N hN (s * θ0 N * 2 ^ j) (qb N hN (1 + j)))

/-- **The Huang–Palsberg circuit** for the conditional on `N` qubits, target `N - 1`. -/
noncomputable def qulin (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  [Gate.one (qb N hN (N - 1)) hGate] ++ root N hN (θ0 N) (qb N hN 0) ++ roots N hN 1 ++
  inc (N / 2) (qb N hN) (qb N hN (N - 1)) ++ roots N hN (-1) ++
  dec (N / 2) (qb N hN) (qb N hN (N - 1)) ++ [Gate.one (qb N hN (N - 1)) hGate]

/-! ### The goal -/

/-- The paper's CNOT count. -/
def qulinCnots (N : ℕ) : ℕ := if N % 2 = 0 then 124 * N - 214 else 132 * N - 358

/-- The number of T gates among the one-qubit gates of the circuit. -/
def qulinT (N : ℕ) : ℕ := if N % 2 = 0 then 100 * N - 170 else 100 * N - 276

/-- The number of phase gates of other angles (rotations) of the circuit. -/
def qulinR (N : ℕ) : ℕ := if N % 2 = 0 then 6 * N - 15 else 14 * N - 35

/-- **The Huang–Palsberg scheme, formalized.**  For every `N ≥ 6` their circuit has
unitary one-qubit gates, equals the conditional with target qubit `N - 1` exactly, has
exactly the CNOT count stated in their paper, and its one-qubit gates split into
`qulinT N` T gates and `qulinR N` rotations. -/
def QulinGoal : Prop :=
  ∀ N : ℕ, (hN : 6 ≤ N) →
    UnitaryGates (qulin N (by omega)) ∧
    circMat (qulin N (by omega)) = condMat (⟨N - 1, by omega⟩ : Fin N) ∧
    cnots (qulin N (by omega)) = qulinCnots N ∧
    TR (qulin N (by omega)) (qulinT N) (qulinR N)

end Qulin
