/-
The scheme of da Silva and Park, "Linear-depth quantum circuits for multiqubit
controlled gates" (Phys. Rev. A 106, 042602, 2022), for the conditional `C^{N-1}(X)`:
the CIRCUIT and the GOAL (definitions only).

The circuit has no helper qubit and lets any two qubits interact.  Qubits `0 .. N-2`
are the controls and qubit `N-1` is the target.  It consists of controlled rotations
between pairs of qubits.  With `e(c, t) = t - c` for `c ≥ 1` and `t - 1` for `c = 0`,
the gate on the pair `(c, t)` is

    controlled X^(s / 2^e)        if t is the target qubit (first two passes),
    controlled R_x(s π / 2^e)     otherwise,

for a sign `s`, in four passes:

    pass 1   all pairs c < t ≤ N-1,       s = +
    pass 2   pairs 1 ≤ c < t ≤ N-1,       s = -
    pass 3   all pairs c < t ≤ N-2,       s = - if c = 0, + otherwise
    pass 4   pairs 1 ≤ c < t ≤ N-2,       s = -

The reference implementation (qclib, `Ldmcu`) orders the gates of a pass by `c + t`,
which gives linear depth.  Here passes 1 and 3 go by decreasing target and passes 2
and 4 by increasing target; the two orders differ only by exchanges of commuting gates
(checked for N ≤ 16 by `checks/lean_mirror_dsp22.py` in the artifact, which also
compares this circuit with qclib's as a matrix).  Every controlled gate is written
with two CNOTs.

Goal (`DspGoal`): for every `N ≥ 3` the circuit equals the conditional exactly and has
exactly `4N² - 12N + 10` CNOTs.
-/
import Mathlib
import ApproxToffoli.Free.QulinDefs

namespace Dsp

open Matrix Free
open Line (St hGate pGate condMat)

variable {N : ℕ}

/-- Controlled `R_x(θ)`, control `c`, target `t`: two CNOTs.
`R_x(θ) = H · diag(e^{-iθ/2}, e^{iθ/2}) · H`. -/
noncomputable def crx (θ : ℝ) (c t : Fin N) : List (Gate N) :=
  [Gate.one t hGate, Gate.one t (pGate (θ / 2))] ++ Qulin.cx c t ++
  [Gate.one t (pGate (-(θ / 2)))] ++ Qulin.cx c t ++ [Gate.one t hGate]

/-- Controlled `X^a`, control `c`, target `t`, with `X^a = H · diag(1, e^{iπa}) · H`:
two CNOTs. -/
noncomputable def cxpow (a : ℝ) (c t : Fin N) : List (Gate N) :=
  [Gate.one t hGate] ++ Qulin.cphase (Real.pi * a) c t ++ [Gate.one t hGate]

/-- The exponent of the pair `(c, t)`. -/
def expo (c t : ℕ) : ℕ := if c = 0 then t - 1 else t - c

/-- The gate on the pair `(c, t)` with sign `s`.  With `top = true`, the gates whose
target is qubit `N - 1` are controlled roots of `X`. -/
noncomputable def pairGate (N : ℕ) (hN : 0 < N) (top : Bool) (s : ℝ) (c t : ℕ) :
    List (Gate N) :=
  if top = true ∧ t = N - 1 then
    cxpow (s / 2 ^ expo c t) (Qulin.qb N hN c) (Qulin.qb N hN t)
  else
    crx (s * Real.pi / 2 ^ expo c t) (Qulin.qb N hN c) (Qulin.qb N hN t)

/-- All gates onto the target `t` from the controls `lo, lo + 1, ..., t - 1`, in this
order; the gate from control `c` has sign `sgn c`. -/
noncomputable def onto (N : ℕ) (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (lo t : ℕ) :
    List (Gate N) :=
  Qulin.forUp (t - lo) (fun i => pairGate N hN top (sgn (lo + i)) (lo + i) t)

/-- Pass 1: targets `N-1, N-2, ..., 1`, all controls below the target, sign `+`. -/
noncomputable def pass1 (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  Qulin.forUp (N - 1) (fun i => onto N hN true (fun _ => 1) 0 (N - 1 - i))

/-- Pass 2: targets `2, 3, ..., N-1`, controls `1 .. t-1`, sign `-`. -/
noncomputable def pass2 (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  Qulin.forUp (N - 2) (fun i => onto N hN true (fun _ => -1) 1 (i + 2))

/-- Pass 3: targets `N-2, ..., 1` (controls only), sign `-` from qubit `0`, `+` otherwise. -/
noncomputable def pass3 (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  Qulin.forUp (N - 2)
    (fun i => onto N hN false (fun c => if c = 0 then -1 else 1) 0 (N - 2 - i))

/-- Pass 4: targets `2, ..., N-2` (controls only), controls `1 .. t-1`, sign `-`. -/
noncomputable def pass4 (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  Qulin.forUp (N - 3) (fun i => onto N hN false (fun _ => -1) 1 (i + 2))

/-- **The da Silva–Park circuit** for the conditional on `N` qubits, target `N - 1`. -/
noncomputable def dsp (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  pass1 N hN ++ pass2 N hN ++ pass3 N hN ++ pass4 N hN

/-- The CNOT count of the circuit. -/
def dspCnots (N : ℕ) : ℕ := 4 * N ^ 2 - 12 * N + 10

/-- **Goal.**  For every `N ≥ 3`, the da Silva–Park circuit consists of unitary gates,
equals the conditional with target qubit `N - 1` exactly, and has exactly
`4N² - 12N + 10` CNOTs. -/
def DspGoal : Prop :=
  ∀ N : ℕ, (hN : 3 ≤ N) →
    UnitaryGates (dsp N (by omega)) ∧
    circMat (dsp N (by omega)) = condMat (⟨N - 1, by omega⟩ : Fin N) ∧
    cnots (dsp N (by omega)) = dspCnots N

end Dsp
