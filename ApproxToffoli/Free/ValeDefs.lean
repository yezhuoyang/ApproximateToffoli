/-
The scheme of Vale et al., "Circuit Decomposition of Multicontrolled Special Unitary
Single-Qubit Gates" (IEEE TCAD 43(3), 2024; arXiv:2302.06377), for the conditional
`C^{N-1}(X)`, in the form Qiskit emits it (`synth_mcx_noaux_v24`): the CIRCUIT and the
GOAL (definitions only).

The circuit has no helper qubit and lets any two qubits interact (`Free.Gate`).  Qubits
`0 .. N-2` are the controls and qubit `N-1` is the target.  The gate lists are those of
the reference implementation `baselines/vale24_reference.py` of the artifact, cell by
cell and in the same order:

    ccx a b t            Toffoli, 6 CNOTs (the gate list is `Qulin.ccx`)
    c3x a b c t          three-controlled X, 14 CNOTs, no helper qubit
    rtof a b t           relative-phase Toffoli, 3 CNOTs
    ladAct u v s         first five gates of `rtof u v s`, 2 CNOTs
    ladRst u v s         inverse of `ladAct u v s`, 2 CNOTs
    chain c0 a0 j        ladder on the controls `c0 .. c0+j+1` and the dirty qubits
                         `a0 .. a0+j`, 4j+3 CNOTs
    mcxHalf k c0 a0 t    `ccx` followed by `chain (k-3)`
    mcx k c0 a0 t        `C^k(X)`, controls `c0 .. c0+k-1`, dirty qubits `a0 .. a0+k-3`
    crz lam c t          controlled `R_z(lam)`, 2 CNOTs
    mcrz lam m           `R_z(lam)` on qubit `m` controlled by the qubits `0 .. m-1`
    phaseChain m lam     `P(lam)` on qubit `m` controlled by the qubits `0 .. m-1`
    vale N               the conditional on `N` qubits

The transliteration of this file into Python, `checks/lean_mirror_vale24.py` of the
artifact, produces the same gate list as the reference implementation.

Goal (`ValeGoal`): for every `N ≥ 2` the circuit equals the conditional exactly (no
global phase), and for every `N ≥ 8` it has exactly `8N² - 32N - 36` CNOTs.
-/
import Mathlib
import ApproxToffoli.Free.QulinDefs

namespace Vale

open Matrix Free
open Line (St hGate pGate condMat)
open Qulin (qb cx ccx)

variable {N : ℕ}

/-! ### One-qubit gates -/

/-- The Hadamard gate on qubit `q`. -/
noncomputable def hG (q : Fin N) : List (Gate N) := [Gate.one q hGate]

/-- The phase gate `P(φ) = diag(1, e^{iφ})` on qubit `q`.  `T = P(π/4)`. -/
noncomputable def pG (φ : ℝ) (q : Fin N) : List (Gate N) := [Gate.one q (pGate φ)]

/-! ### Fixed cells -/

/-- The diagonal part of `c3x`: the phase `(-1)^(x_a x_b x_c x_t)`, 14 CNOTs. -/
noncomputable def c3xCore (a b c t : Fin N) : List (Gate N) :=
  pG (Real.pi / 8) a ++ pG (Real.pi / 8) b ++ pG (Real.pi / 8) c ++ pG (Real.pi / 8) t ++
  cx a b ++ pG (-(Real.pi / 8)) b ++ cx a b ++
  cx b c ++ pG (-(Real.pi / 8)) c ++ cx a c ++ pG (Real.pi / 8) c ++ cx b c ++
  pG (-(Real.pi / 8)) c ++ cx a c ++
  cx c t ++ pG (-(Real.pi / 8)) t ++ cx b t ++ pG (Real.pi / 8) t ++ cx c t ++
  pG (-(Real.pi / 8)) t ++
  cx a t ++ pG (Real.pi / 8) t ++ cx c t ++ pG (-(Real.pi / 8)) t ++ cx b t ++
  pG (Real.pi / 8) t ++
  cx c t ++ pG (-(Real.pi / 8)) t ++ cx a t

/-- `C^3(X)` without helper qubits (controls `a`, `b`, `c`, target `t`): 14 CNOTs. -/
noncomputable def c3x (a b c t : Fin N) : List (Gate N) :=
  hG t ++ c3xCore a b c t ++ hG t

/-- First five gates of `rtof u v s`: 2 CNOTs. -/
noncomputable def ladAct (u v s : Fin N) : List (Gate N) :=
  hG s ++ pG (Real.pi / 4) s ++ cx v s ++ pG (-(Real.pi / 4)) s ++ cx u s

/-- The inverse of `ladAct u v s`: 2 CNOTs. -/
noncomputable def ladRst (u v s : Fin N) : List (Gate N) :=
  cx u s ++ pG (Real.pi / 4) s ++ cx v s ++ pG (-(Real.pi / 4)) s ++ hG s

/-- The relative-phase Toffoli on `a`, `b`, target `t`: 3 CNOTs. -/
noncomputable def rtof (a b t : Fin N) : List (Gate N) :=
  ladAct a b t ++ pG (Real.pi / 4) t ++ cx b t ++ pG (-(Real.pi / 4)) t ++ hG t

/-! ### `C^k(X)` with `k - 2` dirty qubits -/

/-- The ladder on the controls `c0 .. c0+j+1` and the dirty qubits `a0 .. a0+j`. -/
noncomputable def chain (N : ℕ) (hN : 0 < N) (c0 a0 : ℕ) : ℕ → List (Gate N)
  | 0 => rtof (qb N hN c0) (qb N hN (c0 + 1)) (qb N hN a0)
  | j + 1 =>
    ladAct (qb N hN (a0 + j)) (qb N hN (c0 + j + 2)) (qb N hN (a0 + j + 1)) ++
    chain N hN c0 a0 j ++
    ladRst (qb N hN (a0 + j)) (qb N hN (c0 + j + 2)) (qb N hN (a0 + j + 1))

/-- Half of `C^k(X)`, `k ≥ 4`: a Toffoli on (last control, last dirty qubit; target),
then the ladder. -/
noncomputable def mcxHalf (N : ℕ) (hN : 0 < N) (k c0 a0 t : ℕ) : List (Gate N) :=
  ccx (qb N hN (c0 + k - 1)) (qb N hN (a0 + k - 3)) (qb N hN t) ++ chain N hN c0 a0 (k - 3)

/-- `C^k(X)` with controls `c0 .. c0+k-1` and target `t`.  For `k ≥ 4` it borrows the
dirty qubits `a0 .. a0+k-3`; for `k ≤ 3` it uses no other qubit. -/
noncomputable def mcx (N : ℕ) (hN : 0 < N) (k c0 a0 t : ℕ) : List (Gate N) :=
  if k = 1 then cx (qb N hN c0) (qb N hN t)
  else if k = 2 then ccx (qb N hN c0) (qb N hN (c0 + 1)) (qb N hN t)
  else if k = 3 then c3x (qb N hN c0) (qb N hN (c0 + 1)) (qb N hN (c0 + 2)) (qb N hN t)
  else mcxHalf N hN k c0 a0 t ++ mcxHalf N hN k c0 a0 t

/-! ### Multi-controlled `R_z` -/

/-- Controlled `R_z(lam)`, control `c`, target `t`: 2 CNOTs. -/
noncomputable def crz (lam : ℝ) (c t : Fin N) : List (Gate N) :=
  pG (lam / 2) t ++ cx c t ++ pG (-(lam / 2)) t ++ cx c t

/-- `R_z(lam)` on qubit `m` controlled by the qubits `0 .. m-1` (`m ≥ 1`).  For `m ≥ 2`
the first `(m+1)/2` controls and the last `m/2` controls each drive one `C^k(X)` onto
qubit `m`, with `P(-lam/4)` and `P(lam/4)` in between, twice. -/
noncomputable def mcrz (N : ℕ) (hN : 0 < N) (lam : ℝ) (m : ℕ) : List (Gate N) :=
  if m = 1 then crz lam (qb N hN 0) (qb N hN 1)
  else
    mcx N hN ((m + 1) / 2) 0 ((m + 1) / 2) m ++ pG (-(lam / 4)) (qb N hN m) ++
    mcx N hN (m / 2) ((m + 1) / 2) ((m + 1) / 2 - m / 2 + 2) m ++ pG (lam / 4) (qb N hN m) ++
    mcx N hN ((m + 1) / 2) 0 ((m + 1) / 2) m ++ pG (-(lam / 4)) (qb N hN m) ++
    mcx N hN (m / 2) ((m + 1) / 2) ((m + 1) / 2 - m / 2 + 2) m ++ pG (lam / 4) (qb N hN m)

/-! ### The whole circuit -/

/-- `P(lam)` on qubit `m` controlled by the qubits `0 .. m-1`: a diagonal gate on the
qubits `0 .. m`. -/
noncomputable def phaseChain (N : ℕ) (hN : 0 < N) : ℕ → ℝ → List (Gate N)
  | 0, lam => pG lam (qb N hN 0)
  | m + 1, lam => mcrz N hN lam (m + 1) ++ phaseChain N hN m (lam / 2)

/-- **The circuit of Vale et al.** for the conditional on `N` qubits, target `N - 1`. -/
noncomputable def vale (N : ℕ) (hN : 0 < N) : List (Gate N) :=
  hG (qb N hN (N - 1)) ++ phaseChain N hN (N - 1) Real.pi ++ hG (qb N hN (N - 1))

/-! ### The goal -/

/-- **Goal.**  For every `N ≥ 2` the circuit of Vale et al. consists of unitary gates
and equals the conditional with target qubit `N - 1` exactly, with no global phase; for
every `N ≥ 8` it has exactly `8N² - 32N - 36` CNOTs. -/
def ValeGoal : Prop :=
  (∀ N : ℕ, (hN : 2 ≤ N) →
    UnitaryGates (vale N (by omega)) ∧
    circMat (vale N (by omega)) = condMat (⟨N - 1, by omega⟩ : Fin N)) ∧
  (∀ N : ℕ, (hN : 8 ≤ N) → cnots (vale N (by omega)) = 8 * N ^ 2 - 32 * N - 36)

end Vale
