/-
A conditional on a line with ONE CLEAN HELPER QUBIT: definitions and goal only.

The circuit acts on a line of `n + 2` qubits (positions `0 .. n+1`), `n ≥ 4`:

    position 0        the target
    position 1        a control
    position 2        the helper qubit; it starts in `|0⟩` and is returned to `|0⟩`
    positions 3..n+1  the other `n - 1` controls

It has the form `U ; Toffoli(1, 2 → 0) ; U⁻¹`, where `U = compute n` acts on the positions
`1 .. n+1`.  With `K = (n - 2) / 2`, `U` is, in time order,

    top      in-place AND on (1, 2, 3)                                         4 CNOTs
    down     k = 1..K (n even) or 1..K-1 (n odd):
             X on 2k+1;  toffoliEnd (2k+1; 2k+2, 2k+3)                         5 CNOTs
    bottom   n even:  [X on 2K if K ≥ 2];  CX(2K+1, 2K)                        1 CNOT
             n odd:   X on 2K+1;  CX(2K+2, 2K+1)                               1 CNOT
                      X on 2K+2;  toffoliEnd (2K+2; 2K+3, 2K+4)                5 CNOTs
                      [X on 2K if K ≥ 2];  toffoliEnd (2K; 2K+1, 2K+2)         5 CNOTs
    up       k = K-1..1:  [X on 2k if k ≥ 2];  toffoliEnd (2k; 2k+1, 2k+2)     5 CNOTs

MODEL.  The circuit is a list of `Line.Gate (n + 2)`: a CNOT of that type carries a proof
that its two qubits are neighbours on the line, so adjacency of every CNOT is part of the
type.  Gates are placed by natural-number positions through `uAt` and `cxAt`; `cxAt N c t`
produces a CNOT only if `c` and `t` are positions of the line that differ by one (and no
gate otherwise), so that no definition below needs a side condition.  That every intended
gate is really present is part of the goal: the CNOT count is stated as an equality.

GOAL (`HelperGoal`).  For every `n ≥ 4`: all one-qubit gates are unitary, the circuit has
exactly `10 n - 12` CNOTs, and every basis state `x` whose helper bit (position 2) is `0`
is sent to exactly the basis state `condTarget n x` (amplitude `1`, no phase), which agrees
with `x` everywhere except that the target bit (position 0) is flipped iff all `n` control
bits (positions `1, 3, ..., n+1`) are `1`; in particular the helper bit is `0` again.

This file contains definitions only.  The proof is in the other `Line/Helper*.lean` files
and ends with `Helper.helper_goal` in `Line/HelperMain.lean`.
-/
import Mathlib
import ApproxToffoli.Line.Inverse

namespace Helper

open Matrix Line

/-! ### Placing gates by natural-number positions -/

/-- The one-qubit gate `g` on position `p` (no gate if the line has no such position). -/
def uAt (N p : ℕ) (g : Matrix Bool Bool ℂ) : List (Gate N) :=
  if h : p < N then [Gate.one ⟨p, h⟩ g] else []

/-- The CNOT with control `c` and target `t`; it is present only if `c` and `t` are
positions of the line that differ by one. -/
def cxAt (N c t : ℕ) : List (Gate N) :=
  if h : c < N ∧ t < N ∧ (c + 1 = t ∨ t + 1 = c) then
    [Gate.cx ⟨c, h.1⟩ ⟨t, h.2.1⟩ h.2.2]
  else []

/-! ### The cells -/

/-- Relative-phase Toffoli, target `m` between its controls `a` and `b`
(`x_m ^= x_a x_b` up to a phase).  3 CNOTs. -/
noncomputable def toffoliMid (N a m b : ℕ) : List (Gate N) :=
  uAt N m hGate ++ uAt N m (pGate (-Real.pi / 4)) ++ cxAt N a m
    ++ uAt N m (pGate (Real.pi / 4)) ++ cxAt N b m ++ uAt N m (pGate (-Real.pi / 4))
    ++ cxAt N a m ++ uAt N m (pGate (Real.pi / 4)) ++ uAt N m hGate

/-- Relative-phase Toffoli, target `t` at one end of three adjacent qubits
(`x_t ^= x_near x_far` up to a phase).  5 CNOTs. -/
noncomputable def toffoliEnd (N t near far : ℕ) : List (Gate N) :=
  uAt N t hGate ++ uAt N t (pGate (Real.pi / 4)) ++ cxAt N near t
    ++ uAt N t (pGate (-Real.pi / 4)) ++ cxAt N far near ++ cxAt N near t
    ++ uAt N t (pGate (-Real.pi / 4)) ++ cxAt N far near ++ cxAt N near t
    ++ uAt N t (pGate (Real.pi / 4)) ++ uAt N t hGate

/-- In-place AND through a qubit `m` that holds `0`:
`(x_u, 0, x_v) ↦ (x_u x_v, x_u (1 - x_v), x_v)` up to a phase.  4 CNOTs. -/
noncomputable def andInPlace (N u m v : ℕ) : List (Gate N) :=
  uAt N v xGate ++ toffoliMid N u m v ++ uAt N v xGate ++ cxAt N m u

/-- The exact Toffoli on three adjacent qubits `q0, q0 + 1, q0 + 2`, where
`q0 = min t (min a b)`; the target is `t`.  8 CNOTs. -/
noncomputable def toffoliExact (N t a b : ℕ) : List (Gate N) :=
  let q0 := min t (min a b)
  let q1 := q0 + 1
  let q2 := q0 + 2
  uAt N t hGate
    ++ (uAt N q0 (pGate (Real.pi / 4)) ++ uAt N q1 (pGate (Real.pi / 4))
        ++ uAt N q2 (pGate (Real.pi / 4))
        ++ cxAt N q0 q1 ++ uAt N q1 (pGate (-Real.pi / 4)) ++ cxAt N q1 q2
        ++ uAt N q2 (pGate (Real.pi / 4))
        ++ cxAt N q0 q1 ++ cxAt N q1 q2 ++ uAt N q2 (pGate (-Real.pi / 4))
        ++ cxAt N q0 q1 ++ cxAt N q1 q2 ++ uAt N q2 (pGate (-Real.pi / 4))
        ++ cxAt N q0 q1 ++ cxAt N q1 q2)
    ++ uAt N t hGate

/-! ### The circuit `U` -/

/-- The NOT on position `2 k` that precedes a cell writing onto it; it is absent for
`k = 1`, because position `2` holds `0`, not `1`. -/
def flip (N k : ℕ) : List (Gate N) :=
  if 2 ≤ k then uAt N (2 * k) xGate else []

/-- The down sweep: the cells `k, k + 1, ..., k + d - 1`, in this order. -/
noncomputable def down (N : ℕ) : ℕ → ℕ → List (Gate N)
  | _, 0 => []
  | k, d + 1 =>
    uAt N (2 * k + 1) xGate ++ toffoliEnd N (2 * k + 1) (2 * k + 2) (2 * k + 3)
      ++ down N (k + 1) d

/-- The up sweep: the cells `k + d - 1, ..., k + 1, k`, in this order. -/
noncomputable def up (N : ℕ) : ℕ → ℕ → List (Gate N)
  | _, 0 => []
  | k, d + 1 =>
    up N (k + 1) d ++ flip N k ++ toffoliEnd N (2 * k) (2 * k + 1) (2 * k + 2)

/-- The bottom of the ladder, for odd and for even `n`. -/
noncomputable def bottom (N : ℕ) (odd : Bool) (K : ℕ) : List (Gate N) :=
  if odd then
    uAt N (2 * K + 1) xGate ++ cxAt N (2 * K + 2) (2 * K + 1)
      ++ uAt N (2 * K + 2) xGate ++ toffoliEnd N (2 * K + 2) (2 * K + 3) (2 * K + 4)
      ++ flip N K ++ toffoliEnd N (2 * K) (2 * K + 1) (2 * K + 2)
  else
    flip N K ++ cxAt N (2 * K + 1) (2 * K)

/-- `U`: top, down sweep, bottom, up sweep.  `K = (n - 2) / 2`. -/
noncomputable def compute (n : ℕ) : List (Gate (n + 2)) :=
  andInPlace (n + 2) 1 2 3
    ++ down (n + 2) 1 (if n % 2 = 1 then (n - 2) / 2 - 1 else (n - 2) / 2)
    ++ bottom (n + 2) (decide (n % 2 = 1)) ((n - 2) / 2)
    ++ up (n + 2) 1 ((n - 2) / 2 - 1)

/-- The whole circuit: `U ; Toffoli(1, 2 → 0) ; U⁻¹`. -/
noncomputable def helperCirc (n : ℕ) : List (Gate (n + 2)) :=
  compute n ++ toffoliExact (n + 2) 0 1 2 ++ invCirc (compute n)

/-! ### The goal -/

/-- The basis state that the conditional must produce from `x`: the target bit
(position `0`) is flipped iff all `n` control bits (positions `1, 3, ..., n+1`, that is,
every position other than `0` and `2`) are `1`; every other bit is unchanged. -/
def condTarget (n : ℕ) (x : St (n + 2)) : St (n + 2) :=
  Function.update x ⟨0, by omega⟩
    (xor (x ⟨0, by omega⟩)
      (decide (∀ r : Fin (n + 2), r.val ≠ 0 → r.val ≠ 2 → x r = true)))

/-- **A conditional on a line with one clean helper qubit and exactly `10 n - 12` CNOTs.**
For every `n ≥ 4`, the circuit `helperCirc n` on the line of `n + 2` qubits (every CNOT of
a `Line.Gate` is between neighbours) has unitary one-qubit gates and exactly `10 n - 12`
CNOTs, and it sends every basis state `x` whose helper bit (position `2`) is `0` to
exactly the basis state `condTarget n x`, with amplitude `1`. -/
def HelperGoal : Prop :=
  ∀ n : ℕ, (hn : 4 ≤ n) →
    UnitaryGates (helperCirc n) ∧
    cnots (helperCirc n) = 10 * n - 12 ∧
    ∀ x : St (n + 2), x ⟨2, by omega⟩ = false →
      circMat (helperCirc n) *ᵥ Pi.single x 1 = Pi.single (condTarget n x) 1

end Helper
