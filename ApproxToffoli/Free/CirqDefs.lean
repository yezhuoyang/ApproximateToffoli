/-
Cirq's decomposition of the conditional `C^{N-1}(X)` without helper qubits
(`cirq.decompose_multi_controlled_x` with no free qubit: the recursion of Lemma 7.5 of
Barenco et al., "Elementary gates for quantum computation", 1995, with the
multi-controlled X gates of their Lemmas 7.2 and 7.3 inside): the CIRCUIT and the GOAL
(definitions only).

The circuit has no helper qubit and lets any two qubits interact (`Free.Gate`).  Qubits
`0 .. N-2` are the controls and qubit `N-1` is the target.  The gate lists are those of
the reference implementation `baselines/cirq_reference.py` of the artifact, cell by cell
and in the same order:

    ccz a b c            the sign `(-1)^(x_a x_b x_c)`, 8 CNOTs
    ccx c0 c1 t          Toffoli `H_t ; ccz ; H_t`, 8 CNOTs; the order of the three
                         qubits inside `ccz` follows Cirq's rule on the qubit indices
    marg u v s           Toffoli up to a sign, 3 CNOTs (the gate list is `Qulin.marg`)
    chain c a j          palindrome of `marg` cells on the controls `c 0 .. c (j+1)` and
                         the borrowed qubits `a 0 .. a j`, 6j+3 CNOTs
    ladderHalf m c a t   `ccx` followed by `chain (m-3)`
    ladder m c a t       `C^m(X)`, controls `c 0 .. c (m-1)`, borrowed `a 0 .. a (m-3)`
                         (Lemma 7.2), 12m-14 CNOTs
    split N k            `C^{k-1}(X)` onto qubit `k-1` from two ladders, each used twice
                         (Lemma 7.3)
    mcxK N k             `C^{k-1}(X)` with controls `0 .. k-2` and target `k-1`,
                         borrowing among the qubits `k .. N-1`
    croot s c t          controlled `X^s`, 2 CNOTs
    step N k             the part of the recursion that removes control `k-1`
    recur N k            `X^(2^-(N-1-k))` on qubit `N-1` controlled by qubits `0 .. k-1`
    cirqMcx N            the conditional on `N` qubits

The transliteration of this file into Python, `checks/lean_mirror_cirq.py` of the
artifact, produces the same gate list as the reference implementation.

Goal (`CirqGoal`): for every `N ≥ 4` the circuit equals the conditional exactly (no
global phase), and for every `N ≥ 5` it has exactly `21N² - 120N + 164` CNOTs if `N` is
even and `21N² - 126N + 181` if `N` is odd.  (The count is stated over the integers:
at `N = 5` the natural-number subtraction `21N² - 126N` would stop at zero.)
-/
import Mathlib
import ApproxToffoli.Free.QulinDefs

namespace CirqMcx

open Matrix Free
open Line (St hGate pGate ryGate condMat m2)
open Qulin (qb cx marg)

variable {N : ℕ}

/-! ### One-qubit gates -/

/-- The Hadamard gate on qubit `q`. -/
noncomputable def hG (q : Fin N) : List (Gate N) := [Gate.one q hGate]

/-- The phase gate `P(φ) = diag(1, e^{iφ})` on qubit `q`.  `T = P(π/4)`. -/
noncomputable def pG (φ : ℝ) (q : Fin N) : List (Gate N) := [Gate.one q (pGate φ)]

/-- The rotation `R_z(φ) = diag(e^{-iφ/2}, e^{iφ/2})`. -/
noncomputable def rzGate (φ : ℝ) : Matrix Bool Bool ℂ :=
  m2 (ExactLine.e (-(φ / 2))) 0 0 (ExactLine.e (φ / 2))

/-! ### The Toffoli as Cirq emits it -/

/-- The sign `(-1)^(x_a x_b x_c)`: 8 CNOTs, in four sweeps `CX(a,b) ; CX(b,c)`. -/
noncomputable def ccz (a b c : Fin N) : List (Gate N) :=
  pG (Real.pi / 4) a ++ pG (Real.pi / 4) b ++ pG (Real.pi / 4) c ++
  cx a b ++ cx b c ++ pG (-(Real.pi / 4)) b ++ pG (Real.pi / 4) c ++
  cx a b ++ cx b c ++ pG (-(Real.pi / 4)) c ++
  cx a b ++ cx b c ++ pG (-(Real.pi / 4)) c ++
  cx a b ++ cx b c

/-- The Toffoli with controls `c0`, `c1` and target `t`: `H_t ; ccz ; H_t`.  The order
in which `ccz` runs over the three qubits is Cirq's rule on the qubit indices. -/
noncomputable def ccx (c0 c1 t : Fin N) : List (Gate N) :=
  hG t ++
  (if c1.val ≠ c0.val + 1 ∧ c0.val ≠ c1.val + 1 then ccz c0 t c1
   else if c1.val ≠ t.val + 1 ∧ t.val ≠ c1.val + 1 then ccz c1 c0 t
   else ccz c0 c1 t) ++
  hG t

/-! ### `C^m(X)` with `m - 2` borrowed qubits (Lemma 7.2) -/

/-- The palindrome of relative-phase Toffolis on the controls `c 0 .. c (j+1)` and the
borrowed qubits `a 0 .. a j`. -/
noncomputable def chain (c a : ℕ → Fin N) : ℕ → List (Gate N)
  | 0 => marg (c 0) (c 1) (a 0)
  | j + 1 =>
    marg (c (j + 2)) (a j) (a (j + 1)) ++ chain c a j ++ marg (c (j + 2)) (a j) (a (j + 1))

/-- Half of `C^m(X)`: a Toffoli on (last control, last borrowed qubit; target), then the
chain. -/
noncomputable def ladderHalf (m : ℕ) (c a : ℕ → Fin N) (t : Fin N) : List (Gate N) :=
  ccx (c (m - 1)) (a (m - 3)) t ++ chain c a (m - 3)

/-- `C^m(X)` (`m ≥ 3`) with controls `c 0 .. c (m-1)`, target `t`, and borrowed qubits
`a 0 .. a (m-3)`. -/
noncomputable def ladder (m : ℕ) (c a : ℕ → Fin N) (t : Fin N) : List (Gate N) :=
  ladderHalf m c a t ++ ladderHalf m c a t

/-! ### `C^{k-1}(X)` with too few qubits to borrow (Lemma 7.3) -/

/-- The `i`-th natural number different from `j`. -/
def skip (j i : ℕ) : ℕ := if i < j then i else i + 1

/-- First part: the first `N / 2` controls are collected on qubit `k`. -/
noncomputable def splitPart1 (N : ℕ) (hN : 0 < N) (k : ℕ) : List (Gate N) :=
  ladder (N / 2) (fun i => qb N hN i) (fun i => qb N hN (skip k (N / 2 + i))) (qb N hN k)

/-- Second part: qubit `k` and the remaining controls drive the target `k - 1`. -/
noncomputable def splitPart2 (N : ℕ) (hN : 0 < N) (k : ℕ) : List (Gate N) :=
  if k - N / 2 = 2 then ccx (qb N hN (N / 2)) (qb N hN k) (qb N hN (k - 1))
  else
    ladder (k - N / 2) (fun i => qb N hN (skip (k - 1) (N / 2 + i))) (fun i => qb N hN i)
      (qb N hN (k - 1))

/-- `C^{k-1}(X)` on the controls `0 .. k-2` and the target `k - 1`, both parts twice. -/
noncomputable def split (N : ℕ) (hN : 0 < N) (k : ℕ) : List (Gate N) :=
  splitPart1 N hN k ++ splitPart2 N hN k ++ splitPart1 N hN k ++ splitPart2 N hN k

/-- `C^{k-1}(X)` with controls `0 .. k-2` and target `k - 1` inside the `N`-qubit
circuit (`2 ≤ k ≤ N - 1`); the qubits `k .. N-1` may be borrowed. -/
noncomputable def mcxK (N : ℕ) (hN : 0 < N) (k : ℕ) : List (Gate N) :=
  if k = 2 then cx (qb N hN 0) (qb N hN 1)
  else if k = 3 then ccx (qb N hN 0) (qb N hN 1) (qb N hN 2)
  else if 2 * k ≤ N + 3 then
    ladder (k - 1) (fun i => qb N hN i) (fun i => qb N hN (k + i)) (qb N hN (k - 1))
  else split N hN k

/-! ### The recursion (Lemma 7.5) -/

/-- The sign of `s`: `1` if `s > 0` and `-1` otherwise. -/
noncomputable def sg (s : ℝ) : ℝ := if 0 < s then 1 else -1

/-- Controlled `X^s`, control `c`, target `t`: 2 CNOTs.  With `σ = sg s` and `r = |s|`:
`P_c(π s / 2) ; RZ_t(-σ π/2) ; CX ; RY_t(π r / 2) ; CX ; [RZ(σ π/2) RY(-π r / 2)]_t`. -/
noncomputable def croot (s : ℝ) (c t : Fin N) : List (Gate N) :=
  pG (Real.pi * s / 2) c ++ [Gate.one t (rzGate (-sg s * (Real.pi / 2)))] ++ cx c t ++
  [Gate.one t (ryGate (Real.pi * |s| / 2))] ++ cx c t ++
  [Gate.one t (rzGate (sg s * (Real.pi / 2)) * ryGate (-(Real.pi * |s| / 2)))]

/-- The part of the recursion that removes control `k - 1`, with `s = 2^-(N-k)`. -/
noncomputable def step (N : ℕ) (hN : 0 < N) (k : ℕ) : List (Gate N) :=
  croot (1 / 2 ^ (N - k)) (qb N hN (k - 1)) (qb N hN (N - 1)) ++ mcxK N hN k ++
  croot (-(1 / 2 ^ (N - k))) (qb N hN (k - 1)) (qb N hN (N - 1)) ++ mcxK N hN k

/-- `X^(2^-(N-1-k))` on qubit `N - 1` controlled by the qubits `0 .. k-1` (`k ≥ 1`; the
case `k = 0` is not used). -/
noncomputable def recur (N : ℕ) (hN : 0 < N) : ℕ → List (Gate N)
  | 0 => []
  | 1 => croot (1 / 2 ^ (N - 2)) (qb N hN 0) (qb N hN (N - 1))
  | k + 2 => step N hN (k + 2) ++ recur N hN (k + 1)

/-- **Cirq's circuit** for the conditional on `N` qubits, target `N - 1`. -/
noncomputable def cirqMcx (N : ℕ) (hN : 0 < N) : List (Gate N) := recur N hN (N - 1)

/-! ### The goal -/

/-- **Goal.**  For every `N ≥ 4` Cirq's circuit consists of unitary gates and equals the
conditional with target qubit `N - 1` exactly, with no global phase; for every `N ≥ 5`
it has exactly `21N² - 120N + 164` CNOTs if `N` is even and `21N² - 126N + 181` CNOTs if
`N` is odd. -/
def CirqGoal : Prop :=
  (∀ N : ℕ, (hN : 4 ≤ N) →
    UnitaryGates (cirqMcx N (by omega)) ∧
    circMat (cirqMcx N (by omega)) = condMat (⟨N - 1, by omega⟩ : Fin N)) ∧
  (∀ N : ℕ, (hN : 5 ≤ N) →
    (cnots (cirqMcx N (by omega)) : ℤ) =
      if N % 2 = 0 then 21 * (N : ℤ) ^ 2 - 120 * (N : ℤ) + 164
      else 21 * (N : ℤ) ^ 2 - 126 * (N : ℤ) + 181)

end CirqMcx
