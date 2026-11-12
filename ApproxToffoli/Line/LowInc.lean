/-
The low incrementer on a line: `24 a - 23` CNOTs.

Wires (natural-number positions): `S_i = 2a - 2i` (`0 ≤ i ≤ a`), `T_i = 2a - 2i - 1`
(`0 ≤ i < a`).  The circuit

    lowInc N a = invCirc (rest N a) ++ centre N a ++ rest N a ++ terminal N a

is, up to phases of modulus one, the basis permutation that adds one to the number `T`
modulo `2^a`, flips wire `0` iff all `T_i` are one, and leaves every other wire unchanged.

This file: the circuits, their CNOT counts, and the proof that each is a permutation up
to phases.  The basis action is computed in `LowIncWire.lean` and `LowIncSpec.lean`.

In wire positions, `rest N a` is

* for `k = 1, …, a - 1`: `cx (2k) (2k-1)`, then `rtof5 (2k+2) (2k+1) (2k)`;
* for `k = a - 1, …, 2`: `fan2 (2k) (2k-1) (2k-2)`;
* `cx (2a) (2a-1)`, `cx 2 1`.
-/
import Mathlib
import ApproxToffoli.Line.CentreSpec

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The first cell: `cx (o+1) o`, then the relative Toffoli onto `o + 1` -/

/-- `cx (o+1) o`, then `rtof5` with controls `o + 3`, `o + 2` and target `o + 1`.
Six CNOTs. -/
noncomputable def incCellAt (N o : ℕ) : List (Gate N) :=
  if h : o + 3 < N then
    [.cx ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (Or.inr rfl)]
      ++ rtof5 ⟨o + 3, h⟩ ⟨o + 2, by omega⟩ ⟨o + 1, by omega⟩ (Or.inr rfl) (Or.inr rfl)
  else []

/-- The basis permutation of `incCellAt`. -/
def incCellPermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 3 < N then
    ccPerm ⟨o + 3, h⟩ ⟨o + 1, by omega⟩ ⟨o + 2, by omega⟩ (by simp) (by simp)
      * cxPerm ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (by simp)
  else 1

theorem cnots_incCellAt (o : ℕ) (h : o + 3 < N) : cnots (incCellAt N o) = 6 := by
  rw [incCellAt, dif_pos h]
  rfl

theorem unitaryGates_incCellAt (N o : ℕ) : UnitaryGates (incCellAt N o) := by
  unfold incCellAt
  split_ifs
  · exact unitaryGates_append (unitaryGates_cons_cx _ _ _ unitaryGates_nil)
      (unitaryGates_rtof5 _ _ _ _ _)
  · exact unitaryGates_nil

theorem umono_incCellAt (N o : ℕ) : UMono (circMat (incCellAt N o)) (incCellPermAt N o) := by
  by_cases h : o + 3 < N
  · rw [incCellAt, dif_pos h, incCellPermAt, dif_pos h]
    exact umono_append (umono_single (umono_cx _ _ _)) (umono_rtof5 _ _ _ _ _ (by simp))
  · rw [incCellAt, dif_neg h, incCellPermAt, dif_neg h]
    exact umono_nil

/-! ### The fan-out cell at an offset -/

/-- `fan2` with control `o + 2` and targets `o + 1`, `o`.  Three CNOTs. -/
def fanAt (N o : ℕ) : List (Gate N) :=
  if h : o + 2 < N then
    fan2 ⟨o + 2, h⟩ ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (Or.inr rfl) (Or.inr rfl)
  else []

/-- The basis permutation of `fanAt`. -/
def fanPermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 2 < N then
    fanPerm ⟨o + 2, h⟩ ⟨o + 1, by omega⟩ ⟨o, by omega⟩ (by simp) (by simp)
  else 1

theorem cnots_fanAt (o : ℕ) (h : o + 2 < N) : cnots (fanAt N o) = 3 := by
  rw [fanAt, dif_pos h]
  rfl

theorem unitaryGates_fanAt (N o : ℕ) : UnitaryGates (fanAt N o) := by
  unfold fanAt
  split_ifs
  · exact unitaryGates_fan2 _ _ _ _ _
  · exact unitaryGates_nil

theorem umono_fanAt (N o : ℕ) : UMono (circMat (fanAt N o)) (fanPermAt N o) := by
  by_cases h : o + 2 < N
  · rw [fanAt, dif_pos h, fanPermAt, dif_pos h]
    exact umono_fan2 _ _ _ _ _
  · rw [fanAt, dif_neg h, fanPermAt, dif_neg h]
    exact umono_nil

/-! ### The two loops -/

/-- The first loop: the cells at offsets `1, 3, …, 2m - 1`, in this order. -/
noncomputable def incLoop (N : ℕ) : ℕ → List (Gate N)
  | 0 => []
  | m + 1 => incLoop N m ++ incCellAt N (2 * m + 1)

/-- The basis permutation of the first loop. -/
def incLoopPerm (N : ℕ) : ℕ → Equiv.Perm (St N)
  | 0 => 1
  | m + 1 => incCellPermAt N (2 * m + 1) * incLoopPerm N m

/-- The second loop: the fan-out cells at offsets `2m, 2m - 2, …, 2`, in this order. -/
def fanLoop (N : ℕ) : ℕ → List (Gate N)
  | 0 => []
  | m + 1 => fanAt N (2 * m + 2) ++ fanLoop N m

/-- The basis permutation of the second loop. -/
def fanLoopPerm (N : ℕ) : ℕ → Equiv.Perm (St N)
  | 0 => 1
  | m + 1 => fanLoopPerm N m * fanPermAt N (2 * m + 2)

theorem cnots_incLoop (m : ℕ) (h : 2 * m + 2 < N) : cnots (incLoop N m) = 6 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change cnots (incLoop N m ++ incCellAt N (2 * m + 1)) = _
    rw [cnots_append, ih (by omega), cnots_incCellAt _ (by omega)]
    ring

theorem cnots_fanLoop (m : ℕ) (h : 2 * m + 2 < N) : cnots (fanLoop N m) = 3 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change cnots (fanAt N (2 * m + 2) ++ fanLoop N m) = _
    rw [cnots_append, ih (by omega), cnots_fanAt _ (by omega)]
    ring

theorem unitaryGates_incLoop (N m : ℕ) : UnitaryGates (incLoop N m) := by
  induction m with
  | zero => exact unitaryGates_nil
  | succ m ih => exact unitaryGates_append ih (unitaryGates_incCellAt N _)

theorem unitaryGates_fanLoop (N m : ℕ) : UnitaryGates (fanLoop N m) := by
  induction m with
  | zero => exact unitaryGates_nil
  | succ m ih => exact unitaryGates_append (unitaryGates_fanAt N _) ih

theorem umono_incLoop (N m : ℕ) : UMono (circMat (incLoop N m)) (incLoopPerm N m) := by
  induction m with
  | zero => exact umono_nil
  | succ m ih => exact umono_append ih (umono_incCellAt N _)

theorem umono_fanLoop (N m : ℕ) : UMono (circMat (fanLoop N m)) (fanLoopPerm N m) := by
  induction m with
  | zero => exact umono_nil
  | succ m ih => exact umono_append (umono_fanAt N _) ih

/-! ### The closing CNOTs of `rest` and the terminal NOTs -/

theorem rest_ne {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    (⟨2, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
  intro e
  have e' : 2 = 1 := Fin.val_eq_of_eq e
  omega

/-- The two closing CNOTs: `cx S_0 T_0` and `cx S_{a-1} T_{a-1}`. -/
def restTail (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : List (Gate N) :=
  [.cx ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (Or.inr (by change 2 * a - 1 + 1 = 2 * a; omega)),
    .cx ⟨2, by omega⟩ ⟨1, by omega⟩ (Or.inr rfl)]

/-- The basis permutation of the closing CNOTs. -/
def restTailPerm (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : Equiv.Perm (St N) :=
  cxPerm ⟨2, by omega⟩ ⟨1, by omega⟩ (rest_ne h)
    * cxPerm ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (centre_ne h)

/-- A NOT on wire `q` (nothing if there is no such wire). -/
def xAt (N q : ℕ) : List (Gate N) := if h : q < N then [.one ⟨q, h⟩ xGate] else []

/-- The basis permutation of `xAt`. -/
def xPermAt (N q : ℕ) : Equiv.Perm (St N) := if h : q < N then xPerm ⟨q, h⟩ else 1

/-- NOTs on the wires `0, …, n - 1`. -/
def xsAt (N : ℕ) : ℕ → List (Gate N)
  | 0 => []
  | n + 1 => xsAt N n ++ xAt N n

/-- The basis permutation of `xsAt`. -/
def xsPerm (N : ℕ) : ℕ → Equiv.Perm (St N)
  | 0 => 1
  | n + 1 => xPermAt N n * xsPerm N n

theorem cnots_xAt (N q : ℕ) : cnots (xAt N q) = 0 := by
  unfold xAt
  split_ifs <;> rfl

theorem cnots_xsAt (N n : ℕ) : cnots (xsAt N n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cnots (xsAt N n ++ xAt N n) = 0
    rw [cnots_append, ih, cnots_xAt]

theorem unitaryGates_xAt (N q : ℕ) : UnitaryGates (xAt N q) := by
  unfold xAt
  split_ifs
  · exact unitaryGates_cons_one _ xGate_unitary unitaryGates_nil
  · exact unitaryGates_nil

theorem unitaryGates_xsAt (N n : ℕ) : UnitaryGates (xsAt N n) := by
  induction n with
  | zero => exact unitaryGates_nil
  | succ n ih => exact unitaryGates_append ih (unitaryGates_xAt N n)

theorem umono_xAt (N q : ℕ) : UMono (circMat (xAt N q)) (xPermAt N q) := by
  by_cases h : q < N
  · rw [xAt, dif_pos h, xPermAt, dif_pos h]
    exact umono_single (umono_x _)
  · rw [xAt, dif_neg h, xPermAt, dif_neg h]
    exact umono_nil

theorem umono_xsAt (N n : ℕ) : UMono (circMat (xsAt N n)) (xsPerm N n) := by
  induction n with
  | zero => exact umono_nil
  | succ n ih => exact umono_append ih (umono_xAt N n)

/-! ### `rest`, `terminal` and the low incrementer -/

/-- **The circuit `rest`**: the first loop, the second loop, the two closing CNOTs. -/
noncomputable def rest (N a : ℕ) : List (Gate N) :=
  if h : 2 ≤ a ∧ 2 * a < N then
    incLoop N (a - 1) ++ fanLoop N (a - 2) ++ restTail a h
  else []

/-- The basis permutation of `rest`, as the product of its parts. -/
def restPerm (N a : ℕ) : Equiv.Perm (St N) :=
  if h : 2 ≤ a ∧ 2 * a < N then
    restTailPerm a h * (fanLoopPerm N (a - 2) * incLoopPerm N (a - 1))
  else 1

/-- NOTs on the wires `0, …, 2a`. -/
def terminal (N a : ℕ) : List (Gate N) := xsAt N (2 * a + 1)

/-- **The low incrementer.** -/
noncomputable def lowInc (N a : ℕ) : List (Gate N) :=
  invCirc (rest N a) ++ centre N a ++ rest N a ++ terminal N a

/-- The basis permutation of the low incrementer, as the product of its parts. -/
def lowIncPerm (N a : ℕ) : Equiv.Perm (St N) :=
  xsPerm N (2 * a + 1) * (restPerm N a * (centrePerm N a * (restPerm N a)⁻¹))

/-- `rest` has `9 a - 10` CNOTs. -/
theorem cnots_rest {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) : cnots (rest N a) = 9 * a - 10 := by
  have h2 : cnots (restTail a h) = 2 := rfl
  rw [rest, dif_pos h, cnots_append, cnots_append, cnots_incLoop _ (by omega),
    cnots_fanLoop _ (by omega), h2]
  omega

theorem unitaryGates_rest (N a : ℕ) : UnitaryGates (rest N a) := by
  unfold rest
  split_ifs
  · exact unitaryGates_append
      (unitaryGates_append (unitaryGates_incLoop N _) (unitaryGates_fanLoop N _))
      (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _ unitaryGates_nil))
  · exact unitaryGates_nil

/-- **`rest` is a permutation up to phases.** -/
theorem umono_rest (N a : ℕ) : UMono (circMat (rest N a)) (restPerm N a) := by
  by_cases h : 2 ≤ a ∧ 2 * a < N
  · rw [rest, dif_pos h, restPerm, dif_pos h]
    exact umono_append (umono_append (umono_incLoop N _) (umono_fanLoop N _))
      (umono_cons (umono_cx _ _ _) (umono_single (umono_cx _ _ _)))
  · rw [rest, dif_neg h, restPerm, dif_neg h]
    exact umono_nil

/-- **The low incrementer has `24 a - 23` CNOTs.** -/
theorem cnots_lowInc {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) : cnots (lowInc N a) = 24 * a - 23 := by
  rw [lowInc, cnots_append, cnots_append, cnots_append, cnots_invCirc, cnots_rest h,
    cnots_centre h, terminal, cnots_xsAt]
  omega

/-- **The one-qubit gates of the low incrementer are unitary.** -/
theorem unitaryGates_lowInc (N a : ℕ) : UnitaryGates (lowInc N a) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_invCirc (unitaryGates_rest N a)) (unitaryGates_centre N a))
    (unitaryGates_rest N a)) (unitaryGates_xsAt N _)

/-- **The low incrementer is a permutation up to phases.** -/
theorem umono_lowInc (N a : ℕ) : UMono (circMat (lowInc N a)) (lowIncPerm N a) := by
  have hinv : UMono (circMat (invCirc (rest N a))) (restPerm N a)⁻¹ := by
    rw [circMat_invCirc]
    exact (umono_rest N a).conjTranspose
  exact umono_append (umono_append (umono_append hinv (umono_centre N a)) (umono_rest N a))
    (umono_xsAt N _)

end Line
