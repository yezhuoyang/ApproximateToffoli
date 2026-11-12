/-
The basis action of `rest` and of the centre circuit on the states `pqSt x a`.

Wires: `S_i = 2a - 2i` (`0 ≤ i ≤ a`), `T_i = 2a - 2i - 1` (`0 ≤ i < a`).  Carries:
`c_0 = 0`, `c_{i+1} = maj (S_i, T_i, c_i)`.  Three maps on basis states:

* `pqSt x a`: `T_i ↦ T_i ⊕ S_i` (`1 ≤ i < a`), `S_j ↦ S_j ⊕ c_j` (`1 ≤ j ≤ a`);
* `addSt x a`: `T_i ↦ T_i ⊕ S_i ⊕ c_i` (`0 ≤ i < a`), wire `0 ↦ x 0 ⊕ c_a`;
* `chiSt x a`: flip the wires `1, …, 2a`.

Results: `restPerm_pqSt : restPerm (pqSt x) = addSt x` and
`centrePerm_pqSt : centrePerm (pqSt x) = pqSt (chiSt x)`.
-/
import Mathlib
import ApproxToffoli.Line.LowIncWire
import ApproxToffoli.Line.LowIncArith

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### States from bits -/

/-- The basis state with bit `f j` on wire `j`. -/
def ofWires (f : ℕ → Bool) : St N := fun r => f r.val

theorem wire_ofWires (f : ℕ → Bool) (hf : ∀ j, N ≤ j → f j = false) (j : ℕ) :
    wire (ofWires f : St N) j = f j := by
  by_cases h : j < N
  · rw [wire_mk _ j h]
    rfl
  · unfold wire
    rw [dif_neg h, hf j (by omega)]

theorem wire_ge (x : St N) {j : ℕ} (h : N ≤ j) : wire x j = false := by
  unfold wire
  rw [dif_neg (by omega)]

/-! ### The bits `S_i`, `T_i` and the carries -/

/-- The bit `S_i`: wire `2a - 2i`. -/
def sBit (x : St N) (a i : ℕ) : Bool := wire x (2 * a - 2 * i)

/-- The bit `T_i`: wire `2a - 2i - 1`. -/
def tBit (x : St N) (a i : ℕ) : Bool := wire x (2 * a - 2 * i - 1)

/-- The carries of the addition `S + T`. -/
def cr (x : St N) (a : ℕ) : ℕ → Bool := gcarry (sBit x a) (tBit x a)

theorem cr_zero (x : St N) (a : ℕ) : cr x a 0 = false := rfl

theorem cr_succ (x : St N) (a i : ℕ) :
    cr x a (i + 1) = maj (sBit x a i) (tBit x a i) (cr x a i) := rfl

/-! ### The map `PQ` -/

/-- The bit of `pqSt x a` on wire `j`. -/
def pqBit (x : St N) (a j : ℕ) : Bool :=
  if j ≤ 2 * a - 2 then
    (if j % 2 = 1 then xor (wire x j) (wire x (j + 1))
      else xor (wire x j) (cr x a (a - j / 2)))
  else wire x j

/-- The state `PQ x`: `T_i ↦ T_i ⊕ S_i` for `1 ≤ i < a`, `S_j ↦ S_j ⊕ c_j` for
`1 ≤ j ≤ a`. -/
def pqSt (x : St N) (a : ℕ) : St N := ofWires (pqBit x a)

theorem wire_pqSt {a : ℕ} (h : 2 * a < N) (x : St N) (j : ℕ) :
    wire (pqSt x a) j = pqBit x a j := by
  refine wire_ofWires _ (fun i hi => ?_) j
  rw [pqBit, if_neg (by omega), wire_ge x hi]

theorem pqSt_odd {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : j ≤ 2 * a - 2)
    (ho : j % 2 = 1) : wire (pqSt x a) j = xor (wire x j) (wire x (j + 1)) := by
  rw [wire_pqSt h, pqBit, if_pos hj, if_pos ho]

theorem pqSt_even {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : j ≤ 2 * a - 2)
    (he : ¬ j % 2 = 1) : wire (pqSt x a) j = xor (wire x j) (cr x a (a - j / 2)) := by
  rw [wire_pqSt h, pqBit, if_pos hj, if_neg he]

theorem pqSt_top {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : ¬ j ≤ 2 * a - 2) :
    wire (pqSt x a) j = wire x j := by
  rw [wire_pqSt h, pqBit, if_neg hj]

/-! ### The map `Add` -/

/-- The bit of `addSt x a` on wire `j`. -/
def addBit (x : St N) (a j : ℕ) : Bool :=
  if j = 0 then xor (wire x 0) (cr x a a)
  else if j ≤ 2 * a ∧ j % 2 = 1 then
    xor (xor (wire x (j + 1)) (wire x j)) (cr x a (a - 1 - j / 2))
  else wire x j

/-- The state `Add x`: `T_i ↦ T_i ⊕ S_i ⊕ c_i` for `i < a`, wire `0 ↦ x 0 ⊕ c_a`. -/
def addSt (x : St N) (a : ℕ) : St N := ofWires (addBit x a)

theorem wire_addSt {a : ℕ} (h : 2 * a < N) (x : St N) (j : ℕ) :
    wire (addSt x a) j = addBit x a j := by
  refine wire_ofWires _ (fun i hi => ?_) j
  rw [addBit, if_neg (by omega), if_neg (by omega), wire_ge x hi]

theorem addSt_zero {a : ℕ} (h : 2 * a < N) (x : St N) :
    wire (addSt x a) 0 = xor (wire x 0) (cr x a a) := by
  rw [wire_addSt h, addBit, if_pos rfl]

theorem addSt_odd {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : j ≤ 2 * a)
    (ho : j % 2 = 1) :
    wire (addSt x a) j = xor (xor (wire x (j + 1)) (wire x j)) (cr x a (a - 1 - j / 2)) := by
  rw [wire_addSt h, addBit, if_neg (by omega), if_pos ⟨hj, ho⟩]

theorem addSt_other {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (h0 : j ≠ 0)
    (hj : ¬ (j ≤ 2 * a ∧ j % 2 = 1)) : wire (addSt x a) j = wire x j := by
  rw [wire_addSt h, addBit, if_neg h0, if_neg hj]

/-! ### The map `χ` -/

/-- The bit of `chiSt x a` on wire `j`. -/
def chiBit (x : St N) (a j : ℕ) : Bool :=
  if 1 ≤ j ∧ j ≤ 2 * a then !wire x j else wire x j

/-- The state `χ x`: the wires `1, …, 2a` are flipped. -/
def chiSt (x : St N) (a : ℕ) : St N := ofWires (chiBit x a)

theorem wire_chiSt {a : ℕ} (h : 2 * a < N) (x : St N) (j : ℕ) :
    wire (chiSt x a) j = chiBit x a j := by
  refine wire_ofWires _ (fun i hi => ?_) j
  rw [chiBit, if_neg (by omega), wire_ge x hi]

theorem chiSt_in {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 2 * a) :
    wire (chiSt x a) j = !wire x j := by
  rw [wire_chiSt h, chiBit, if_pos ⟨h1, h2⟩]

theorem chiSt_out {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : ¬ (1 ≤ j ∧ j ≤ 2 * a)) :
    wire (chiSt x a) j = wire x j := by
  rw [wire_chiSt h, chiBit, if_neg hj]

/-! ### The closed forms of the loops, case by case -/

theorem incLoopSpec_odd (x : St N) {m j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 2 * m) (ho : j % 2 = 1) :
    incLoopSpec x m j = xor (wire x j) (wire x (j + 1)) := by
  rw [incLoopSpec, if_pos ⟨h1, h2⟩, if_pos ho]

theorem incLoopSpec_even (x : St N) {m j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 2 * m)
    (he : ¬ j % 2 = 1) :
    incLoopSpec x m j = xor (wire x j) (wire x (j + 2) && wire x (j + 1)) := by
  rw [incLoopSpec, if_pos ⟨h1, h2⟩, if_neg he]

theorem incLoopSpec_out (x : St N) {m j : ℕ} (h : ¬ (1 ≤ j ∧ j ≤ 2 * m)) :
    incLoopSpec x m j = wire x j := by
  rw [incLoopSpec, if_neg h]

theorem fanLoopInvSpec_even (w : St N) {m j : ℕ} (h1 : 2 ≤ j) (h2 : j ≤ 2 * m + 1)
    (he : j % 2 = 0) : fanLoopInvSpec w m j = xor (wire w j) (wire w (j + 2)) := by
  rw [fanLoopInvSpec, if_pos ⟨h1, h2⟩, if_pos he]

theorem fanLoopInvSpec_odd (w : St N) {m j : ℕ} (h1 : 2 ≤ j) (h2 : j ≤ 2 * m + 1)
    (ho : ¬ j % 2 = 0) : fanLoopInvSpec w m j = xor (wire w j) (wire w (j + 1)) := by
  rw [fanLoopInvSpec, if_pos ⟨h1, h2⟩, if_neg ho]

theorem fanLoopInvSpec_out (w : St N) {m j : ℕ} (h : ¬ (2 ≤ j ∧ j ≤ 2 * m + 1)) :
    fanLoopInvSpec w m j = wire w j := by
  rw [fanLoopInvSpec, if_neg h]

/-! ### The closing CNOTs on `Add x` -/

section tailAdd

variable {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N)
include h

theorem tailAdd_zero : wire (restTailPerm a h (addSt x a)) 0 = xor (wire x 0) (cr x a a) := by
  rw [restTailPerm_wire h, if_neg (by omega), if_neg (by omega), addSt_zero h.2]

theorem tailAdd_one :
    wire (restTailPerm a h (addSt x a)) 1 = xor (wire x 1) (cr x a (a - 1)) := by
  have e : ∀ u v c : Bool, xor (xor (xor u v) c) u = xor v c := by decide
  have hA1 : wire (addSt x a) 1 = xor (xor (wire x 2) (wire x 1)) (cr x a (a - 1)) :=
    addSt_odd h.2 x (by omega) (by omega)
  rw [restTailPerm_wire h, if_pos rfl, hA1, addSt_other h.2 x (j := 2) (by omega) (by omega), e]

theorem tailAdd_top :
    wire (restTailPerm a h (addSt x a)) (2 * a - 1) = wire x (2 * a - 1) := by
  have e : ∀ u v : Bool, xor (xor (xor u v) false) u = v := by decide
  have e1 : 2 * a - 1 + 1 = 2 * a := by omega
  have e2 : a - 1 - (2 * a - 1) / 2 = 0 := by omega
  rw [restTailPerm_wire h, if_neg (by omega), if_pos rfl,
    addSt_odd h.2 x (j := 2 * a - 1) (by omega) (by omega),
    addSt_other h.2 x (j := 2 * a) (by omega) (by omega), e1, e2, cr_zero, e]

/-- The odd wires `3 ≤ j ≤ 2a - 3` are those of `Add x`. -/
theorem tailAdd_odd {j : ℕ} (h3 : 3 ≤ j) (hj : j ≤ 2 * a - 3) (ho : j % 2 = 1) :
    wire (restTailPerm a h (addSt x a)) j
      = xor (xor (wire x (j + 1)) (wire x j)) (cr x a (a - 1 - j / 2)) := by
  rw [restTailPerm_wire h, if_neg (by omega), if_neg (by omega),
    addSt_odd h.2 x (by omega) ho]

/-- The even wires `≥ 2` and the wires above `2a` are those of `x`. -/
theorem tailAdd_other {j : ℕ} (h0 : j ≠ 0) (hj : ¬ (j ≤ 2 * a ∧ j % 2 = 1)) :
    wire (restTailPerm a h (addSt x a)) j = wire x j := by
  rw [restTailPerm_wire h, if_neg (by omega), if_neg (by omega), addSt_other h.2 x h0 hj]

end tailAdd

/-! ### (i) `rest` sends `PQ x` to `Add x` -/

/-- The first loop on `PQ x` is the inverse of the second loop on the closing CNOTs of
`Add x`. -/
theorem incLoopPerm_pqSt {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) :
    incLoopPerm N (a - 1) (pqSt x a)
      = (fanLoopPerm N (a - 2))⁻¹ (restTailPerm a h (addSt x a)) := by
  have ha := h.1
  have hN := h.2
  apply wire_ext
  intro j
  rw [incLoopPerm_wire _ (by omega), fanLoopPerm_inv_wire _ (by omega)]
  by_cases h0 : j = 0
  · rw [h0, incLoopSpec_out _ (by omega), fanLoopInvSpec_out _ (by omega),
      pqSt_even hN x (by omega) (by omega), tailAdd_zero h]
    rfl
  by_cases hF : 2 * a ≤ j
  · rw [incLoopSpec_out _ (by omega), fanLoopInvSpec_out _ (by omega),
      pqSt_top hN x (by omega), tailAdd_other h x h0 (by omega)]
  by_cases hE : j = 2 * a - 1
  · rw [hE, incLoopSpec_out _ (by omega), fanLoopInvSpec_out _ (by omega),
      pqSt_top hN x (by omega), tailAdd_top h]
  by_cases hD : j = 2 * a - 2
  · have e : ∀ u s t : Bool, xor (xor u (maj s t false)) (s && t) = u := by decide
    have e1 : a - j / 2 = 0 + 1 := by omega
    have e2 : 2 * a - 2 * 0 = j + 2 := by omega
    have e3 : 2 * a - 2 * 0 - 1 = j + 1 := by omega
    rw [incLoopSpec_even _ (by omega) (by omega) (by omega), fanLoopInvSpec_out _ (by omega),
      pqSt_even hN x (j := j) (by omega) (by omega), pqSt_top hN x (j := j + 2) (by omega),
      pqSt_top hN x (j := j + 1) (by omega), tailAdd_other h x h0 (by omega), e1, cr_succ,
      cr_zero, sBit, tBit, e3, e2, e]
  by_cases ho : j % 2 = 1
  · have e1 : a - (j + 1) / 2 = a - 1 - j / 2 := by omega
    rw [incLoopSpec_odd _ (by omega) (by omega) ho, pqSt_odd hN x (j := j) (by omega) ho,
      pqSt_even hN x (j := j + 1) (by omega) (by omega), e1]
    by_cases h1 : j = 1
    · have e : ∀ u v c : Bool, xor (xor u v) (xor v c) = xor u c := by decide
      rw [h1, fanLoopInvSpec_out _ (by omega), tailAdd_one h, e]
      rfl
    · have e : ∀ u v c : Bool, xor (xor u v) (xor v c) = xor (xor (xor v u) c) v := by decide
      rw [fanLoopInvSpec_odd _ (by omega) (by omega) (by omega),
        tailAdd_odd h x (j := j) (by omega) (by omega) ho,
        tailAdd_other h x (j := j + 1) (by omega) (by omega)]
      exact e _ _ _
  · have e : ∀ u s t c : Bool, xor (xor u (maj s t c)) (xor s c && xor t s) = xor u s := by
      decide
    have e1 : a - j / 2 = (a - (j + 2) / 2) + 1 := by omega
    have e2 : 2 * a - 2 * (a - (j + 2) / 2) = j + 2 := by omega
    have e3 : 2 * a - 2 * (a - (j + 2) / 2) - 1 = j + 1 := by omega
    have e4 : j + 1 + 1 = j + 2 := rfl
    rw [incLoopSpec_even _ (by omega) (by omega) ho,
      fanLoopInvSpec_even _ (by omega) (by omega) (by omega),
      pqSt_even hN x (j := j) (by omega) ho, pqSt_even hN x (j := j + 2) (by omega) (by omega),
      pqSt_odd hN x (j := j + 1) (by omega) (by omega),
      tailAdd_other h x (j := j) h0 (by omega), tailAdd_other h x (j := j + 2) (by omega)
        (by omega), e4, e1, cr_succ, sBit, tBit, e3, e2]
    exact e _ _ _ _

/-- **(i)** `rest` sends `PQ x` to `Add x`. -/
theorem restPerm_pqSt {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) :
    restPerm N a (pqSt x a) = addSt x a :=
  restPerm_eq_of h (incLoopPerm_pqSt h x)

end Line
