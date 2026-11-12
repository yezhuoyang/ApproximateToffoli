/-
The parts of the low incrementer on basis states, wire by wire.

* `incLoopPerm_wire`: the first loop of `rest` in closed form.
* `fanLoopPerm_inv_wire`: the INVERSE of the second loop of `rest` in closed form.
* `restTailPerm_wire`, `xsPerm_wire`: the closing CNOTs and the terminal NOTs.
-/
import Mathlib
import ApproxToffoli.Line.LowInc

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The first loop -/

/-- The first cell: wire `o` gets `⊕ (o+1)`, wire `o + 1` gets `⊕ (o+3) ∧ (o+2)`. -/
theorem incCellPermAt_wire (o : ℕ) (h : o + 3 < N) (x : St N) (j : ℕ) :
    wire (incCellPermAt N o x) j
      = if j = o + 1 then xor (wire x (o + 1)) (wire x (o + 3) && wire x (o + 2))
        else if j = o then xor (wire x o) (wire x (o + 1)) else wire x j := by
  have n1 : (⟨o + 1, by omega⟩ : Fin N) ≠ ⟨o, by omega⟩ := by simp
  have n2 : (⟨o + 2, by omega⟩ : Fin N) ≠ ⟨o, by omega⟩ := by simp
  have n3 : (⟨o + 3, h⟩ : Fin N) ≠ ⟨o, by omega⟩ := by simp
  rw [incCellPermAt, dif_pos h, Equiv.Perm.mul_apply, ccPerm_apply, cxPerm_apply, wire_update,
    wire_update, Function.update_of_ne n1, Function.update_of_ne n2, Function.update_of_ne n3,
    wire_mk x o (by omega), wire_mk x (o + 1) (by omega), wire_mk x (o + 2) (by omega),
    wire_mk x (o + 3) h]

/-- The bit on wire `j` after the first loop with `m` cells: the odd wires `j ≤ 2m` get
`⊕ (j+1)`, the even wires `2 ≤ j ≤ 2m` get `⊕ (j+2) ∧ (j+1)`. -/
def incLoopSpec (x : St N) (m j : ℕ) : Bool :=
  if 1 ≤ j ∧ j ≤ 2 * m then
    (if j % 2 = 1 then xor (wire x j) (wire x (j + 1))
      else xor (wire x j) (wire x (j + 2) && wire x (j + 1)))
  else wire x j

/-- **Basis action of the first loop.** -/
theorem incLoopPerm_wire (m : ℕ) (h : 2 * m + 2 < N) (x : St N) (j : ℕ) :
    wire (incLoopPerm N m x) j = incLoopSpec x m j := by
  induction m generalizing j with
  | zero =>
    have h0 : ¬ (1 ≤ j ∧ j ≤ 2 * 0) := by omega
    rw [incLoopSpec, if_neg h0]
    rfl
  | succ m ih =>
    have ih' := ih (by omega)
    have hgt : ∀ i, 2 * m < i → wire (incLoopPerm N m x) i = wire x i := by
      intro i hi
      rw [ih', incLoopSpec, if_neg (by omega)]
    change wire (incCellPermAt N (2 * m + 1) (incLoopPerm N m x)) j = _
    rw [incCellPermAt_wire _ (by omega), incLoopSpec]
    by_cases h1 : j = 2 * m + 1 + 1
    · rw [if_pos h1, if_pos (by omega), if_neg (by omega), hgt _ (by omega),
        hgt _ (by omega), hgt _ (by omega), h1]
    · by_cases h2 : j = 2 * m + 1
      · rw [if_neg h1, if_pos h2, if_pos (by omega), if_pos (by omega), hgt _ (by omega),
          hgt _ (by omega), h2]
      · have hc : (1 ≤ j ∧ j ≤ 2 * (m + 1)) ↔ (1 ≤ j ∧ j ≤ 2 * m) := by omega
        rw [if_neg h1, if_neg h2, ih', incLoopSpec]
        simp only [hc]

/-! ### The second loop -/

/-- The fan-out cell: wires `o` and `o + 1` get `⊕ (o+2)`. -/
theorem fanPermAt_wire (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) :
    wire (fanPermAt N o x) j
      = if j = o then xor (wire x o) (wire x (o + 2))
        else if j = o + 1 then xor (wire x (o + 1)) (wire x (o + 2)) else wire x j := by
  rw [fanPermAt, dif_pos h, fanPerm_apply _ _ _ _ _ (by simp), wire_update, wire_update,
    wire_mk x o (by omega), wire_mk x (o + 1) (by omega), wire_mk x (o + 2) h]

/-- The fan-out cell is its own inverse. -/
theorem fanPermAt_inv (N o : ℕ) : (fanPermAt N o)⁻¹ = fanPermAt N o := by
  have e : ∀ u v : Bool, xor (xor u v) v = u := by decide
  by_cases h : o + 2 < N
  · rw [inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one]
    apply Equiv.ext
    intro x
    apply wire_ext
    intro j
    have hx := fanPermAt_wire o h x
    have y0 : wire (fanPermAt N o x) o = xor (wire x o) (wire x (o + 2)) := by
      rw [hx, if_pos rfl]
    have y1 : wire (fanPermAt N o x) (o + 1) = xor (wire x (o + 1)) (wire x (o + 2)) := by
      rw [hx, if_neg (by omega), if_pos rfl]
    have y2 : wire (fanPermAt N o x) (o + 2) = wire x (o + 2) := by
      rw [hx, if_neg (by omega), if_neg (by omega)]
    rw [Equiv.Perm.mul_apply, fanPermAt_wire o h (fanPermAt N o x) j, y0, y1, y2, e, e]
    change _ = wire x j
    by_cases h0 : j = o
    · rw [if_pos h0, h0]
    · by_cases h1 : j = o + 1
      · rw [if_neg h0, if_pos h1, h1]
      · rw [if_neg h0, if_neg h1, hx, if_neg h0, if_neg h1]
  · rw [fanPermAt, dif_neg h, inv_one]

/-- The bit on wire `j` after the inverse of the second loop with `m` cells: the even
wires `2 ≤ j ≤ 2m` get `⊕ (j+2)`, the odd wires `3 ≤ j ≤ 2m + 1` get `⊕ (j+1)`. -/
def fanLoopInvSpec (w : St N) (m j : ℕ) : Bool :=
  if 2 ≤ j ∧ j ≤ 2 * m + 1 then
    (if j % 2 = 0 then xor (wire w j) (wire w (j + 2)) else xor (wire w j) (wire w (j + 1)))
  else wire w j

/-- **Basis action of the inverse of the second loop.** -/
theorem fanLoopPerm_inv_wire (m : ℕ) (h : 2 * m + 2 < N) (w : St N) (j : ℕ) :
    wire ((fanLoopPerm N m)⁻¹ w) j = fanLoopInvSpec w m j := by
  induction m generalizing j with
  | zero =>
    have h0 : ¬ (2 ≤ j ∧ j ≤ 2 * 0 + 1) := by omega
    rw [fanLoopInvSpec, if_neg h0]
    rfl
  | succ m ih =>
    have ih' := ih (by omega)
    have hgt : ∀ i, 2 * m + 1 < i → wire ((fanLoopPerm N m)⁻¹ w) i = wire w i := by
      intro i hi
      rw [ih', fanLoopInvSpec, if_neg (by omega)]
    have hp : (fanLoopPerm N (m + 1))⁻¹ = fanPermAt N (2 * m + 2) * (fanLoopPerm N m)⁻¹ := by
      change (fanLoopPerm N m * fanPermAt N (2 * m + 2))⁻¹ = _
      rw [_root_.mul_inv_rev, fanPermAt_inv]
    rw [hp, Equiv.Perm.mul_apply, fanPermAt_wire _ (by omega), fanLoopInvSpec]
    by_cases h1 : j = 2 * m + 2
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega), hgt _ (by omega),
        hgt _ (by omega), h1]
    · by_cases h2 : j = 2 * m + 2 + 1
      · rw [if_neg h1, if_pos h2, if_pos (by omega), if_neg (by omega), hgt _ (by omega),
          hgt _ (by omega), h2]
      · have hc : (2 ≤ j ∧ j ≤ 2 * (m + 1) + 1) ↔ (2 ≤ j ∧ j ≤ 2 * m + 1) := by omega
        rw [if_neg h1, if_neg h2, ih', fanLoopInvSpec]
        simp only [hc]

/-! ### The closing CNOTs and the terminal NOTs -/

/-- The closing CNOTs: wire `1` gets `⊕ 2`, wire `2a - 1` gets `⊕ 2a`. -/
theorem restTailPerm_wire {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) (j : ℕ) :
    wire (restTailPerm a h x) j
      = if j = 1 then xor (wire x 1) (wire x 2)
        else if j = 2 * a - 1 then xor (wire x (2 * a - 1)) (wire x (2 * a)) else wire x j := by
  have n1 : (⟨1, by omega⟩ : Fin N) ≠ ⟨2 * a - 1, by omega⟩ := by
    intro e
    have e' : 1 = 2 * a - 1 := Fin.val_eq_of_eq e
    omega
  have n2 : (⟨2, by omega⟩ : Fin N) ≠ ⟨2 * a - 1, by omega⟩ := by
    intro e
    have e' : 2 = 2 * a - 1 := Fin.val_eq_of_eq e
    omega
  rw [restTailPerm, Equiv.Perm.mul_apply, cxPerm_apply, cxPerm_apply, wire_update, wire_update,
    Function.update_of_ne n1, Function.update_of_ne n2, wire_mk x 1 (by omega),
    wire_mk x 2 (by omega), wire_mk x (2 * a - 1) (by omega), wire_mk x (2 * a) h.2]

/-- The closing CNOTs are their own inverse. -/
theorem restTailPerm_restTailPerm {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) :
    restTailPerm a h (restTailPerm a h x) = x := by
  have e : ∀ u v : Bool, xor (xor u v) v = u := by decide
  have hx := restTailPerm_wire h x
  have y1 : wire (restTailPerm a h x) 1 = xor (wire x 1) (wire x 2) := by
    rw [hx, if_pos rfl]
  have y2 : wire (restTailPerm a h x) 2 = wire x 2 := by
    rw [hx, if_neg (by omega), if_neg (by omega)]
  have y3 : wire (restTailPerm a h x) (2 * a - 1) = xor (wire x (2 * a - 1)) (wire x (2 * a)) := by
    rw [hx, if_neg (by omega), if_pos rfl]
  have y4 : wire (restTailPerm a h x) (2 * a) = wire x (2 * a) := by
    rw [hx, if_neg (by omega), if_neg (by omega)]
  apply wire_ext
  intro j
  rw [restTailPerm_wire h (restTailPerm a h x) j, y1, y2, y3, y4, e, e]
  by_cases h0 : j = 1
  · rw [if_pos h0, h0]
  · by_cases h1 : j = 2 * a - 1
    · rw [if_neg h0, if_pos h1, h1]
    · rw [if_neg h0, if_neg h1, hx, if_neg h0, if_neg h1]

theorem xPermAt_wire (q : ℕ) (h : q < N) (x : St N) (j : ℕ) :
    wire (xPermAt N q x) j = if j = q then !wire x q else wire x j := by
  rw [xPermAt, dif_pos h, xPerm_apply, wire_update, wire_mk x q h]

/-- **Basis action of the terminal NOTs**: the wires `< n` are flipped. -/
theorem xsPerm_wire (n : ℕ) (h : n ≤ N) (x : St N) (j : ℕ) :
    wire (xsPerm N n x) j = if j < n then !wire x j else wire x j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (by omega)
    change wire (xPermAt N n (xsPerm N n x)) j = _
    rw [xPermAt_wire n (by omega)]
    by_cases h0 : j = n
    · rw [if_pos h0, if_pos (by omega), ih', if_neg (by omega), h0]
    · rw [if_neg h0, ih']
      by_cases h1 : j < n
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-! ### `rest` from its parts -/

/-- To show `restPerm y = w` it is enough to compare the first loop on `y` with the
inverse of the second loop on the closing CNOTs of `w`; both have closed forms. -/
theorem restPerm_eq_of {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) {y w : St N}
    (hyw : incLoopPerm N (a - 1) y = (fanLoopPerm N (a - 2))⁻¹ (restTailPerm a h w)) :
    restPerm N a y = w := by
  rw [restPerm, dif_pos h]
  change restTailPerm a h (fanLoopPerm N (a - 2) (incLoopPerm N (a - 1) y)) = w
  have e : fanLoopPerm N (a - 2) ((fanLoopPerm N (a - 2))⁻¹ (restTailPerm a h w))
      = restTailPerm a h w := Equiv.apply_symm_apply _ _
  rw [hyw, e, restTailPerm_restTailPerm]

end Line
