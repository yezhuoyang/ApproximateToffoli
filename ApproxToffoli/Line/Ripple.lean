/-
The ripple-carry adder on a line.

Wire `0` holds the carry-in `b`; wires `2i+1` hold the addend bits `u_i` and wires
`2i+2` the target bits `h_i` (`i < k`); the top target bit is on wire `2k+1`
(`gap = false`) or `2k+2` (`gap = true`, wire `2k+1` is then left unchanged).

    rippleAt o 0 gap       = copy wire `o` onto the top wire
    rippleAt o (k+1) gap   = fwdCell(o, o+1, o+2) ++ rippleAt (o+2) k gap ++ revCell(o, o+1, o+2)

`ripple k gap = rippleAt 0 k gap` has `13 k + 1` (resp. `13 k + 4`) CNOTs and is, up to
phases of modulus one, the permutation that adds `u + b` to the target register.
-/
import Mathlib
import ApproxToffoli.Line.Carry

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The cells at a natural-number offset -/

/-- The forward cell on wires `o, o+1, o+2` (empty if the line is too short). -/
noncomputable def fwdAt (N o : ℕ) : List (Gate N) :=
  if h : o + 2 < N then
    fwdCell ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ rfl rfl
  else []

/-- The basis permutation of `fwdAt`. -/
def fwdPermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 2 < N then
    fwdPerm ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ rfl rfl
  else 1

/-- The reverse cell on wires `o, o+1, o+2` (empty if the line is too short). -/
noncomputable def revAt (N o : ℕ) : List (Gate N) :=
  if h : o + 2 < N then
    revCell ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ rfl rfl
  else []

/-- The basis permutation of `revAt`. -/
def revPermAt (N o : ℕ) : Equiv.Perm (St N) :=
  if h : o + 2 < N then
    revPerm ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ rfl rfl
  else 1

theorem umono_fwdAt (N o : ℕ) : UMono (circMat (fwdAt N o)) (fwdPermAt N o) := by
  by_cases h : o + 2 < N
  · rw [fwdAt, dif_pos h, fwdPermAt, dif_pos h]
    exact umono_fwdCell _ _ _ _ _
  · rw [fwdAt, dif_neg h, fwdPermAt, dif_neg h]
    exact umono_nil

theorem umono_revAt (N o : ℕ) : UMono (circMat (revAt N o)) (revPermAt N o) := by
  by_cases h : o + 2 < N
  · rw [revAt, dif_pos h, revPermAt, dif_pos h]
    exact umono_revCell _ _ _ _ _
  · rw [revAt, dif_neg h, revPermAt, dif_neg h]
    exact umono_nil

theorem cnots_fwdAt (o : ℕ) (h : o + 2 < N) : cnots (fwdAt N o) = 6 := by
  rw [fwdAt, dif_pos h]
  rfl

theorem cnots_revAt (o : ℕ) (h : o + 2 < N) : cnots (revAt N o) = 7 := by
  rw [revAt, dif_pos h]
  rfl

theorem unitaryGates_fwdAt (N o : ℕ) : UnitaryGates (fwdAt N o) := by
  unfold fwdAt
  split_ifs
  · exact unitaryGates_fwdCell _ _ _ _ _
  · exact unitaryGates_nil

theorem unitaryGates_revAt (N o : ℕ) : UnitaryGates (revAt N o) := by
  unfold revAt
  split_ifs
  · exact unitaryGates_revCell _ _ _ _ _
  · exact unitaryGates_nil

/-- Wire form of the forward cell. -/
theorem wire_fwdPermAt (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) :
    wire (fwdPermAt N o x) j
      = if j = o + 2 then maj (wire x o) (wire x (o + 1)) (wire x (o + 2))
        else if j = o + 1 then
          xor (xor (wire x (o + 1)) (wire x (o + 2)))
            (maj (wire x o) (wire x (o + 1)) (wire x (o + 2)))
        else if j = o then xor (wire x o) (wire x (o + 1)) else wire x j := by
  rw [fwdPermAt, dif_pos h, fwdPerm_apply, wire_upd3, wire_mk x o (by omega),
    wire_mk x (o + 1) (by omega), wire_mk x (o + 2) h]

/-- Wire form of the reverse cell. -/
theorem wire_revPermAt (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) :
    wire (revPermAt N o x) j
      = if j = o + 2 then rev2 (wire x o) (wire x (o + 1)) (wire x (o + 2))
        else if j = o + 1 then rev1 (wire x o) (wire x (o + 1)) (wire x (o + 2))
        else if j = o then rev0 (wire x o) (wire x (o + 1)) (wire x (o + 2)) else wire x j := by
  rw [revPermAt, dif_pos h, revPerm_apply, wire_upd3, wire_mk x o (by omega),
    wire_mk x (o + 1) (by omega), wire_mk x (o + 2) h]

theorem wire_fwdPermAt_gt (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) (hj : o + 2 < j) :
    wire (fwdPermAt N o x) j = wire x j := by
  rw [wire_fwdPermAt o h, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem wire_fwdPermAt_lt (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) (hj : j < o) :
    wire (fwdPermAt N o x) j = wire x j := by
  rw [wire_fwdPermAt o h, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem wire_fwdPermAt_0 (o : ℕ) (h : o + 2 < N) (x : St N) :
    wire (fwdPermAt N o x) o = xor (wire x o) (wire x (o + 1)) := by
  rw [wire_fwdPermAt o h, if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem wire_fwdPermAt_1 (o : ℕ) (h : o + 2 < N) (x : St N) :
    wire (fwdPermAt N o x) (o + 1)
      = xor (xor (wire x (o + 1)) (wire x (o + 2)))
          (maj (wire x o) (wire x (o + 1)) (wire x (o + 2))) := by
  rw [wire_fwdPermAt o h, if_neg (by omega), if_pos rfl]

theorem wire_fwdPermAt_2 (o : ℕ) (h : o + 2 < N) (x : St N) :
    wire (fwdPermAt N o x) (o + 2) = maj (wire x o) (wire x (o + 1)) (wire x (o + 2)) := by
  rw [wire_fwdPermAt o h, if_pos rfl]

/-! ### The copy -/

/-- The copy at offset `o`: flip the top wire (`o + 1`, or `o + 2` when `gap`) iff wire
`o` holds a one.  With a gap it is four CNOTs that restore wire `o + 1`. -/
def copyAt (N o : ℕ) : Bool → List (Gate N)
  | false => if h : o + 1 < N then [.cx ⟨o, by omega⟩ ⟨o + 1, h⟩ (Or.inl rfl)] else []
  | true =>
    if h : o + 2 < N then
      [.cx ⟨o, by omega⟩ ⟨o + 1, by omega⟩ (Or.inl rfl),
       .cx ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ (Or.inl rfl),
       .cx ⟨o, by omega⟩ ⟨o + 1, by omega⟩ (Or.inl rfl),
       .cx ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ (Or.inl rfl)]
    else []

/-- The basis permutation of `copyAt`. -/
def copyPermAt (N o : ℕ) : Bool → Equiv.Perm (St N)
  | false =>
    if h : o + 1 < N then
      cxPerm ⟨o, by omega⟩ ⟨o + 1, h⟩ (adj_ne (Or.inl rfl))
    else 1
  | true =>
    if h : o + 2 < N then
      ((cxPerm ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ (adj_ne (Or.inl rfl))
          * cxPerm ⟨o, by omega⟩ ⟨o + 1, by omega⟩ (adj_ne (Or.inl rfl)))
        * cxPerm ⟨o + 1, by omega⟩ ⟨o + 2, h⟩ (adj_ne (Or.inl rfl)))
      * cxPerm ⟨o, by omega⟩ ⟨o + 1, by omega⟩ (adj_ne (Or.inl rfl))
    else 1

theorem umono_copyAt (N o : ℕ) (gap : Bool) :
    UMono (circMat (copyAt N o gap)) (copyPermAt N o gap) := by
  cases gap
  · by_cases h : o + 1 < N
    · rw [copyAt, dif_pos h, copyPermAt, dif_pos h]
      exact umono_single (umono_cx _ _ _)
    · rw [copyAt, dif_neg h, copyPermAt, dif_neg h]
      exact umono_nil
  · by_cases h : o + 2 < N
    · rw [copyAt, dif_pos h, copyPermAt, dif_pos h]
      exact umono_cons (umono_cx _ _ _) (umono_cons (umono_cx _ _ _)
        (umono_cons (umono_cx _ _ _) (umono_single (umono_cx _ _ _))))
    · rw [copyAt, dif_neg h, copyPermAt, dif_neg h]
      exact umono_nil

theorem cnots_copyAt (o : ℕ) (gap : Bool) (h : o + 1 + gap.toNat < N) :
    cnots (copyAt N o gap) = 1 + 3 * gap.toNat := by
  cases gap
  · have h1 : o + 1 < N := h
    rw [copyAt, dif_pos h1]
    rfl
  · have h2 : o + 2 < N := h
    rw [copyAt, dif_pos h2]
    rfl

theorem unitaryGates_copyAt (N o : ℕ) (gap : Bool) : UnitaryGates (copyAt N o gap) := by
  cases gap <;> rw [copyAt] <;> split_ifs <;>
    repeat first
      | exact unitaryGates_nil
      | apply unitaryGates_cons_cx

/-- Four CNOTs on three wires flip `q2` iff `q0` holds a one and restore `q1`. -/
theorem copy4_apply (q0 q1 q2 : Fin N) (n01 : q0 ≠ q1) (n12 : q1 ≠ q2) (n02 : q0 ≠ q2)
    (x : St N) :
    (((cxPerm q1 q2 n12 * cxPerm q0 q1 n01) * cxPerm q1 q2 n12) * cxPerm q0 q1 n01) x
      = Function.update x q2 (xor (x q2) (x q0)) := by
  have key : ∀ a b c : Bool,
      (((cxPerm q1 q2 n12 * cxPerm q0 q1 n01) * cxPerm q1 q2 n12) * cxPerm q0 q1 n01)
          (upd3 q0 q1 q2 x a b c)
        = upd3 q0 q1 q2 x a b (xor c a) := by
    intro a b c
    simp only [Equiv.Perm.mul_apply, cxPerm_apply, upd3_get0 n01 n02, upd3_get1 n12,
      upd3_get2, upd3_set1 n12, upd3_set2]
    cases a <;> cases b <;> cases c <;> rfl
  have h := key (x q0) (x q1) (x q2)
  rwa [upd3_self, upd3_eq_update] at h

/-- Wire form of the copy: the top wire is flipped iff wire `o` holds a one. -/
theorem wire_copyPermAt (o : ℕ) (gap : Bool) (h : o + 1 + gap.toNat < N) (x : St N) (j : ℕ) :
    wire (copyPermAt N o gap x) j
      = if j = o + 1 + gap.toNat then xor (wire x (o + 1 + gap.toNat)) (wire x o)
        else wire x j := by
  cases gap
  · have h1 : o + 1 < N := h
    change wire (copyPermAt N o false x) j
      = if j = o + 1 then xor (wire x (o + 1)) (wire x o) else wire x j
    rw [copyPermAt, dif_pos h1, cxPerm_apply, wire_update, wire_mk x o (by omega),
      wire_mk x (o + 1) h1]
  · have h2 : o + 2 < N := h
    change wire (copyPermAt N o true x) j
      = if j = o + 2 then xor (wire x (o + 2)) (wire x o) else wire x j
    rw [copyPermAt, dif_pos h2, copy4_apply _ _ _ _ _ (fin_ne _ _ (by omega)), wire_update,
      wire_mk x o (by omega), wire_mk x (o + 2) h2]

/-! ### The ripple: circuit, permutation, cost -/

/-- The ripple at offset `o` with `k` cells: all forward cells, the copy, all reverse
cells. -/
noncomputable def rippleAt (N : ℕ) : ℕ → ℕ → Bool → List (Gate N)
  | o, 0, gap => copyAt N o gap
  | o, k + 1, gap => fwdAt N o ++ rippleAt N (o + 2) k gap ++ revAt N o

/-- The basis permutation of `rippleAt`. -/
def ripplePermAt (N : ℕ) : ℕ → ℕ → Bool → Equiv.Perm (St N)
  | o, 0, gap => copyPermAt N o gap
  | o, k + 1, gap => revPermAt N o * (ripplePermAt N (o + 2) k gap * fwdPermAt N o)

theorem rippleAt_zero (N o : ℕ) (gap : Bool) : rippleAt N o 0 gap = copyAt N o gap := rfl

theorem rippleAt_succ (N o k : ℕ) (gap : Bool) :
    rippleAt N o (k + 1) gap = fwdAt N o ++ rippleAt N (o + 2) k gap ++ revAt N o := rfl

theorem ripplePermAt_zero (N o : ℕ) (gap : Bool) :
    ripplePermAt N o 0 gap = copyPermAt N o gap := rfl

theorem ripplePermAt_succ_apply (N o k : ℕ) (gap : Bool) (x : St N) :
    ripplePermAt N o (k + 1) gap x
      = revPermAt N o (ripplePermAt N (o + 2) k gap (fwdPermAt N o x)) := rfl

/-- The ripple is a permutation up to phases of modulus one. -/
theorem umono_rippleAt (N o k : ℕ) (gap : Bool) :
    UMono (circMat (rippleAt N o k gap)) (ripplePermAt N o k gap) := by
  induction k generalizing o with
  | zero => exact umono_copyAt N o gap
  | succ k ih => exact umono_append (umono_append (umono_fwdAt N o) (ih (o + 2))) (umono_revAt N o)

theorem unitaryGates_rippleAt (N o k : ℕ) (gap : Bool) : UnitaryGates (rippleAt N o k gap) := by
  induction k generalizing o with
  | zero => exact unitaryGates_copyAt N o gap
  | succ k ih =>
    exact unitaryGates_append (unitaryGates_append (unitaryGates_fwdAt N o) (ih (o + 2)))
      (unitaryGates_revAt N o)

theorem cnots_rippleAt (o k : ℕ) (gap : Bool) (hN : o + 2 * k + 1 + gap.toNat < N) :
    cnots (rippleAt N o k gap) = 13 * k + (1 + 3 * gap.toNat) := by
  induction k generalizing o with
  | zero =>
    rw [rippleAt_zero, cnots_copyAt o gap (by omega)]
    omega
  | succ k ih =>
    rw [rippleAt_succ, cnots_append, cnots_append, cnots_fwdAt o (by omega),
      cnots_revAt o (by omega), ih (o + 2) (by omega)]
    omega

/-! ### The carries and the action on basis states -/

/-- The carries at offset `o`: `c_0 = x o` and
`c_{i+1} = maj c_i (x (o + 2i + 1)) (x (o + 2i + 2))`. -/
def carry (x : St N) (o : ℕ) : ℕ → Bool
  | 0 => wire x o
  | i + 1 => maj (carry x o i) (wire x (o + 2 * i + 1)) (wire x (o + 2 * i + 2))

theorem carry_zero (x : St N) (o : ℕ) : carry x o 0 = wire x o := rfl

theorem carry_succ (x : St N) (o i : ℕ) :
    carry x o (i + 1)
      = maj (carry x o i) (wire x (o + 2 * i + 1)) (wire x (o + 2 * i + 2)) := rfl

/-- After the forward cell, the carries of the rest of the line are the next carries. -/
theorem carry_fwd (o : ℕ) (h : o + 2 < N) (x : St N) (i : ℕ) :
    carry (fwdPermAt N o x) (o + 2) i = carry x o (i + 1) := by
  induction i with
  | zero =>
    change wire (fwdPermAt N o x) (o + 2) = maj (wire x o) (wire x (o + 1)) (wire x (o + 2))
    rw [wire_fwdPermAt_2 o h]
  | succ i ih =>
    have e1 : o + 2 + 2 * i + 1 = o + 2 * (i + 1) + 1 := by omega
    have e2 : o + 2 + 2 * i + 2 = o + 2 * (i + 1) + 2 := by omega
    rw [carry_succ, ih, carry_succ x o (i + 1),
      wire_fwdPermAt_gt o h x (o + 2 + 2 * i + 1) (by omega),
      wire_fwdPermAt_gt o h x (o + 2 + 2 * i + 2) (by omega), e1, e2]

/-- One step of the ripple, given that the inner ripple leaves the low wires alone. -/
theorem ripple_succ_wire_aux (o k : ℕ) (gap : Bool) (h2 : o + 2 < N) (x : St N)
    (hlow : ∀ j ≤ o + 2, wire (ripplePermAt N (o + 2) k gap (fwdPermAt N o x)) j
      = wire (fwdPermAt N o x) j) (j : ℕ) :
    wire (ripplePermAt N o (k + 1) gap x) j
      = if j = o + 2 then xor (xor (wire x o) (wire x (o + 1))) (wire x (o + 2))
        else if j = o + 1 then wire x (o + 1)
        else if j = o then wire x o
        else wire (ripplePermAt N (o + 2) k gap (fwdPermAt N o x)) j := by
  rw [ripplePermAt_succ_apply, wire_revPermAt o h2, hlow o (by omega), hlow (o + 1) (by omega),
    hlow (o + 2) (by omega), wire_fwdPermAt_0 o h2, wire_fwdPermAt_1 o h2, wire_fwdPermAt_2 o h2,
    rev0_fwd, rev1_fwd, rev2_fwd]

/-- The ripple at offset `o` leaves the wires `≤ o` unchanged. -/
theorem ripple_low (o k : ℕ) (gap : Bool) (hN : o + 2 * k + 1 + gap.toNat < N) (x : St N)
    (j : ℕ) (hj : j ≤ o) : wire (ripplePermAt N o k gap x) j = wire x j := by
  induction k generalizing o x j with
  | zero => rw [ripplePermAt_zero, wire_copyPermAt o gap (by omega), if_neg (by omega)]
  | succ k ih =>
    have h2 : o + 2 < N := by omega
    have hk : o + 2 + 2 * k + 1 + gap.toNat < N := by omega
    rw [ripple_succ_wire_aux o k gap h2 x (fun j' hj' => ih (o + 2) hk _ j' hj'),
      if_neg (by omega), if_neg (by omega)]
    by_cases hjo : j = o
    · rw [if_pos hjo, hjo]
    · rw [if_neg hjo, ih (o + 2) hk _ j (by omega), wire_fwdPermAt_lt o h2 x j (by omega)]

/-- **One step of the ripple** on basis states. -/
theorem ripple_succ_wire (o k : ℕ) (gap : Bool) (hN : o + 2 * (k + 1) + 1 + gap.toNat < N)
    (x : St N) (j : ℕ) :
    wire (ripplePermAt N o (k + 1) gap x) j
      = if j = o + 2 then xor (xor (wire x o) (wire x (o + 1))) (wire x (o + 2))
        else if j = o + 1 then wire x (o + 1)
        else if j = o then wire x o
        else wire (ripplePermAt N (o + 2) k gap (fwdPermAt N o x)) j :=
  ripple_succ_wire_aux o k gap (by omega) x
    (fun j' hj' => ripple_low (o + 2) k gap (by omega) _ j' hj') j

/-- The ripple changes only the target wires `o + 2i + 2` (`i < k`) and the top wire. -/
theorem ripple_other (o k : ℕ) (gap : Bool) (hN : o + 2 * k + 1 + gap.toNat < N) (x : St N)
    (j : ℕ) (hj : ∀ i < k, j ≠ o + 2 * i + 2) (ht : j ≠ o + 2 * k + 1 + gap.toNat) :
    wire (ripplePermAt N o k gap x) j = wire x j := by
  induction k generalizing o x with
  | zero => rw [ripplePermAt_zero, wire_copyPermAt o gap (by omega), if_neg (by omega)]
  | succ k ih =>
    have h2 : o + 2 < N := by omega
    have hk : o + 2 + 2 * k + 1 + gap.toNat < N := by omega
    have hj0 : j ≠ o + 2 := by
      have := hj 0 (by omega)
      omega
    rw [ripple_succ_wire o k gap hN x j, if_neg hj0]
    by_cases h1 : j = o + 1
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      by_cases h0 : j = o
      · rw [if_pos h0, h0]
      · rw [if_neg h0, ih (o + 2) hk _ ?_ ?_]
        · by_cases hlt : j < o
          · exact wire_fwdPermAt_lt o h2 x j hlt
          · exact wire_fwdPermAt_gt o h2 x j (by omega)
        · intro i hi
          have := hj (i + 1) (by omega)
          omega
        · omega

/-- Target wire `i` receives the sum bit `h_i ⊕ u_i ⊕ c_i`. -/
theorem ripple_target (o k : ℕ) (gap : Bool) (hN : o + 2 * k + 1 + gap.toNat < N) (x : St N)
    (i : ℕ) (hi : i < k) :
    wire (ripplePermAt N o k gap x) (o + 2 * i + 2)
      = xor (xor (wire x (o + 2 * i + 2)) (wire x (o + 2 * i + 1))) (carry x o i) := by
  induction k generalizing o x i with
  | zero => omega
  | succ k ih =>
    have h2 : o + 2 < N := by omega
    have hk : o + 2 + 2 * k + 1 + gap.toNat < N := by omega
    rw [ripple_succ_wire o k gap hN x]
    cases i with
    | zero =>
      rw [if_pos (by omega)]
      change xor (xor (wire x o) (wire x (o + 1))) (wire x (o + 2))
        = xor (xor (wire x (o + 2)) (wire x (o + 1))) (wire x o)
      cases wire x o <;> cases wire x (o + 1) <;> cases wire x (o + 2) <;> rfl
    | succ i =>
      have e2 : o + 2 * (i + 1) + 2 = o + 2 + 2 * i + 2 := by omega
      have e1 : o + 2 * (i + 1) + 1 = o + 2 + 2 * i + 1 := by omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), e2, e1,
        ih (o + 2) hk _ i (by omega), carry_fwd o h2,
        wire_fwdPermAt_gt o h2 x (o + 2 + 2 * i + 2) (by omega),
        wire_fwdPermAt_gt o h2 x (o + 2 + 2 * i + 1) (by omega)]

/-- The top wire receives the last carry. -/
theorem ripple_top (o k : ℕ) (gap : Bool) (hN : o + 2 * k + 1 + gap.toNat < N) (x : St N) :
    wire (ripplePermAt N o k gap x) (o + 2 * k + 1 + gap.toNat)
      = xor (wire x (o + 2 * k + 1 + gap.toNat)) (carry x o k) := by
  induction k generalizing o x with
  | zero =>
    have e : o + 2 * 0 + 1 + gap.toNat = o + 1 + gap.toNat := by omega
    rw [e, ripplePermAt_zero, wire_copyPermAt o gap (by omega), if_pos rfl, carry_zero]
  | succ k ih =>
    have h2 : o + 2 < N := by omega
    have hk : o + 2 + 2 * k + 1 + gap.toNat < N := by omega
    have e : o + 2 * (k + 1) + 1 + gap.toNat = o + 2 + 2 * k + 1 + gap.toNat := by omega
    rw [ripple_succ_wire o k gap hN x, if_neg (by omega), if_neg (by omega), if_neg (by omega),
      e, ih (o + 2) hk, carry_fwd o h2,
      wire_fwdPermAt_gt o h2 x (o + 2 + 2 * k + 1 + gap.toNat) (by omega)]

end Line
