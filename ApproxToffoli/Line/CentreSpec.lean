/-
The basis action of the centre circuit (`6 a - 3` CNOTs) on a line.

Wires: `S_i = 2a - 2i` (`0 ≤ i ≤ a`), `T_i = 2a - 2i - 1` (`0 ≤ i < a`).  With
`p = x(S_0) ⊕ x(T_0)`, the circuit `centre N a` is, up to phases of modulus one, the
permutation `centrePerm N a` of basis states that

* flips `S_0` (wire `2a`) and `T_0` (wire `2a - 1`);
* adds `p` to `S_1` (wire `2a - 2`);
* adds `p ∧ x(T_1) ∧ … ∧ x(T_j)` to `S_{j+1}` (wire `2a - 2j - 2`), `1 ≤ j < a`;
* flips `S_a` (wire `0`) once more;
* leaves every other wire unchanged.

`tAnd x o m` is the conjunction of the bits on wires `o + 1, o + 3, …, o + 2m - 1`.
-/
import Mathlib
import ApproxToffoli.Line.Centre

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Conjunctions of every other wire -/

/-- The conjunction of the bits of `x` on wires `o + 1, o + 3, …, o + 2 m - 1`. -/
def tAnd (x : St N) : ℕ → ℕ → Bool
  | _, 0 => true
  | o, m + 1 => wire x (o + 1) && tAnd x (o + 2) m

theorem tAnd_zero (x : St N) (o : ℕ) : tAnd x o 0 = true := rfl

theorem tAnd_succ (x : St N) (o m : ℕ) :
    tAnd x o (m + 1) = (wire x (o + 1) && tAnd x (o + 2) m) := rfl

theorem tAnd_congr {x y : St N} (o m : ℕ)
    (h : ∀ i, o < i → i < o + 2 * m → wire x i = wire y i) : tAnd x o m = tAnd y o m := by
  induction m generalizing o with
  | zero => rfl
  | succ m ih =>
    rw [tAnd_succ, tAnd_succ, h (o + 1) (by omega) (by omega),
      ih (o + 2) (fun i h1 h2 => h i (by omega) (by omega))]

theorem tAnd_eq_true_iff (x : St N) (o m : ℕ) :
    tAnd x o m = true ↔ ∀ i, i < m → wire x (o + 2 * i + 1) = true := by
  induction m generalizing o with
  | zero => simp [tAnd]
  | succ m ih =>
    rw [tAnd_succ, Bool.and_eq_true, ih (o + 2)]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ k =>
        have := h1 k (by omega)
        rwa [show o + 2 + 2 * k + 1 = o + 2 * (k + 1) + 1 by ring] at this
    · intro h
      refine ⟨h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      rwa [show o + 2 * (i + 1) + 1 = o + 2 + 2 * i + 1 by ring] at this

/-! ### The cells on basis states, wire by wire -/

theorem jPermAt_wire (o : ℕ) (h : o + 2 < N) (x : St N) (j : ℕ) :
    wire (jPermAt N o x) j
      = if j = o then wire x (o + 1)
        else if j = o + 1 then xor (wire x o) (wire x (o + 2) && wire x (o + 1))
        else wire x j := by
  rw [jPermAt, dif_pos h, wire_mk x (o + 1) (by omega), wire_mk x o (by omega),
    wire_mk x (o + 2) h]
  exact jPerm_wire _ _ _ _ _ (by simp) x j

theorem jPermAt_inv_wire (o : ℕ) (h : o + 2 < N) (y : St N) (j : ℕ) :
    wire ((jPermAt N o)⁻¹ y) j
      = if j = o then xor (wire y (o + 1)) (wire y (o + 2) && wire y o)
        else if j = o + 1 then wire y o
        else wire y j := by
  rw [jPermAt, dif_pos h, wire_mk y (o + 1) (by omega), wire_mk y o (by omega),
    wire_mk y (o + 2) h]
  exact jPerm_inv_wire _ _ _ _ _ (by simp) y j

/-- The core on basis states: `q2 ^= q3`, `q0 ^= q3 ∧ q1`. -/
theorem core_apply (q0 q1 q2 q3 : Fin N) (h30 : q3 ≠ q0) (h10 : q1 ≠ q0) (h32 : q3 ≠ q2)
    (h20 : q2 ≠ q0) (x : St N) :
    (cxPerm q3 q2 h32 * ccPerm q3 q0 q1 h30 h10) x
      = Function.update (Function.update x q2 (xor (x q2) (x q3))) q0
          (xor (x q0) (x q3 && x q1)) :=
  gapPerm_apply q3 q2 q1 q0 h32 h30 h10 h20 x

theorem corePermAt_wire (o : ℕ) (h : o + 3 < N) (x : St N) (j : ℕ) :
    wire (corePermAt N o x) j
      = if j = o then xor (wire x o) (wire x (o + 3) && wire x (o + 1))
        else if j = o + 2 then xor (wire x (o + 2)) (wire x (o + 3))
        else wire x j := by
  rw [corePermAt, dif_pos h,
    core_apply ⟨o, by omega⟩ ⟨o + 1, by omega⟩ ⟨o + 2, by omega⟩ ⟨o + 3, h⟩ (by simp) (by simp)
      (by simp) (by simp),
    wire_update, wire_update, wire_mk x o (by omega), wire_mk x (o + 1) (by omega),
    wire_mk x (o + 2) (by omega), wire_mk x (o + 3) h]

/-! ### The bit on each wire after the nested permutation -/

/-- The bit on wire `j` after `nestPerm N o n`: with `p` the bit on wire `o + 2n + 3`,
wire `o + 2n + 2` gets `⊕ p`, and wire `o + 2k` (`k ≤ n`) gets `⊕ p ∧ ⋀ (wires o + 2k + 1,
o + 2k + 3, …, o + 2n + 1)`. -/
def nestSpec (x : St N) (o n j : ℕ) : Bool :=
  if j = o + 2 * n + 2 then xor (wire x j) (wire x (o + 2 * n + 3))
  else if o ≤ j ∧ j ≤ o + 2 * n ∧ (j - o) % 2 = 0 then
    xor (wire x j) (wire x (o + 2 * n + 3) && tAnd x j ((o + 2 * n + 2 - j) / 2))
  else wire x j

theorem nestSpec_lt (x : St N) {o n j : ℕ} (h : j < o) : nestSpec x o n j = wire x j := by
  have h1 : ¬ j = o + 2 * n + 2 := by omega
  have h2 : ¬ (o ≤ j ∧ j ≤ o + 2 * n ∧ (j - o) % 2 = 0) := by omega
  rw [nestSpec, if_neg h1, if_neg h2]

theorem nestSpec_gt (x : St N) {o n j : ℕ} (h : o + 2 * n + 2 < j) :
    nestSpec x o n j = wire x j := by
  have h1 : ¬ j = o + 2 * n + 2 := by omega
  have h2 : ¬ (o ≤ j ∧ j ≤ o + 2 * n ∧ (j - o) % 2 = 0) := by omega
  rw [nestSpec, if_neg h1, if_neg h2]

theorem nestSpec_base (x : St N) (o n : ℕ) :
    nestSpec x o n o = xor (wire x o) (wire x (o + 2 * n + 3) && tAnd x o (n + 1)) := by
  have h1 : ¬ o = o + 2 * n + 2 := by omega
  have h2 : o ≤ o ∧ o ≤ o + 2 * n ∧ (o - o) % 2 = 0 := by omega
  have h3 : (o + 2 * n + 2 - o) / 2 = n + 1 := by omega
  rw [nestSpec, if_neg h1, if_pos h2, h3]

theorem nestSpec_congr {x y : St N} {o : ℕ} (n : ℕ) {j : ℕ}
    (h : ∀ i, o ≤ i → wire x i = wire y i) (hj : o ≤ j) :
    nestSpec x o n j = nestSpec y o n j := by
  rw [nestSpec, nestSpec, h j hj, h (o + 2 * n + 3) (by omega),
    tAnd_congr (x := x) (y := y) j _ (fun i h1 _ => h i (by omega))]

theorem nestSpec_shift (x : St N) {o n j : ℕ} (hj : o + 2 ≤ j) :
    nestSpec x (o + 2) n j = nestSpec x o (n + 1) j := by
  have e0 : o + 2 + 2 * n = o + 2 * (n + 1) := by ring
  have hc : (o + 2 ≤ j ∧ j ≤ o + 2 * (n + 1) ∧ (j - (o + 2)) % 2 = 0)
      ↔ (o ≤ j ∧ j ≤ o + 2 * (n + 1) ∧ (j - o) % 2 = 0) := by omega
  rw [nestSpec, nestSpec, e0]
  simp only [hc]

/-- **Basis action of the nested circuit.** -/
theorem nestPerm_wire (o n : ℕ) (h : o + 2 * n + 3 < N) (x : St N) (j : ℕ) :
    wire (nestPerm N o n x) j = nestSpec x o n j := by
  induction n generalizing o x j with
  | zero =>
    change wire (corePermAt N o x) j = _
    have hs : nestSpec x o 0 j
        = if j = o + 2 then xor (wire x j) (wire x (o + 3))
          else if o ≤ j ∧ j ≤ o ∧ (j - o) % 2 = 0 then
            xor (wire x j) (wire x (o + 3) && tAnd x j ((o + 2 - j) / 2))
          else wire x j := rfl
    rw [corePermAt_wire o (by omega), hs]
    by_cases h0 : j = o
    · have h1 : ¬ j = o + 2 := by omega
      have h3 : o ≤ j ∧ j ≤ o ∧ (j - o) % 2 = 0 := by omega
      have h4 : (o + 2 - j) / 2 = 0 + 1 := by omega
      rw [if_pos h0, if_neg h1, if_pos h3, h4, tAnd_succ, tAnd_zero, Bool.and_true, h0]
    · by_cases h2 : j = o + 2
      · rw [if_neg h0, if_pos h2, if_pos h2, h2]
      · have h3 : ¬ (o ≤ j ∧ j ≤ o ∧ (j - o) % 2 = 0) := by omega
        rw [if_neg h0, if_neg h2, if_neg h2, if_neg h3]
  | succ n ih =>
    have ho : o + 2 < N := by omega
    have e : ∀ a b c p T : Bool,
        xor (xor a (c && b)) (xor c (p && T) && b) = xor a (p && (b && T)) := by decide
    change wire ((jPermAt N o)⁻¹ (nestPerm N (o + 2) n (jPermAt N o x))) j = _
    have hJ := jPermAt_wire o ho x
    have hy := ih (o + 2) (by omega) (jPermAt N o x)
    have hJx : ∀ i, o + 2 ≤ i → wire (jPermAt N o x) i = wire x i := by
      intro i hi
      rw [hJ, if_neg (by omega), if_neg (by omega)]
    have y0 : wire (nestPerm N (o + 2) n (jPermAt N o x)) o = wire x (o + 1) := by
      rw [hy, nestSpec_lt _ (by omega), hJ, if_pos rfl]
    have y1 : wire (nestPerm N (o + 2) n (jPermAt N o x)) (o + 1)
        = xor (wire x o) (wire x (o + 2) && wire x (o + 1)) := by
      rw [hy, nestSpec_lt _ (by omega), hJ, if_neg (by omega), if_pos rfl]
    have y2 : wire (nestPerm N (o + 2) n (jPermAt N o x)) (o + 2)
        = xor (wire x (o + 2)) (wire x (o + 2 + 2 * n + 3) && tAnd x (o + 2) (n + 1)) := by
      rw [hy, nestSpec_congr n hJx (le_refl _), nestSpec_base]
    rw [jPermAt_inv_wire o ho]
    by_cases h0 : j = o
    · rw [h0, if_pos rfl, y1, y2, y0, nestSpec_base, tAnd_succ x o (n + 1),
        show o + 2 * (n + 1) + 3 = o + 2 + 2 * n + 3 by ring]
      exact e _ _ _ _ _
    · by_cases h1 : j = o + 1
      · have h3 : ¬ j = o + 2 * (n + 1) + 2 := by omega
        have h4 : ¬ (o ≤ j ∧ j ≤ o + 2 * (n + 1) ∧ (j - o) % 2 = 0) := by omega
        rw [if_neg h0, if_pos h1, y0, nestSpec, if_neg h3, if_neg h4, h1]
      · rw [if_neg h0, if_neg h1, hy]
        by_cases hlt : j < o
        · rw [nestSpec_lt (jPermAt N o x) (o := o + 2) (by omega), nestSpec_lt x hlt, hJ,
            if_neg h0, if_neg h1]
        · rw [nestSpec_congr n hJx (by omega), nestSpec_shift x (by omega)]

/-! ### The centre circuit -/

theorem centre_ne {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    (⟨2 * a, h.2⟩ : Fin N) ≠ ⟨2 * a - 1, by omega⟩ := by
  intro e
  have e' : 2 * a = 2 * a - 1 := Fin.val_eq_of_eq e
  omega

theorem centre_ne0 {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    (⟨0, by omega⟩ : Fin N) ≠ ⟨2 * a - 1, by omega⟩ := by
  intro e
  have e' : 0 = 2 * a - 1 := Fin.val_eq_of_eq e
  omega

/-- The three opening gates: NOT on `S_0` and on `T_0`, then a CNOT from `S_0` to `T_0`. -/
noncomputable def centreHead (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : List (Gate N) :=
  [.one ⟨2 * a, h.2⟩ xGate, .one ⟨2 * a - 1, by omega⟩ xGate,
    .cx ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (Or.inr (by change 2 * a - 1 + 1 = 2 * a; omega))]

/-- The two closing gates: the CNOT from `S_0` to `T_0` again, then a NOT on wire `0`. -/
noncomputable def centreTail (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : List (Gate N) :=
  [.cx ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (Or.inr (by change 2 * a - 1 + 1 = 2 * a; omega)),
    .one ⟨0, by omega⟩ xGate]

/-- **The centre circuit** on wires `0, …, 2a` (`a ≥ 2`, `2a + 1 ≤ N`):

    [X S_0, X T_0, cx S_0 T_0] ++ halves ++ core ++ invCirc halves ++ [cx S_0 T_0, X S_a]

where `halves` are the half cells `jHalf (S_i, T_i, S_{i+1})` for `i = a-1, …, 2` and
`core` is on `T_0, S_1, T_1, S_2`. -/
noncomputable def centre (N a : ℕ) : List (Gate N) :=
  if h : 2 ≤ a ∧ 2 * a < N then
    centreHead a h ++ halvesAt N 0 (a - 2) ++ coreAt N (2 * a - 4)
      ++ invCirc (halvesAt N 0 (a - 2)) ++ centreTail a h
  else []

/-- The basis permutation of the opening gates. -/
def centreHeadPerm (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : Equiv.Perm (St N) :=
  (cxPerm ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (centre_ne h) * xPerm ⟨2 * a - 1, by omega⟩)
    * xPerm ⟨2 * a, h.2⟩

/-- The basis permutation of the closing gates. -/
def centreTailPerm (a : ℕ) (h : 2 ≤ a ∧ 2 * a < N) : Equiv.Perm (St N) :=
  xPerm ⟨0, by omega⟩ * cxPerm ⟨2 * a, h.2⟩ ⟨2 * a - 1, by omega⟩ (centre_ne h)

/-- The basis permutation of the centre circuit, as the product of its parts. -/
def centrePerm (N a : ℕ) : Equiv.Perm (St N) :=
  if h : 2 ≤ a ∧ 2 * a < N then
    centreTailPerm a h * nestPerm N 0 (a - 2) * centreHeadPerm a h
  else 1

theorem centre_eq {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) :
    centre N a = centreHead a h ++ (nest N 0 (a - 2) ++ centreTail a h) := by
  have e : 0 + 2 * (a - 2) = 2 * a - 4 := by omega
  rw [centre, dif_pos h, ← halves_core_eq_nest N 0 (a - 2), e]
  simp only [List.append_assoc]

/-- **The centre circuit has `6 a - 3` CNOTs.** -/
theorem cnots_centre {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) : cnots (centre N a) = 6 * a - 3 := by
  have h1 : cnots (centreHead a h) = 1 := rfl
  have h2 : cnots (centreTail a h) = 1 := rfl
  rw [centre_eq h, cnots_append, cnots_append, cnots_nest 0 (a - 2) (by omega), h1, h2]
  omega

theorem unitaryGates_centre (N a : ℕ) : UnitaryGates (centre N a) := by
  by_cases h : 2 ≤ a ∧ 2 * a < N
  · rw [centre_eq h]
    exact unitaryGates_append
      (unitaryGates_cons_one _ xGate_unitary (unitaryGates_cons_one _ xGate_unitary
        (unitaryGates_cons_cx _ _ _ unitaryGates_nil)))
      (unitaryGates_append (unitaryGates_nest N 0 (a - 2))
        (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ xGate_unitary unitaryGates_nil)))
  · rw [centre, dif_neg h]
    exact unitaryGates_nil

/-- **The centre circuit is a permutation up to phases.** -/
theorem umono_centre (N a : ℕ) : UMono (circMat (centre N a)) (centrePerm N a) := by
  by_cases h : 2 ≤ a ∧ 2 * a < N
  · have hH : UMono (circMat (centreHead a h)) (centreHeadPerm a h) :=
      umono_cons (umono_x _) (umono_cons (umono_x _) (umono_single (umono_cx _ _ _)))
    have hT : UMono (circMat (centreTail a h)) (centreTailPerm a h) :=
      umono_cons (umono_cx _ _ _) (umono_single (umono_x _))
    rw [centre_eq h, centrePerm, dif_pos h]
    exact umono_append hH (umono_append (umono_nest N 0 (a - 2)) hT)
  · rw [centre, dif_neg h, centrePerm, dif_neg h]
    exact umono_nil

/-! ### The opening and closing gates on basis states -/

theorem head_wire (s t : Fin N) (hst : s ≠ t) (x : St N) (j : ℕ) :
    wire (((cxPerm s t hst * xPerm t) * xPerm s) x) j
      = if j = t.val then xor (x s) (x t) else if j = s.val then !x s else wire x j := by
  by_cases h1 : j = t.val
  · simp only [Equiv.Perm.mul_apply, cxPerm_apply, xPerm_apply, wire_update,
      Function.update_self, Function.update_of_ne hst, Function.update_of_ne hst.symm,
      if_pos h1]
    cases x s <;> cases x t <;> rfl
  · simp only [Equiv.Perm.mul_apply, cxPerm_apply, xPerm_apply, wire_update,
      Function.update_self, Function.update_of_ne hst, Function.update_of_ne hst.symm,
      if_neg h1]

theorem tail_wire (z s t : Fin N) (hst : s ≠ t) (hzt : z ≠ t) (y : St N) (j : ℕ) :
    wire ((xPerm z * cxPerm s t hst) y) j
      = if j = z.val then !y z else if j = t.val then xor (y t) (y s) else wire y j := by
  simp only [Equiv.Perm.mul_apply, cxPerm_apply, xPerm_apply, wire_update,
    Function.update_of_ne hzt]

/-- The nested permutation in the centre circuit: its input `x1` agrees with `x` on the
wires `≤ 2a - 2` and holds `p` on wire `2a - 1`. -/
theorem nestSpec_centre {a : ℕ} (ha : 2 ≤ a) {x x1 : St N} {p : Bool}
    (hp : wire x1 (2 * a - 1) = p) (hx : ∀ i, i ≤ 2 * a - 2 → wire x1 i = wire x i) {j : ℕ}
    (hj : j ≤ 2 * a - 2) :
    nestSpec x1 0 (a - 2) j
      = if j = 2 * a - 2 then xor (wire x j) p
        else if j < 2 * a - 2 ∧ j % 2 = 0 then
          xor (wire x j) (p && tAnd x j ((2 * a - 2 - j) / 2))
        else wire x j := by
  have e3 : 0 + 2 * (a - 2) + 3 = 2 * a - 1 := by omega
  have e2 : 0 + 2 * (a - 2) + 2 = 2 * a - 2 := by omega
  have hc : (0 ≤ j ∧ j ≤ 0 + 2 * (a - 2) ∧ (j - 0) % 2 = 0) ↔ (j < 2 * a - 2 ∧ j % 2 = 0) := by
    omega
  rw [nestSpec, e3, e2, hp, hx j hj,
    tAnd_congr (x := x1) (y := x) j ((2 * a - 2 - j) / 2) (fun i _ h2 => hx i (by omega))]
  simp only [hc]

/-! ### The basis action of the centre circuit -/

/-- The bit on wire `j` after the centre permutation, with
`p = x(S_0) ⊕ x(T_0) = wire x (2a) ⊕ wire x (2a - 1)`. -/
def centreSpec (x : St N) (a j : ℕ) : Bool :=
  if j = 0 then
    !(xor (wire x 0) (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd x 0 (a - 1)))
  else if j = 2 * a - 1 then !wire x (2 * a - 1)
  else if j = 2 * a then !wire x (2 * a)
  else if j = 2 * a - 2 then xor (wire x j) (xor (wire x (2 * a)) (wire x (2 * a - 1)))
  else if j < 2 * a - 2 ∧ j % 2 = 0 then
    xor (wire x j)
      (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd x j ((2 * a - 2 - j) / 2))
  else wire x j

/-- **Basis action of the centre circuit**, wire by wire. -/
theorem centrePerm_wire {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) (j : ℕ) :
    wire (centrePerm N a x) j = centreSpec x a j := by
  have ha := h.1
  have hN := h.2
  have e : ∀ s t : Bool, xor (xor s t) (!s) = !t := by decide
  rw [centrePerm, dif_pos h]
  change wire (centreTailPerm a h (nestPerm N 0 (a - 2) (centreHeadPerm a h x))) j = _
  have hx1 : ∀ i, wire (centreHeadPerm a h x) i
      = if i = 2 * a - 1 then xor (wire x (2 * a)) (wire x (2 * a - 1))
        else if i = 2 * a then !wire x (2 * a) else wire x i := by
    intro i
    rw [wire_mk x (2 * a) hN, wire_mk x (2 * a - 1) (by omega)]
    exact head_wire _ _ (centre_ne h) x i
  have ht : ∀ (y : St N) (i : ℕ), wire (centreTailPerm a h y) i
      = if i = 0 then !wire y 0
        else if i = 2 * a - 1 then xor (wire y (2 * a - 1)) (wire y (2 * a)) else wire y i := by
    intro y i
    rw [wire_mk y 0 (by omega), wire_mk y (2 * a) hN, wire_mk y (2 * a - 1) (by omega)]
    exact tail_wire _ _ _ (centre_ne h) (centre_ne0 h) y i
  have hy := nestPerm_wire 0 (a - 2) (by omega) (centreHeadPerm a h x)
  have hgt : ∀ i, 2 * a - 2 < i → wire (nestPerm N 0 (a - 2) (centreHeadPerm a h x)) i
      = wire (centreHeadPerm a h x) i := by
    intro i hi
    rw [hy, nestSpec_gt _ (by omega)]
  have hp : wire (centreHeadPerm a h x) (2 * a - 1)
      = xor (wire x (2 * a)) (wire x (2 * a - 1)) := by
    rw [hx1, if_pos rfl]
  have hxle : ∀ i, i ≤ 2 * a - 2 → wire (centreHeadPerm a h x) i = wire x i := by
    intro i hi
    rw [hx1, if_neg (by omega), if_neg (by omega)]
  have hle : ∀ i, i ≤ 2 * a - 2 → wire (nestPerm N 0 (a - 2) (centreHeadPerm a h x)) i
      = if i = 2 * a - 2 then xor (wire x i) (xor (wire x (2 * a)) (wire x (2 * a - 1)))
        else if i < 2 * a - 2 ∧ i % 2 = 0 then
          xor (wire x i)
            (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd x i ((2 * a - 2 - i) / 2))
        else wire x i := by
    intro i hi
    rw [hy]
    exact nestSpec_centre ha hp hxle hi
  rw [ht, centreSpec]
  by_cases h0 : j = 0
  · have h5 : (2 * a - 2 - 0) / 2 = a - 1 := by omega
    rw [if_pos h0, if_pos h0, hle 0 (by omega), if_neg (by omega), if_pos (by omega), h5]
  · by_cases h1 : j = 2 * a - 1
    · rw [if_neg h0, if_neg h0, if_pos h1, if_pos h1, hgt (2 * a - 1) (by omega),
        hgt (2 * a) (by omega), hx1 (2 * a - 1), if_pos rfl, hx1 (2 * a), if_neg (by omega),
        if_pos rfl]
      exact e _ _
    · by_cases h2 : j = 2 * a
      · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, if_pos h2, h2, hgt (2 * a) (by omega),
          hx1 (2 * a), if_neg (by omega), if_pos rfl]
      · by_cases h3 : j ≤ 2 * a - 2
        · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, if_neg h2, hle j h3]
        · rw [if_neg h0, if_neg h0, if_neg h1, if_neg h1, if_neg h2, if_neg (by omega),
            if_neg (by omega), hgt j (by omega), hx1 j, if_neg h1, if_neg h2]

/-! ### The action on each kind of wire -/

section wires

variable {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N)
include h

/-- `S_0` (wire `2a`) is flipped. -/
theorem centrePerm_wire_S0 : wire (centrePerm N a x) (2 * a) = !wire x (2 * a) := by
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- `T_0` (wire `2a - 1`) is flipped. -/
theorem centrePerm_wire_T0 : wire (centrePerm N a x) (2 * a - 1) = !wire x (2 * a - 1) := by
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_pos rfl]

/-- `S_1` (wire `2a - 2`) gets `⊕ p`, with `p = x(S_0) ⊕ x(T_0)`. -/
theorem centrePerm_wire_S1 :
    wire (centrePerm N a x) (2 * a - 2)
      = xor (wire x (2 * a - 2)) (xor (wire x (2 * a)) (wire x (2 * a - 1))) := by
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

/-- `S_{a-k}` (wire `2k`, `0 < k ≤ a - 2`) gets `⊕ p ∧ x(T_1) ∧ … ∧ x(T_{a-k-1})`; the
`T`s involved are the wires `2k + 1, 2k + 3, …, 2a - 3`. -/
theorem centrePerm_wire_S {k : ℕ} (hk : 0 < k) (hk2 : k + 2 ≤ a) :
    wire (centrePerm N a x) (2 * k)
      = xor (wire x (2 * k))
          (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd x (2 * k) (a - 1 - k)) := by
  have e : (2 * a - 2 - 2 * k) / 2 = a - 1 - k := by omega
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), e]

/-- `S_a` (wire `0`) gets `⊕ p ∧ x(T_1) ∧ … ∧ x(T_{a-1})` and is then flipped. -/
theorem centrePerm_wire_zero :
    wire (centrePerm N a x) 0
      = !(xor (wire x 0) (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd x 0 (a - 1))) := by
  rw [centrePerm_wire h, centreSpec, if_pos rfl]

/-- `T_i` with `i ≥ 1` (wire `2k + 1 ≤ 2a - 3`) is unchanged. -/
theorem centrePerm_wire_T {k : ℕ} (hk : k + 2 ≤ a) :
    wire (centrePerm N a x) (2 * k + 1) = wire x (2 * k + 1) := by
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- The wires above `2a` are unchanged. -/
theorem centrePerm_wire_above {j : ℕ} (hj : 2 * a < j) :
    wire (centrePerm N a x) j = wire x j := by
  rw [centrePerm_wire h, centreSpec, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

end wires

end Line
