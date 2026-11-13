/-
The cells of the helper-qubit circuit (`Line/HelperDefs.lean`) as permutations up to
phases.

* `Sem c F`: the matrix of the circuit `c` is a permutation of the basis states up to
  phases of modulus one, and the permutation acts on the bits (read as a function
  `ℕ → Bool` through `Line.wire`) as `F`.
* `Spec c F k`: `Sem c F`, every one-qubit gate of `c` is unitary, `c` touches only the
  positions `≥ 1` (it does not touch the target), and `c` has exactly `k` CNOTs.
  `Spec.append` composes two such statements.
* The cells: a NOT (`spec_x`), a CNOT (`spec_cx`), the 5-CNOT relative-phase Toffoli with
  its target at an end (`spec_toffoliEnd`, the cell `W` of the paper; its gate list is
  `Line.rtof5`), the 3-CNOT relative-phase Toffoli (`spec_toffoliMid`, the cell `V`; its
  gate list is `Line.rccx`) and the in-place AND (`spec_andInPlace`, the cell `A`).
-/
import Mathlib
import ApproxToffoli.Line.HelperDefs
import ApproxToffoli.Line.Cells2

namespace Helper

open Matrix Line ExactLine

variable {N : ℕ}

/-! ### The gates that `uAt` and `cxAt` place -/

theorem uAt_eq (p : ℕ) (hp : p < N) (g : Matrix Bool Bool ℂ) :
    uAt N p g = [Gate.one ⟨p, hp⟩ g] := dif_pos hp

theorem cxAt_eq (c t : ℕ) (hc : c < N) (ht : t < N) (adj : c + 1 = t ∨ t + 1 = c) :
    cxAt N c t = [Gate.cx ⟨c, hc⟩ ⟨t, ht⟩ adj] := dif_pos ⟨hc, ht, adj⟩

theorem toffoliEnd_eq (t near far : ℕ) (ht : t < N) (hn : near < N) (hf : far < N)
    (h1 : far + 1 = near ∨ near + 1 = far) (h2 : near + 1 = t ∨ t + 1 = near) :
    toffoliEnd N t near far = rtof5 ⟨far, hf⟩ ⟨near, hn⟩ ⟨t, ht⟩ h1 h2 := by
  simp only [toffoliEnd, uAt_eq t ht, cxAt_eq near t hn ht h2, cxAt_eq far near hf hn h1]
  rfl

theorem toffoliMid_eq (a m b : ℕ) (ha : a < N) (hm : m < N) (hb : b < N)
    (h1 : a + 1 = m ∨ m + 1 = a) (h2 : b + 1 = m ∨ m + 1 = b) :
    toffoliMid N a m b = rccx ⟨a, ha⟩ ⟨m, hm⟩ ⟨b, hb⟩ h1 h2 := by
  simp only [toffoliMid, uAt_eq m hm, cxAt_eq a m ha hm h1, cxAt_eq b m hb hm h2]
  rfl

/-! ### Semantics: a permutation up to phases with a given action on the bits -/

/-- The matrix of `c` is a permutation up to unit phases, and the permutation acts on the
bits as `F`. -/
def Sem (c : List (Gate N)) (F : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  ∃ σ : Equiv.Perm (St N), UMono (circMat c) σ ∧ ∀ x, wire (σ x) = F (wire x)

/-- `Sem c F`, unitary one-qubit gates, no gate on position `0`, exactly `k` CNOTs. -/
structure Spec (c : List (Gate N)) (F : (ℕ → Bool) → (ℕ → Bool)) (k : ℕ) : Prop where
  sem : Sem c F
  unitary : UnitaryGates c
  above : Above 1 c
  count : cnots c = k

theorem spec_nil : Spec ([] : List (Gate N)) (fun w => w) 0 where
  sem := ⟨1, umono_nil, fun _ => rfl⟩
  unitary := unitaryGates_nil
  above := circOn_nil _
  count := rfl

theorem Spec.append {c d : List (Gate N)} {F G : (ℕ → Bool) → (ℕ → Bool)} {j k : ℕ}
    (hc : Spec c F j) (hd : Spec d G k) : Spec (c ++ d) (fun w => G (F w)) (j + k) where
  sem := by
    obtain ⟨σ, hσ, h1⟩ := hc.sem
    obtain ⟨τ, hτ, h2⟩ := hd.sem
    exact ⟨τ * σ, umono_append hσ hτ, fun x => by rw [Equiv.Perm.mul_apply, h2, h1]⟩
  unitary := unitaryGates_append hc.unitary hd.unitary
  above := circOn_append.2 ⟨hc.above, hd.above⟩
  count := by rw [cnots_append, hc.count, hd.count]

theorem Spec.cast {c : List (Gate N)} {F G : (ℕ → Bool) → (ℕ → Bool)} {j k : ℕ}
    (hc : Spec c F j) (hF : ∀ w, F w = G w) (hk : j = k) : Spec c G k := by
  have : F = G := funext hF
  subst this
  subst hk
  exact hc

/-! ### The actions of the cells on the bits -/

/-- NOT on position `p`. -/
def notW (p : ℕ) (w : ℕ → Bool) : ℕ → Bool := Function.update w p (!w p)

/-- CNOT with control `c` and target `t`. -/
def cxW (c t : ℕ) (w : ℕ → Bool) : ℕ → Bool := Function.update w t (xor (w t) (w c))

/-- Toffoli with target `t` and controls `a`, `b`. -/
def ccW (t a b : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  Function.update w t (xor (w t) (w a && w b))

/-! ### The cells -/

theorem spec_x (p : ℕ) (h1 : 1 ≤ p) (hp : p < N) : Spec (uAt N p xGate) (notW p) 0 where
  sem := ⟨xPerm ⟨p, hp⟩, by rw [uAt_eq p hp]; exact umono_single (umono_x _), fun x => by
    funext i
    rw [xPerm_apply, wire_update, notW, Function.update_apply, wire_mk x p hp]⟩
  unitary := by
    rw [uAt_eq p hp]
    exact unitaryGates_cons_one _ xGate_unitary unitaryGates_nil
  above := by
    rw [uAt_eq p hp]
    exact circOn_cons.2 ⟨h1, circOn_nil _⟩
  count := by
    rw [uAt_eq p hp]
    rfl

theorem spec_cx (c t : ℕ) (h1 : 1 ≤ c) (h2 : 1 ≤ t) (hc : c < N) (ht : t < N)
    (adj : c + 1 = t ∨ t + 1 = c) : Spec (cxAt N c t) (cxW c t) 1 where
  sem := ⟨cxPerm ⟨c, hc⟩ ⟨t, ht⟩ (fin_ne hc ht (by omega)), by
    rw [cxAt_eq c t hc ht adj]
    exact umono_single (umono_cx _ _ _), fun x => by
    funext i
    rw [cxPerm_apply, wire_update, cxW, Function.update_apply, wire_mk x t ht,
      wire_mk x c hc]⟩
  unitary := by
    rw [cxAt_eq c t hc ht adj]
    exact unitaryGates_cons_cx _ _ _ unitaryGates_nil
  above := by
    rw [cxAt_eq c t hc ht adj]
    exact circOn_cons.2 ⟨⟨h1, h2⟩, circOn_nil _⟩
  count := by
    rw [cxAt_eq c t hc ht adj]
    rfl

theorem above_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (a1 : 1 ≤ c1.val) (a2 : 1 ≤ c2.val)
    (a3 : 1 ≤ t.val) : Above 1 (rtof5 c1 c2 t h1 h2) := by
  intro g hg
  simp only [rtof5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact a3 | exact ⟨a2, a3⟩ | exact ⟨a1, a2⟩

theorem above_rccx (top mid bot : Fin N)
    (h1 : top.val + 1 = mid.val ∨ mid.val + 1 = top.val)
    (h2 : bot.val + 1 = mid.val ∨ mid.val + 1 = bot.val) (a1 : 1 ≤ top.val)
    (a2 : 1 ≤ mid.val) (a3 : 1 ≤ bot.val) : Above 1 (rccx top mid bot h1 h2) := by
  intro g hg
  simp only [rccx, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact a2 | exact ⟨a1, a2⟩ | exact ⟨a3, a2⟩

/-- **The cell `W`**: the relative-phase Toffoli with its target at one end of three
adjacent positions flips the target iff both controls are one, up to a phase; 5 CNOTs. -/
theorem spec_toffoliEnd (t near far : ℕ) (ht1 : 1 ≤ t) (hn1 : 1 ≤ near) (hf1 : 1 ≤ far)
    (ht : t < N) (hn : near < N) (hf : far < N)
    (h1 : far + 1 = near ∨ near + 1 = far) (h2 : near + 1 = t ∨ t + 1 = near)
    (h13 : far ≠ t) : Spec (toffoliEnd N t near far) (ccW t far near) 5 where
  sem := ⟨ccPerm ⟨far, hf⟩ ⟨t, ht⟩ ⟨near, hn⟩ (fin_ne hf ht h13) (fin_ne hn ht (by omega)), by
    rw [toffoliEnd_eq t near far ht hn hf h1 h2]
    exact umono_rtof5 _ _ _ h1 h2 (fin_ne hf ht h13), fun x => by
    funext i
    rw [ccPerm_apply, wire_update, ccW, Function.update_apply, wire_mk x t ht,
      wire_mk x far hf, wire_mk x near hn]⟩
  unitary := by
    rw [toffoliEnd_eq t near far ht hn hf h1 h2]
    exact unitaryGates_rtof5 _ _ _ _ _
  above := by
    rw [toffoliEnd_eq t near far ht hn hf h1 h2]
    exact above_rtof5 _ _ _ _ _ hf1 hn1 ht1
  count := by
    rw [toffoliEnd_eq t near far ht hn hf h1 h2]
    rfl

/-- **The cell `V`**: the relative-phase Toffoli with its target between its controls;
3 CNOTs. -/
theorem spec_toffoliMid (a m b : ℕ) (ha1 : 1 ≤ a) (hm1 : 1 ≤ m) (hb1 : 1 ≤ b)
    (ha : a < N) (hm : m < N) (hb : b < N)
    (h1 : a + 1 = m ∨ m + 1 = a) (h2 : b + 1 = m ∨ m + 1 = b) :
    Spec (toffoliMid N a m b) (ccW m a b) 3 where
  sem := ⟨ccPerm ⟨a, ha⟩ ⟨m, hm⟩ ⟨b, hb⟩ (fin_ne ha hm (by omega)) (fin_ne hb hm (by omega)), by
    rw [toffoliMid_eq a m b ha hm hb h1 h2]
    exact umono_rccx _ _ _ h1 h2, fun x => by
    funext i
    rw [ccPerm_apply, wire_update, ccW, Function.update_apply, wire_mk x m hm,
      wire_mk x a ha, wire_mk x b hb]⟩
  unitary := by
    rw [toffoliMid_eq a m b ha hm hb h1 h2]
    exact unitaryGates_rccx _ _ _ _ _
  above := by
    rw [toffoliMid_eq a m b ha hm hb h1 h2]
    exact above_rccx _ _ _ _ _ ha1 hm1 hb1
  count := by
    rw [toffoliMid_eq a m b ha hm hb h1 h2]
    rfl

/-- The action of the in-place AND on the bits: `x_2 ^= x_1 (1 - x_3)`, then
`x_1 ^= x_2`. -/
def andW (w : ℕ → Bool) : ℕ → Bool := cxW 2 1 (notW 3 (ccW 2 1 3 (notW 3 w)))

/-- **The cell `A`** on the positions `1, 2, 3`; 4 CNOTs. -/
theorem spec_andInPlace (hN : 3 < N) : Spec (andInPlace N 1 2 3) andW 4 :=
  (((spec_x 3 (by omega) hN).append
    (spec_toffoliMid 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) hN
      (by omega) (by omega))).append (spec_x 3 (by omega) hN)).append
    (spec_cx 2 1 (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The in-place AND on a state whose helper bit is `0`:
`(x_1, 0, x_3) ↦ (x_1 x_3, x_1 (1 - x_3), x_3)`; the other bits are unchanged. -/
theorem andW_apply (w : ℕ → Bool) (h2 : w 2 = false) (i : ℕ) :
    andW w i = if i = 1 then (w 1 && w 3) else if i = 2 then (w 1 && !w 3) else w i := by
  simp only [andW, cxW, notW, ccW, Function.update_apply]
  by_cases h : i = 1
  · subst h
    cases h1 : w 1 <;> cases h3 : w 3 <;> simp [h2]
  · by_cases h' : i = 2
    · subst h'
      cases h1 : w 1 <;> cases h3 : w 3 <;> simp [h2]
    · by_cases h'' : i = 3
      · subst h''
        simp
      · simp [h, h', h'']

end Helper
