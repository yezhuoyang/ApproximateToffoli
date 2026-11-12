/-
(ii) The centre circuit on the states `pqSt x a`:

    centrePerm (pqSt x) = pqSt (chiSt x),

where `chiSt x` flips the wires `1, …, 2a`.  The carries `c'` of the complemented input
satisfy `¬c'_j = c_j ⊕ ∏_{l < j} (S_l ⊕ T_l)` (`cr_chiSt`), and the product is what the
centre circuit adds to `S_j` when it runs on `pqSt x` (`gprop_pqSt`).
-/
import Mathlib
import ApproxToffoli.Line.LowIncSpec

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- The carries of the complemented input. -/
theorem cr_chiSt {a : ℕ} (h : 2 * a < N) (x : St N) {j : ℕ} (hj : j ≤ a) :
    cr (chiSt x a) a j = !(xor (cr x a j) (gprop (sBit x a) (tBit x a) j)) := by
  refine Eq.trans (gcarry_congr j (fun i hi => ?_) (fun i hi => ?_))
    (gcarry_not (sBit x a) (tBit x a) j)
  · exact chiSt_in h x (by omega) (by omega)
  · exact chiSt_in h x (by omega) (by omega)

/-- The product of the propagate bits `S_l ⊕ T_l`, `l < a - k`, read off `pqSt x`: the
bit `S_0 ⊕ T_0` and the conjunction of the odd wires `2k + 1, …, 2a - 3` of `pqSt x`. -/
theorem gprop_pqSt {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) {k : ℕ} (hk : k + 1 ≤ a) :
    gprop (sBit x a) (tBit x a) (a - k)
      = (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd (pqSt x a) (2 * k) (a - 1 - k)) := by
  rw [Bool.eq_iff_iff, gprop_eq_true_iff, Bool.and_eq_true, tAnd_eq_true_iff]
  constructor
  · intro H
    refine ⟨H 0 (by omega), fun i hi => ?_⟩
    have e1 : 2 * a - 2 * (a - 1 - k - i) = 2 * k + 2 * i + 1 + 1 := by omega
    have e2 : 2 * a - 2 * (a - 1 - k - i) - 1 = 2 * k + 2 * i + 1 := by omega
    have := H (a - 1 - k - i) (by omega)
    rw [sBit, tBit, e2, e1, Bool.xor_comm] at this
    rw [pqSt_odd h.2 x (by omega) (by omega)]
    exact this
  · rintro ⟨hp, G⟩ l hl
    by_cases h0 : l = 0
    · rw [h0]
      exact hp
    · have e1 : 2 * a - 2 * l = 2 * k + 2 * (a - 1 - k - l) + 1 + 1 := by omega
      have e2 : 2 * a - 2 * l - 1 = 2 * k + 2 * (a - 1 - k - l) + 1 := by omega
      have := G (a - 1 - k - l) (by omega)
      rw [pqSt_odd h.2 x (by omega) (by omega), Bool.xor_comm] at this
      rw [sBit, tBit, e2, e1]
      exact this

/-- **(ii)** The centre circuit sends `PQ x` to `PQ (χ x)`. -/
theorem centrePerm_pqSt {a : ℕ} (h : 2 ≤ a ∧ 2 * a < N) (x : St N) :
    centrePerm N a (pqSt x a) = pqSt (chiSt x a) a := by
  have ha := h.1
  have hN := h.2
  have y1 : wire (pqSt x a) (2 * a) = wire x (2 * a) := pqSt_top hN x (by omega)
  have y2 : wire (pqSt x a) (2 * a - 1) = wire x (2 * a - 1) := pqSt_top hN x (by omega)
  apply wire_ext
  intro j
  by_cases hF : 2 * a < j
  · rw [centrePerm_wire_above h _ hF, pqSt_top hN x (by omega), pqSt_top hN _ (by omega),
      chiSt_out hN x (by omega)]
  by_cases hS0 : j = 2 * a
  · rw [hS0, centrePerm_wire_S0 h, y1, pqSt_top hN _ (by omega),
      chiSt_in hN x (by omega) (by omega)]
  by_cases hT0 : j = 2 * a - 1
  · rw [hT0, centrePerm_wire_T0 h, y2, pqSt_top hN _ (by omega),
      chiSt_in hN x (by omega) (by omega)]
  by_cases ho : j % 2 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    have e : ∀ u v : Bool, xor u v = xor (!u) (!v) := by decide
    rw [centrePerm_wire_T h _ (by omega), pqSt_odd hN x (by omega) ho,
      pqSt_odd hN _ (by omega) ho, chiSt_in hN x (j := 2 * k + 1) (by omega) (by omega),
      chiSt_in hN x (j := 2 * k + 1 + 1) (by omega) (by omega)]
    exact e _ _
  by_cases h0 : j = 0
  · have e : ∀ u c g : Bool, (!(xor (xor u c) g)) = xor u (!(xor c g)) := by decide
    have hc := cr_chiSt hN x (j := a) (le_refl a)
    have hg : gprop (sBit x a) (tBit x a) a
        = (xor (wire x (2 * a)) (wire x (2 * a - 1)) && tAnd (pqSt x a) 0 (a - 1)) :=
      gprop_pqSt h x (k := 0) (by omega)
    have e0 : a - 0 / 2 = a := by omega
    rw [h0, centrePerm_wire_zero h, y1, y2, pqSt_even hN x (j := 0) (by omega) (by omega),
      pqSt_even hN (chiSt x a) (j := 0) (by omega) (by omega),
      chiSt_out hN x (j := 0) (by omega), e0, hc, hg]
    exact e _ _ _
  have e : ∀ u c p : Bool, xor (xor u c) p = xor (!u) (!(xor c p)) := by decide
  by_cases hS1 : j = 2 * a - 2
  · have hc := cr_chiSt hN x (j := 1) (by omega)
    have hg : gprop (sBit x a) (tBit x a) 1 = xor (wire x (2 * a)) (wire x (2 * a - 1)) :=
      Bool.true_and _
    have e1 : a - (2 * a - 2) / 2 = 1 := by omega
    rw [hS1, centrePerm_wire_S1 h, y1, y2,
      pqSt_even hN x (j := 2 * a - 2) (by omega) (by omega),
      pqSt_even hN (chiSt x a) (j := 2 * a - 2) (by omega) (by omega),
      chiSt_in hN x (j := 2 * a - 2) (by omega) (by omega), e1, hc, hg]
    exact e _ _ _
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    have hc := cr_chiSt hN x (j := a - k) (by omega)
    have hg := gprop_pqSt h x (k := k) (by omega)
    have ek : a - 2 * k / 2 = a - k := by omega
    rw [centrePerm_wire_S h _ (by omega) (by omega), y1, y2,
      pqSt_even hN x (j := 2 * k) (by omega) (by omega),
      pqSt_even hN (chiSt x a) (j := 2 * k) (by omega) (by omega),
      chiSt_in hN x (j := 2 * k) (by omega) (by omega), ek, hc, hg]
    exact e _ _ _

end Line
