/-
The increment circuit on a line.

`incOf K M R = K ++ M ++ K⁻¹ ++ R` with `K` the ripple, `M` the toggle and `R` the low
incrementer.  `inc_general` (`2 ≤ a`) and `inc_small` (`a = 1`) show that it is, up to
phases, a permutation that leaves wire `0` unchanged and, when wire `0` is one, adds one
to the address `val a k gap` modulo `2^(a+k+1)`.  `exists_increment` packages both cases
for every `N ≥ 4`, with at most `29 (N - 1)` CNOTs.
-/
import Mathlib
import ApproxToffoli.Line.Increment
import ApproxToffoli.Line.Toggle

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-- The increment circuit built from a ripple `K`, a toggle `M`, a low incrementer `R`. -/
def incOf (K M R : List (Gate N)) : List (Gate N) := K ++ M ++ invCirc K ++ R

theorem cnots_incOf (K M R : List (Gate N)) :
    cnots (incOf K M R) = 2 * cnots K + cnots M + cnots R := by
  simp only [incOf, cnots_append, cnots_invCirc]
  omega

theorem unitaryGates_incOf {K M R : List (Gate N)} (hK : UnitaryGates K)
    (hM : UnitaryGates M) (hR : UnitaryGates R) : UnitaryGates (incOf K M R) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append hK hM)
    (unitaryGates_invCirc hK)) hR

theorem umono_incOf {K M R : List (Gate N)} {κ μ ρ : Equiv.Perm (St N)}
    (hK : UMono (circMat K) κ) (hM : UMono (circMat M) μ) (hR : UMono (circMat R) ρ) :
    UMono (circMat (incOf K M R)) (ρ * (κ⁻¹ * (μ * κ))) := by
  have hKi : UMono (circMat (invCirc K)) κ⁻¹ := by
    rw [circMat_invCirc]
    exact hK.conjTranspose
  exact umono_append (umono_append (umono_append hK hM) hKi) hR

/-- "All odd wires below `2a` are one" is "all bits of the low half are one". -/
theorem oddOnes_eq_allT (a : ℕ) (hN : 2 * a ≤ N) (x : St N) : oddOnes a x = allT a x := by
  unfold oddOnes allT
  rw [decide_eq_decide]
  constructor
  · intro H i hi
    rw [wire_mk x _ (by omega)]
    exact H ⟨2 * a - 2 * i - 1, by omega⟩ (by show 2 * a - 2 * i - 1 < 2 * a; omega)
      (by show (2 * a - 2 * i - 1) % 2 = 1; omega)
  · intro H r h1 h2
    have := H (a - 1 - r.val / 2) (by omega)
    rw [show 2 * a - 2 * (a - 1 - r.val / 2) - 1 = r.val by omega, wire_val] at this
    exact this

/-- The toggle on wires. -/
theorem markPerm_wire (a : ℕ) (h0 : 0 < N) (hN : 2 * a ≤ N) (x : St N) (j : ℕ) :
    wire (flipPerm ⟨0, h0⟩ (oddOnes a) (oddOnes_update a h0) x) j
      = if j = 0 then xor (wire x 0) (allT a x) else wire x j := by
  rw [flipPerm_apply, wire_update, oddOnes_eq_allT a hN, wire_mk x 0 h0]

/-- The ripple leaves wire `0` and the odd wires below `2a` unchanged. -/
theorem ripple_facts {a k : ℕ} {gap : Bool} (hat : 2 * a ≤ rippleTop k gap)
    (hN : rippleTop k gap < N) :
    (∀ x : St N, wire (ripplePerm N k gap x) 0 = wire x 0) ∧
    (∀ (x : St N) (j : ℕ), j % 2 = 1 → j < 2 * a →
      wire (ripplePerm N k gap x) j = wire x j) :=
  ⟨fun x => ripplePerm_other k gap hN x 0 (fun i _ => by omega) (by unfold rippleTop; omega),
   fun x j h1 h2 => ripplePerm_other k gap hN x j (fun i _ => by omega) (by omega)⟩

/-- **The increment, `2 ≤ a`.** -/
theorem inc_general {a k : ℕ} {gap : Bool} (ha : 2 ≤ a) (hka : k ≤ a)
    (hat : 2 * a ≤ rippleTop k gap) (hN : rippleTop k gap < N) :
    ∃ ι : Equiv.Perm (St N),
      UMono (circMat (incOf (ripple N k gap) (mark a (by omega) ha) (lowInc N a))) ι ∧
      ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (a + (k + 1))) := by
  have h2a : 2 * a < N := by omega
  obtain ⟨-, -, ρ, hρ, hρs⟩ := lowInc_spec (N := N) ⟨ha, h2a⟩
  have h0 : 0 < N := by omega
  refine ⟨_, umono_incOf (circMat_ripple N k gap) (circMat_mark a (by omega) ha) hρ,
    fun x => ?_⟩
  refine inc_core hka _ _ ρ (ripple_facts hat hN).1 (ripple_facts hat hN).2
    (ripple_add k gap hN) ?_ ?_ ?_ ?_ ?_ x
  · intro y
    rw [markPerm_wire a h0 (by omega)]
    rfl
  · intro y j hj
    rw [markPerm_wire a h0 (by omega), if_neg hj]
  · intro y
    refine targetVal_congr (fun i hi => ?_) ?_
    · have := (hρs y).1 (i + 1) (by omega) (by omega)
      rwa [show 2 * (i + 1) = 2 * i + 2 by omega] at this
    · by_cases ht : rippleTop k gap = 2 * a
      · rw [ht]
        exact (hρs y).1 a (by omega) le_rfl
      · exact (hρs y).2.1 _ (by omega)
  · exact fun y => (hρs y).2.2.1
  · exact fun y => (hρs y).2.2.2

/-! ### The case `a = 1` -/

/-- The toggle for `a = 1`: one CNOT. -/
def markS (h : 1 < N) : List (Gate N) := [.cx ⟨1, h⟩ ⟨0, by omega⟩ (Or.inr rfl)]

/-- The low incrementer for `a = 1`: one CNOT and a NOT. -/
def lowIncS (h : 1 < N) : List (Gate N) :=
  [.cx ⟨1, h⟩ ⟨0, by omega⟩ (Or.inr rfl), .one ⟨1, h⟩ xGate]

theorem allT_one (x : St N) : allT 1 x = wire x 1 := by
  unfold allT
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro H
    exact H 0 (by omega)
  · intro H i hi
    have : i = 0 := by omega
    subst this
    exact H

theorem Tval_one (x : St N) : Tval 1 x = (wire x 1).toNat := by
  simp [Tval]

/-- **The increment, `a = 1`.** -/
theorem inc_small {k : ℕ} {gap : Bool} (hk : k ≤ 1) (hat : 2 ≤ rippleTop k gap)
    (hN : rippleTop k gap < N) :
    ∃ ι : Equiv.Perm (St N),
      UMono (circMat (incOf (ripple N k gap) (markS (by omega)) (lowIncS (by omega)))) ι ∧
      ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val 1 k gap (ι x) = (val 1 k gap x + 1) % 2 ^ (1 + (k + 1))) := by
  have h1 : 1 < N := by omega
  have h0 : 0 < N := by omega
  have n10 : (⟨1, h1⟩ : Fin N) ≠ ⟨0, h0⟩ := by
    intro h
    simpa using congrArg Fin.val h
  have hμ : UMono (circMat (markS (N := N) h1)) (cxPerm ⟨1, h1⟩ ⟨0, h0⟩ n10) :=
    umono_single (umono_cx _ _ _)
  have hρ : UMono (circMat (lowIncS (N := N) h1))
      (xPerm ⟨1, h1⟩ * cxPerm ⟨1, h1⟩ ⟨0, h0⟩ n10) :=
    umono_cons (umono_cx _ _ _) (umono_single (umono_x _))
  have hcx : ∀ (y : St N) (j : ℕ), wire (cxPerm ⟨1, h1⟩ ⟨0, h0⟩ n10 y) j
      = if j = 0 then xor (wire y 0) (wire y 1) else wire y j := by
    intro y j
    rw [cxPerm_apply, wire_update, wire_mk y 0 h0, wire_mk y 1 h1]
  have hx : ∀ (y : St N) (j : ℕ), wire (xPerm ⟨1, h1⟩ y) j
      = if j = 1 then !wire y 1 else wire y j := by
    intro y j
    rw [xPerm_apply, wire_update, wire_mk y 1 h1]
  refine ⟨_, umono_incOf (circMat_ripple N k gap) hμ hρ, fun x => ?_⟩
  refine inc_core (a := 1) hk _ _ _ (ripple_facts (a := 1) hat hN).1
    (ripple_facts (a := 1) hat hN).2 (ripple_add k gap hN) ?_ ?_ ?_ ?_ ?_ x
  · intro y
    rw [hcx, if_pos rfl, allT_one]
  · intro y j hj
    rw [hcx, if_neg hj]
  · intro y
    have hw : ∀ j, 2 ≤ j →
        wire ((xPerm ⟨1, h1⟩ * cxPerm ⟨1, h1⟩ ⟨0, h0⟩ n10) y) j = wire y j := by
      intro j hj
      rw [Equiv.Perm.mul_apply, hx, if_neg (by omega), hcx, if_neg (by omega)]
    exact targetVal_congr (fun i _ => hw _ (by omega)) (hw _ hat)
  · intro y
    rw [Tval_one, Tval_one, Equiv.Perm.mul_apply, hx, if_pos rfl, hcx, if_neg (by omega)]
    cases wire y 1 <;> rfl
  · intro y
    rw [Equiv.Perm.mul_apply, hx, if_neg (by omega), hcx, if_pos rfl, allT_one]

/-! ### Every `N ≥ 4` -/

/-- The CNOT count of the increment: `30` for `N = 4`; with `m = N - 1`, `29 m - 50` for
even `m ≥ 4` and `29 m - 59` for odd `m ≥ 5`. -/
def incCnots (N : ℕ) : ℕ :=
  if N = 4 then 30 else if N % 2 = 1 then 29 * (N - 1) - 50 else 29 * (N - 1) - 59

theorem incCnots_le (N : ℕ) (hN : 4 ≤ N) : incCnots N ≤ 29 * (N - 1) := by
  unfold incCnots
  split_ifs <;> omega

theorem exists_increment_aux {a k : ℕ} {gap : Bool} (ha : 2 ≤ a) (hka : k ≤ a)
    (hat : 2 * a ≤ rippleTop k gap) (ht : rippleTop k gap = N - 1) (hN : 4 ≤ N)
    (hs : a + (k + 1) = N - 1)
    (hc : 2 * (13 * k + (if gap then 4 else 1)) + (8 * a - 9) + (24 * a - 23)
      = incCnots N) :
    ∃ (a k : ℕ) (gap : Bool) (inc : List (Gate N)) (ι : Equiv.Perm (St N)),
      k ≤ a ∧ 2 * a ≤ rippleTop k gap ∧ rippleTop k gap = N - 1 ∧ a + (k + 1) = N - 1 ∧
      UnitaryGates inc ∧ cnots inc = incCnots N ∧ UMono (circMat inc) ι ∧
      ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1)) := by
  have hN' : rippleTop k gap < N := by omega
  have h2a : 2 * a < N := by omega
  obtain ⟨ι, hι, hs'⟩ := inc_general (N := N) ha hka hat hN'
  refine ⟨a, k, gap, _, ι, hka, hat, ht, hs,
    unitaryGates_incOf (unitaryGates_ripple N k gap) (unitaryGates_mark a _ ha)
      (lowInc_spec (N := N) ⟨ha, h2a⟩).2.1, ?_, hι, ?_⟩
  · rw [cnots_incOf, cnots_ripple k gap hN', cnots_mark,
      (lowInc_spec (N := N) ⟨ha, h2a⟩).1]
    exact hc
  · rw [← hs]
    exact hs'

/-- **The increment on a line, with its exact CNOT count.**  For every `N ≥ 4` there is a
circuit with exactly `incCnots N` CNOTs that is, up to phases, a permutation `ι` leaving
wire `0` unchanged and adding one to the address modulo `2^(N-1)` when wire `0` is one. -/
theorem exists_increment_count (hN : 4 ≤ N) :
    ∃ (a k : ℕ) (gap : Bool) (inc : List (Gate N)) (ι : Equiv.Perm (St N)),
      k ≤ a ∧ 2 * a ≤ rippleTop k gap ∧ rippleTop k gap = N - 1 ∧ a + (k + 1) = N - 1 ∧
      UnitaryGates inc ∧ cnots inc = incCnots N ∧ UMono (circMat inc) ι ∧
      ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1)) := by
  rcases Nat.lt_or_ge N 5 with h5 | h5
  · have h4 : N = 4 := by omega
    subst h4
    obtain ⟨ι, hι, hs⟩ := inc_small (N := 4) (k := 1) (gap := false) le_rfl
      (by decide) (by decide)
    refine ⟨1, 1, false, _, ι, le_rfl, by decide, rfl, rfl,
      unitaryGates_incOf (unitaryGates_ripple 4 1 false)
        (unitaryGates_cons_cx _ _ _ unitaryGates_nil)
        (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ xGate_unitary
          unitaryGates_nil)), ?_, hι, hs⟩
    rw [cnots_incOf, cnots_ripple 1 false (by decide)]
    exact (by decide : 2 * (13 * 1 + 1) + 1 + 1 = incCnots 4)
  · rcases Nat.even_or_odd' (N - 1) with ⟨a, ha | ha⟩
    · have hi : incCnots N = 29 * (N - 1) - 50 := by
        rw [incCnots, if_neg (by omega), if_pos (by omega)]
      refine exists_increment_aux (a := a) (k := a - 1) (gap := true) (by omega) (by omega)
        ?_ ?_ hN (by omega) ?_
      · rw [rippleTop_true]
        omega
      · rw [rippleTop_true]
        omega
      · rw [hi]
        simp only [↓reduceIte]
        omega
    · have hi : incCnots N = 29 * (N - 1) - 59 := by
        rw [incCnots, if_neg (by omega), if_neg (by omega)]
      refine exists_increment_aux (a := a) (k := a) (gap := false) (by omega) le_rfl
        ?_ ?_ hN (by omega) ?_
      · rw [rippleTop_false]
        omega
      · rw [rippleTop_false]
        omega
      · rw [hi]
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega

/-- **The increment on a line.**  For every `N ≥ 4` there is a circuit with at most
`29 (N - 1)` CNOTs that is, up to phases, a permutation `ι` leaving wire `0` unchanged
and adding one to the address modulo `2^(N-1)` when wire `0` is one. -/
theorem exists_increment (hN : 4 ≤ N) :
    ∃ (a k : ℕ) (gap : Bool) (inc : List (Gate N)) (ι : Equiv.Perm (St N)),
      k ≤ a ∧ 2 * a ≤ rippleTop k gap ∧ rippleTop k gap = N - 1 ∧ a + (k + 1) = N - 1 ∧
      UnitaryGates inc ∧ cnots inc ≤ 29 * (N - 1) ∧ UMono (circMat inc) ι ∧
      ∀ x : St N, wire (ι x) 0 = wire x 0 ∧ (wire x 0 = true →
        val a k gap (ι x) = (val a k gap x + 1) % 2 ^ (N - 1)) := by
  obtain ⟨a, k, gap, inc, ι, h1, h2, h3, h4, h5, h6, h7⟩ := exists_increment_count hN
  exact ⟨a, k, gap, inc, ι, h1, h2, h3, h4, h5, le_of_eq_of_le h6 (incCnots_le N hN), h7⟩

end Line
