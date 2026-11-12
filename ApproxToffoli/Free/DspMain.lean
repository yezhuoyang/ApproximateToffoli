/-
The da Silva–Park circuit is the conditional, exactly, with `4N² - 12N + 10` CNOTs.

Passes 1 and 2 are `wcirc` on the targets `1 .. N-1`: bit `j` is flipped iff the bits
`0 .. j-1` are all one, with phase `-i` for every flip of a control.  Passes 3 and 4 are
`wcirc` on the targets `1 .. N-2` with the opposite signs: they undo the flips of the
controls and cancel the phases.  What remains is the flip of the target.
-/
import Mathlib
import ApproxToffoli.Free.DspPass

namespace Dsp

open Matrix Free ExactLine
open Line (St hGate pGate xGate oneMat ctrlMat m2 condMat)
open Qulin (qb forUp)

variable {N : ℕ}

/-! ### The four passes are two instances of `wcirc` -/

theorem wcirc_eq (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (m : ℕ) :
    wcirc N hN top sgn (m + 1)
      = forUp (m + 1) (fun i => onto N hN top sgn 0 (m + 1 - i)) ++
        forUp m (fun i => onto N hN top (fun _ => -1) 1 (i + 2)) := by
  unfold wcirc
  rw [forUp_succ' m (fun i => onto N hN top (fun _ => -1) 1 (i + 1))]
  rfl

theorem pass12_eq (M : ℕ) (hN : 0 < M + 3) :
    pass1 (M + 3) hN ++ pass2 (M + 3) hN = wcirc (M + 3) hN true (fun _ => 1) (M + 2) := by
  rw [wcirc_eq]
  rfl

theorem pass34_eq (M : ℕ) (hN : 0 < M + 3) :
    pass3 (M + 3) hN ++ pass4 (M + 3) hN
      = wcirc (M + 3) hN false (fun c => if c = 0 then -1 else 1) (M + 1) := by
  rw [wcirc_eq]
  rfl

theorem dsp_eq (M : ℕ) (hN : 0 < M + 3) :
    dsp (M + 3) hN = wcirc (M + 3) hN true (fun _ => 1) (M + 2)
      ++ wcirc (M + 3) hN false (fun c => if c = 0 then -1 else 1) (M + 1) := by
  unfold dsp
  rw [List.append_assoc (pass1 (M + 3) hN ++ pass2 (M + 3) hN), pass12_eq, pass34_eq]

/-! ### Counting -/

theorem cnots_wcirc (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (m : ℕ) (hm : m < N) :
    cnots (wcirc N hN top sgn m) = 2 * m * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [wcirc_succ, cnots_append, cnots_append, cnots_onto hN _ _ hm, cnots_onto hN _ _ hm,
      ih (by omega), Nat.sub_zero, Nat.add_sub_cancel]
    ring

theorem cnots_dsp (M : ℕ) (hN : 0 < M + 3) : cnots (dsp (M + 3) hN) = dspCnots (M + 3) := by
  rw [dsp_eq, cnots_append, cnots_wcirc hN _ _ _ (by omega), cnots_wcirc hN _ _ _ (by omega)]
  unfold dspCnots
  have h : 4 * (M + 3) ^ 2 = 12 * (M + 3) + (4 * M ^ 2 + 12 * M) := by ring
  rw [h, Nat.add_sub_cancel_left]
  ring

theorem unitaryGates_wcirc (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (m : ℕ) :
    UnitaryGates (wcirc N hN top sgn m) :=
  unitaryGates_append
    (Qulin.unitaryGates_forUp _ _ (fun _ _ => unitaryGates_onto hN top _ _ _))
    (Qulin.unitaryGates_forUp _ _ (fun _ _ => unitaryGates_onto hN top _ _ _))

theorem unitaryGates_dsp (M : ℕ) (hN : 0 < M + 3) : UnitaryGates (dsp (M + 3) hN) := by
  rw [dsp_eq]
  exact unitaryGates_append (unitaryGates_wcirc hN _ _ _) (unitaryGates_wcirc hN _ _ _)

/-! ### Passes 3 and 4 undo passes 1 and 2 on the controls -/

/-- After passes 1 and 2, "bit `0` is one and bits `1 .. j` are zero" holds exactly when
the bits `0 .. j` were all one before. -/
theorem Qp_true_spec (hN : 0 < N) {m : ℕ} (hm : m < N) {σ : Equiv.Perm (St N)}
    (hσ : WSpec N hN false m σ) (x : St N) (j : ℕ) (hj : j ≤ m) :
    Qp N hN true j (σ x) = Qp N hN false j x := by
  induction j with
  | zero =>
    rw [Qp_zero, Qp_zero,
      hσ.2 x _ (fun j' hj' => Qulin.qb_ne hN (by omega) (by omega) (by omega))]
  | succ j ih =>
    rw [Qp_succ, Qp_succ, ih (by omega), hσ.1 x j (by omega)]
    cases Qp N hN false j x <;> cases x (qb N hN (j + 1)) <;> rfl

/-- The permutation of the whole circuit: only bit `m + 1` (the target) is flipped. -/
theorem comb_perm (hN : 0 < N) {m : ℕ} (hm : m + 1 < N) {σ1 σ2 : Equiv.Perm (St N)}
    (h1 : WSpec N hN false (m + 1) σ1) (h2 : WSpec N hN true m σ2) (x : St N) :
    σ2 (σ1 x) = Function.update x (qb N hN (m + 1))
      (xor (x (qb N hN (m + 1))) (Qp N hN false m x)) := by
  funext r
  by_cases hr : ∃ j, j < m ∧ r = qb N hN (j + 1)
  · obtain ⟨j, hj, rfl⟩ := hr
    rw [h2.1 _ j hj, h1.1 x j (by omega), Qp_true_spec hN hm h1 x j (by omega),
      Function.update_of_ne (Qulin.qb_ne hN (by omega) hm (by omega)), Bool.xor_assoc,
      Bool.xor_self, Bool.xor_false]
  · have hr' : ∀ j < m, r ≠ qb N hN (j + 1) := fun j hj e => hr ⟨j, hj, e⟩
    rw [h2.2 _ r hr']
    by_cases hrt : r = qb N hN (m + 1)
    · subst hrt
      rw [h1.1 x m (by omega), Function.update_self]
    · rw [Function.update_of_ne hrt]
      refine h1.2 x r (fun j hj => ?_)
      by_cases hjm : j < m
      · exact hr' j hjm
      · have hjm' : j = m := by omega
        subst hjm'
        exact hrt

/-- The phases of the whole circuit cancel. -/
theorem comb_phase (hN : 0 < N) {m : ℕ} (hm : m + 2 = N) {σ1 : Equiv.Perm (St N)}
    (h1 : WSpec N hN false (m + 1) σ1) (x : St N) :
    wphase N hN false true m (σ1 x) * wphase N hN true false (m + 1) x = 1 := by
  unfold wphase
  have hlast : (true && decide (m + 1 = N - 1)) = true := by
    simp
    omega
  rw [Finset.prod_range_succ, hlast, ← mul_assoc, ← Finset.prod_mul_distrib]
  have hone : (if Qp N hN false m x then kap true false else 1) = 1 := by
    cases Qp N hN false m x <;> simp [kap]
  rw [hone, mul_one]
  apply Finset.prod_eq_one
  intro j hj
  have hj' := Finset.mem_range.1 hj
  have hd : decide (j + 1 = N - 1) = false := by
    simp
    omega
  rw [Qp_true_spec hN (by omega) h1 x j (by omega), hd]
  cases Qp N hN false j x <;> simp [kap]

theorem Qp_false_iff (hN : 0 < N) (x : St N) (j : ℕ) :
    Qp N hN false j x = true ↔ ∀ i ≤ j, x (qb N hN i) = true := by
  induction j with
  | zero =>
    rw [Qp_zero]
    exact ⟨fun h i hi => by rw [Nat.le_zero.1 hi]; exact h, fun h => h 0 le_rfl⟩
  | succ j ih =>
    rw [Qp_succ, Bool.and_eq_true, ih, Bool.xor_false]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hij : i ≤ j
      · exact h1 i hij
      · have hij' : i = j + 1 := by omega
        rw [hij']
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h (j + 1) le_rfl⟩

/-- The flip condition of the target is "all controls are one". -/
theorem Qp_allOthers (hN : 0 < N) {m : ℕ} (hm : m + 2 = N) (x : St N) :
    Qp N hN false m x = Line.allOthers (qb N hN (m + 1)) x := by
  rw [Bool.eq_iff_iff, Qp_false_iff]
  unfold Line.allOthers
  rw [decide_eq_true_iff]
  constructor
  · intro h r hr
    have hlt := r.isLt
    have h1 : r.val ≠ m + 1 := fun e => hr (by rw [← Qulin.qb_self hN r, e])
    have h2 := h r.val (by omega)
    rwa [Qulin.qb_self] at h2
  · intro h i hi
    exact h _ (Qulin.qb_ne hN (by omega) (by omega) (by omega))

/-! ### The theorem -/

/-- **The da Silva–Park circuit is the conditional**, exactly. -/
theorem circMat_dsp (M : ℕ) (hN : 0 < M + 3) :
    circMat (dsp (M + 3) hN) = condMat (qb (M + 3) hN (M + 2)) := by
  obtain ⟨σ1, hc1, hs1⟩ := circMat_wcirc hN true false (fun _ => 1) (by simp)
    (fun _ _ => rfl) (M + 2) (by omega)
  obtain ⟨σ2, hc2, hs2⟩ := circMat_wcirc hN false true (fun c => if c = 0 then -1 else 1)
    (by simp) (fun c hc => if_neg (by omega)) (M + 1) (by omega)
  have hperm : σ2 * σ1 = Line.condPerm (qb (M + 3) hN (M + 2)) := by
    apply Equiv.ext
    intro x
    rw [Equiv.Perm.mul_apply, comb_perm hN (m := M + 1) (by omega) hs1 hs2,
      Qp_allOthers hN (by omega)]
    rfl
  have hph : (fun x => wphase (M + 3) hN false true (M + 1) (σ1 x)
      * wphase (M + 3) hN true false (M + 2) x) = fun _ => 1 :=
    funext fun x => comb_phase hN (by omega) hs1 x
  rw [dsp_eq, circMat_append, hc1, hc2, Line.mono_mul, hperm, hph]
  rfl

/-- **The da Silva–Park scheme, formalized.**  For every `N ≥ 3` the circuit has unitary
one-qubit gates, equals the conditional with target qubit `N - 1` exactly, and has
exactly `4N² - 12N + 10` CNOTs. -/
theorem dsp_goal : DspGoal := by
  intro N hN3
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  have hN : 0 < M + 3 := by omega
  have ht : (⟨M + 3 - 1, by omega⟩ : Fin (M + 3)) = qb (M + 3) hN (M + 2) :=
    Fin.ext (Qulin.qb_val hN (by omega)).symm
  refine ⟨unitaryGates_dsp M hN, ?_, cnots_dsp M hN⟩
  rw [ht]
  exact circMat_dsp M hN

end Dsp
