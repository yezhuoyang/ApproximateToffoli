/-
The da Silva–Park circuit: a forward pass followed by a backward pass.

`wcirc m` is the forward pass onto the targets `m, m-1, ..., 1` (all controls below the
target) followed by the backward pass onto the targets `1, ..., m` (controls `≥ 1`,
sign `-`).  Its matrix is a permutation up to phases (`circMat_wcirc`): bit `j + 1` is
flipped exactly when `Qp j` holds (bit `0` is one and bits `1 .. j` all differ from
`neg`), and each flip contributes the phase `kap`.
-/
import Mathlib
import ApproxToffoli.Free.DspCells

namespace Dsp

open Matrix Free ExactLine
open Line (St hGate pGate xGate oneMat ctrlMat m2)
open Qulin (qb forUp)

variable {N : ℕ}

/-! ### A block on one qubit moves through a permutation that does not touch that qubit -/

theorem ctrlMat_mul_mono (t : Fin N) (g : St N → Matrix Bool Bool ℂ) (σ : Equiv.Perm (St N))
    (φ : St N → ℂ)
    (hσ : ∀ x b, σ (Function.update x t b) = Function.update (σ x) t b)
    (hφ : ∀ x b, φ (Function.update x t b) = φ x) :
    ctrlMat t g * mono σ φ = mono σ φ * ctrlMat t (fun x => g (σ x)) := by
  have hbit : ∀ x, σ x t = x t := by
    intro x
    have h := congrFun (hσ x (x t)) t
    rw [Function.update_eq_self, Function.update_self] at h
    exact h
  have hupd : ∀ w x : St N, (∀ r, r ≠ t → w r = x r) → w = Function.update x t (w t) :=
    fun w x h => Function.eq_update_iff.2 ⟨rfl, h⟩
  ext y x
  rw [mul_mono_apply, Line.mono_mul_apply']
  obtain ⟨w, rfl⟩ := σ.surjective y
  rw [Equiv.symm_apply_apply]
  simp only [ctrlMat, Matrix.of_apply]
  rw [hbit w, hbit x]
  have hiff : (∀ r, r ≠ t → σ w r = σ x r) ↔ (∀ r, r ≠ t → w r = x r) := by
    constructor
    · intro h
      have h1 := hupd (σ w) (σ x) h
      rw [hbit w, ← hσ] at h1
      have h2 := σ.injective h1
      intro r hr
      rw [h2, Function.update_of_ne hr]
    · intro h r hr
      rw [hupd w x h, hσ, Function.update_of_ne hr]
  by_cases h : ∀ r, r ≠ t → w r = x r
  · have hw : φ w = φ x := by rw [hupd w x h, hφ]
    rw [if_pos (hiff.2 h), if_pos h, hw, mul_comm]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul, mul_zero]

/-! ### The condition of a flip -/

/-- `Qp neg j x`: bit `0` is one and the bits `1, ..., j` all differ from `neg`. -/
def Qp (N : ℕ) (hN : 0 < N) (neg : Bool) : ℕ → St N → Bool
  | 0, x => x (qb N hN 0)
  | j + 1, x => Qp N hN neg j x && xor (x (qb N hN (j + 1))) neg

theorem Qp_zero (hN : 0 < N) (neg : Bool) (x : St N) : Qp N hN neg 0 x = x (qb N hN 0) := rfl

theorem Qp_succ (hN : 0 < N) (neg : Bool) (j : ℕ) (x : St N) :
    Qp N hN neg (j + 1) x = (Qp N hN neg j x && xor (x (qb N hN (j + 1))) neg) := rfl

/-- `Qp j` reads only the bits `0, ..., j`. -/
theorem Qp_update (hN : 0 < N) (neg : Bool) {j r : ℕ} (hr : r < N) (hj : j < r) (x : St N)
    (b : Bool) : Qp N hN neg j (Function.update x (qb N hN r) b) = Qp N hN neg j x := by
  induction j with
  | zero =>
    rw [Qp_zero, Qp_zero, Function.update_of_ne (Qulin.qb_ne hN (by omega) hr (by omega))]
  | succ j ih =>
    rw [Qp_succ, Qp_succ, ih (by omega),
      Function.update_of_ne (Qulin.qb_ne hN (by omega) hr (by omega))]

/-! ### The telescoping sum of the angles -/

theorem tele (a : ℕ → ℝ) (m : ℕ) :
    a 0 / 2 ^ m + ∑ i ∈ Finset.range m, (2 * a (i + 1) - a i) / 2 ^ (m - i) = a m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : ∑ i ∈ Finset.range m, (2 * a (i + 1) - a i) / 2 ^ (m + 1 - i)
        = (∑ i ∈ Finset.range m, (2 * a (i + 1) - a i) / 2 ^ (m - i)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ, div_div]
    rw [Finset.sum_range_succ, h, show m + 1 - m = 1 by omega]
    linear_combination ih / 2

theorem expo_zero (t : ℕ) : expo 0 t = t - 1 := by simp [expo]

theorem expo_succ (c t : ℕ) : expo (c + 1) t = t - (c + 1) := by simp [expo]

/-- The gates from one control `c ≥ 1` in the two passes: `u` is its bit before the
forward pass and `u xor q` its bit before the backward pass. -/
theorem term_merge (u q neg : Bool) (d : ℝ) :
    (if xor u q = true then -1 * Real.pi / d else 0) + (if u = true then 1 * Real.pi / d else 0)
      = (if neg then -1 else 1) * Real.pi
          * ((2 * (if (q && xor u neg) = true then 1 else 0) - (if q = true then 1 else 0))
              / d) := by
  cases u <;> cases q <;> cases neg <;> simp <;> ring

/-- **The angles of the two passes add up to `± π` times the flip condition.**  Here `x`
is the state before the forward pass and `w` the state before the backward pass. -/
theorem ang_merge (hN : 0 < N) (neg : Bool) (sgn : ℕ → ℝ)
    (h0 : sgn 0 = if neg then -1 else 1) (h1 : ∀ c, 1 ≤ c → sgn c = 1) (m : ℕ) (x w : St N)
    (hw : ∀ i < m, w (qb N hN (i + 1)) = xor (x (qb N hN (i + 1))) (Qp N hN neg i x)) :
    ang N hN (fun _ => -1) 1 (m + 1) m w + ang N hN sgn 0 (m + 1) (m + 1) x
      = if Qp N hN neg m x then (if neg then -1 else 1) * Real.pi else 0 := by
  have ht := tele (fun i => if Qp N hN neg i x then (1 : ℝ) else 0) m
  have key : ang N hN (fun _ => -1) 1 (m + 1) m w + ang N hN sgn 0 (m + 1) (m + 1) x
      = (∑ i ∈ Finset.range m, (if neg then -1 else 1) * Real.pi
            * ((2 * (if Qp N hN neg (i + 1) x then (1 : ℝ) else 0)
                - (if Qp N hN neg i x then 1 else 0)) / 2 ^ (m - i)))
        + (if neg then -1 else 1) * Real.pi
            * ((if Qp N hN neg 0 x then (1 : ℝ) else 0) / 2 ^ m) := by
    unfold ang
    rw [Finset.sum_range_succ', ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [Nat.zero_add, Nat.add_comm 1 i, hw i hi', h1 (i + 1) (by omega), expo_succ,
        Nat.add_sub_add_right, Qp_succ]
      exact term_merge _ _ _ _
    · rw [Nat.add_zero, h0, expo_zero, Nat.add_sub_cancel, Qp_zero]
      cases x (qb N hN 0) <;> cases neg <;> simp <;> ring
  rw [key, ← Finset.mul_sum, ← mul_add, add_comm, ht]
  cases Qp N hN neg m x <;> simp

/-! ### A block of angle `± π` or `0` is a conditional flip up to a phase -/

theorem ctrlMat_flip (t : Fin N) (top neg : Bool) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x t b) = f x) :
    ctrlMat t (fun x => blk top (if f x then (if neg then -1 else 1) * Real.pi else 0))
      = mono (Line.flipPerm t f hf) (fun x => if f x then kap top neg else 1) := by
  rw [Line.ctrlMat_eq_mono t f hf]
  · congr 1
    funext x
    cases hfx : f x
    · simp [blk_zero]
    · simp only [↓reduceIte, blk_pi]
      cases x t <;> simp [m2]
  · intro x a b hab
    cases hfx : f x
    · rw [hfx] at hab
      simp only [Bool.false_eq_true, ↓reduceIte, blk_zero]
      exact Matrix.one_apply_ne (by simpa using hab)
    · rw [hfx] at hab
      simp only [↓reduceIte, blk_pi]
      cases a <;> cases b <;> simp_all [m2]

/-! ### The two passes -/

/-- The forward pass onto the targets `m, ..., 1` (all controls below the target, signs
`sgn`), then the backward pass onto the targets `1, ..., m` (controls `≥ 1`, sign `-`). -/
noncomputable def wcirc (N : ℕ) (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (m : ℕ) :
    List (Gate N) :=
  forUp m (fun i => onto N hN top sgn 0 (m - i)) ++
  forUp m (fun i => onto N hN top (fun _ => -1) 1 (i + 1))

theorem forUp_succ' (m : ℕ) (f : ℕ → List (Gate N)) :
    forUp (m + 1) f = f 0 ++ forUp m (fun i => f (i + 1)) := by
  simp [forUp, List.range_succ_eq_map, List.flatMap_map]

theorem wcirc_zero (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) : wcirc N hN top sgn 0 = [] := rfl

theorem wcirc_succ (hN : 0 < N) (top : Bool) (sgn : ℕ → ℝ) (m : ℕ) :
    wcirc N hN top sgn (m + 1)
      = onto N hN top sgn 0 (m + 1) ++ wcirc N hN top sgn m
        ++ onto N hN top (fun _ => -1) 1 (m + 1) := by
  unfold wcirc
  rw [forUp_succ' m, Qulin.forUp_succ m]
  simp only [Nat.add_sub_add_right, Nat.sub_zero, List.append_assoc]

/-- The phase of the two passes: `kap` for every flip. -/
noncomputable def wphase (N : ℕ) (hN : 0 < N) (top neg : Bool) (m : ℕ) (x : St N) : ℂ :=
  ∏ j ∈ Finset.range m,
    if Qp N hN neg j x then kap (top && decide (j + 1 = N - 1)) neg else 1

theorem wphase_update (hN : 0 < N) (top neg : Bool) {m r : ℕ} (hr : r < N) (hm : m ≤ r)
    (x : St N) (b : Bool) :
    wphase N hN top neg m (Function.update x (qb N hN r) b) = wphase N hN top neg m x := by
  unfold wphase
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.1 hj
  rw [Qp_update hN neg hr (by omega)]

/-- The permutation of the two passes: bit `j + 1` is flipped iff `Qp j` holds
(`j < m`), and no other bit changes. -/
def WSpec (N : ℕ) (hN : 0 < N) (neg : Bool) (m : ℕ) (σ : Equiv.Perm (St N)) : Prop :=
  (∀ x, ∀ j < m, σ x (qb N hN (j + 1)) = xor (x (qb N hN (j + 1))) (Qp N hN neg j x)) ∧
  (∀ x r, (∀ j < m, r ≠ qb N hN (j + 1)) → σ x r = x r)

theorem WSpec.update {hN : 0 < N} {neg : Bool} {m : ℕ} {σ : Equiv.Perm (St N)}
    (h : WSpec N hN neg m σ) {r : ℕ} (hr : r < N) (hm : m < r) (x : St N) (b : Bool) :
    σ (Function.update x (qb N hN r) b) = Function.update (σ x) (qb N hN r) b := by
  funext s
  by_cases hs : ∃ j, j < m ∧ s = qb N hN (j + 1)
  · obtain ⟨j, hj, rfl⟩ := hs
    have hne : qb N hN (j + 1) ≠ qb N hN r := Qulin.qb_ne hN (by omega) hr (by omega)
    rw [h.1 (Function.update x (qb N hN r) b) j hj, Function.update_of_ne hne,
      Function.update_of_ne hne, h.1 x j hj, Qp_update hN neg hr (by omega)]
  · have hs' : ∀ j < m, s ≠ qb N hN (j + 1) := fun j hj e => hs ⟨j, hj, e⟩
    rw [h.2 _ s hs']
    by_cases hst : s = qb N hN r
    · subst hst
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hst, Function.update_of_ne hst, h.2 x s hs']

/-- One more target: the backward gates onto `m + 1` move through the permutation of
the first `m` targets and merge with the forward gates onto `m + 1` into one flip. -/
theorem wstep (hN : 0 < N) (top neg : Bool) (sgn : ℕ → ℝ)
    (h0 : sgn 0 = if neg then -1 else 1) (h1 : ∀ c, 1 ≤ c → sgn c = 1) {m : ℕ}
    (hm : m + 1 < N) {σ : Equiv.Perm (St N)} (hσ : WSpec N hN neg m σ)
    (hc : circMat (wcirc N hN top sgn m) = mono σ (wphase N hN top neg m)) :
    ∃ σ' : Equiv.Perm (St N),
      circMat (wcirc N hN top sgn (m + 1)) = mono σ' (wphase N hN top neg (m + 1)) ∧
      WSpec N hN neg (m + 1) σ' := by
  have hQ : ∀ (x : St N) (b : Bool),
      Qp N hN neg m (Function.update x (qb N hN (m + 1)) b) = Qp N hN neg m x :=
    fun x b => Qp_update hN neg hm (by omega) x b
  have hA := circMat_onto hN top sgn (lo := 0) hm (Nat.zero_le _)
  have hB := circMat_onto hN top (fun _ => -1) (lo := 1) hm (by omega)
  rw [Nat.sub_zero] at hA
  rw [Nat.add_sub_cancel] at hB
  refine ⟨σ * Line.flipPerm (qb N hN (m + 1)) (Qp N hN neg m) hQ, ?_, ?_, ?_⟩
  · rw [wcirc_succ, circMat_append, circMat_append, hc, hA, hB, ← Matrix.mul_assoc,
      ctrlMat_mul_mono _ _ σ _ (hσ.update hm (by omega))
        (wphase_update hN top neg hm (by omega)),
      Matrix.mul_assoc, Line.ctrlMat_mul _ _ _ ?_]
    · have hblk : (fun x : St N =>
            blk (top && decide (m + 1 = N - 1)) (ang N hN (fun _ => -1) 1 (m + 1) m (σ x))
              * blk (top && decide (m + 1 = N - 1)) (ang N hN sgn 0 (m + 1) (m + 1) x))
          = fun x => blk (top && decide (m + 1 = N - 1))
              (if Qp N hN neg m x then (if neg then -1 else 1) * Real.pi else 0) := by
        funext x
        rw [← blk_add, ang_merge hN neg sgn h0 h1 m x (σ x) (fun i hi => hσ.1 x i hi)]
      rw [hblk, ctrlMat_flip _ _ _ _ hQ, Line.mono_mul]
      congr 1
      funext x
      rw [Line.flipPerm_apply, wphase_update hN top neg hm (by omega)]
      exact (Finset.prod_range_succ _ _).symm
    · intro x b
      rw [hσ.update hm (by omega), ang_update hN _ hm (by omega)]
  · intro x j hj
    rw [Equiv.Perm.mul_apply, Line.flipPerm_apply]
    by_cases hjm : j < m
    · rw [hσ.1 _ j hjm, Function.update_of_ne (Qulin.qb_ne hN (by omega) hm (by omega)),
        Qp_update hN neg hm (by omega)]
    · have hjm' : j = m := by omega
      subst hjm'
      rw [hσ.2 _ _ (fun j' hj' => Qulin.qb_ne hN hm (by omega) (by omega)),
        Function.update_self]
  · intro x r hr
    rw [Equiv.Perm.mul_apply, Line.flipPerm_apply, hσ.2 _ r (fun j hj => hr j (by omega)),
      Function.update_of_ne (hr m (by omega))]

/-- **The two passes are a permutation up to phases.** -/
theorem circMat_wcirc (hN : 0 < N) (top neg : Bool) (sgn : ℕ → ℝ)
    (h0 : sgn 0 = if neg then -1 else 1) (h1 : ∀ c, 1 ≤ c → sgn c = 1) (m : ℕ) (hm : m < N) :
    ∃ σ : Equiv.Perm (St N),
      circMat (wcirc N hN top sgn m) = mono σ (wphase N hN top neg m) ∧ WSpec N hN neg m σ := by
  induction m with
  | zero =>
    refine ⟨1, ?_, ?_, ?_⟩
    · have h : wphase N hN top neg 0 = fun _ => 1 := by
        funext x
        simp [wphase]
      rw [wcirc_zero, h, Line.mono_one]
      rfl
    · intro x j hj
      omega
    · intro x r _
      rfl
  | succ m ih =>
    obtain ⟨σ, hc, hσ⟩ := ih (by omega)
    exact wstep hN top neg sgn h0 h1 hm hσ hc

end Dsp
