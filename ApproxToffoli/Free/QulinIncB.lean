/-
The increment with as many borrowed qubits as register qubits of the Huang–Palsberg
circuit (`Qulin.incB`, paper Eq. (6)): the register `q` is incremented modulo `2 ^ m`,
every other qubit (in particular every borrowed `g i`) is unchanged.  `34 m - 30` CNOTs,
`28 (m - 1)` T gates.
-/
import Mathlib
import ApproxToffoli.Free.QulinAdd

namespace Qulin

open Matrix Free
open Line (St xGate cxFun)

variable {N : ℕ}

/-! ### A fan of CNOTs -/

/-- A fan of CNOTs from `c` to the register `q`: every bit of `q` is XORed with `c`. -/
theorem acts_fan {m : ℕ} {q : ℕ → Fin N} {c : Fin N} (hq : Inj m q) (hc : ∀ i < m, c ≠ q i) :
    ∃ f : St N → St N, Acts (forUp m (fun i => cx c (q i))) f ∧ ∀ x,
      (∀ i < m, f x (q i) = xor (x (q i)) (x c)) ∧
      ∀ s, (∀ i < m, s ≠ q i) → f x s = x s := by
  induction m with
  | zero =>
    refine ⟨id, ?_, ?_⟩
    · rw [forUp_zero]
      exact acts_nil
    · intro x
      exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun s _ => rfl⟩
  | succ m ih =>
    obtain ⟨f, hf, hf'⟩ := ih (fun i hi j hj e => hq i (by omega) j (by omega) e)
      (fun i hi => hc i (by omega))
    have hA := acts_append hf (acts_cx (hc m (Nat.lt_succ_self m)))
    rw [← forUp_succ m (fun i => cx c (q i))] at hA
    refine ⟨_, hA, ?_⟩
    intro x
    obtain ⟨h1, h2⟩ := hf' x
    simp only [Function.comp_apply, cxFun]
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · have hne : q i ≠ q m := fun e => by
          have := hq i (by omega) m (by omega) e
          omega
        rw [Function.update_of_ne hne, h1 i h]
      · subst h
        have hqi : ∀ j < i, q i ≠ q j := fun j hj e => by
          have := hq i (by omega) j (by omega) e
          omega
        rw [Function.update_self, h2 (q i) hqi, h2 c (fun j hj => hc j (by omega))]
    · intro s hs
      rw [Function.update_of_ne (hs m (Nat.lt_succ_self m)), h2 s (fun j hj => hs j (by omega))]

/-- `fanX` complements the register `q` when `g 0` is zero, and changes nothing else. -/
theorem acts_fanX {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hq : Inj m q) (hqg : Disj m q m g) :
    ∃ f : St N → St N, Acts (fanX m q g) f ∧ ∀ x,
      regVal m q (f x)
        = (if x (g 0) = true then regVal m q x else 2 ^ m - 1 - regVal m q x) ∧
      ∀ s, (∀ i < m, s ≠ q i) → f x s = x s := by
  have hc : ∀ i < m, g 0 ≠ q i := fun i hi e => hqg i hi 0 (by omega) e.symm
  obtain ⟨f, hf, hf'⟩ := acts_fan hq hc
  refine ⟨_, acts_append (acts_append (acts_x (g 0)) hf) (acts_x (g 0)), ?_⟩
  intro x
  simp only [Function.comp_apply]
  obtain ⟨h1, h2⟩ := hf' (Function.update x (g 0) (!x (g 0)))
  have hb : ∀ i < m, Function.update (f (Function.update x (g 0) (!x (g 0)))) (g 0)
      (!f (Function.update x (g 0) (!x (g 0))) (g 0)) (q i) = xor (x (q i)) (!x (g 0)) := by
    intro i hi
    rw [Function.update_of_ne (hc i hi).symm, h1 i hi, Function.update_of_ne (hc i hi).symm,
      Function.update_self]
  refine ⟨?_, ?_⟩
  · by_cases hx : x (g 0) = true
    · rw [if_pos hx]
      exact regVal_congr (fun i hi => by rw [hb i hi, hx]; simp)
    · have hx' : x (g 0) = false := by simpa using hx
      rw [if_neg hx]
      exact regVal_compl (fun i hi => by rw [hb i hi, hx']; simp)
  · intro s hs
    by_cases h : s = g 0
    · rw [h, Function.update_self, h2 (g 0) hc, Function.update_self, Bool.not_not]
    · rw [Function.update_of_ne h, h2 s hs, Function.update_of_ne h]

/-! ### NOT on every qubit of a register -/

/-- `flips` complements every qubit of the register and changes nothing else. -/
theorem acts_flips {r : ℕ} {reg : ℕ → Fin N} (hreg : Inj r reg) :
    ∃ f : St N → St N, Acts (flips r reg) f ∧ ∀ x,
      (∀ i < r, f x (reg i) = !x (reg i)) ∧ ∀ s, (∀ i < r, s ≠ reg i) → f x s = x s := by
  unfold flips
  induction r with
  | zero =>
    refine ⟨id, ?_, ?_⟩
    · rw [forUp_zero]
      exact acts_nil
    · intro x
      exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun s _ => rfl⟩
  | succ r ih =>
    obtain ⟨f, hf, hf'⟩ := ih (fun i hi j hj e => hreg i (by omega) j (by omega) e)
    have hA := acts_append hf (acts_x (reg r))
    rw [← forUp_succ r (fun i => [Gate.one (reg i) xGate])] at hA
    refine ⟨_, hA, ?_⟩
    intro x
    obtain ⟨h1, h2⟩ := hf' x
    simp only [Function.comp_apply]
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · have hne : reg i ≠ reg r := fun e => by
          have := hreg i (by omega) r (by omega) e
          omega
        rw [Function.update_of_ne hne, h1 i h]
      · have hri : ∀ j < r, reg r ≠ reg j := fun j hj e => by
          have := hreg r (by omega) j (by omega) e
          omega
        rw [h, Function.update_self, h2 (reg r) hri]
    · intro s hs
      rw [Function.update_of_ne (hs r (Nat.lt_succ_self r)), h2 s (fun j hj => hs j (by omega))]

theorem cnots_flips (r : ℕ) (reg : ℕ → Fin N) : cnots (flips r reg) = 0 := by
  unfold flips
  rw [cnots_forUp r _ 0 (fun i _ => rfl), Nat.mul_zero]

theorem tr_flips (r : ℕ) (reg : ℕ → Fin N) : TR (flips r reg) 0 0 :=
  (tr_forUp r _ 0 0 (fun i _ => tr_one (reg i) Line.tcost_xGate)).congr (Nat.mul_zero r)
    (Nat.mul_zero r)

theorem unitaryGates_flips (r : ℕ) (reg : ℕ → Fin N) : UnitaryGates (flips r reg) :=
  unitaryGates_forUp r _ (fun i _ => unitaryGates_singleton_one (reg i) Line.xGate_unitary)

theorem notG_eq_flips (m : ℕ) (g : ℕ → Fin N) : notG m g = flips (m - 1) (fun i => g (i + 1)) :=
  rfl

/-! ### The increment -/

/-- The arithmetic of the increment, with `P = 2 ^ (m - 1)`: `v` the register, `G` the
number held by the borrowed qubits `g 1 .. g (m-1)`, `s` the borrowed qubit `g 0`. -/
theorem incB_arith {P v G v1 v2 v4 v6 v7 : ℕ} (s : Bool) (hv : v < 2 * P) (hG : G < P)
    (h1 : v1 = if s = true then v else 2 * P - 1 - v)
    (h2 : v2 = (v1 + (G + if s = true then 1 else 0)) % (2 * P))
    (h4 : v4 = (v2 + (P - 1 - G + if s = true then 1 else 0)) % (2 * P))
    (h6 : v6 = (v4 + P) % (2 * P))
    (h7 : v7 = if s = true then v6 else 2 * P - 1 - v6) :
    v7 = (v + 1) % (2 * P) := by
  have key : v6 = (v1 + (G + if s = true then 1 else 0)
      + ((P - 1 - G + if s = true then 1 else 0) + P)) % (2 * P) := by
    rw [h6, h4, h2, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]
  cases s
  · rw [if_neg Bool.false_ne_true] at h1 h7
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at key
    by_cases hlt : v + 1 < 2 * P
    · have e6 : v6 = 2 * P - 2 - v := by
        rw [key]
        exact mod_eq_of_add_mul 1 (by omega) (by omega)
      rw [h7, e6, Nat.mod_eq_of_lt hlt]
      omega
    · have e6 : v6 = 2 * P - 1 := by
        rw [key]
        exact mod_eq_of_add_mul 0 (by omega) (by omega)
      have hv' : v + 1 = 2 * P := by omega
      rw [h7, e6, hv', Nat.mod_self]
      omega
  · rw [if_pos rfl] at h1 h7
    rw [if_pos rfl] at key
    rw [h7, key, h1, show v + (G + 1) + (P - 1 - G + 1 + P) = v + 1 + 2 * P by omega,
      Nat.add_mod_right]

/-- **The increment with borrowed qubits.**  The register `q` is incremented modulo
`2 ^ m`; every other qubit, in particular every borrowed `g i`, is unchanged. -/
theorem acts_incB {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hq : Inj m q) (hg : Inj m g)
    (hqg : Disj m q m g) :
    ∃ f : St N → St N, Acts (incB m q g) f ∧ AddsTo m q (fun _ => 1) f := by
  obtain ⟨F, hF, hF'⟩ := acts_fanX hm hq hqg
  obtain ⟨A, hA, hA'⟩ := acts_addPass hm hq hg hqg
  have hg' : Inj (m - 1) (fun i => g (i + 1)) := fun i hi j hj e => by
    have := hg (i + 1) (by omega) (j + 1) (by omega) e
    omega
  obtain ⟨C, hC, hC'⟩ := acts_flips hg'
  rw [← notG_eq_flips] at hC
  refine ⟨_, acts_append (acts_append (acts_append (acts_append (acts_append (acts_append
    hF hA) hC) hA) hC) (acts_x (q (m - 1)))) hF, ?_⟩
  intro x
  simp only [Function.comp_apply]
  have gq : ∀ j < m, ∀ i < m, g j ≠ q i := fun j hj i hi e => hqg i hi j hj e.symm
  have g0 : ∀ i < m - 1, g 0 ≠ g (i + 1) := fun i hi e => by
    have := hg 0 (by omega) (i + 1) (by omega) e
    omega
  have hM : 2 ^ m = 2 * 2 ^ (m - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm]
  obtain ⟨F1v, F1o⟩ := hF' x
  set x1 := F x
  obtain ⟨A2v, A2o⟩ := hA' x1
  set x2 := A x1
  obtain ⟨C3b, C3o⟩ := hC' x2
  set x3 := C x2
  obtain ⟨A4v, A4o⟩ := hA' x3
  set x4 := A x3
  obtain ⟨C5b, C5o⟩ := hC' x4
  set x5 := C x4
  set x6 := Function.update x5 (q (m - 1)) (!x5 (q (m - 1))) with hx6
  obtain ⟨F7v, F7o⟩ := hF' x6
  have s1 : x1 (g 0) = x (g 0) := F1o _ (gq 0 (by omega))
  have s2 : x2 (g 0) = x1 (g 0) := A2o _ (gq 0 (by omega))
  have s3 : x3 (g 0) = x2 (g 0) := C3o _ g0
  have s4 : x4 (g 0) = x3 (g 0) := A4o _ (gq 0 (by omega))
  have s5 : x5 (g 0) = x4 (g 0) := C5o _ g0
  have s6 : x6 (g 0) = x5 (g 0) :=
    Function.update_of_ne (gq 0 (by omega) (m - 1) (by omega)) _ _
  have G1 : regVal (m - 1) (fun i => g (i + 1)) x1 = regVal (m - 1) (fun i => g (i + 1)) x :=
    regVal_congr (fun i hi => F1o _ (gq (i + 1) (by omega)))
  have G2 : regVal (m - 1) (fun i => g (i + 1)) x2 = regVal (m - 1) (fun i => g (i + 1)) x1 :=
    regVal_congr (fun i hi => A2o _ (gq (i + 1) (by omega)))
  have G3 : regVal (m - 1) (fun i => g (i + 1)) x3
      = 2 ^ (m - 1) - 1 - regVal (m - 1) (fun i => g (i + 1)) x2 := regVal_compl C3b
  have V3 : regVal m q x3 = regVal m q x2 :=
    regVal_congr (fun i hi => C3o _ (fun j hj => (gq (j + 1) (by omega) i hi).symm))
  have V5 : regVal m q x5 = regVal m q x4 :=
    regVal_congr (fun i hi => C5o _ (fun j hj => (gq (j + 1) (by omega) i hi).symm))
  have V6 : regVal m q x6 = (regVal m q x5 + 2 ^ (m - 1)) % 2 ^ m :=
    regVal_flip_top hm (Function.update_self _ _ _) (fun i hi => Function.update_of_ne
      (fun e => by
        have := hq i (by omega) (m - 1) (by omega) e
        omega) _ _)
  refine ⟨?_, ?_⟩
  · beta_reduce at A2v A4v
    rw [s1, G1] at A2v
    rw [V3, G3, G2, G1, s3, s2, s1] at A4v
    rw [V5] at V6
    rw [s6, s5, s4, s3, s2, s1] at F7v
    rw [hM] at F1v A2v A4v V6 F7v ⊢
    exact incB_arith (x (g 0)) (by rw [← hM]; exact regVal_lt m q x) (regVal_lt (m - 1) _ x)
      F1v A2v A4v V6 F7v
  · intro r hr
    rw [F7o r hr, hx6, Function.update_of_ne (hr (m - 1) (by omega))]
    by_cases hgr : ∃ i < m - 1, r = g (i + 1)
    · obtain ⟨i, hi, rfl⟩ := hgr
      rw [C5b i hi, A4o _ hr, C3b i hi, A2o _ hr, F1o _ hr, Bool.not_not]
    · have hr' : ∀ i < m - 1, r ≠ g (i + 1) := fun i hi e => hgr ⟨i, hi, e⟩
      rw [C5o _ hr', A4o _ hr, C3o _ hr', A2o _ hr, F1o _ hr]

/-! ### Counts -/

theorem cnots_fanX {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hqg : Disj m q m g) :
    cnots (fanX m q g) = m := by
  unfold fanX
  rw [cnots_append, cnots_append,
    cnots_forUp m _ 1 (fun i hi => cnots_cx (fun e => hqg i hi 0 (by omega) e.symm))]
  simp only [cnots, Nat.mul_one, Nat.zero_add, Nat.add_zero]

theorem tr_fanX (m : ℕ) (q g : ℕ → Fin N) : TR (fanX m q g) 0 0 :=
  (tr_append (tr_append (tr_one (g 0) Line.tcost_xGate)
    (tr_forUp m _ 0 0 (fun i _ => tr_cx (g 0) (q i))))
    (tr_one (g 0) Line.tcost_xGate)).congr (by simp) (by simp)

theorem unitaryGates_fanX (m : ℕ) (q g : ℕ → Fin N) : UnitaryGates (fanX m q g) :=
  unitaryGates_append (unitaryGates_append
    (unitaryGates_singleton_one (g 0) Line.xGate_unitary)
    (unitaryGates_forUp m _ (fun i _ => unitaryGates_cx (g 0) (q i))))
    (unitaryGates_singleton_one (g 0) Line.xGate_unitary)

theorem cnots_notG (m : ℕ) (g : ℕ → Fin N) : cnots (notG m g) = 0 :=
  cnots_flips (m - 1) (fun i => g (i + 1))

theorem tr_notG (m : ℕ) (g : ℕ → Fin N) : TR (notG m g) 0 0 :=
  tr_flips (m - 1) (fun i => g (i + 1))

theorem unitaryGates_notG (m : ℕ) (g : ℕ → Fin N) : UnitaryGates (notG m g) :=
  unitaryGates_flips (m - 1) (fun i => g (i + 1))

theorem cnots_incB {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hg : Inj m g)
    (hqg : Disj m q m g) : cnots (incB m q g) = 34 * m - 30 := by
  unfold incB
  simp only [cnots_append, cnots_fanX hm hqg, cnots_addPass hm hg hqg, cnots_notG, cnots]
  omega

theorem tr_incB (m : ℕ) (q g : ℕ → Fin N) : TR (incB m q g) (28 * (m - 1)) 0 :=
  (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append
    (tr_fanX m q g) (tr_addPass m q g)) (tr_notG m g)) (tr_addPass m q g)) (tr_notG m g))
    (tr_one (q (m - 1)) Line.tcost_xGate)) (tr_fanX m q g)).congr (by omega) rfl

theorem unitaryGates_incB (m : ℕ) (q g : ℕ → Fin N) : UnitaryGates (incB m q g) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_append
    (unitaryGates_fanX m q g) (unitaryGates_addPass m q g)) (unitaryGates_notG m g))
    (unitaryGates_addPass m q g)) (unitaryGates_notG m g))
    (unitaryGates_singleton_one (q (m - 1)) Line.xGate_unitary)) (unitaryGates_fanX m q g)

end Qulin
