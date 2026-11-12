/-
The ripple adder of the Huang–Palsberg circuit (`Qulin.addPass`, paper Eq. (6)): the
register `q` receives `q + G + g 0` modulo `2 ^ m`, where `G` is the number held by
`g 1 .. g (m-1)`; every other qubit is unchanged.  `16 (m - 1) + 1` CNOTs,
`14 (m - 1)` T gates.

The file starts with general facts about `regVal` (namespace `Free`).
-/
import Mathlib
import ApproxToffoli.Free.QulinCells

namespace Free

open Line (St)

variable {N : ℕ}

/-! ### General facts about `regVal` -/

theorem regVal_zero (q : ℕ → Fin N) (x : St N) : regVal 0 q x = 0 := by
  simp [regVal]

/-- Split off the high bit. -/
theorem regVal_succ (m : ℕ) (q : ℕ → Fin N) (x : St N) :
    regVal (m + 1) q x = regVal m q x + (if x (q m) = true then 2 ^ m else 0) := by
  unfold regVal
  rw [Finset.sum_range_succ]

/-- Split off the low bit. -/
theorem regVal_succ' (m : ℕ) (q : ℕ → Fin N) (x : St N) :
    regVal (m + 1) q x
      = (if x (q 0) = true then 1 else 0) + 2 * regVal m (fun j => q (j + 1)) x := by
  unfold regVal
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [pow_succ, mul_comm]
  · rfl

theorem regVal_lt (m : ℕ) (q : ℕ → Fin N) (x : St N) : regVal m q x < 2 ^ m := by
  induction m with
  | zero => simp [regVal]
  | succ m ih =>
    rw [regVal_succ, pow_succ]
    split_ifs <;> omega

/-- The register value only depends on the qubits of the register. -/
theorem regVal_congr {m : ℕ} {q : ℕ → Fin N} {x y : St N} (h : ∀ i < m, x (q i) = y (q i)) :
    regVal m q x = regVal m q y := by
  unfold regVal
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.1 hi)]

/-- The register value only depends on the first `m` qubits of the register. -/
theorem regVal_congr_reg {m : ℕ} {q q' : ℕ → Fin N} (x : St N) (h : ∀ i < m, q i = q' i) :
    regVal m q x = regVal m q' x := by
  unfold regVal
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.1 hi)]

theorem Disj.symm {m m' : ℕ} {q g : ℕ → Fin N} (h : Disj m q m' g) : Disj m' g m q :=
  fun j hj i hi e => h i hi j hj e.symm

/-- A map that only changes qubits of `q` does not change the value of a register
disjoint from `q`. -/
theorem regVal_of_disj {m m' : ℕ} {q g : ℕ → Fin N} {x y : St N} (hd : Disj m' g m q)
    (h : ∀ r, (∀ i < m, r ≠ q i) → y r = x r) : regVal m' g y = regVal m' g x :=
  regVal_congr (fun j hj => h (g j) (fun i hi => hd j hj i hi))

/-- `a % M = r` from `a = r + M * k`. -/
theorem mod_eq_of_add_mul {a r M : ℕ} (k : ℕ) (h : a = r + M * k) (hr : r < M) : a % M = r := by
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Complementing every bit of a register. -/
theorem regVal_compl {m : ℕ} {q : ℕ → Fin N} {x y : St N} (h : ∀ i < m, y (q i) = !x (q i)) :
    regVal m q y = 2 ^ m - 1 - regVal m q x := by
  induction m with
  | zero => simp [regVal]
  | succ m ih =>
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := regVal_lt m q x
    have h3 := h m (Nat.lt_succ_self m)
    rw [regVal_succ, regVal_succ, h1, h3, pow_succ]
    cases x (q m)
    · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
      omega
    · simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
      omega

/-- Flipping the top bit of a register adds `2 ^ (m - 1)` modulo `2 ^ m`. -/
theorem regVal_flip_top {m : ℕ} {q : ℕ → Fin N} {x y : St N} (hm : 1 ≤ m)
    (ht : y (q (m - 1)) = !x (q (m - 1))) (hl : ∀ i < m - 1, y (q i) = x (q i)) :
    regVal m q y = (regVal m q x + 2 ^ (m - 1)) % 2 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at ht hl ⊢
  have h1 : regVal k q y = regVal k q x := regVal_congr hl
  have h2 := regVal_lt k q x
  rw [regVal_succ, regVal_succ, h1, ht, pow_succ]
  cases x (q k)
  · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
    exact (mod_eq_of_add_mul 0 (by omega) (by omega)).symm
  · simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
    exact (mod_eq_of_add_mul 1 (by omega) (by omega)).symm

/-- The value of a register determines the bits of the register. -/
theorem regVal_inj {m : ℕ} {q : ℕ → Fin N} {x y : St N} (h : regVal m q x = regVal m q y) :
    ∀ i < m, x (q i) = y (q i) := by
  induction m with
  | zero =>
    intro i hi
    omega
  | succ m ih =>
    rw [regVal_succ, regVal_succ] at h
    have hx := regVal_lt m q x
    have hy := regVal_lt m q y
    have hb : x (q m) = y (q m) := by
      cases hxm : x (q m) <;> cases hym : y (q m) <;> rw [hxm, hym] at h <;>
        simp only [if_true, Bool.false_eq_true, if_false] at h <;> first | rfl | omega
    rw [hb] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
    · exact ih (Nat.add_right_cancel h) i h'
    · rw [h']
      exact hb

/-- A state is determined by the value of a register together with the qubits outside
the register. -/
theorem eq_of_regVal_eq {m : ℕ} {q : ℕ → Fin N} {x y : St N} (h : regVal m q x = regVal m q y)
    (ho : ∀ r, (∀ i < m, r ≠ q i) → x r = y r) : x = y := by
  funext r
  by_cases hr : ∃ i < m, r = q i
  · obtain ⟨i, hi, rfl⟩ := hr
    exact regVal_inj h i hi
  · exact ho r (fun i hi e => hr ⟨i, hi, e⟩)

/-- Split off the low bit of the register `q i, q (i+1), ...`. -/
theorem regVal_succ_shift (m : ℕ) (q : ℕ → Fin N) (i : ℕ) (x : St N) :
    regVal (m + 1) (fun j => q (i + j)) x
      = (if x (q i) = true then 1 else 0) + 2 * regVal m (fun j => q (i + 1 + j)) x := by
  have h : (fun j => q (i + (j + 1))) = fun j => q (i + 1 + j) := by
    funext j
    congr 1
    omega
  rw [regVal_succ']
  simp only [Nat.add_zero, h]

end Free

namespace Qulin

open Matrix Free
open Line (St xGate cxFun)

variable {N : ℕ}

set_option linter.unusedSimpArgs false

/-! ### The carry cells -/

/-- The carry step: `c ^= a`, `b ^= a`, then `a ^= b c`. -/
theorem acts_ux {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ f : St N → St N, Acts (ux a b c) f ∧ ∀ x,
      f x c = xor (x c) (x a) ∧ f x b = xor (x b) (x a) ∧
      f x a = xor (x a) (xor (x b) (x a) && xor (x c) (x a)) ∧
      ∀ s, s ≠ a → s ≠ b → s ≠ c → f x s = x s := by
  refine ⟨_, acts_append (acts_append (acts_cx hac) (acts_cx hab))
    (acts_ccx hbc hab.symm hac.symm), ?_⟩
  intro x
  simp only [Function.comp_apply, cxFun]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · intro s h1 h2 h3
    simp [Function.update_apply, h1, h2, h3]

/-- The inverse carry step, leaving the sum bit: `a ^= b c`, `b ^= a`, `c ^= b`. -/
theorem acts_uz {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ f : St N → St N, Acts (uz a b c) f ∧ ∀ x,
      f x a = xor (x a) (x b && x c) ∧ f x b = xor (x b) (xor (x a) (x b && x c)) ∧
      f x c = xor (x c) (xor (x b) (xor (x a) (x b && x c))) ∧
      ∀ s, s ≠ a → s ≠ b → s ≠ c → f x s = x s := by
  refine ⟨_, acts_append (acts_append (acts_ccx hbc hab.symm hac.symm) (acts_cx hab))
    (acts_cx hbc), ?_⟩
  intro x
  simp only [Function.comp_apply, cxFun]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · simp [Function.update_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  · intro s h1 h2 h3
    simp [Function.update_apply, h1, h2, h3]

theorem cnots_ux {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cnots (ux a b c) = 8 := by
  unfold ux
  rw [cnots_append, cnots_append, cnots_cx hac, cnots_cx hab, cnots_ccx hbc hab.symm hac.symm]

theorem cnots_uz {a b c : Fin N} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cnots (uz a b c) = 8 := by
  unfold uz
  rw [cnots_append, cnots_append, cnots_cx hbc, cnots_cx hab, cnots_ccx hbc hab.symm hac.symm]

theorem tr_ux (a b c : Fin N) : TR (ux a b c) 7 0 :=
  tr_append (tr_append (tr_cx a c) (tr_cx a b)) (tr_ccx b c a)

theorem tr_uz (a b c : Fin N) : TR (uz a b c) 7 0 :=
  tr_append (tr_append (tr_ccx b c a) (tr_cx a b)) (tr_cx b c)

theorem unitaryGates_ux (a b c : Fin N) : UnitaryGates (ux a b c) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_cx a c) (unitaryGates_cx a b))
    (unitaryGates_ccx b c a)

theorem unitaryGates_uz (a b c : Fin N) : UnitaryGates (uz a b c) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_ccx b c a) (unitaryGates_cx a b))
    (unitaryGates_cx b c)

/-! ### The adder -/

/-- One full adder: sum bit and carry (majority). -/
theorem bit_add (a b c : Bool) :
    (if c = true then 1 else 0) + (if b = true then 1 else 0) + (if a = true then 1 else 0)
      = (if xor (xor c a) b = true then 1 else 0)
        + 2 * (if xor a (xor b a && xor c a) = true then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> simp

theorem add_step_arith (e t H G M sc sb sa : ℕ) (hM : 0 < M) (he : e ≤ 1)
    (h : sc + sb + sa = e + 2 * t) :
    e + 2 * ((H + G + t) % M) = (sc + 2 * H + (sb + 2 * G) + sa) % (M * 2) := by
  have h1 : sc + 2 * H + (sb + 2 * G) + sa = e + 2 * (H + G + t) := by omega
  have h2 := Nat.div_add_mod (H + G + t) M
  have h3 := Nat.mod_lt (H + G + t) hM
  rw [h1]
  symm
  apply mod_eq_of_add_mul ((H + G + t) / M)
  · rw [Nat.mul_right_comm]
    omega
  · omega

/-- The adder from position `i` on with `r` carry steps: the register `q i .. q (i+r)`
receives itself plus the number held by `g (i+1) .. g (i+r)` plus the carry `g 0`. -/
theorem acts_addFrom {m : ℕ} {q g : ℕ → Fin N} (hq : Inj m q) (hg : Inj m g)
    (hqg : Disj m q m g) (r : ℕ) : ∀ i, i + r + 1 ≤ m →
    ∃ f : St N → St N, Acts (addFrom (g 0) g q r i) f ∧ ∀ x,
      regVal (r + 1) (fun j => q (i + j)) (f x)
        = (regVal (r + 1) (fun j => q (i + j)) x + regVal r (fun j => g (i + j + 1)) x
            + (if x (g 0) = true then 1 else 0)) % 2 ^ (r + 1) ∧
      ∀ s, (∀ j ≤ r, s ≠ q (i + j)) → f x s = x s := by
  induction r with
  | zero =>
    intro i hi
    have h0 : g 0 ≠ q i := fun e => hqg i (by omega) 0 (by omega) e.symm
    refine ⟨_, acts_cx h0, ?_⟩
    intro x
    refine ⟨?_, ?_⟩
    · have e1 : ∀ y : St N,
          regVal (0 + 1) (fun j => q (i + j)) y = if y (q i) = true then 1 else 0 := by
        intro y
        simp [regVal]
      rw [e1, e1, regVal_zero]
      simp only [cxFun, Function.update_self]
      cases x (q i) <;> cases x (g 0) <;> simp
    · intro s hs
      have h1 : s ≠ q i := hs 0 (le_refl 0)
      simp only [cxFun]
      rw [Function.update_of_ne h1]
  | succ r ih =>
    intro i hi
    have hab : g 0 ≠ g (i + 1) := fun e => by
      have := hg 0 (by omega) (i + 1) (by omega) e
      omega
    have hac : g 0 ≠ q i := fun e => hqg i (by omega) 0 (by omega) e.symm
    have hbc : g (i + 1) ≠ q i := fun e => hqg i (by omega) (i + 1) (by omega) e.symm
    obtain ⟨u, hu, hu'⟩ := acts_ux hab hac hbc
    obtain ⟨f, hf, hf'⟩ := ih (i + 1) (by omega)
    obtain ⟨z, hz, hz'⟩ := acts_uz hab hac hbc
    refine ⟨_, acts_append (acts_append hu hf) hz, ?_⟩
    intro x
    simp only [Function.comp_apply]
    obtain ⟨uc, ub, ua, uo⟩ := hu' x
    obtain ⟨fv, fo⟩ := hf' (u x)
    obtain ⟨za, zb, zc, zo⟩ := hz' (f (u x))
    -- the three qubits of the cell are not in the higher part of the register
    have na : ∀ j, j ≤ r → g 0 ≠ q (i + 1 + j) :=
      fun j hj e => hqg (i + 1 + j) (by omega) 0 (by omega) e.symm
    have nb : ∀ j, j ≤ r → g (i + 1) ≠ q (i + 1 + j) :=
      fun j hj e => hqg (i + 1 + j) (by omega) (i + 1) (by omega) e.symm
    have nc : ∀ j, j ≤ r → q i ≠ q (i + 1 + j) := fun j hj e => by
      have := hq i (by omega) (i + 1 + j) (by omega) e
      omega
    have fa : f (u x) (g 0) = u x (g 0) := fo _ na
    have fb : f (u x) (g (i + 1)) = u x (g (i + 1)) := fo _ nb
    have fc : f (u x) (q i) = u x (q i) := fo _ nc
    have Za : z (f (u x)) (g 0) = x (g 0) := by
      rw [za, fa, fb, fc, ua, ub, uc]
      cases x (g 0) <;> cases x (g (i + 1)) <;> cases x (q i) <;> rfl
    have Zb : z (f (u x)) (g (i + 1)) = x (g (i + 1)) := by
      rw [zb, fa, fb, fc, ua, ub, uc]
      cases x (g 0) <;> cases x (g (i + 1)) <;> cases x (q i) <;> rfl
    have Zc : z (f (u x)) (q i) = xor (xor (x (q i)) (x (g 0))) (x (g (i + 1))) := by
      rw [zc, fa, fb, fc, ua, ub, uc]
      cases x (g 0) <;> cases x (g (i + 1)) <;> cases x (q i) <;> rfl
    refine ⟨?_, ?_⟩
    · have hG := regVal_succ_shift r (fun j => g (j + 1)) i x
      have hZ : regVal (r + 1) (fun j => q (i + 1 + j)) (z (f (u x)))
          = regVal (r + 1) (fun j => q (i + 1 + j)) (f (u x)) :=
        regVal_congr (fun j hj => zo _ (na j (by omega)).symm (nb j (by omega)).symm
          (nc j (by omega)).symm)
      have hU1 : regVal (r + 1) (fun j => q (i + 1 + j)) (u x)
          = regVal (r + 1) (fun j => q (i + 1 + j)) x :=
        regVal_congr (fun j hj => uo _ (na j (by omega)).symm (nb j (by omega)).symm
          (nc j (by omega)).symm)
      have hU2 : regVal r (fun j => g (i + 1 + j + 1)) (u x)
          = regVal r (fun j => g (i + 1 + j + 1)) x :=
        regVal_congr (fun j hj => uo _
          (fun e => by
            have := hg _ (by omega) _ (by omega) e
            omega)
          (fun e => by
            have := hg _ (by omega) _ (by omega) e
            omega)
          (fun e => hqg i (by omega) (i + 1 + j + 1) (by omega) e.symm))
      rw [regVal_succ_shift (r + 1) q i, regVal_succ_shift (r + 1) q i, hG, hZ, fv, hU1, hU2,
        ua, Zc, pow_succ 2 (r + 1)]
      exact add_step_arith _ _ _ _ _ _ _ _ (by positivity) (by split_ifs <;> omega)
        (bit_add _ _ _)
    · intro s hs
      by_cases h1 : s = g 0
      · rw [h1, Za]
      by_cases h2 : s = g (i + 1)
      · rw [h2, Zb]
      have h3 : s ≠ q i := hs 0 (Nat.zero_le _)
      have h4 : ∀ j, j ≤ r → s ≠ q (i + 1 + j) := fun j hj => by
        have := hs (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this
      rw [zo s h1 h2 h3, fo s h4, uo s h1 h2 h3]

/-- **The adder.**  The register `q` receives `q + G + g 0` modulo `2 ^ m`, where `G` is
the number held by `g 1 .. g (m-1)`; every qubit outside `q` is unchanged. -/
theorem acts_addPass {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hq : Inj m q) (hg : Inj m g)
    (hqg : Disj m q m g) :
    ∃ f : St N → St N, Acts (addPass m q g) f ∧
      AddsTo m q (fun x => regVal (m - 1) (fun i => g (i + 1)) x
        + (if x (g 0) = true then 1 else 0)) f := by
  obtain ⟨f, hf, hf'⟩ := acts_addFrom hq hg hqg (m - 1) 0 (by omega)
  refine ⟨f, hf, ?_⟩
  intro x
  obtain ⟨h1, h2⟩ := hf' x
  simp only [Nat.zero_add] at h1 h2
  rw [Nat.sub_add_cancel hm] at h1
  refine ⟨?_, fun s hs => h2 s (fun j hj => hs j (by omega))⟩
  rw [h1, Nat.add_assoc]

theorem cnots_addFrom {m : ℕ} {q g : ℕ → Fin N} (hg : Inj m g) (hqg : Disj m q m g) (r : ℕ) :
    ∀ i, i + r + 1 ≤ m → cnots (addFrom (g 0) g q r i) = 16 * r + 1 := by
  induction r with
  | zero =>
    intro i hi
    exact cnots_cx (fun e => hqg i (by omega) 0 (by omega) e.symm)
  | succ r ih =>
    intro i hi
    have hab : g 0 ≠ g (i + 1) := fun e => by
      have := hg 0 (by omega) (i + 1) (by omega) e
      omega
    have hac : g 0 ≠ q i := fun e => hqg i (by omega) 0 (by omega) e.symm
    have hbc : g (i + 1) ≠ q i := fun e => hqg i (by omega) (i + 1) (by omega) e.symm
    rw [addFrom, cnots_append, cnots_append, cnots_ux hab hac hbc, cnots_uz hab hac hbc,
      ih (i + 1) (by omega)]
    omega

theorem cnots_addPass {m : ℕ} {q g : ℕ → Fin N} (hm : 1 ≤ m) (hg : Inj m g)
    (hqg : Disj m q m g) : cnots (addPass m q g) = 16 * (m - 1) + 1 :=
  cnots_addFrom hg hqg (m - 1) 0 (by omega)

theorem tr_addFrom (g0 : Fin N) (g q : ℕ → Fin N) (r : ℕ) :
    ∀ i, TR (addFrom g0 g q r i) (14 * r) 0 := by
  induction r with
  | zero =>
    intro i
    exact tr_cx g0 (q i)
  | succ r ih =>
    intro i
    rw [addFrom]
    exact (tr_append (tr_append (tr_ux _ _ _) (ih (i + 1))) (tr_uz _ _ _)).congr (by omega) rfl

theorem tr_addPass (m : ℕ) (q g : ℕ → Fin N) : TR (addPass m q g) (14 * (m - 1)) 0 :=
  tr_addFrom (g 0) g q (m - 1) 0

theorem unitaryGates_addFrom (g0 : Fin N) (g q : ℕ → Fin N) (r : ℕ) :
    ∀ i, UnitaryGates (addFrom g0 g q r i) := by
  induction r with
  | zero =>
    intro i
    exact unitaryGates_cx g0 (q i)
  | succ r ih =>
    intro i
    rw [addFrom]
    exact unitaryGates_append (unitaryGates_append (unitaryGates_ux _ _ _) (ih (i + 1)))
      (unitaryGates_uz _ _ _)

theorem unitaryGates_addPass (m : ℕ) (q g : ℕ → Fin N) : UnitaryGates (addPass m q g) :=
  unitaryGates_addFrom (g 0) g q (m - 1) 0

end Qulin
