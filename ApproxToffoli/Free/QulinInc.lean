/-
The increment with ONE borrowed qubit of the Huang–Palsberg circuit (`Qulin.inc`, paper
Fig. 6) and the decrement (`Qulin.dec`, Fig. 5): the register `reg 0 .. reg (2k-2)` is
incremented (decremented) modulo `2 ^ (2k-1)`; every other qubit, in particular the
borrowed `h`, is unchanged.  `120 k - 104` CNOTs, `100 k - 88` T gates.
-/
import Mathlib
import ApproxToffoli.Free.QulinIncB
import ApproxToffoli.Free.QulinMcx

namespace Free

open Line (St)

variable {N : ℕ}

/-- Split a register into a low part of `m` qubits and a high part of `n` qubits. -/
theorem regVal_add (m n : ℕ) (q : ℕ → Fin N) (x : St N) :
    regVal (m + n) q x = regVal m q x + 2 ^ m * regVal n (fun i => q (m + i)) x := by
  induction n with
  | zero => simp [regVal]
  | succ n ih =>
    rw [← Nat.add_assoc, regVal_succ, regVal_succ, ih, pow_add]
    split_ifs <;> ring

/-- A register whose qubits are all one holds `2 ^ m - 1`. -/
theorem regVal_all_one {m : ℕ} {q : ℕ → Fin N} {x : St N} (h : ∀ i < m, x (q i) = true) :
    regVal m q x = 2 ^ m - 1 := by
  induction m with
  | zero => simp [regVal]
  | succ m ih =>
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := Nat.one_le_two_pow (n := m)
    rw [regVal_succ, h1, if_pos (h m (Nat.lt_succ_self m)), pow_succ]
    omega

/-- All qubits of a register are one exactly when it holds `2 ^ m - 1`. -/
theorem regVal_eq_top_iff {m : ℕ} {q : ℕ → Fin N} {x : St N} :
    (∀ i < m, x (q i) = true) ↔ regVal m q x = 2 ^ m - 1 := by
  refine ⟨regVal_all_one, fun h i hi => ?_⟩
  have h1 : regVal m q (fun _ => true) = 2 ^ m - 1 := regVal_all_one (fun _ _ => rfl)
  exact regVal_inj (h.trans h1.symm) i hi

end Free

namespace Qulin

open Matrix Free
open Line (St xGate cxFun)

variable {N : ℕ}

/-! ### Arithmetic -/

/-- A number below `2 d`, reduced modulo `d`. -/
theorem mod_cases (n d : ℕ) (h : n < 2 * d) :
    (n < d ∧ n % d = n) ∨ (d ≤ n ∧ n % d = n - d) := by
  by_cases hn : n < d
  · exact Or.inl ⟨hn, Nat.mod_eq_of_lt hn⟩
  · refine Or.inr ⟨by omega, mod_eq_of_add_mul 1 (by omega) (by omega)⟩

/-- The arithmetic of steps 1 to 8 of the increment, with `M = 2 ^ (k - 1)`: `y` the
high half, `b` the borrowed qubit, `a` says that the low half is all ones. -/
theorem inc_arith {M y y1 y3 y5 y8 : ℕ} {b a b1 b5 : Bool} (hy : y < M) (hy1 : y1 < M)
    (hy5 : y5 < M)
    (h1 : (if b1 = true then 1 else 0) + 2 * y1
      = ((if b = true then 1 else 0) + 2 * y + 1) % (2 * M))
    (h3 : y3 = if (!b1) = true then M - 1 - y1 else y1)
    (h5 : (if b5 = true then 1 else 0) + 2 * y5
      = ((if xor (!b1) a = true then 1 else 0) + 2 * y3 + 1) % (2 * M))
    (h8 : y8 = if xor (!b5) a = true then M - 1 - y5 else y5) :
    y8 = (y + if a = true then 1 else 0) % M ∧ xor (!b5) a = b := by
  have m1 := mod_cases ((if b = true then 1 else 0) + 2 * y + 1) (2 * M)
    (by split_ifs <;> omega)
  have m5 := mod_cases ((if xor (!b1) a = true then 1 else 0) + 2 * y3 + 1) (2 * M)
    (by rw [h3]; split_ifs <;> omega)
  have m8 := mod_cases (y + if a = true then 1 else 0) M (by split_ifs <;> omega)
  cases b <;> cases a <;> cases b1 <;> cases b5 <;>
    simp only [Bool.not_true, Bool.not_false, Bool.xor_true, Bool.xor_false, if_true,
      if_false, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false] at * <;>
    omega

/-- The arithmetic of the whole increment: `X` the low half, `Y` the high half. -/
theorem inc_arith_top {K M X Y : ℕ} (hX : X < K) (hY : Y < M) :
    (X + 1) % K + K * ((Y + if X = K - 1 then 1 else 0) % M) = (X + K * Y + 1) % (K * M) := by
  have hKM : K * (Y + 1) ≤ K * M := Nat.mul_le_mul_left K hY
  rw [Nat.mul_add, Nat.mul_one] at hKM
  by_cases h : X = K - 1
  · rw [if_pos h, show X + 1 = K by omega, Nat.mod_self, Nat.zero_add,
      show X + K * Y + 1 = K * (Y + 1) by rw [Nat.mul_add]; omega, Nat.mul_mod_mul_left]
  · rw [if_neg h, show Y + 0 = Y from rfl, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hY]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### The sub-registers -/

section Reg

variable {k : ℕ} {reg : ℕ → Fin N} {h : Fin N}

theorem regVal_consReg (hk : 1 ≤ k) (h : Fin N) (ys : ℕ → Fin N) (x : St N) :
    regVal k (consReg h ys) x = (if x h = true then 1 else 0) + 2 * regVal (k - 1) ys x := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact regVal_succ' m (consReg h ys) x

/-- The register splits into its low half and its high half. -/
theorem regVal_split (hk : 1 ≤ k) (reg : ℕ → Fin N) (x : St N) :
    regVal (2 * k - 1) reg x = regVal k reg x + 2 ^ k * regVal (k - 1) (hi k reg) x := by
  rw [show 2 * k - 1 = k + (k - 1) by omega, regVal_add]
  rfl

theorem inj_lo (hreg : Inj (2 * k - 1) reg) : Inj k reg :=
  fun i hi j hj e => hreg i (by omega) j (by omega) e

theorem inj_hi (hreg : Inj (2 * k - 1) reg) : Inj (k - 1) (hi k reg) := fun i hi j hj e => by
  have := hreg (k + i) (by omega) (k + j) (by omega) e
  omega

theorem disj_lo_hi (hreg : Inj (2 * k - 1) reg) : Disj k reg (k - 1) (hi k reg) :=
  fun i hi j hj e => by
    have := hreg i (by omega) (k + j) (by omega) e
    omega

theorem ne_hi (hh : ∀ i < 2 * k - 1, h ≠ reg i) : ∀ i < k - 1, h ≠ hi k reg i :=
  fun i hi => hh (k + i) (by omega)

theorem ne_lo (hh : ∀ i < 2 * k - 1, h ≠ reg i) : ∀ i < k, h ≠ reg i :=
  fun i hi => hh i (by omega)

theorem inj_consReg (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    Inj k (consReg h (hi k reg)) := by
  intro i hi j hj e
  cases i <;> cases j
  · rfl
  · exact absurd e (ne_hi hh _ (by omega))
  · exact absurd e.symm (ne_hi hh _ (by omega))
  · have := inj_hi hreg _ (by omega) _ (by omega) e
    omega

theorem disj_consReg_lo (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    Disj k (consReg h (hi k reg)) k reg := by
  intro i hi j hj e
  cases i
  · exact ne_lo hh j hj e
  · exact disj_lo_hi hreg j hj _ (by omega) e.symm

theorem inj_snocReg (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    Inj k (snocReg (hi k reg) (k - 1) h) := by
  intro i hi j hj e
  simp only [snocReg] at e
  split_ifs at e with h1 h2 h2
  · exact inj_hi hreg i h1 j h2 e
  · exact absurd e.symm (ne_hi hh i h1)
  · exact absurd e (ne_hi hh j h2)
  · omega

theorem disj_lo_snocReg (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    Disj k reg k (snocReg (hi k reg) (k - 1) h) := by
  intro i hi j hj e
  simp only [snocReg] at e
  split_ifs at e with h1
  · exact disj_lo_hi hreg i hi j h1 e
  · exact ne_lo hh i hi e.symm

/-! ### The steps on the borrowed qubit and the high half -/

/-- NOT on the borrowed qubit. -/
def xh (h : Fin N) (y : St N) : St N := Function.update y h (!y h)

/-- Flip the borrowed qubit when the low half is all ones. -/
def mc (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) (y : St N) : St N :=
  Function.update y h (xor (y h) (decide (∀ i < k, y (reg i) = true)))

theorem xh_self (h : Fin N) (y : St N) : xh h y h = !y h := Function.update_self _ _ _

theorem xh_of_ne {r : Fin N} (hr : r ≠ h) (y : St N) : xh h y r = y r :=
  Function.update_of_ne hr _ _

theorem mc_self (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) (y : St N) :
    mc k reg h y h = xor (y h) (decide (∀ i < k, y (reg i) = true)) :=
  Function.update_self _ _ _

theorem mc_of_ne {r : Fin N} (hr : r ≠ h) (y : St N) : mc k reg h y r = y r :=
  Function.update_of_ne hr _ _

theorem regVal_hi_update (hh : ∀ i < 2 * k - 1, h ≠ reg i) (y : St N) (b : Bool) :
    regVal (k - 1) (hi k reg) (Function.update y h b) = regVal (k - 1) (hi k reg) y :=
  regVal_congr (fun i hi => Function.update_of_ne (ne_hi hh i hi).symm _ _)

/-- The increment on `(h, ys)`, read on `h` and the high half `ys`. -/
theorem stepA (hk : 1 ≤ k) {A : St N → St N}
    (hA : AddsTo k (consReg h (hi k reg)) (fun _ => 1) A) (x : St N) :
    ((if A x h = true then 1 else 0) + 2 * regVal (k - 1) (hi k reg) (A x)
      = ((if x h = true then 1 else 0) + 2 * regVal (k - 1) (hi k reg) x + 1)
          % (2 * 2 ^ (k - 1))) ∧
    ∀ r, r ≠ h → (∀ i < k - 1, r ≠ hi k reg i) → A x r = x r := by
  obtain ⟨v, o⟩ := hA x
  beta_reduce at v
  have hM : 2 ^ k = 2 * 2 ^ (k - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm]
  rw [regVal_consReg hk, regVal_consReg hk, hM] at v
  refine ⟨v, fun r h1 h2 => o r (fun i hi => ?_)⟩
  cases i
  · exact h1
  · exact h2 _ (by omega)

/-- The fan complements the high half exactly when `h` is one. -/
theorem stepF (hh : ∀ i < 2 * k - 1, h ≠ reg i) {F : St N → St N}
    (hF : ∀ x, (∀ i < k - 1, F x (hi k reg i) = xor (x (hi k reg i)) (x h)) ∧
      ∀ s, (∀ i < k - 1, s ≠ hi k reg i) → F x s = x s) (x : St N) :
    regVal (k - 1) (hi k reg) (F x)
      = (if x h = true then 2 ^ (k - 1) - 1 - regVal (k - 1) (hi k reg) x
          else regVal (k - 1) (hi k reg) x) ∧ F x h = x h := by
  obtain ⟨h1, h2⟩ := hF x
  refine ⟨?_, h2 h (ne_hi hh)⟩
  by_cases hx : x h = true
  · rw [if_pos hx]
    exact regVal_compl (fun i hi => by rw [h1 i hi, hx, Bool.xor_true])
  · rw [if_neg hx]
    have hx' : x h = false := by simpa using hx
    exact regVal_congr (fun i hi => by rw [h1 i hi, hx', Bool.xor_false])

/-- **Steps 1 to 8 of the increment.**  The high half receives the carry out of the low
half; the borrowed qubit and all other qubits come back unchanged. -/
theorem inc_head (hk : 1 ≤ k) (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i)
    {A F : St N → St N} (hA : AddsTo k (consReg h (hi k reg)) (fun _ => 1) A)
    (hF : ∀ x, (∀ i < k - 1, F x (hi k reg i) = xor (x (hi k reg i)) (x h)) ∧
      ∀ s, (∀ i < k - 1, s ≠ hi k reg i) → F x s = x s)
    {x x1 x2 x3 x4 x5 x6 x7 x8 : St N} (e1 : x1 = A x) (e2 : x2 = xh h x1) (e3 : x3 = F x2)
    (e4 : x4 = mc k reg h x3) (e5 : x5 = A x4) (e6 : x6 = xh h x5) (e7 : x7 = mc k reg h x6)
    (e8 : x8 = F x7) :
    regVal (k - 1) (hi k reg) x8
      = (regVal (k - 1) (hi k reg) x + if (∀ i < k, x (reg i) = true) then 1 else 0)
          % 2 ^ (k - 1) ∧
    x8 h = x h ∧ ∀ r, r ≠ h → (∀ i < k - 1, r ≠ hi k reg i) → x8 r = x r := by
  obtain ⟨v1, o1⟩ := stepA hk hA x
  obtain ⟨v3, b3⟩ := stepF hh hF x2
  have o3 := (hF x2).2
  obtain ⟨v5, o5⟩ := stepA hk hA x4
  obtain ⟨v8, b8⟩ := stepF hh hF x7
  have o8 := (hF x7).2
  rw [← e1] at v1 o1
  rw [← e3] at v3 b3 o3
  rw [← e5] at v5 o5
  rw [← e8] at v8 b8 o8
  have b2 : x2 h = !x1 h := by rw [e2, xh_self]
  have b4 : x4 h = xor (x3 h) (decide (∀ i < k, x3 (reg i) = true)) := by rw [e4, mc_self]
  have b6 : x6 h = !x5 h := by rw [e6, xh_self]
  have b7 : x7 h = xor (x6 h) (decide (∀ i < k, x6 (reg i) = true)) := by rw [e7, mc_self]
  have y2 : regVal (k - 1) (hi k reg) x2 = regVal (k - 1) (hi k reg) x1 := by
    rw [e2]
    exact regVal_hi_update hh _ _
  have y4 : regVal (k - 1) (hi k reg) x4 = regVal (k - 1) (hi k reg) x3 := by
    rw [e4]
    exact regVal_hi_update hh _ _
  have y6 : regVal (k - 1) (hi k reg) x6 = regVal (k - 1) (hi k reg) x5 := by
    rw [e6]
    exact regVal_hi_update hh _ _
  have y7 : regVal (k - 1) (hi k reg) x7 = regVal (k - 1) (hi k reg) x6 := by
    rw [e7]
    exact regVal_hi_update hh _ _
  have O : ∀ r, r ≠ h → (∀ i < k - 1, r ≠ hi k reg i) →
      x3 r = x r ∧ x6 r = x r ∧ x8 r = x r := by
    intro r hr hr'
    have r3 : x3 r = x r := by rw [o3 r hr', e2, xh_of_ne hr, o1 r hr hr']
    have r6 : x6 r = x r := by rw [e6, xh_of_ne hr, o5 r hr hr', e4, mc_of_ne hr, r3]
    exact ⟨r3, r6, by rw [o8 r hr', e7, mc_of_ne hr, r6]⟩
  have lo : ∀ i < k, reg i ≠ h ∧ ∀ j < k - 1, reg i ≠ hi k reg j :=
    fun i hi => ⟨(ne_lo hh i hi).symm, fun j hj => disj_lo_hi hreg i hi j hj⟩
  have a3 : decide (∀ i < k, x3 (reg i) = true) = decide (∀ i < k, x (reg i) = true) :=
    decide_eq_decide.2 (forall₂_congr (fun i hi => by rw [(O _ (lo i hi).1 (lo i hi).2).1]))
  have a6 : decide (∀ i < k, x6 (reg i) = true) = decide (∀ i < k, x (reg i) = true) :=
    decide_eq_decide.2 (forall₂_congr (fun i hi => by rw [(O _ (lo i hi).1 (lo i hi).2).2.1]))
  rw [b2, y2] at v3
  rw [b4, b3, b2, a3, y4] at v5
  rw [b7, b6, a6, y7, y6] at v8
  obtain ⟨c1, c2⟩ := inc_arith (regVal_lt _ _ x) (regVal_lt _ _ x1) (regVal_lt _ _ x5)
    v1 v3 v5 v8
  simp only [decide_eq_true_eq] at c1
  refine ⟨c1, ?_, fun r hr hr' => (O r hr hr').2.2⟩
  rw [b8, b7, b6, a6]
  exact c2

/-! ### The increment and the decrement -/

/-- **The increment with one borrowed qubit.**  The register `reg 0 .. reg (2k-2)` is
incremented modulo `2 ^ (2k-1)`; every other qubit, in particular the borrowed `h`, is
unchanged. -/
theorem acts_inc (hk : 3 ≤ k) (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    ∃ f : St N → St N, Acts (inc k reg h) f ∧ AddsTo (2 * k - 1) reg (fun _ => 1) f := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨A, hA, hA'⟩ :=
    acts_incB hk1 (inj_consReg hreg hh) (inj_lo hreg) (disj_consReg_lo hreg hh)
  obtain ⟨F, hF, hF'⟩ := acts_fan (inj_hi hreg) (ne_hi hh)
  have hX : Acts [Gate.one h xGate] (xh h) := acts_x h
  have hM : Acts (mcx k reg (hi k reg) h) (mc k reg h) :=
    acts_mcx hk (inj_lo hreg) (fun i hi j hj e => inj_hi hreg i (by omega) j (by omega) e)
      (fun i hi j hj => disj_lo_hi hreg i hi j (by omega)) (ne_lo hh)
      (fun i hi => ne_hi hh i (by omega))
  obtain ⟨I, hI, hI'⟩ :=
    acts_incB hk1 (inj_lo hreg) (inj_snocReg hreg hh) (disj_lo_snocReg hreg hh)
  refine ⟨_, acts_append (acts_append (acts_append (acts_append (acts_append (acts_append
    (acts_append (acts_append hA hX) hF) hM) hA) hX) hM) hF) hI, ?_⟩
  intro x
  simp only [Function.comp_apply]
  obtain ⟨g1, g2, g3⟩ := inc_head hk1 hreg hh hA' hF' (x := x) rfl rfl rfl rfl rfl rfl rfl rfl
  set y := F (mc k reg h (xh h (A (mc k reg h (F (xh h (A x)))))))
  obtain ⟨i1, i2⟩ := hI' y
  beta_reduce at i1
  have lo : ∀ i < k, reg i ≠ h ∧ ∀ j < k - 1, reg i ≠ hi k reg j :=
    fun i hi => ⟨(ne_lo hh i hi).symm, fun j hj => disj_lo_hi hreg i hi j hj⟩
  have X8 : regVal k reg y = regVal k reg x :=
    regVal_congr (fun i hi => g3 _ (lo i hi).1 (lo i hi).2)
  have Y9 : regVal (k - 1) (hi k reg) (I y) = regVal (k - 1) (hi k reg) y :=
    regVal_congr (fun i hi => i2 _ (fun j hj => (disj_lo_hi hreg j hj i hi).symm))
  have hpow : 2 ^ (2 * k - 1) = 2 ^ k * 2 ^ (k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨?_, ?_⟩
  · rw [regVal_split hk1, regVal_split hk1, i1, X8, Y9, g1, hpow,
      if_congr regVal_eq_top_iff rfl rfl]
    exact inc_arith_top (regVal_lt _ _ x) (regVal_lt _ _ x)
  · intro r hr
    by_cases hrh : r = h
    · rw [hrh, i2 h (ne_lo hh), g2]
    · have hr' : ∀ i < k - 1, r ≠ hi k reg i := fun i hi => hr (k + i) (by omega)
      rw [i2 r (fun i hi => hr i (by omega)), g3 r hrh hr']

/-- Complement, add one, complement: subtract one. -/
theorem dec_arith {R v : ℕ} (hv : v < R) : R - 1 - (R - 1 - v + 1) % R = (v + (R - 1)) % R := by
  by_cases h0 : v = 0
  · subst h0
    rw [show R - 1 - 0 + 1 = R by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact (mod_eq_of_add_mul 1 (by omega) (by omega)).symm

/-- **The decrement with one borrowed qubit.**  The register `reg 0 .. reg (2k-2)` is
decremented modulo `2 ^ (2k-1)`; every other qubit, in particular the borrowed `h`, is
unchanged. -/
theorem acts_dec (hk : 3 ≤ k) (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    ∃ f : St N → St N, Acts (dec k reg h) f ∧
      AddsTo (2 * k - 1) reg (fun _ => 2 ^ (2 * k - 1) - 1) f := by
  obtain ⟨C, hC, hC'⟩ := acts_flips hreg
  obtain ⟨f, hf, hf'⟩ := acts_inc hk hreg hh
  refine ⟨_, acts_append (acts_append hC hf) hC, ?_⟩
  intro x
  simp only [Function.comp_apply]
  obtain ⟨c1, c2⟩ := hC' x
  obtain ⟨f1, f2⟩ := hf' (C x)
  obtain ⟨d1, d2⟩ := hC' (f (C x))
  beta_reduce at f1
  refine ⟨?_, fun r hr => by rw [d2 r hr, f2 r hr, c2 r hr]⟩
  rw [regVal_compl d1, f1, regVal_compl c1]
  exact dec_arith (regVal_lt _ _ x)

/-! ### Counts -/

theorem cnots_fanH (hh : ∀ i < 2 * k - 1, h ≠ reg i) : cnots (fanH k reg h) = k - 1 := by
  unfold fanH
  rw [cnots_forUp (k - 1) _ 1 (fun i hi => cnots_cx (ne_hi hh i hi)), Nat.mul_one]

theorem cnots_inc (hk : 3 ≤ k) (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    cnots (inc k reg h) = 120 * k - 104 := by
  have hk1 : 1 ≤ k := by omega
  have hm : cnots (mcx k reg (hi k reg) h) = 8 * k - 6 :=
    cnots_mcx hk (inj_lo hreg) (fun i hi j hj e => inj_hi hreg i (by omega) j (by omega) e)
      (fun i hi j hj => disj_lo_hi hreg i hi j (by omega)) (ne_lo hh)
      (fun i hi => ne_hi hh i (by omega))
  unfold inc
  simp only [cnots_append, cnots_incB hk1 (inj_lo hreg) (disj_consReg_lo hreg hh),
    cnots_incB hk1 (inj_snocReg hreg hh) (disj_lo_snocReg hreg hh), cnots_fanH hh, hm, cnots]
  omega

theorem cnots_dec (hk : 3 ≤ k) (hreg : Inj (2 * k - 1) reg) (hh : ∀ i < 2 * k - 1, h ≠ reg i) :
    cnots (dec k reg h) = 120 * k - 104 := by
  unfold dec
  rw [cnots_append, cnots_append, cnots_flips, cnots_inc hk hreg hh]
  omega

end Reg

theorem tr_fanH (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : TR (fanH k reg h) 0 0 :=
  (tr_forUp (k - 1) _ 0 0 (fun i _ => tr_cx h (hi k reg i))).congr (Nat.mul_zero _)
    (Nat.mul_zero _)

theorem tr_inc (k : ℕ) (hk : 3 ≤ k) (reg : ℕ → Fin N) (h : Fin N) :
    TR (inc k reg h) (100 * k - 88) 0 :=
  (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append (tr_append
    (tr_incB k _ reg) (tr_one h Line.tcost_xGate)) (tr_fanH k reg h)) (tr_mcx k hk reg _ h))
    (tr_incB k _ reg)) (tr_one h Line.tcost_xGate)) (tr_mcx k hk reg _ h)) (tr_fanH k reg h))
    (tr_incB k reg _)).congr (by omega) rfl

theorem tr_dec (k : ℕ) (hk : 3 ≤ k) (reg : ℕ → Fin N) (h : Fin N) :
    TR (dec k reg h) (100 * k - 88) 0 :=
  (tr_append (tr_append (tr_flips _ reg) (tr_inc k hk reg h)) (tr_flips _ reg)).congr
    (by omega) rfl

theorem unitaryGates_fanH (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : UnitaryGates (fanH k reg h) :=
  unitaryGates_forUp (k - 1) _ (fun i _ => unitaryGates_cx h (hi k reg i))

theorem unitaryGates_inc (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : UnitaryGates (inc k reg h) :=
  have hx : UnitaryGates [Gate.one h xGate] := unitaryGates_singleton_one h Line.xGate_unitary
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_incB k _ reg) hx) (unitaryGates_fanH k reg h)) (unitaryGates_mcx k reg _ h))
    (unitaryGates_incB k _ reg)) hx) (unitaryGates_mcx k reg _ h)) (unitaryGates_fanH k reg h))
    (unitaryGates_incB k reg _)

theorem unitaryGates_dec (k : ℕ) (reg : ℕ → Fin N) (h : Fin N) : UnitaryGates (dec k reg h) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_flips _ reg) (unitaryGates_inc k reg h))
    (unitaryGates_flips _ reg)

end Qulin
