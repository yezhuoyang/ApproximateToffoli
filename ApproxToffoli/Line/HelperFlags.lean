/-
The flags of the helper-qubit construction (Lemma "Flags" of the paper): what the circuit
`U = compute n` does to the bits.

This file is about functions on bit assignments `ℕ → Bool` only; there are no matrices.

* `Level k m G`: the part `G` of the circuit below level `k` does not change the positions
  `< 2 k`, and if position `2 k + 1` holds a one then `G` adds to position `2 k` (after
  the NOT that is present for `k ≥ 2`) the conjunction of the `m` positions
  `2 k + 2, ..., 2 k + m + 1`.
* `level_step`: one cell `D_k` before and one cell `E_k` after raise the level by one.
* `level_botOdd`, `level_botEven`: the two bottoms.
* `computeW_flags`: if position `2` holds a zero, then after `U` the conjunction of the
  bits on positions `1` and `2` is the conjunction of the bits on the positions
  `1, 3, 4, ..., n + 1`.
-/
import Mathlib
import ApproxToffoli.Line.HelperSweep

namespace Helper

/-! ### The cells, position by position -/

theorem notW_apply (p : ℕ) (w : ℕ → Bool) (i : ℕ) :
    notW p w i = if i = p then !w p else w i := by
  rw [notW, Function.update_apply]

theorem cxW_apply (c t : ℕ) (w : ℕ → Bool) (i : ℕ) :
    cxW c t w i = if i = t then xor (w t) (w c) else w i := by
  rw [cxW, Function.update_apply]

theorem ccW_apply (t a b : ℕ) (w : ℕ → Bool) (i : ℕ) :
    ccW t a b w i = if i = t then xor (w t) (w a && w b) else w i := by
  rw [ccW, Function.update_apply]

/-- The NOT before a cell that writes onto position `2 k`: present only for `k ≥ 2`. -/
def fl (k : ℕ) (b : Bool) : Bool := if 2 ≤ k then !b else b

theorem flW_apply (k : ℕ) (w : ℕ → Bool) (i : ℕ) :
    flW k w i = if i = 2 * k then fl k (w (2 * k)) else w i := by
  unfold flW fl
  by_cases hk : 2 ≤ k
  · rw [if_pos hk, if_pos hk, notW_apply]
  · rw [if_neg hk, if_neg hk]
    by_cases hi : i = 2 * k
    · rw [if_pos hi, hi]
      rfl
    · rw [if_neg hi]
      rfl

theorem dW_apply (k : ℕ) (w : ℕ → Bool) (i : ℕ) :
    dW k w i
      = if i = 2 * k + 1 then xor (!w (2 * k + 1)) (w (2 * k + 3) && w (2 * k + 2))
        else w i := by
  by_cases hi : i = 2 * k + 1 <;> simp [dW, ccW_apply, notW_apply, hi]

theorem eW_apply (k : ℕ) (w : ℕ → Bool) (i : ℕ) :
    eW k w i
      = if i = 2 * k then xor (fl k (w (2 * k))) (w (2 * k + 2) && w (2 * k + 1))
        else w i := by
  by_cases hi : i = 2 * k <;> simp [eW, ccW_apply, flW_apply, hi]

/-! ### Conjunctions of consecutive positions -/

/-- The conjunction of the bits on the `m` positions `lo, lo + 1, ..., lo + m - 1`. -/
def allB (w : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, m + 1 => w lo && allB w (lo + 1) m

theorem allB_succ (w : ℕ → Bool) (lo m : ℕ) :
    allB w lo (m + 1) = (w lo && allB w (lo + 1) m) := rfl

theorem allB_eq_true_iff (w : ℕ → Bool) (lo m : ℕ) :
    allB w lo m = true ↔ ∀ p, lo ≤ p → p < lo + m → w p = true := by
  induction m generalizing lo with
  | zero =>
    constructor
    · intro _ p h1 h2
      omega
    · intro _
      rfl
  | succ m ih =>
    rw [allB_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ p hp1 hp2
      rcases Nat.eq_or_lt_of_le hp1 with rfl | h
      · exact h0
      · exact h1 p h (by omega)
    · intro h
      exact ⟨h lo le_rfl (by omega), fun p hp1 hp2 => h p (by omega) (by omega)⟩

theorem allB_congr {w w' : ℕ → Bool} (lo m : ℕ) (h : ∀ p, lo ≤ p → w p = w' p) :
    allB w lo m = allB w' lo m := by
  induction m generalizing lo with
  | zero => rfl
  | succ m ih =>
    rw [allB_succ, allB_succ, h lo le_rfl, ih (lo + 1) (fun p hp => h p (by omega))]

/-! ### Levels -/

/-- `Level k m G`: `G` does not change the positions `< 2 k`; and if position `2 k + 1`
holds a one, then `G` adds to position `2 k`, after the NOT that is present for `k ≥ 2`,
the conjunction of the `m` positions `2 k + 2, ..., 2 k + m + 1`. -/
def Level (k m : ℕ) (G : (ℕ → Bool) → (ℕ → Bool)) : Prop :=
  ∀ w : ℕ → Bool, (∀ p, p < 2 * k → G w p = w p) ∧
    (w (2 * k + 1) = true →
      G w (2 * k) = xor (fl k (w (2 * k))) (allB w (2 * k + 2) m))

theorem level_bool (g b2 b3 A : Bool) (h : b2 = true → b3 = true → g = A) :
    (g && xor (!true) (b3 && b2)) = (b2 && (b3 && A)) := by
  cases b2 <;> cases b3 <;> first | (simp; done) | (rw [h rfl rfl]; simp)

/-- **One level up**: the cell `D_k` before and the cell `E_k` after. -/
theorem level_step (k m : ℕ) (hk : 1 ≤ k) (G : (ℕ → Bool) → (ℕ → Bool))
    (hG : Level (k + 1) m G) :
    Level k (m + 2) (fun w => eW k (G (dW k w))) := by
  intro w
  obtain ⟨hlt, htop⟩ := hG (dW k w)
  have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have e3 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  have e1 : 2 * (k + 1) = 2 * k + 2 := by omega
  rw [e2, e3, e1] at htop
  constructor
  · intro p hp
    change eW k (G (dW k w)) p = w p
    rw [eW_apply, if_neg (by omega), hlt p (by omega), dW_apply, if_neg (by omega)]
  · intro h1
    change eW k (G (dW k w)) (2 * k)
      = xor (fl k (w (2 * k))) (w (2 * k + 2) && (w (2 * k + 3) && allB w (2 * k + 4) m))
    rw [eW_apply, if_pos rfl, hlt (2 * k) (by omega), hlt (2 * k + 1) (by omega),
      dW_apply, if_neg (by omega), dW_apply, if_pos rfl, h1]
    congr 1
    apply level_bool
    intro h2 h3
    have h3' : dW k w (2 * k + 3) = true := by
      rw [dW_apply, if_neg (by omega)]
      exact h3
    have hc : allB (dW k w) (2 * k + 4) m = allB w (2 * k + 4) m :=
      allB_congr _ _ (fun p hp => by rw [dW_apply, if_neg (by omega)])
    have hf : fl (k + 1) true = false := by
      unfold fl
      rw [if_pos (show 2 ≤ k + 1 by omega)]
      rfl
    rw [htop h3', hc, dW_apply, if_neg (by omega), h2, hf]
    simp

/-- **`d` levels up**: a down sweep before and an up sweep after. -/
theorem level_iter (d k m : ℕ) (hk : 1 ≤ k) (B : (ℕ → Bool) → (ℕ → Bool))
    (hB : Level (k + d) m B) :
    Level k (m + 2 * d) (fun w => upW k d (B (downW k d w))) := by
  induction d generalizing k with
  | zero => exact hB
  | succ d ih =>
    have h1 : Level (k + 1) (m + 2 * d) (fun w => upW (k + 1) d (B (downW (k + 1) d w))) :=
      ih (k + 1) (by omega) (by rwa [show k + 1 + d = k + (d + 1) by omega])
    have h2 := level_step k _ hk _ h1
    rw [show m + 2 * (d + 1) = m + 2 * d + 2 by omega]
    exact h2

/-- The bottom for odd `n` is a level with three positions below it. -/
theorem level_botOdd (K : ℕ) : Level K 3 (botOddW K) := by
  intro w
  constructor
  · intro p hp
    have h0 : p ≠ 2 * K := by omega
    have h1 : p ≠ 2 * K + 1 := by omega
    have h2 : p ≠ 2 * K + 2 := by omega
    simp [botOddW, eW_apply, ccW_apply, notW_apply, cxW_apply, h0, h1, h2]
  · intro h1
    change botOddW K w (2 * K)
      = xor (fl K (w (2 * K))) (w (2 * K + 2) && (w (2 * K + 3) && (w (2 * K + 4) && true)))
    cases h2 : w (2 * K + 2) <;> cases h3 : w (2 * K + 3) <;> cases h4 : w (2 * K + 4) <;>
      simp [botOddW, eW_apply, ccW_apply, notW_apply, cxW_apply, h1, h2, h3, h4]

/-- The last cell `D_K` of the down sweep and the bottom for even `n` are a level with two
positions below it. -/
theorem level_botEven (K : ℕ) : Level K 2 (fun w => botEvenW K (dW K w)) := by
  intro w
  constructor
  · intro p hp
    have h0 : p ≠ 2 * K := by omega
    have h1 : p ≠ 2 * K + 1 := by omega
    simp [botEvenW, cxW_apply, flW_apply, dW_apply, h0, h1]
  · intro h1
    change botEvenW K (dW K w) (2 * K)
      = xor (fl K (w (2 * K))) (w (2 * K + 2) && (w (2 * K + 3) && true))
    cases h2 : w (2 * K + 2) <;> cases h3 : w (2 * K + 3) <;>
      simp [botEvenW, cxW_apply, flW_apply, dW_apply, h1, h2, h3]

/-! ### The circuit `U` -/

theorem downW_snoc (d k : ℕ) (w : ℕ → Bool) :
    downW k (d + 1) w = dW (k + d) (downW k d w) := by
  induction d generalizing k w with
  | zero => rfl
  | succ d ih =>
    change downW (k + 1) (d + 1) (dW k w) = dW (k + (d + 1)) (downW (k + 1) d (dW k w))
    rw [ih, show k + 1 + d = k + (d + 1) by omega]

/-- The part of `U` after the top cell, as a function of the bits. -/
def restW (n : ℕ) (w : ℕ → Bool) : ℕ → Bool :=
  if n % 2 = 1 then upW 1 ((n - 2) / 2 - 1) (botOddW ((n - 2) / 2) (downW 1 ((n - 2) / 2 - 1) w))
  else upW 1 ((n - 2) / 2 - 1) (botEvenW ((n - 2) / 2) (downW 1 ((n - 2) / 2) w))

theorem computeW_eq (n : ℕ) (w : ℕ → Bool) : computeW n w = restW n (andW w) := by
  unfold computeW restW
  split_ifs <;> rfl

/-- The part of `U` after the top cell is a level `1` with the `n - 2` positions
`4, ..., n + 1` below it. -/
theorem level_rest (n : ℕ) (hn : 4 ≤ n) : Level 1 (n - 2) (restW n) := by
  obtain ⟨J, hJ⟩ : ∃ J, (n - 2) / 2 = J + 1 := ⟨(n - 2) / 2 - 1, by omega⟩
  by_cases hodd : n % 2 = 1
  · have hfun : restW n = fun w => upW 1 J (botOddW (1 + J) (downW 1 J w)) := by
      funext w
      unfold restW
      rw [if_pos hodd, hJ, Nat.add_sub_cancel, Nat.add_comm J 1]
    rw [hfun, show n - 2 = 3 + 2 * J by omega]
    exact level_iter J 1 3 le_rfl _ (level_botOdd (1 + J))
  · have hfun : restW n
        = fun w => upW 1 J ((fun s => botEvenW (1 + J) (dW (1 + J) s)) (downW 1 J w)) := by
      funext w
      unfold restW
      rw [if_neg hodd, hJ, Nat.add_sub_cancel, downW_snoc, Nat.add_comm J 1]
    rw [hfun, show n - 2 = 2 + 2 * J by omega]
    exact level_iter J 1 2 le_rfl _ (level_botEven (1 + J))

/-- **The flags.**  If position `2` (the helper) holds a zero, then after `U` the
conjunction of the bits on positions `1` and `2` is the conjunction of the bits on the
positions `1, 3, 4, ..., n + 1` (the controls). -/
theorem computeW_flags (n : ℕ) (hn : 4 ≤ n) (w : ℕ → Bool) (h2 : w 2 = false) :
    (computeW n w 1 && computeW n w 2) = (w 1 && (w 3 && allB w 4 (n - 2))) := by
  obtain ⟨hlt, htop⟩ := level_rest n hn (andW w)
  have h1 : computeW n w 1 = (w 1 && w 3) := by
    rw [computeW_eq, hlt 1 (by omega), andW_apply w h2, if_pos rfl]
  rw [h1]
  cases h3 : w 3
  · simp
  · have ha3 : andW w (2 * 1 + 1) = true := by
      rw [andW_apply w h2, if_neg (by omega), if_neg (by omega)]
      exact h3
    have hc : allB (andW w) (2 * 1 + 2) (n - 2) = allB w 4 (n - 2) :=
      allB_congr _ _ (fun p hp => by
        rw [andW_apply w h2, if_neg (by omega), if_neg (by omega)])
    have ha2 : andW w (2 * 1) = false := by
      rw [andW_apply w h2, if_neg (by omega), if_pos rfl, h3]
      simp
    have hf : fl 1 false = false := rfl
    have h22 : computeW n w 2 = allB w 4 (n - 2) := by
      rw [computeW_eq]
      change restW n (andW w) (2 * 1) = _
      rw [htop ha3, hc, ha2, hf]
      simp
    rw [h22]
    simp

end Helper
