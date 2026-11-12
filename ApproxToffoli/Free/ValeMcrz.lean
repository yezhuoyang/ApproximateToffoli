/-
The circuit of Vale et al.: the multi-controlled `R_z` (S9), the chain of controlled
phases (S10) and the whole circuit (S11).

`mcrz lam m` is two multi-controlled X gates onto qubit `m`, each used twice, with
phase gates in between: a diagonal 2×2 block on qubit `m` that is `R_z(lam)` when all
controls are one and the identity otherwise.  The chain of these gates is the phase
`-1` on the all-ones state, and two Hadamard gates turn it into the conditional.
-/
import Mathlib
import ApproxToffoli.Free.ValeMcx

namespace Vale

open Matrix Free ExactLine
open Line (St hGate pGate xGate condMat cxFun cxPerm oneMat ctrlMat m2)
open Qulin (qb cx ccx pc)

variable {N : ℕ}

/-! ### `pc`: the first controls are all one -/

theorem pc_add (c : ℕ → Fin N) (n n' : ℕ) (x : St N) :
    pc c (n + n') x = (pc c n x && pc (fun i => c (n + i)) n' x) := by
  induction n' with
  | zero => exact (Bool.and_true _).symm
  | succ n' ih =>
    change (pc c (n + n') x && x (c (n + n')))
      = (pc c n x && (pc (fun i => c (n + i)) n' x && x (c (n + n'))))
    rw [ih, Bool.and_assoc]

/-! ### `mcx` as a block on its target -/

/-- `mcx` is a NOT block on its target, switched on by its controls. -/
theorem circMat_mcx (hN : 0 < N) {k c0 a0 t : ℕ} (h : McxOk N k c0 a0 t) :
    circMat (mcx N hN k c0 a0 t)
      = ctrlMat (qb N hN t)
          (fun x => if pc (fun i => qb N hN (c0 + i)) k x then xGate else 1) := by
  have hf : ∀ (x : St N) (b : Bool),
      pc (fun i => qb N hN (c0 + i)) k (Function.update x (qb N hN t) b)
        = pc (fun i => qb N hN (c0 + i)) k x :=
    fun x b => Qulin.pc_update _ k _
      (fun i hi => Qulin.qb_ne hN h.2.2.1 (by have := h.2.1; omega)
        (by have := h.2.2.2.1; omega)) x b
  rw [← Line.flip_eq_ctrlMat (qb N hN t) _ hf]
  exact acts_mcx hN h

/-! ### S9. The multi-controlled `R_z` -/

theorem ctrlMat_const_mul (q : Fin N) (g : Matrix Bool Bool ℂ)
    (h : St N → Matrix Bool Bool ℂ) :
    ctrlMat q (fun _ => g) * ctrlMat q h = ctrlMat q (fun x => g * h x) :=
  Line.ctrlMat_mul q _ _ (fun _ _ => rfl)

theorem ctrlMat_flip_mul (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) (h : St N → Matrix Bool Bool ℂ) :
    ctrlMat q (fun x => if f x then xGate else 1) * ctrlMat q h
      = ctrlMat q (fun x => (if f x then xGate else 1) * h x) :=
  Line.ctrlMat_mul q _ _ (fun x b => by rw [hf])

/-- The 2×2 fact of S9: with `S = P(-lam/4)`, the block `S⁻¹ X^b S X^a S⁻¹ X^b S X^a` is
`diag(e^{-i lam/2}, e^{i lam/2})` if `a = b = 1` and the identity otherwise. -/
theorem mcrz_block (lam : ℝ) (a b : Bool) :
    pGate (lam / 4) * ((if b then xGate else 1) * (pGate (-(lam / 4))
      * ((if a then xGate else 1) * (pGate (lam / 4) * ((if b then xGate else 1)
      * (pGate (-(lam / 4)) * (if a then xGate else 1)))))))
      = dg (if a && b then -(lam / 2) else 0) (if a && b then lam / 2 else 0) := by
  cases a <;> cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_mul, Matrix.mul_one,
      pGate_eq_dg, x_mul_dg_assoc, x_mul_dg, x_mul_x, dg_mul_assoc, dg_mul,
      Bool.and_self, Bool.and_true, Bool.and_false] <;>
    congr 1 <;> ring

/-- Two conditional flips of `t`, each used twice, with phase gates in between: the
phase `e^{± i lam/2}` when both conditions hold, and nothing otherwise. -/
theorem mcrz_core (t : Fin N) (fa fb : St N → Bool)
    (ha : ∀ x s, fa (Function.update x t s) = fa x)
    (hb : ∀ x s, fb (Function.update x t s) = fb x) (A B : List (Gate N))
    (hA : circMat A = ctrlMat t (fun x => if fa x then xGate else 1))
    (hB : circMat B = ctrlMat t (fun x => if fb x then xGate else 1)) (lam : ℝ) :
    circMat (A ++ pG (-(lam / 4)) t ++ B ++ pG (lam / 4) t ++
        A ++ pG (-(lam / 4)) t ++ B ++ pG (lam / 4) t)
      = Matrix.diagonal
          (fun x => e (if fa x && fb x then (if x t then lam / 2 else -(lam / 2)) else 0)) := by
  simp only [circMat_append, hA, hB, circMat_pG_ctrl]
  rw [ctrlMat_const_mul, ctrlMat_flip_mul t fb hb, ctrlMat_const_mul, ctrlMat_flip_mul t fa ha,
    ctrlMat_const_mul, ctrlMat_flip_mul t fb hb, ctrlMat_const_mul]
  refine (congrArg (ctrlMat t) (funext fun x => mcrz_block lam (fa x) (fb x))).trans ?_
  rw [ctrlMat_dg]
  congr 1
  funext x
  cases fa x && fb x <;> cases x t <;> rfl

theorem mcxOk_first {m : ℕ} (hm2 : 2 ≤ m) (hm : m < N) :
    McxOk N ((m + 1) / 2) 0 ((m + 1) / 2) m :=
  ⟨by omega, by omega, hm, by omega, fun _ => ⟨by omega, by omega, by omega⟩⟩

theorem mcxOk_second {m : ℕ} (hm2 : 2 ≤ m) (hm : m < N) :
    McxOk N (m / 2) ((m + 1) / 2) ((m + 1) / 2 - m / 2 + 2) m :=
  ⟨by omega, by omega, hm, by omega, fun _ => ⟨by omega, by omega, by omega⟩⟩

/-- **S9.**  `mcrz lam m` is diagonal: the phase `e^{± i lam/2}` (sign `+` if bit `m` is
one) when the bits `0 .. m-1` are all one, and `1` otherwise. -/
theorem circMat_mcrz (hN : 0 < N) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < N) (lam : ℝ) :
    circMat (mcrz N hN lam m)
      = Matrix.diagonal (fun x => e (if pc (qb N hN) m x
          then (if x (qb N hN m) then lam / 2 else -(lam / 2)) else 0)) := by
  by_cases h1 : m = 1
  · subst h1
    rw [mcrz, if_pos rfl, circMat_crz (Qulin.qb_ne hN (by omega) hm (by omega))]
    congr 1
  · have hupd : ∀ (c0 k : ℕ), c0 + k ≤ m → ∀ (x : St N) (s : Bool),
        pc (fun i => qb N hN (c0 + i)) k (Function.update x (qb N hN m) s)
          = pc (fun i => qb N hN (c0 + i)) k x :=
      fun c0 k hk x s => Qulin.pc_update _ k _
        (fun i hi => Qulin.qb_ne hN hm (by omega) (by omega)) x s
    have h0 : (fun i => qb N hN (0 + i)) = qb N hN := funext fun i => by rw [Nat.zero_add]
    rw [mcrz, if_neg h1,
      mcrz_core (qb N hN m) _ _ (hupd 0 ((m + 1) / 2) (by omega))
        (hupd ((m + 1) / 2) (m / 2) (by omega)) _ _
        (circMat_mcx hN (mcxOk_first (by omega) hm))
        (circMat_mcx hN (mcxOk_second (by omega) hm)) lam]
    congr 1
    funext x
    have hsplit := pc_add (qb N hN) ((m + 1) / 2) (m / 2) x
    rw [show (m + 1) / 2 + m / 2 = m by omega] at hsplit
    rw [h0, ← hsplit]

/-! ### S10. The chain of controlled phases -/

/-- **S10.**  `phaseChain m lam` is diagonal: the phase `e^{i lam}` when the bits
`0 .. m` are all one, and `1` otherwise. -/
theorem circMat_phaseChain (hN : 0 < N) (m : ℕ) (hm : m < N) (lam : ℝ) :
    circMat (phaseChain N hN m lam)
      = Matrix.diagonal (fun x => e (if pc (qb N hN) (m + 1) x then lam else 0)) := by
  induction m generalizing lam with
  | zero =>
    rw [phaseChain, circMat_pG]
    congr 1
  | succ m ih =>
    rw [phaseChain, circMat_append, ih (by omega), circMat_mcrz hN (by omega) hm, diag_e_mul]
    congr 1
    funext x
    congr 1
    have hp : pc (qb N hN) (m + 1 + 1) x
        = (pc (qb N hN) (m + 1) x && x (qb N hN (m + 1))) := rfl
    rw [hp]
    cases pc (qb N hN) (m + 1) x <;> cases x (qb N hN (m + 1)) <;> simp

/-! ### S11. The whole circuit -/

/-- **S11.  The circuit of Vale et al. is the conditional**, exactly. -/
theorem circMat_vale (hN : 0 < N) : circMat (vale N hN) = condMat (qb N hN (N - 1)) := by
  have hs : Matrix.diagonal
        (fun x : St N => e (if pc (qb N hN) (N - 1 + 1) x then Real.pi else 0))
      = Line.signMat N := by
    unfold Line.signMat
    congr 1
    funext x
    have hiff : (∀ i < N - 1 + 1, x (qb N hN i) = true) ↔ ∀ r, x r = true := by
      constructor
      · intro h r
        have h1 := h r.val (by have := r.isLt; omega)
        rwa [Qulin.qb_self] at h1
      · intro h i _
        exact h _
    rw [Qulin.pc_eq_decide]
    by_cases hall : ∀ r, x r = true
    · rw [if_pos hall, if_pos (decide_eq_true (hiff.2 hall)), e_pi]
    · rw [if_neg hall, if_neg (fun h => hall (hiff.1 (of_decide_eq_true h))), e_zero]
  have hH : circMat (hG (qb N hN (N - 1))) = oneMat (qb N hN (N - 1)) hGate :=
    circMat_singleton _
  unfold vale
  rw [circMat_append, circMat_append, circMat_phaseChain hN (N - 1) (by omega), hs, hH,
    ← Matrix.mul_assoc]
  exact Line.hGate_sign_hGate _

/-! ### Unitary gates -/

theorem unitaryGates_mcrz (hN : 0 < N) (lam : ℝ) (m : ℕ) : UnitaryGates (mcrz N hN lam m) := by
  unfold mcrz
  split_ifs
  · exact unitaryGates_crz _ _ _
  · simp only [unitaryGates_append_iff, unitaryGates_pG, unitaryGates_mcx, and_self]

theorem unitaryGates_phaseChain (hN : 0 < N) (m : ℕ) (lam : ℝ) :
    UnitaryGates (phaseChain N hN m lam) := by
  induction m generalizing lam with
  | zero => exact unitaryGates_pG _ _
  | succ m ih => exact unitaryGates_append (unitaryGates_mcrz hN _ _) (ih _)

theorem unitaryGates_vale (hN : 0 < N) : UnitaryGates (vale N hN) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_hG _) (unitaryGates_phaseChain hN _ _))
    (unitaryGates_hG _)

end Vale
