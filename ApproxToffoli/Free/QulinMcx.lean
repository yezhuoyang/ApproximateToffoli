/-
The multi-controlled X gate with borrowed qubits of the Huang–Palsberg circuit
(`Qulin.mcx`, paper Eq. (2)): it flips the target iff all `k` controls are one, exactly
(no phase, borrowed qubits restored), with `8k - 6` CNOTs and `8k - 2` T gates.
-/
import Mathlib
import ApproxToffoli.Free.QulinCells

namespace Qulin

open Matrix Free ExactLine
open Line (St hGate pGate xGate ryGate condMat cxFun cxPerm oneMat ctrlMat m2)

variable {N : ℕ}

/-! ### Functions on basis states up to phases -/

/-- The matrix that sends basis state `x` to `φ x` times basis state `F x`. -/
def fmono (F : St N → St N) (φ : St N → ℂ) : Matrix (St N) (St N) ℂ :=
  Matrix.of fun y x => if y = F x then φ x else 0

theorem permMat_eq_fmono (F : St N → St N) : permMat F = fmono F (fun _ => 1) := rfl

theorem mul_fmono_apply (M : Matrix (St N) (St N) ℂ) (F : St N → St N) (φ : St N → ℂ)
    (y x : St N) : (M * fmono F φ) y x = M y (F x) * φ x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (F x)]
  · simp [fmono]
  · intro z _ hz
    simp [fmono, hz]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fmono_mul (G F : St N → St N) (ψ φ : St N → ℂ) :
    fmono G ψ * fmono F φ = fmono (G ∘ F) (fun x => ψ (F x) * φ x) := by
  ext y x
  rw [mul_fmono_apply]
  simp [fmono]

theorem fmono_congr {F G : St N → St N} {φ ψ : St N → ℂ} (hF : ∀ x, F x = G x)
    (hφ : ∀ x, φ x = ψ x) : fmono F φ = fmono G ψ := by
  rw [funext hF, funext hφ]

/-- **Conjugating a function up to phases by two cells on a qubit it does not involve.**
If `F` and `φ` do not involve qubit `s`, and the product of the two blocks is supported
on the entries `(q xor f x, q)`, the result is again a function up to phases: `F`
followed by "flip `s` iff `f x`". -/
theorem ctrl_fmono_ctrl (s : Fin N) (F : St N → St N) (φ : St N → ℂ)
    (G₁ G₂ : St N → Matrix Bool Bool ℂ) (f : St N → Bool)
    (hF : ∀ x b, F (Function.update x s b) = Function.update (F x) s b)
    (hφ : ∀ x b, φ (Function.update x s b) = φ x)
    (hG : ∀ x b, G₂ (Function.update x s b) = G₂ x)
    (hK : ∀ x p q, p ≠ xor q (f x) → (G₂ (F x) * G₁ x) p q = 0) :
    ctrlMat s G₂ * fmono F φ * ctrlMat s G₁
      = fmono (fun x => Function.update (F x) s (xor (x s) (f x)))
          (fun x => φ x * (G₂ (F x) * G₁ x) (xor (x s) (f x)) (x s)) := by
  ext y x
  have hFs : F x s = x s := by
    have h := congrFun (hF x (x s)) s
    rw [Function.update_eq_self, Function.update_self] at h
    exact h
  have key : (y = Function.update (F x) s (xor (x s) (f x))) ↔
      (y s = xor (x s) (f x)) ∧ ∀ r, r ≠ s → y r = F x r := Function.eq_update_iff
  have hx : ∀ b, (∀ r, r ≠ s → Function.update x s b r = x r) :=
    fun b r hr => Function.update_of_ne hr _ _
  rw [Matrix.mul_apply, Line.sum_agree s x]
  · simp only [mul_fmono_apply, hF, hφ]
    simp only [ctrlMat, fmono, Matrix.of_apply, hG, if_pos (hx true), if_pos (hx false),
      Function.update_self]
    by_cases h1 : ∀ r, r ≠ s → y r = F x r
    · have h2 : ∀ b, (∀ r, r ≠ s → y r = Function.update (F x) s b r) := by
        intro b r hr
        rw [Function.update_of_ne hr]
        exact h1 r hr
      rw [if_pos (h2 true), if_pos (h2 false)]
      have e : G₂ (F x) (y s) true * φ x * G₁ x true (x s)
          + G₂ (F x) (y s) false * φ x * G₁ x false (x s)
          = φ x * (G₂ (F x) * G₁ x) (y s) (x s) := by
        rw [Matrix.mul_apply, Fintype.sum_bool]
        ring
      rw [e]
      by_cases h3 : y s = xor (x s) (f x)
      · rw [if_pos (key.2 ⟨h3, h1⟩), h3]
      · rw [if_neg (fun h => h3 (key.1 h).1), hK x _ _ h3, mul_zero]
    · have h2 : ∀ b, ¬ (∀ r, r ≠ s → y r = Function.update (F x) s b r) := by
        intro b hb
        apply h1
        intro r hr
        have := hb r hr
        rwa [Function.update_of_ne hr] at this
      rw [if_neg (h2 true), if_neg (h2 false), if_neg (fun h => h1 (key.1 h).2)]
      simp
  · intro z hz
    simp [ctrlMat, hz]

/-! ### The 2×2 blocks of the relative-phase pieces -/

/-- The block of `ryA` on its target, for the bits `u`, `v` of its controls. -/
noncomputable def aBlk (u v : Bool) : Matrix Bool Bool ℂ :=
  (if u then xGate else 1) * ryGate (-(Real.pi / 4)) * (if v then xGate else 1)
    * ryGate (-(Real.pi / 4))

/-- The block of `ryAinv` on its target. -/
noncomputable def aInvBlk (u v : Bool) : Matrix Bool Bool ℂ :=
  ryGate (Real.pi / 4) * (if v then xGate else 1) * ryGate (Real.pi / 4)
    * (if u then xGate else 1)

/-- The block of the relative-phase Toffoli: `1` if `d` is zero, `X` if `d = v = 1`,
`diag(-1, 1)` if `d = 1`, `v = 0`. -/
def wBlk (d v : Bool) : Matrix Bool Bool ℂ :=
  if d then (if v then m2 0 1 1 0 else m2 (-1) 0 0 1) else m2 1 0 0 1

theorem ryGate_neg_quarter :
    ryGate (-(Real.pi / 4))
      = m2 (Real.cos (Real.pi / 8) : ℂ) (Real.sin (Real.pi / 8) : ℂ)
          (-(Real.sin (Real.pi / 8) : ℂ)) (Real.cos (Real.pi / 8) : ℂ) := by
  rw [Line.ryGate, show -(Real.pi / 4) / 2 = -(Real.pi / 8) by ring, Real.cos_neg, Real.sin_neg]
  simp only [Complex.ofReal_neg, neg_neg]

theorem ryN_sq :
    ryGate (-(Real.pi / 4)) * ryGate (-(Real.pi / 4)) = m2 Line.rh Line.rh (-Line.rh) Line.rh := by
  have hC : _ = Line.rh := Line.cos_sq_sub_sin_sq_eighth
  have hS : _ = Line.rh := Line.two_sin_cos_eighth
  rw [ryGate_neg_quarter, Line.m2_mul]
  congr 1
  · linear_combination hC
  · linear_combination hS
  · linear_combination -hS
  · linear_combination hC

theorem ryN_x : ryGate (-(Real.pi / 4)) * xGate * ryGate (-(Real.pi / 4)) = xGate := by
  have hP := Line.cos_sq_add_sin_sq_eighth
  rw [ryGate_neg_quarter, Line.xGate_eq_m2, Line.m2_mul, Line.m2_mul]
  congr 1
  · ring
  · linear_combination hP
  · linear_combination hP
  · ring

/-- **The key 2×2 fact**: `ryA` with first control `u` followed by `ryAinv` with first
control `u'` is the relative-phase Toffoli block controlled by `u xor u'`. -/
theorem aInv_mul_a (u u' v : Bool) : aInvBlk u' v * aBlk u v = wBlk (xor u u') v := by
  have hh := Line.rh_sq
  have hre : aInvBlk u' v * aBlk u v
      = (ryGate (Real.pi / 4) * (if v then xGate else 1) * ryGate (Real.pi / 4))
        * (if u' then xGate else 1) * (if u then xGate else 1)
        * (ryGate (-(Real.pi / 4)) * (if v then xGate else 1) * ryGate (-(Real.pi / 4))) := by
    simp only [aBlk, aInvBlk, Matrix.mul_assoc]
  rw [hre]
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one, Line.ry1_sq, ryN_sq]
    cases u <;> cases u' <;>
      simp only [Bool.false_eq_true, ↓reduceIte, wBlk, Line.xGate_eq_m2, Line.one_eq_m2,
        Line.m2_mul, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true] <;>
      congr 1 <;>
      first
        | ring1
        | linear_combination (-2) * hh
        | linear_combination 2 * hh
  · simp only [↓reduceIte, Line.ry1_x, ryN_x]
    cases u <;> cases u' <;>
      simp only [Bool.false_eq_true, ↓reduceIte, wBlk, Line.xGate_eq_m2, Line.one_eq_m2,
        Line.m2_mul, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true] <;>
      congr 1 <;> ring1

/-! ### The matrices of `ryA`, `ryAinv` and `marg` -/

theorem circMat_ryA {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (ryA u v s) = ctrlMat s (fun x => aBlk (x u) (x v)) := by
  unfold ryA
  rw [cx_eq u s hu, cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, one_mat_eq_ctrl2 u s v,
    cx_top_mat_eq_ctrl2 u s v, cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  rfl

theorem circMat_ryAinv {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (ryAinv u v s) = ctrlMat s (fun x => aInvBlk (x u) (x v)) := by
  unfold ryAinv
  rw [cx_eq u s hu, cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, one_mat_eq_ctrl2 u s v,
    cx_top_mat_eq_ctrl2 u s v, cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  rfl

/-- The last three gates of `marg` are `ryAinv` with its first control switched off. -/
theorem circMat_margTail {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat ([Gate.one s (ryGate (Real.pi / 4))] ++ cx v s ++ [Gate.one s (ryGate (Real.pi / 4))])
      = ctrlMat s (fun x => aInvBlk false (x v)) := by
  rw [cx_eq v s hv]
  simp only [List.cons_append, List.nil_append, circMat, one_mul, one_mat_eq_ctrl2 u s v,
    cx_bot_mat_eq_ctrl2 u s v, Line.ctrl2_mul u s v hu hv]
  unfold Line.ctrl2
  congr 1
  funext x
  simp [aInvBlk]

/-! ### What the chain does: the function and the sign -/

/-- The first `n` controls `c 0, ..., c (n-1)` are all one. -/
def pc (c : ℕ → Fin N) : ℕ → St N → Bool
  | 0, _ => true
  | n + 1, x => pc c n x && x (c n)

/-- The function of `wChain c a j`: for every `i ≤ j`, flip `a i` iff
`c 0, ..., c (i+1)` are all one. -/
def wF (c a : ℕ → Fin N) : ℕ → St N → St N
  | 0, x => Function.update x (a 0) (xor (x (a 0)) (pc c 2 x))
  | j + 1, x => Function.update (wF c a j x) (a (j + 1)) (xor (x (a (j + 1))) (pc c (j + 3) x))

/-- The sign of one level of the chain. -/
def wSgn (p v s : Bool) : ℂ := if p && !v && !s then -1 else 1

/-- The sign of `wChain c a j`. -/
def wS (c a : ℕ → Fin N) : ℕ → St N → ℂ
  | 0, x => wSgn (x (c 0)) (x (c 1)) (x (a 0))
  | j + 1, x => wS c a j x * wSgn (pc c (j + 2) x) (x (c (j + 2))) (x (a (j + 1)))

theorem pc_eq_decide (c : ℕ → Fin N) (n : ℕ) (x : St N) :
    pc c n x = decide (∀ i < n, x (c i) = true) := by
  induction n with
  | zero => simp [pc]
  | succ n ih =>
    rw [pc, ih, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · rw [h]
        exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-- `pc` looks only at the controls. -/
theorem pc_congr (c : ℕ → Fin N) (n : ℕ) {x y : St N} (h : ∀ i < n, y (c i) = x (c i)) :
    pc c n y = pc c n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pc, pc, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem pc_update (c : ℕ → Fin N) (n : ℕ) (s : Fin N) (hs : ∀ i < n, s ≠ c i) (x : St N)
    (b : Bool) : pc c n (Function.update x s b) = pc c n x :=
  pc_congr c n (fun i hi => Function.update_of_ne (hs i hi).symm _ _)

/-- `wF` changes only the borrowed qubits `a 0, ..., a j`. -/
theorem wF_of_ne (c a : ℕ → Fin N) (j : ℕ) (r : Fin N) (hr : ∀ i ≤ j, r ≠ a i) (x : St N) :
    wF c a j x r = x r := by
  induction j with
  | zero => rw [wF, Function.update_of_ne (hr 0 le_rfl)]
  | succ j ih =>
    rw [wF, Function.update_of_ne (hr (j + 1) le_rfl), ih (fun i hi => hr i (Nat.le_succ_of_le hi))]

theorem wF_last (c a : ℕ → Fin N) (j : ℕ) (x : St N) :
    wF c a j x (a j) = xor (x (a j)) (pc c (j + 2) x) := by
  cases j <;> rw [wF, Function.update_self]

/-- `wF` commutes with setting a qubit that is neither one of `a 0 .. a j` nor one of
`c 0 .. c (j+1)`. -/
theorem wF_update (c a : ℕ → Fin N) (j : ℕ) (s : Fin N) (hsa : ∀ i ≤ j, s ≠ a i)
    (hsc : ∀ i < j + 2, s ≠ c i) (x : St N) (b : Bool) :
    wF c a j (Function.update x s b) = Function.update (wF c a j x) s b := by
  induction j with
  | zero =>
    rw [wF, wF, Function.update_of_ne (hsa 0 le_rfl).symm, pc_update c 2 s hsc,
      Function.update_comm (hsa 0 le_rfl)]
  | succ j ih =>
    rw [wF, wF, Function.update_of_ne (hsa (j + 1) le_rfl).symm, pc_update c (j + 3) s hsc,
      ih (fun i hi => hsa i (Nat.le_succ_of_le hi)) (fun i hi => hsc i (Nat.lt_succ_of_lt hi)),
      Function.update_comm (hsa (j + 1) le_rfl)]

theorem wS_update (c a : ℕ → Fin N) (j : ℕ) (s : Fin N) (hsa : ∀ i ≤ j, s ≠ a i)
    (hsc : ∀ i < j + 2, s ≠ c i) (x : St N) (b : Bool) :
    wS c a j (Function.update x s b) = wS c a j x := by
  induction j with
  | zero =>
    rw [wS, wS, Function.update_of_ne (hsa 0 le_rfl).symm,
      Function.update_of_ne (hsc 0 (by omega)).symm, Function.update_of_ne (hsc 1 (by omega)).symm]
  | succ j ih =>
    rw [wS, wS, Function.update_of_ne (hsa (j + 1) le_rfl).symm,
      Function.update_of_ne (hsc (j + 2) (by omega)).symm,
      pc_update c (j + 2) s (fun i hi => hsc i (Nat.lt_succ_of_lt hi)),
      ih (fun i hi => hsa i (Nat.le_succ_of_le hi)) (fun i hi => hsc i (Nat.lt_succ_of_lt hi))]

/-! ### The relative-phase Toffoli and the chain -/

theorem wBlk_support (d v p q : Bool) (h : p ≠ xor q (d && v)) : wBlk d v p q = 0 := by
  revert h
  cases d <;> cases v <;> cases p <;> cases q <;> simp [wBlk, m2]

theorem wBlk_entry (d v q : Bool) : wBlk d v (xor q (d && v)) q = wSgn d v q := by
  cases d <;> cases v <;> cases q <;> simp [wBlk, m2, wSgn]

theorem fmono_id_one : fmono (id : St N → St N) (fun _ => 1) = 1 := by
  rw [← permMat_eq_fmono, permMat_id]

/-- **The relative-phase Toffoli**: flip `s` iff `u` and `v` are one, with the sign `-1`
exactly when `u = 1`, `v = 0`, `s = 0`. -/
theorem circMat_marg {u v s : Fin N} (hu : u ≠ s) (hv : v ≠ s) :
    circMat (marg u v s)
      = fmono (fun x => Function.update x s (xor (x s) (x u && x v)))
          (fun x => wSgn (x u) (x v) (x s)) := by
  have hl : marg u v s = ryA u v s ++ ([Gate.one s (ryGate (Real.pi / 4))] ++ cx v s ++
      [Gate.one s (ryGate (Real.pi / 4))]) := by
    simp only [marg, List.append_assoc]
  have hprod : ∀ x : St N, aInvBlk false (x v) * aBlk (x u) (x v) = wBlk (x u) (x v) := by
    intro x
    rw [aInv_mul_a, Bool.xor_false]
  rw [hl, circMat_append, circMat_margTail hu hv, circMat_ryA hu hv,
    ← Matrix.mul_one (ctrlMat s fun x => aInvBlk false (x v)), ← fmono_id_one,
    ctrl_fmono_ctrl s id (fun _ => 1) _ _ (fun x => x u && x v) (fun _ _ => rfl)
      (fun _ _ => rfl)]
  · apply fmono_congr
    · intro x
      rfl
    · intro x
      simp only [id, one_mul]
      rw [hprod, wBlk_entry]
  · intro x b
    simp only [Function.update_of_ne hv]
  · intro x p q h
    simp only [id]
    rw [hprod]
    exact wBlk_support _ _ _ _ h

theorem xor_xor_self_left (u p : Bool) : xor u (xor u p) = p := by
  cases u <;> cases p <;> rfl

/-- **The chain** is a function up to signs: `wF` with the sign `wS`. -/
theorem circMat_wChain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    circMat (wChain c a j) = fmono (wF c a j) (wS c a j) := by
  induction j with
  | zero =>
    rw [wChain, circMat_marg (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)]
    apply fmono_congr
    · intro x
      simp [wF, pc]
    · intro x
      rfl
  | succ j ih =>
    have hu : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hv : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    have hprod : ∀ x : St N,
        aInvBlk (wF c a j x (a j)) (wF c a j x (c (j + 2))) * aBlk (x (a j)) (x (c (j + 2)))
          = wBlk (pc c (j + 2) x) (x (c (j + 2))) := by
      intro x
      rw [wF_last, wF_of_ne c a j (c (j + 2)) (fun i hi => hca (j + 2) (by omega) i (by omega)),
        aInv_mul_a, xor_xor_self_left]
    rw [wChain, circMat_append, circMat_append, circMat_ryA hu hv, circMat_ryAinv hu hv,
      ih (by omega), ← Matrix.mul_assoc,
      ctrl_fmono_ctrl (a (j + 1)) (wF c a j) (wS c a j) _ _ (pc c (j + 3))
        (wF_update c a j _ hsa hsc) (wS_update c a j _ hsa hsc)]
    · apply fmono_congr
      · intro x
        rfl
      · intro x
        rw [hprod]
        exact congrArg _ (wBlk_entry _ _ _)
    · intro x b
      simp only [Function.update_of_ne hu, Function.update_of_ne hv]
    · intro x p q h
      rw [hprod]
      exact wBlk_support _ _ _ _ h

/-! ### The chain applied twice -/

theorem wF_ctrl {k : ℕ} {c a : ℕ → Fin N} (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2)
    (i : ℕ) (hi : i < k) (x : St N) : wF c a j x (c i) = x (c i) :=
  wF_of_ne c a j (c i) (fun l hl => hca i hi l (by omega)) x

theorem pc_wF {k : ℕ} {c a : ℕ → Fin N} (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2)
    (n : ℕ) (hn : n ≤ k) (x : St N) : pc c n (wF c a j x) = pc c n x :=
  pc_congr c n (fun i hi => wF_ctrl hca j hj i (by omega) x)

theorem flip_flip (x : St N) (s : Fin N) (p : Bool) :
    Function.update (Function.update x s (xor (x s) p)) s (xor (xor (x s) p) p) = x := by
  rw [Function.update_idem, Bool.xor_assoc, Bool.xor_self, Bool.xor_false,
    Function.update_eq_self]

/-- The function of the chain is an involution. -/
theorem wF_wF {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a)
    (j : ℕ) (hj : j < k - 2) (x : St N) : wF c a j (wF c a j x) = x := by
  induction j with
  | zero =>
    rw [wF, pc_wF hca 0 hj 2 (by omega), wF_last, wF]
    exact flip_flip x (a 0) (pc c 2 x)
  | succ j ih =>
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    rw [wF, pc_wF hca (j + 1) hj (j + 3) (by omega), wF_last, wF, wF_update c a j _ hsa hsc,
      ih (by omega)]
    exact flip_flip x (a (j + 1)) (pc c (j + 3) x)

theorem wSgn_flip (p v s : Bool) : wSgn p v (xor s (p && v)) = wSgn p v s := by
  cases p <;> cases v <;> cases s <;> rfl

theorem wSgn_sq (p v s : Bool) : wSgn p v s * wSgn p v s = 1 := by
  cases p <;> cases v <;> cases s <;> simp [wSgn]

theorem wS_sq (c a : ℕ → Fin N) (j : ℕ) (x : St N) : wS c a j x * wS c a j x = 1 := by
  induction j with
  | zero => exact wSgn_sq _ _ _
  | succ j ih =>
    rw [wS, mul_mul_mul_comm, ih, wSgn_sq, one_mul]

/-- The sign of the chain is the same before and after the chain. -/
theorem wS_wF {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a)
    (j : ℕ) (hj : j < k - 2) (x : St N) : wS c a j (wF c a j x) = wS c a j x := by
  induction j with
  | zero =>
    rw [wS, wF_ctrl hca 0 hj 0 (by omega), wF_ctrl hca 0 hj 1 (by omega), wF_last]
    change wSgn (x (c 0)) (x (c 1)) (xor (x (a 0)) ((true && x (c 0)) && x (c 1))) = _
    rw [Bool.true_and, wSgn_flip]
    rfl
  | succ j ih =>
    have hsa : ∀ i ≤ j, a (j + 1) ≠ a i := fun i hi h => by
      have := ha (j + 1) hj i (by omega) h
      omega
    have hsc : ∀ i < j + 2, a (j + 1) ≠ c i := fun i hi => (hca i (by omega) (j + 1) hj).symm
    rw [wS, pc_wF hca (j + 1) hj (j + 2) (by omega), wF_ctrl hca (j + 1) hj (j + 2) (by omega),
      wF_last, wF, wS_update c a j _ hsa hsc, ih (by omega)]
    change _ * wSgn (pc c (j + 2) x) (x (c (j + 2)))
      (xor (x (a (j + 1))) (pc c (j + 2) x && x (c (j + 2)))) = _
    rw [wSgn_flip]
    rfl

/-! ### The multi-controlled gate -/

/-- Half of the gate: the Toffoli onto the target, then the chain. -/
theorem circMat_mcxHalf {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) :
    circMat (mcxHalf k c a t)
      = fmono (fun x => Function.update (wF c a (k - 3) x) t
            (xor (x t) (x (a (k - 3)) && x (c (k - 1)))))
          (wS c a (k - 3)) := by
  have hj : k - 3 < k - 2 := by omega
  have hab : a (k - 3) ≠ c (k - 1) := (hca (k - 1) (by omega) (k - 3) hj).symm
  have hat : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  have hbt : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  have h1 : circMat (ccx (a (k - 3)) (c (k - 1)) t) = permMat _ := acts_ccx hab hat hbt
  have hsa : ∀ i ≤ k - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < k - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold mcxHalf
  rw [circMat_append, circMat_wChain ha hca _ hj, h1, permMat_eq_fmono, fmono_mul]
  apply fmono_congr
  · intro x
    exact wF_update c a (k - 3) t hsa hsc x _
  · intro x
    rw [mul_one]
    exact wS_update c a (k - 3) t hsa hsc x _

theorem mcx_bit (s u v p : Bool) : xor (xor s (u && v)) (xor u p && v) = xor s (p && v) := by
  cases s <;> cases u <;> cases v <;> cases p <;> rfl

/-- **The multi-controlled X with borrowed qubits**, exactly: flip `t` iff all `k`
controls are one; the borrowed qubits come back unchanged and there is no phase. -/
theorem acts_mcx {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k) (_hc : Inj k c)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) :
    Acts (mcx k c a t)
      (fun x => Function.update x t (xor (x t) (decide (∀ i < k, x (c i) = true)))) := by
  have hj : k - 3 < k - 2 := by omega
  have hat : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  have hbt : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  have hsa : ∀ i ≤ k - 3, t ≠ a i := fun i hi => hta i (by omega)
  have hsc : ∀ i < k - 3 + 2, t ≠ c i := fun i hi => htc i (by omega)
  unfold Acts mcx
  rw [circMat_append, circMat_mcxHalf hk ha hca htc hta, fmono_mul, permMat_eq_fmono]
  apply fmono_congr
  · intro x
    have e : pc c k x = (pc c (k - 3 + 2) x && x (c (k - 1))) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rfl
    simp only [Function.comp_apply]
    rw [wF_update c a (k - 3) t hsa hsc, wF_wF ha hca _ hj, Function.update_self,
      Function.update_of_ne hat, Function.update_of_ne hbt, wF_last,
      wF_ctrl hca _ hj (k - 1) (by omega), Function.update_idem, ← pc_eq_decide, e, mcx_bit]
  · intro x
    change wS c a (k - 3) (Function.update (wF c a (k - 3) x) t _) * wS c a (k - 3) x = 1
    rw [wS_update c a (k - 3) t hsa hsc, wS_wF ha hca _ hj, wS_sq]

/-! ### Counting -/

theorem cnots_wChain {k : ℕ} {c a : ℕ → Fin N} (ha : Inj (k - 2) a)
    (hca : Disj k c (k - 2) a) (j : ℕ) (hj : j < k - 2) :
    cnots (wChain c a j) = 3 + 4 * j := by
  induction j with
  | zero => exact cnots_marg (hca 0 (by omega) 0 hj) (hca 1 (by omega) 0 hj)
  | succ j ih =>
    have hu : a j ≠ a (j + 1) := fun h => by
      have := ha j (by omega) (j + 1) hj h
      omega
    have hv : c (j + 2) ≠ a (j + 1) := hca (j + 2) (by omega) (j + 1) hj
    rw [wChain, cnots_append, cnots_append, cnots_ryA hu hv, cnots_ryAinv hu hv, ih (by omega)]
    omega

theorem tr_wChain (c a : ℕ → Fin N) (j : ℕ) : TR (wChain c a j) (4 + 4 * j) 0 := by
  induction j with
  | zero => exact tr_marg _ _ _
  | succ j ih =>
    exact (tr_append (tr_append (tr_ryA _ _ _) ih) (tr_ryAinv _ _ _)).congr (by omega) rfl

theorem unitaryGates_wChain (c a : ℕ → Fin N) (j : ℕ) : UnitaryGates (wChain c a j) := by
  induction j with
  | zero => exact unitaryGates_marg _ _ _
  | succ j ih =>
    exact unitaryGates_append (unitaryGates_append (unitaryGates_ryA _ _ _) ih)
      (unitaryGates_ryAinv _ _ _)

theorem cnots_mcxHalf {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) : cnots (mcxHalf k c a t) = 4 * k - 3 := by
  have hj : k - 3 < k - 2 := by omega
  have hab : a (k - 3) ≠ c (k - 1) := (hca (k - 1) (by omega) (k - 3) hj).symm
  have hat : a (k - 3) ≠ t := (hta (k - 3) hj).symm
  have hbt : c (k - 1) ≠ t := (htc (k - 1) (by omega)).symm
  unfold mcxHalf
  rw [cnots_append, cnots_ccx hab hat hbt, cnots_wChain ha hca _ hj]
  omega

theorem cnots_mcx {k : ℕ} {c a : ℕ → Fin N} {t : Fin N} (hk : 3 ≤ k) (_hc : Inj k c)
    (ha : Inj (k - 2) a) (hca : Disj k c (k - 2) a) (htc : ∀ i < k, t ≠ c i)
    (hta : ∀ i < k - 2, t ≠ a i) : cnots (mcx k c a t) = 8 * k - 6 := by
  unfold mcx
  rw [cnots_append, cnots_mcxHalf hk ha hca htc hta]
  omega

theorem tr_mcxHalf (k : ℕ) (hk : 3 ≤ k) (c a : ℕ → Fin N) (t : Fin N) :
    TR (mcxHalf k c a t) (4 * k - 1) 0 :=
  (tr_append (tr_ccx _ _ _) (tr_wChain c a (k - 3))).congr (by omega) rfl

theorem tr_mcx (k : ℕ) (hk : 3 ≤ k) (c a : ℕ → Fin N) (t : Fin N) :
    TR (mcx k c a t) (8 * k - 2) 0 :=
  (tr_append (tr_mcxHalf k hk c a t) (tr_mcxHalf k hk c a t)).congr (by omega) rfl

theorem unitaryGates_mcx (k : ℕ) (c a : ℕ → Fin N) (t : Fin N) : UnitaryGates (mcx k c a t) :=
  unitaryGates_append
    (unitaryGates_append (unitaryGates_ccx _ _ _) (unitaryGates_wChain c a (k - 3)))
    (unitaryGates_append (unitaryGates_ccx _ _ _) (unitaryGates_wChain c a (k - 3)))

end Qulin
