/-
Three more cells on a line, each a permutation up to phases of modulus one.

* `rtof5 c1 c2 t` (5 CNOTs): the relative-phase Toffoli whose target `t` is at one end
  of three neighbouring wires; flips `t` iff `c1` and `c2` are both one.
* `fan2 c m t` (3 CNOTs): `m ^= c`, `t ^= c`; a permutation matrix.
* `jCell a b c` (4 CNOTs): the moving cell, `(xa, xb, xc) ↦ (xa, xc ⊕ (xa ∧ xb), xb)`.
-/
import Mathlib
import ApproxToffoli.Line.Commute

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### The end-target relative-phase Toffoli (5 CNOTs) -/

/-- The inner nine gates on the target, for control bits `a` (far) and `b` (near):
`1, X, X, -iZ` for `(a, b) = (0,0), (1,0), (0,1), (1,1)`. -/
theorem rtof5_mid (a b : Bool) :
    pGate (Real.pi / 4) * (if b then xGate else 1) * pGate (-Real.pi / 4)
        * (if xor b a then xGate else 1) * pGate (-Real.pi / 4) * (if b then xGate else 1)
        * pGate (Real.pi / 4)
      = if a then (if b then m2 (-Complex.I) 0 0 Complex.I else m2 0 1 1 0)
        else (if b then m2 0 1 1 0 else m2 1 0 0 1) := by
  cases a <;> cases b <;>
    simp only [↓reduceIte, Bool.false_eq_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, bne_self_eq_false, pGate_eq_m2, xGate_eq_m2, one_eq_m2, m2_mul,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, e_quarter_sq,
      e_neg_quarter_sq, e_quarter_mul_neg, e_neg_mul_quarter]

/-- The block of the whole cell: `1, Z, Z, -iX`. -/
def rtof5Block (a b : Bool) : Matrix Bool Bool ℂ :=
  if a then (if b then m2 0 (-Complex.I) (-Complex.I) 0 else m2 1 0 0 (-1))
  else (if b then m2 1 0 0 (-1) else m2 1 0 0 1)

theorem rtof5_block (a b : Bool) :
    hGate * (pGate (Real.pi / 4) * (if b then xGate else 1) * pGate (-Real.pi / 4)
        * (if xor b a then xGate else 1) * pGate (-Real.pi / 4) * (if b then xGate else 1)
        * pGate (Real.pi / 4)) * hGate
      = rtof5Block a b := by
  rw [rtof5_mid]
  cases a <;> cases b <;>
    simp only [↓reduceIte, Bool.false_eq_true, hGate_mul_mul, rtof5Block] <;>
    congr 1 <;> ring

/-- The end-target relative-phase Toffoli: controls `c1`, `c2`, target `t`, with `c2`
adjacent to both.  Eleven gates, five of them CNOTs. -/
noncomputable def rtof5 (c1 c2 t : Fin N)
    (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) : List (Gate N) :=
  [.one t hGate, .one t (pGate (Real.pi / 4)), .cx c2 t h2, .one t (pGate (-Real.pi / 4)),
   .cx c1 c2 h1, .cx c2 t h2, .one t (pGate (-Real.pi / 4)), .cx c1 c2 h1, .cx c2 t h2,
   .one t (pGate (Real.pi / 4)), .one t hGate]

theorem cnots_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) : cnots (rtof5 c1 c2 t h1 h2) = 5 := rfl

theorem unitaryGates_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) : UnitaryGates (rtof5 c1 c2 t h1 h2) := by
  unfold rtof5
  repeat first
    | exact unitaryGates_nil
    | apply unitaryGates_cons_cx
    | apply unitaryGates_cons_one _ hGate_unitary
    | apply unitaryGates_cons_one _ (pGate_unitary _)

/-- The four middle gates `cx c1 c2, cx c2 t, P, cx c1 c2`: a block on `t` controlled by
`c1 ⊕ c2`. -/
theorem rtof5_mid4 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (h13 : c1 ≠ t) (p : Matrix Bool Bool ℂ) :
    (Gate.cx c1 c2 h1).mat * (Gate.one t p).mat * (Gate.cx c2 t h2).mat * (Gate.cx c1 c2 h1).mat
      = ctrl2 c1 t c2 (fun a b => p * (if xor b a then xGate else 1)) := by
  have n12 : c1 ≠ c2 := adj_ne h1
  have n2t : c2 ≠ t := adj_ne h2
  have hf : ∀ (x : St N) (b : Bool),
      xor (Function.update x t b c2) (Function.update x t b c1) = xor (x c2) (x c1) := by
    intro x b
    rw [Function.update_of_ne n2t, Function.update_of_ne h13]
  rw [← one_mat_mul_cx_mat_comm t c1 c2 h1 h13.symm n2t.symm p, Matrix.mul_assoc,
    Matrix.mul_assoc]
  have hmid : (Gate.cx c1 c2 h1).mat * ((Gate.cx c2 t h2).mat * (Gate.cx c1 c2 h1).mat)
      = ctrlMat t (fun x => if xor (x c2) (x c1) then xGate else 1) := by
    simp only [Gate.mat]
    rw [mono_mul, mono_mul, ← mul_assoc, cx3_perm c1 c2 t n12 n2t h13 hf]
    simp only [mul_one]
    exact flip_eq_ctrlMat t _ hf
  rw [hmid]
  exact ctrlMat_mul t (fun _ => p) _ (fun _ _ => rfl)

theorem circMat_rtof5_ctrl2 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (h13 : c1 ≠ t) :
    circMat (rtof5 c1 c2 t h1 h2) = ctrl2 c1 t c2 rtof5Block := by
  have hre : circMat (rtof5 c1 c2 t h1 h2)
      = (Gate.one t hGate).mat * (Gate.one t (pGate (Real.pi / 4))).mat * (Gate.cx c2 t h2).mat
        * ((Gate.cx c1 c2 h1).mat * (Gate.one t (pGate (-Real.pi / 4))).mat
            * (Gate.cx c2 t h2).mat * (Gate.cx c1 c2 h1).mat)
        * (Gate.one t (pGate (-Real.pi / 4))).mat * (Gate.cx c2 t h2).mat
        * (Gate.one t (pGate (Real.pi / 4))).mat * (Gate.one t hGate).mat := by
    simp only [rtof5, circMat, one_mul, Matrix.mul_assoc]
  rw [hre, rtof5_mid4 c1 c2 t h1 h2 h13]
  simp only [one_eq_ctrl2 c1 t c2, cx_bot_eq_ctrl2 c1 t c2,
    ctrl2_mul c1 t c2 h13 (adj_ne h2)]
  congr 1
  funext a b
  rw [← rtof5_block a b]
  simp only [Matrix.mul_assoc]

/-- The phases of the end-target cell. -/
noncomputable def rtof5Phase (c1 c2 t : Fin N) (x : St N) : ℂ :=
  if x c1 then (if x c2 then -Complex.I else (if x t then -1 else 1))
  else (if x c2 then (if x t then -1 else 1) else 1)

theorem rtof5Phase_unit (c1 c2 t : Fin N) (x : St N) :
    star (rtof5Phase c1 c2 t x) * rtof5Phase c1 c2 t x = 1 := by
  unfold rtof5Phase
  cases x c1 <;> cases x c2 <;> cases x t <;> simp

/-- **The end-target relative-phase Toffoli is a Toffoli up to phases.**  Its matrix
sends the basis state `x` to `rtof5Phase x` times the basis state with bit `t` flipped
iff bits `c1` and `c2` are both one. -/
theorem circMat_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (h13 : c1 ≠ t) :
    circMat (rtof5 c1 c2 t h1 h2)
      = mono (ccPerm c1 t c2 h13 (adj_ne h2)) (rtof5Phase c1 c2 t) := by
  have hg : ∀ (x : St N) (a b : Bool), a ≠ xor b (x c1 && x c2) →
      rtof5Block (x c1) (x c2) a b = 0 := by
    intro x a b
    unfold rtof5Block
    cases x c1 <;> cases x c2 <;> cases a <;> cases b <;> simp [m2]
  rw [circMat_rtof5_ctrl2 c1 c2 t h1 h2 h13, ctrl2, ccPerm,
    ctrlMat_eq_mono t (fun x => x c1 && x c2) _ _ hg]
  · congr 1
    funext x
    unfold rtof5Phase rtof5Block
    cases x c1 <;> cases x c2 <;> cases x t <;> simp [m2]
  · intro x b
    change (Function.update x t b c1 && Function.update x t b c2) = (x c1 && x c2)
    rw [Function.update_of_ne h13, Function.update_of_ne (adj_ne h2)]

theorem umono_rtof5 (c1 c2 t : Fin N) (h1 : c1.val + 1 = c2.val ∨ c2.val + 1 = c1.val)
    (h2 : c2.val + 1 = t.val ∨ t.val + 1 = c2.val) (h13 : c1 ≠ t) :
    UMono (circMat (rtof5 c1 c2 t h1 h2)) (ccPerm c1 t c2 h13 (adj_ne h2)) :=
  ⟨rtof5Phase c1 c2 t, rtof5Phase_unit c1 c2 t, circMat_rtof5 c1 c2 t h1 h2 h13⟩

/-! ### The fan-out cell (3 CNOTs) -/

/-- `fan2 c m t`: three CNOTs on neighbouring wires `c, m, t` with basis action
`m ^= c`, `t ^= c`. -/
def fan2 (c m t : Fin N) (h1 : c.val + 1 = m.val ∨ m.val + 1 = c.val)
    (h2 : m.val + 1 = t.val ∨ t.val + 1 = m.val) : List (Gate N) :=
  [.cx m t h2, .cx c m h1, .cx m t h2]

/-- The basis permutation of `fan2`, as the product of its gates. -/
def fanPerm (c m t : Fin N) (hcm : c ≠ m) (hmt : m ≠ t) : Equiv.Perm (St N) :=
  cxPerm m t hmt * cxPerm c m hcm * cxPerm m t hmt

theorem cnots_fan2 (c m t : Fin N) (h1 : c.val + 1 = m.val ∨ m.val + 1 = c.val)
    (h2 : m.val + 1 = t.val ∨ t.val + 1 = m.val) : cnots (fan2 c m t h1 h2) = 3 := rfl

theorem unitaryGates_fan2 (c m t : Fin N) (h1 : c.val + 1 = m.val ∨ m.val + 1 = c.val)
    (h2 : m.val + 1 = t.val ∨ t.val + 1 = m.val) : UnitaryGates (fan2 c m t h1 h2) :=
  unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _
    (unitaryGates_cons_cx _ _ _ unitaryGates_nil))

/-- **`fan2` is a permutation matrix.** -/
theorem circMat_fan2 (c m t : Fin N) (h1 : c.val + 1 = m.val ∨ m.val + 1 = c.val)
    (h2 : m.val + 1 = t.val ∨ t.val + 1 = m.val) :
    circMat (fan2 c m t h1 h2) = mono (fanPerm c m t (adj_ne h1) (adj_ne h2)) (fun _ => 1) := by
  simp only [fan2, circMat, one_mul, Gate.mat]
  rw [mono_mul, mono_mul]
  simp only [mul_one]
  rfl

theorem umono_fan2 (c m t : Fin N) (h1 : c.val + 1 = m.val ∨ m.val + 1 = c.val)
    (h2 : m.val + 1 = t.val ∨ t.val + 1 = m.val) :
    UMono (circMat (fan2 c m t h1 h2)) (fanPerm c m t (adj_ne h1) (adj_ne h2)) :=
  ⟨fun _ => 1, fun _ => by simp, circMat_fan2 c m t h1 h2⟩

/-- **Basis action of `fan2`**: `m ^= c`, `t ^= c`, all other wires unchanged. -/
theorem fanPerm_apply (c m t : Fin N) (hcm : c ≠ m) (hmt : m ≠ t) (hct : c ≠ t) (x : St N) :
    fanPerm c m t hcm hmt x
      = Function.update (Function.update x m (xor (x m) (x c))) t (xor (x t) (x c)) := by
  have e : ∀ u v w : Bool, xor (xor u v) (xor v w) = xor u w := by decide
  funext r
  simp only [fanPerm, Equiv.Perm.mul_apply, cxPerm_apply]
  by_cases hr : r = t
  · rw [hr]
    simp only [Function.update_self, Function.update_of_ne hmt, Function.update_of_ne hct,
      Function.update_of_ne hmt.symm]
    exact e _ _ _
  · by_cases hr' : r = m
    · rw [hr']
      simp only [Function.update_self, Function.update_of_ne hmt, Function.update_of_ne hct,
        Function.update_of_ne hmt.symm]
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr']

/-! ### Real rotations -/

/-- The real rotation `R_y(φ)`. -/
noncomputable def ryGate (φ : ℝ) : Matrix Bool Bool ℂ :=
  m2 (Real.cos (φ / 2) : ℂ) (-(Real.sin (φ / 2) : ℂ)) (Real.sin (φ / 2) : ℂ)
    (Real.cos (φ / 2) : ℂ)

theorem ryGate_unitary (φ : ℝ) : ryGate φ ∈ Matrix.unitaryGroup Bool ℂ := by
  have hP : ((Real.cos (φ / 2) : ℝ) : ℂ) ^ 2 + ((Real.sin (φ / 2) : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (φ / 2)
  have hs : star (ryGate φ)
      = m2 (Real.cos (φ / 2) : ℂ) (Real.sin (φ / 2) : ℂ) (-(Real.sin (φ / 2) : ℂ))
          (Real.cos (φ / 2) : ℂ) := by
    rw [ryGate, star_m2]
    simp only [star_neg, Complex.star_def, Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff, hs, ryGate, m2_mul, one_eq_m2]
  congr 1
  · linear_combination hP
  · ring
  · ring
  · linear_combination hP

theorem ryGate_quarter : ryGate (Real.pi / 4) = rGate := by
  rw [ryGate, rGate, show Real.pi / 4 / 2 = Real.pi / 8 by ring]

/-- `R_y(3π/4)` in terms of `cos (π/8)` and `sin (π/8)`. -/
theorem ryGate_three_quarter :
    ryGate (3 * Real.pi / 4)
      = m2 (Real.sin (Real.pi / 8) : ℂ) (-(Real.cos (Real.pi / 8) : ℂ))
          (Real.cos (Real.pi / 8) : ℂ) (Real.sin (Real.pi / 8) : ℂ) := by
  rw [ryGate, show 3 * Real.pi / 4 / 2 = Real.pi / 2 - Real.pi / 8 by ring,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

/-- The number `1 / √2`. -/
noncomputable def rh : ℂ := 1 / ((Real.sqrt 2 : ℝ) : ℂ)

theorem rh_sq : rh * rh = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [rh, div_mul_div_comm, h2, one_mul]

theorem ry1_sq : ryGate (Real.pi / 4) * ryGate (Real.pi / 4) = m2 rh (-rh) rh rh := by
  have hC : _ = rh := cos_sq_sub_sin_sq_eighth
  have hS : _ = rh := two_sin_cos_eighth
  rw [ryGate_quarter, rGate, m2_mul]
  congr 1
  · linear_combination hC
  · linear_combination -hS
  · linear_combination hS
  · linear_combination hC

theorem ry3_sq :
    ryGate (3 * Real.pi / 4) * ryGate (3 * Real.pi / 4) = m2 (-rh) (-rh) rh (-rh) := by
  have hC : _ = rh := cos_sq_sub_sin_sq_eighth
  have hS : _ = rh := two_sin_cos_eighth
  rw [ryGate_three_quarter, m2_mul]
  congr 1
  · linear_combination -hC
  · linear_combination -hS
  · linear_combination hS
  · linear_combination -hC

theorem ry1_x : ryGate (Real.pi / 4) * xGate * ryGate (Real.pi / 4) = xGate := by
  have hP := cos_sq_add_sin_sq_eighth
  rw [ryGate_quarter, rGate, xGate_eq_m2, m2_mul, m2_mul]
  congr 1
  · ring
  · linear_combination hP
  · linear_combination hP
  · ring

theorem ry3_x : ryGate (3 * Real.pi / 4) * xGate * ryGate (3 * Real.pi / 4) = xGate := by
  have hP := cos_sq_add_sin_sq_eighth
  rw [ryGate_three_quarter, xGate_eq_m2, m2_mul, m2_mul]
  congr 1
  · ring
  · linear_combination hP
  · linear_combination hP
  · ring

/-- The block of the moving cell on the middle wire, for the bits `a` on wire `a` and
`c` on wire `c` (after the swap): `-1, 1, diag(-1, 1), X`. -/
def jBlock (a c : Bool) : Matrix Bool Bool ℂ :=
  if a then (if c then m2 0 1 1 0 else m2 (-1) 0 0 1)
  else (if c then m2 1 0 0 1 else m2 (-1) 0 0 (-1))

theorem j_block (a c : Bool) :
    ryGate (3 * Real.pi / 4) * (if c then xGate else 1) * ryGate (3 * Real.pi / 4)
        * (if a then xGate else 1)
        * ryGate (Real.pi / 4) * (if c then xGate else 1) * ryGate (Real.pi / 4)
      = jBlock a c := by
  have hh := rh_sq
  have hre : ryGate (3 * Real.pi / 4) * (if c then xGate else 1) * ryGate (3 * Real.pi / 4)
        * (if a then xGate else 1)
        * ryGate (Real.pi / 4) * (if c then xGate else 1) * ryGate (Real.pi / 4)
      = (ryGate (3 * Real.pi / 4) * (if c then xGate else 1) * ryGate (3 * Real.pi / 4))
        * (if a then xGate else 1)
        * (ryGate (Real.pi / 4) * (if c then xGate else 1) * ryGate (Real.pi / 4)) := by
    simp only [Matrix.mul_assoc]
  rw [hre]
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one, ry3_sq, ry1_sq]
    cases a <;>
      simp only [Bool.false_eq_true, ↓reduceIte, jBlock, xGate_eq_m2, one_eq_m2, m2_mul] <;>
      congr 1 <;>
      first
        | ring1
        | linear_combination (-2) * hh
        | linear_combination 2 * hh
  · simp only [↓reduceIte, ry3_x, ry1_x]
    cases a <;>
      simp only [Bool.false_eq_true, ↓reduceIte, jBlock, xGate_eq_m2, one_eq_m2, m2_mul] <;>
      congr 1 <;> ring1

/-! ### Swapping two wires -/

/-- Exchange the bits on wires `b` and `c`. -/
def swapFun (b c : Fin N) (x : St N) : St N := fun r => x (Equiv.swap b c r)

theorem swapFun_involutive (b c : Fin N) : Function.Involutive (swapFun b c) := by
  intro x
  funext r
  simp [swapFun]

/-- The basis permutation that exchanges the bits on wires `b` and `c`. -/
def swapPerm (b c : Fin N) : Equiv.Perm (St N) := (swapFun_involutive b c).toPerm _

theorem swapPerm_apply (b c : Fin N) (x : St N) (r : Fin N) :
    swapPerm b c x r = x (Equiv.swap b c r) := rfl

/-- `cx c b` then `cx b c` is the swap of `b` and `c` followed by `cx c b`. -/
theorem cxPerm_mul_cxPerm_swap (b c : Fin N) (hbc : b ≠ c) :
    cxPerm b c hbc * cxPerm c b hbc.symm = cxPerm c b hbc.symm * swapPerm b c := by
  have e : ∀ u v : Bool, xor v (xor u v) = u := by decide
  apply Equiv.ext
  intro x
  funext r
  simp only [Equiv.Perm.mul_apply, cxPerm_apply]
  by_cases hr : r = c
  · rw [hr]
    simp only [Function.update_self, Function.update_of_ne hbc.symm, swapPerm_apply,
      Equiv.swap_apply_right]
    exact e _ _
  · by_cases hr' : r = b
    · rw [hr']
      simp only [Function.update_self, Function.update_of_ne hbc, swapPerm_apply,
        Equiv.swap_apply_right, Equiv.swap_apply_left]
      exact Bool.xor_comm _ _
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr', swapPerm_apply,
        Equiv.swap_apply_of_ne_of_ne hr' hr]

/-- A one-qubit gate on `c` followed by the swap is the swap followed by the same gate
on `b`. -/
theorem swap_mul_oneMat (b c : Fin N) (g : Matrix Bool Bool ℂ) :
    mono (swapPerm b c) (fun _ => (1 : ℂ)) * oneMat c g
      = oneMat b g * mono (swapPerm b c) (fun _ => (1 : ℂ)) := by
  ext y x
  rw [mul_mono_apply, mono_mul_apply', mul_one, one_mul]
  have hs : (swapPerm b c).symm y = swapPerm b c y := rfl
  rw [hs]
  simp only [oneMat, of_apply, swapPerm_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have key : (∀ r, r ≠ c → y (Equiv.swap b c r) = x r)
      ↔ (∀ r, r ≠ b → y r = x (Equiv.swap b c r)) := by
    constructor
    · intro H r hr
      have h1 : Equiv.swap b c r ≠ c := by
        intro h
        apply hr
        have := congrArg (Equiv.swap b c) h
        simpa using this
      have := H _ h1
      rwa [Equiv.swap_apply_self] at this
    · intro H r hr
      have h1 : Equiv.swap b c r ≠ b := by
        intro h
        apply hr
        have := congrArg (Equiv.swap b c) h
        simpa using this
      have := H _ h1
      rwa [Equiv.swap_apply_self] at this
  by_cases hA : ∀ r, r ≠ c → y (Equiv.swap b c r) = x r
  · rw [if_pos hA, if_pos (key.1 hA)]
  · rw [if_neg hA, if_neg (fun H => hA (key.2 H))]

theorem umono_swap (b c : Fin N) :
    UMono (mono (swapPerm b c) (fun _ => (1 : ℂ))) (swapPerm b c) :=
  ⟨fun _ => 1, fun _ => by simp, rfl⟩

/-! ### The moving cell (4 CNOTs) -/

/-- The first five gates of the moving cell on wires `a, b, c` (`b` in the middle). -/
noncomputable def jHalf (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : List (Gate N) :=
  [.one c (ryGate (Real.pi / 4)), .cx c b h2, .cx b c h2.symm,
   .one b (ryGate (Real.pi / 4)), .cx a b h1]

/-- The last three gates of the moving cell; they touch only wires `b` and `c`. -/
noncomputable def jTail (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    List (Gate N) :=
  [.one b (ryGate (3 * Real.pi / 4)), .cx c b h2, .one b (ryGate (3 * Real.pi / 4))]

/-- The moving cell. -/
noncomputable def jCell (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : List (Gate N) :=
  jHalf a b c h1 h2 ++ jTail b c h2

theorem cnots_jHalf (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : cnots (jHalf a b c h1 h2) = 3 := rfl

theorem cnots_jTail (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    cnots (jTail b c h2) = 1 := rfl

theorem cnots_jCell (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : cnots (jCell a b c h1 h2) = 4 := rfl

theorem unitaryGates_jHalf (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : UnitaryGates (jHalf a b c h1 h2) :=
  unitaryGates_cons_one _ (ryGate_unitary _) (unitaryGates_cons_cx _ _ _
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_one _ (ryGate_unitary _)
      (unitaryGates_cons_cx _ _ _ unitaryGates_nil))))

theorem unitaryGates_jTail (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    UnitaryGates (jTail b c h2) :=
  unitaryGates_cons_one _ (ryGate_unitary _) (unitaryGates_cons_cx _ _ _
    (unitaryGates_cons_one _ (ryGate_unitary _) unitaryGates_nil))

theorem unitaryGates_jCell (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) : UnitaryGates (jCell a b c h1 h2) :=
  unitaryGates_append (unitaryGates_jHalf a b c h1 h2) (unitaryGates_jTail b c h2)

/-- Every gate of `jTail b c` touches only the wires `b` and `c`. -/
theorem circOn_jTail (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    CircOn (fun r => r = b ∨ r = c) (jTail b c h2) := by
  intro g hg
  simp only [jTail, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact ⟨Or.inr rfl, Or.inl rfl⟩
  · exact Or.inl rfl

/-- `jTail b c` on any set of wires that contains `b` and `c`. -/
theorem circOn_jTail' (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val)
    (P : Fin N → Prop) (hb : P b) (hc : P c) : CircOn P (jTail b c h2) :=
  (circOn_jTail b c h2).mono (fun r hr => by rcases hr with rfl | rfl <;> assumption)

/-- Every gate of `jHalf a b c` touches only the wires `a`, `b` and `c`. -/
theorem circOn_jHalf (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) (P : Fin N → Prop) (ha : P a) (hb : P b)
    (hc : P c) : CircOn P (jHalf a b c h1 h2) := by
  intro g hg
  simp only [jHalf, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact hc
  · exact ⟨hc, hb⟩
  · exact ⟨hb, hc⟩
  · exact hb
  · exact ⟨ha, hb⟩

/-- A gate on `c`, then `cx c b`, then `cx b c`: the swap of `b` and `c`, then the same
gate on `b`, then `cx c b`. -/
theorem jHead (b c : Fin N) (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val)
    (g : Matrix Bool Bool ℂ) :
    (Gate.cx b c h2.symm).mat * ((Gate.cx c b h2).mat * (Gate.one c g).mat)
      = (Gate.cx c b h2).mat
        * ((Gate.one b g).mat * mono (swapPerm b c) (fun _ => (1 : ℂ))) := by
  have hbc : b ≠ c := (adj_ne h2).symm
  have h : (Gate.cx b c h2.symm).mat * (Gate.cx c b h2).mat
      = (Gate.cx c b h2).mat * mono (swapPerm b c) (fun _ => (1 : ℂ)) := by
    simp only [Gate.mat]
    rw [mono_mul, mono_mul, cxPerm_mul_cxPerm_swap b c hbc]
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
  congr 1
  exact swap_mul_oneMat b c g

/-- The moving cell is the swap of `b` and `c` followed by a block on `b` controlled
classically by `a` and `c`. -/
theorem circMat_jCell_eq (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    circMat (jCell a b c h1 h2)
      = ctrl2 a b c jBlock * mono (swapPerm b c) (fun _ => (1 : ℂ)) := by
  have hre : circMat (jCell a b c h1 h2)
      = (Gate.one b (ryGate (3 * Real.pi / 4))).mat * ((Gate.cx c b h2).mat
        * ((Gate.one b (ryGate (3 * Real.pi / 4))).mat * ((Gate.cx a b h1).mat
        * ((Gate.one b (ryGate (Real.pi / 4))).mat * ((Gate.cx b c h2.symm).mat
        * ((Gate.cx c b h2).mat * (Gate.one c (ryGate (Real.pi / 4))).mat)))))) := by
    simp only [jCell, jHalf, jTail, List.cons_append, List.nil_append, circMat, one_mul,
      Matrix.mul_assoc]
  rw [hre, jHead]
  simp only [← Matrix.mul_assoc]
  simp only [one_eq_ctrl2 a b c, cx_top_eq_ctrl2 a b c, cx_bot_eq_ctrl2 a b c,
    ctrl2_mul a b c (adj_ne h1) (adj_ne h2)]
  congr 2
  funext t b'
  exact j_block t b'

/-- The phases of the block part of the moving cell. -/
noncomputable def jPhase (a b c : Fin N) (x : St N) : ℂ :=
  if x a then (if x c then 1 else (if x b then 1 else -1)) else (if x c then 1 else -1)

theorem jPhase_unit (a b c : Fin N) (x : St N) :
    star (jPhase a b c x) * jPhase a b c x = 1 := by
  unfold jPhase
  cases x a <;> cases x c <;> cases x b <;> simp

theorem ctrl2_jBlock (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) :
    ctrl2 a b c jBlock = mono (ccPerm a b c hab hcb) (jPhase a b c) := by
  have hg : ∀ (x : St N) (p q : Bool), p ≠ xor q (x a && x c) →
      jBlock (x a) (x c) p q = 0 := by
    intro x p q
    unfold jBlock
    cases x a <;> cases x c <;> cases p <;> cases q <;> simp [m2]
  rw [ctrl2, ccPerm, ctrlMat_eq_mono b (fun x => x a && x c) _ _ hg]
  · congr 1
    funext x
    unfold jPhase jBlock
    cases x a <;> cases x c <;> cases x b <;> simp [m2]
  · intro x p
    change (Function.update x b p a && Function.update x b p c) = (x a && x c)
    rw [Function.update_of_ne hab, Function.update_of_ne hcb]

/-- The basis permutation of the moving cell: swap `b` and `c`, then flip `b` iff `a`
and `c` are both one. -/
def jPerm (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) : Equiv.Perm (St N) :=
  ccPerm a b c hab hcb * swapPerm b c

/-- **The moving cell is a permutation up to phases.** -/
theorem umono_jCell (a b c : Fin N) (h1 : a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (h2 : c.val + 1 = b.val ∨ b.val + 1 = c.val) :
    UMono (circMat (jCell a b c h1 h2)) (jPerm a b c (adj_ne h1) (adj_ne h2)) := by
  rw [circMat_jCell_eq, ctrl2_jBlock a b c (adj_ne h1) (adj_ne h2)]
  exact UMono.mul ⟨jPhase a b c, jPhase_unit a b c, rfl⟩ (umono_swap b c)

/-- **Basis action of the moving cell**: the bits `(xa, xb, xc)` on wires `(a, b, c)`
become `(xa, xc ⊕ (xa ∧ xb), xb)`; all other wires are unchanged. -/
theorem jPerm_apply (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) (x : St N) :
    jPerm a b c hab hcb x = upd3 a b c x (x a) (xor (x c) (x a && x b)) (x b) := by
  funext r
  simp only [jPerm, Equiv.Perm.mul_apply, ccPerm_apply, upd3]
  by_cases hr : r = c
  · rw [hr]
    simp only [Function.update_self, Function.update_of_ne hcb, swapPerm_apply,
      Equiv.swap_apply_right]
  · by_cases hr' : r = b
    · rw [hr']
      simp only [Function.update_self, Function.update_of_ne hcb.symm, swapPerm_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hab hac]
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr', swapPerm_apply,
        Equiv.swap_apply_of_ne_of_ne hr' hr, Function.update_eq_self]

/-- The moving cell on basis states, wire by wire. -/
theorem jPerm_wire (a b c : Fin N) (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) (x : St N)
    (j : ℕ) :
    wire (jPerm a b c hab hcb x) j
      = if j = c.val then x b else if j = b.val then xor (x c) (x a && x b)
        else wire x j := by
  rw [jPerm_apply a b c hab hcb hac, wire_upd3]
  by_cases h1 : j = c.val
  · rw [if_pos h1, if_pos h1]
  · by_cases h2 : j = b.val
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      by_cases h3 : j = a.val
      · rw [if_pos h3, h3, wire_val]
      · rw [if_neg h3]

end Line
