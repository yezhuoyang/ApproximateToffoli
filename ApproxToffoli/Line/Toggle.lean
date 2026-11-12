/-
The long relative-phase toggle on a line.

On wires `0 .. 2a-1` (with `a ≥ 2`) the circuit

    mark a = CH ++ steps ++ base ++ invCirc steps ++ CH

flips wire `0` exactly when all odd wires `1, 3, …, 2a-1` hold a one, up to phases of
modulus one.  It has `8a - 9` CNOTs.

* `steps` sweeps up the line: step `s` is the CNOT `cx s (s+1)` for even `s` and the
  relative-phase Toffoli cell `rccx (s+2) (s+1) s` for odd `s`.
* `base` is a controlled-Z between wires `2a-1` and `2a-2`, conjugated by `cx (2a-3) (2a-2)`.
* `CH` is a controlled Hadamard from wire `1` onto wire `0` with one CNOT.
-/
import Mathlib
import ApproxToffoli.Line.Inverse

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Small helpers -/

theorem mono_mul_unit {ι : Type*} [Fintype ι] [DecidableEq ι] (σ τ : Equiv.Perm ι)
    (φ ψ : ι → ℂ) (hφ : ∀ x, star (φ x) * φ x = 1) (hψ : ∀ x, star (ψ x) * ψ x = 1) :
    ∃ χ : ι → ℂ, (∀ x, star (χ x) * χ x = 1) ∧ mono σ φ * mono τ ψ = mono (σ * τ) χ := by
  refine ⟨fun j => φ (τ j) * ψ j, fun x => ?_, mono_mul σ τ φ ψ⟩
  show star (φ (τ x) * ψ x) * (φ (τ x) * ψ x) = 1
  rw [star_mul', mul_mul_mul_comm, hφ, hψ, one_mul]

theorem fin_ne {i j : ℕ} (hi : i < N) (hj : j < N) (h : i ≠ j) :
    (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun hh => h (congrArg Fin.val hh)

/-! ### The sweep: gates, basis permutation -/

/-- The classical control of step `s`: wire `s` for even `s`, wires `s + 2` and `s`
for odd `s`. -/
def stepCtl (s : ℕ) (h : s + 2 < N) (x : St N) : Bool :=
  if s % 2 = 0 then x ⟨s, by omega⟩ else (x ⟨s + 2, h⟩ && x ⟨s, by omega⟩)

theorem stepCtl_update (s : ℕ) (h : s + 2 < N) (x : St N) (b : Bool) :
    stepCtl s h (Function.update x ⟨s + 1, by omega⟩ b) = stepCtl s h x := by
  have h0 : (⟨s, by omega⟩ : Fin N) ≠ ⟨s + 1, by omega⟩ := fin_ne _ _ (by omega)
  have h2 : (⟨s + 2, h⟩ : Fin N) ≠ ⟨s + 1, by omega⟩ := fin_ne _ _ (by omega)
  unfold stepCtl
  rw [Function.update_of_ne h0, Function.update_of_ne h2]

/-- The basis permutation of step `s`: flip wire `s + 1` iff the control holds. -/
def stepPerm (N s : ℕ) : Equiv.Perm (St N) :=
  if h : s + 2 < N then flipPerm ⟨s + 1, by omega⟩ (stepCtl s h) (stepCtl_update s h) else 1

theorem stepPerm_apply (s : ℕ) (h : s + 2 < N) (x : St N) :
    stepPerm N s x
      = Function.update x ⟨s + 1, by omega⟩ (xor (x ⟨s + 1, by omega⟩) (stepCtl s h x)) := by
  rw [stepPerm, dif_pos h]
  rfl

/-- The gates of step `s`: the CNOT `cx s (s+1)` for even `s`, the relative-phase
Toffoli cell `rccx (s+2) (s+1) s` for odd `s`. -/
noncomputable def stepGate (N s : ℕ) : List (Gate N) :=
  if h : s + 2 < N then
    if s % 2 = 0 then [Gate.cx ⟨s, by omega⟩ ⟨s + 1, by omega⟩ (Or.inl rfl)]
    else rccx ⟨s + 2, h⟩ ⟨s + 1, by omega⟩ ⟨s, by omega⟩ (Or.inr rfl) (Or.inl rfl)
  else []

theorem circMat_stepGate (N s : ℕ) :
    ∃ ψ : St N → ℂ, (∀ x, star (ψ x) * ψ x = 1) ∧
      circMat (stepGate N s) = mono (stepPerm N s) ψ := by
  by_cases h : s + 2 < N
  · by_cases hs : s % 2 = 0
    · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
      rw [stepGate, dif_pos h, if_pos hs, stepPerm, dif_pos h]
      simp only [circMat, one_mul, Gate.mat]
      congr 1
      apply Equiv.ext
      intro x
      rw [cxPerm_apply, flipPerm_apply, stepCtl, if_pos hs]
    · refine ⟨rccxPhase ⟨s + 2, h⟩ ⟨s + 1, by omega⟩ ⟨s, by omega⟩, rccxPhase_unit _ _ _, ?_⟩
      rw [stepGate, dif_pos h, if_neg hs, stepPerm, dif_pos h, circMat_rccx]
      congr 1
      apply Equiv.ext
      intro x
      rw [ccPerm_apply, flipPerm_apply, stepCtl, if_neg hs]
  · refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    rw [stepGate, dif_neg h, stepPerm, dif_neg h, circMat, mono_one]

theorem cnots_stepGate (s : ℕ) (h : s + 2 < N) :
    cnots (stepGate N s) = if s % 2 = 0 then 1 else 3 := by
  rw [stepGate, dif_pos h]
  split_ifs
  · rfl
  · exact cnots_rccx _ _ _ _ _

theorem unitaryGates_stepGate (N s : ℕ) : UnitaryGates (stepGate N s) := by
  unfold stepGate
  split_ifs
  · exact unitaryGates_cons_cx _ _ _ unitaryGates_nil
  · exact unitaryGates_rccx _ _ _ _ _
  · exact unitaryGates_nil

/-- The first `n` steps of the sweep (steps `0, 1, …, n - 1`, in this order). -/
noncomputable def steps (N : ℕ) : ℕ → List (Gate N)
  | 0 => []
  | n + 1 => steps N n ++ stepGate N n

/-- The basis permutation of the first `n` steps. -/
def sweepPerm (N : ℕ) : ℕ → Equiv.Perm (St N)
  | 0 => 1
  | n + 1 => stepPerm N n * sweepPerm N n

theorem steps_succ (N n : ℕ) : steps N (n + 1) = steps N n ++ stepGate N n := rfl

theorem sweepPerm_succ_apply (n : ℕ) (x : St N) :
    sweepPerm N (n + 1) x = stepPerm N n (sweepPerm N n x) := rfl

/-- The sweep is a permutation up to phases of modulus one. -/
theorem circMat_steps (N n : ℕ) :
    ∃ ψ : St N → ℂ, (∀ x, star (ψ x) * ψ x = 1) ∧
      circMat (steps N n) = mono (sweepPerm N n) ψ := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
    show (1 : Matrix (St N) (St N) ℂ) = mono 1 (fun _ => 1)
    rw [mono_one]
  | succ n ih =>
    obtain ⟨ψ, hψ, h⟩ := ih
    obtain ⟨χ, hχ, h'⟩ := circMat_stepGate N n
    obtain ⟨ω, hω, h''⟩ := mono_mul_unit (stepPerm N n) (sweepPerm N n) χ ψ hχ hψ
    refine ⟨ω, hω, ?_⟩
    rw [steps_succ, circMat_append, h, h', h'']
    rfl

theorem cnots_steps (n : ℕ) (h : n + 1 < N) :
    cnots (steps N n) = (n + 1) / 2 + 3 * (n / 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [steps_succ, cnots_append, ih (by omega), cnots_stepGate n (by omega)]
    split_ifs <;> omega

theorem unitaryGates_steps (N n : ℕ) : UnitaryGates (steps N n) := by
  induction n with
  | zero => exact unitaryGates_nil
  | succ n ih => exact unitaryGates_append ih (unitaryGates_stepGate N n)

/-! ### The sweep on basis states -/

/-- The first `n` steps touch only wires `1 .. n`. -/
theorem sweepPerm_untouched (n : ℕ) (h : n + 1 < N) (x : St N) (r : Fin N) (hr : n < r.val) :
    sweepPerm N n x r = x r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sweepPerm_succ_apply, stepPerm_apply n h, Function.update_of_ne]
    · exact ih (by omega) (by omega)
    · intro hh
      have h1 : r.val = n + 1 := congrArg Fin.val hh
      omega

/-- The recursion for the last wire reached by the sweep. -/
theorem sweepPerm_succ_top (n : ℕ) (h : n + 2 < N) (x : St N) :
    sweepPerm N (n + 1) x ⟨n + 1, by omega⟩
      = xor (x ⟨n + 1, by omega⟩)
          (if n % 2 = 0 then sweepPerm N n x ⟨n, by omega⟩
           else (x ⟨n + 2, h⟩ && sweepPerm N n x ⟨n, by omega⟩)) := by
  rw [sweepPerm_succ_apply, stepPerm_apply n h, Function.update_self, stepCtl,
    sweepPerm_untouched n (by omega) x ⟨n + 1, by omega⟩ (Nat.lt_succ_self n),
    sweepPerm_untouched n (by omega) x ⟨n + 2, h⟩ (by show n < n + 2; omega)]

/-- All odd wires `r` with `3 ≤ r ≤ n + 1` hold a one. -/
def oddAll (n : ℕ) (x : St N) : Bool :=
  decide (∀ r : Fin N, 3 ≤ r.val → r.val ≤ n + 1 → r.val % 2 = 1 → x r = true)

theorem oddAll_zero (x : St N) : oddAll 0 x = true := by
  simp only [oddAll, decide_eq_true_eq]
  intro r h1 h2
  omega

theorem oddAll_succ_even (n : ℕ) (hn : n % 2 = 0) (x : St N) :
    oddAll (n + 1) x = oddAll n x := by
  unfold oddAll
  rw [decide_eq_decide]
  constructor
  · intro H r h1 h2 h3
    exact H r h1 (by omega) h3
  · intro H r h1 h2 h3
    exact H r h1 (by omega) h3

theorem oddAll_succ_odd (n : ℕ) (hn : n % 2 = 1) (h : n + 2 < N) (x : St N) :
    oddAll (n + 1) x = (x ⟨n + 2, h⟩ && oddAll n x) := by
  rw [Bool.eq_iff_iff]
  simp only [oddAll, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro H
    refine ⟨H ⟨n + 2, h⟩ ?_ ?_ ?_, fun r h1 h2 h3 => H r h1 (by omega) h3⟩
    · show 3 ≤ n + 2
      omega
    · show n + 2 ≤ n + 1 + 1
      omega
    · show (n + 2) % 2 = 1
      omega
  · rintro ⟨H1, H2⟩ r h1 h2 h3
    by_cases hr : r.val = n + 2
    · have hr' : r = ⟨n + 2, h⟩ := Fin.ext hr
      rw [hr']
      exact H1
    · exact H2 r h1 (by omega) h3

theorem oddAll_update (n : ℕ) (h0 : 0 < N) (x : St N) (b : Bool) :
    oddAll n (Function.update x ⟨0, h0⟩ b) = oddAll n x := by
  have key : ∀ r : Fin N, 3 ≤ r.val → Function.update x ⟨0, h0⟩ b r = x r := by
    intro r hr
    apply Function.update_of_ne
    intro hh
    have h1 : r.val = 0 := congrArg Fin.val hh
    omega
  unfold oddAll
  rw [decide_eq_decide]
  constructor
  · intro H r h1 h2 h3
    rw [← key r h1]
    exact H r h1 h2 h3
  · intro H r h1 h2 h3
    rw [key r h1]
    exact H r h1 h2 h3

theorem bool_step_even (a P d : Bool) : xor a (xor P d) = xor (xor a P) d := by
  cases a <;> cases P <;> cases d <;> rfl

theorem bool_step_odd (a c P b G : Bool) :
    xor a (c && xor P (b && G)) = xor (xor a (c && P)) (b && (c && G)) := by
  cases a <;> cases c <;> cases P <;> cases b <;> cases G <;> rfl

/-- **The invariant of the sweep.**  The last wire reached by the first `n` steps
depends on bit `0` only through `x 0 ∧ x 3 ∧ x 5 ∧ …` (odd wires up to `n + 1`). -/
theorem sweep_invariant (n : ℕ) (h : n + 1 < N) (x : St N) :
    sweepPerm N n x ⟨n, by omega⟩
      = xor (sweepPerm N n (Function.update x ⟨0, by omega⟩ false) ⟨n, by omega⟩)
          (x ⟨0, by omega⟩ && oddAll n x) := by
  induction n with
  | zero => simp [sweepPerm, oddAll_zero]
  | succ n ih =>
    have h0 : 0 < N := by omega
    have e1 : Function.update x ⟨0, h0⟩ false ⟨n + 1, by omega⟩ = x ⟨n + 1, by omega⟩ :=
      Function.update_of_ne (fin_ne _ _ (by omega)) _ _
    have e2 : Function.update x ⟨0, h0⟩ false ⟨n + 2, h⟩ = x ⟨n + 2, h⟩ :=
      Function.update_of_ne (fin_ne _ _ (by omega)) _ _
    rw [sweepPerm_succ_top n h, sweepPerm_succ_top n h, e1, e2, ih (by omega)]
    by_cases hn : n % 2 = 0
    · rw [if_pos hn, if_pos hn, oddAll_succ_even n hn]
      exact bool_step_even _ _ _
    · rw [if_neg hn, if_neg hn, oddAll_succ_odd n (by omega) h]
      exact bool_step_odd _ _ _ _ _

/-! ### The base: a controlled sign on three wires -/

theorem diagonal_eq_m2 (d : Bool → ℂ) : Matrix.diagonal d = m2 (d false) 0 0 (d true) := by
  ext i j
  cases i <;> cases j <;> simp [m2]

theorem hGate_x_hGate (p : Bool) :
    hGate * (if p then xGate else 1) * hGate
      = Matrix.diagonal (fun b => if p && b then (-1 : ℂ) else 1) := by
  rw [diagonal_eq_m2]
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, one_eq_m2, hGate_mul_mul]
    congr 1 <;> norm_num
  · simp only [↓reduceIte, Bool.true_and, xGate_eq_m2, hGate_mul_mul]
    congr 1 <;> norm_num

/-- A conditional flip is a controlled NOT block. -/
theorem flip_eq_ctrlMat (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) :
    mono (flipPerm q f hf) (fun _ => (1 : ℂ)) = ctrlMat q (fun x => if f x then xGate else 1) := by
  rw [ctrlMat_eq_mono q f hf]
  · congr 1
    funext x
    cases hc : f x <;> cases hq : x q <;> simp [xGate, Matrix.one_apply]
  · intro x a b hab
    cases hc : f x <;> cases a <;> cases b <;> simp_all [xGate]

theorem cx3_perm (q3 q2 q1 : Fin N) (h32 : q3 ≠ q2) (h21 : q2 ≠ q1) (h31 : q3 ≠ q1)
    (hf : ∀ (x : St N) (b : Bool),
      xor (Function.update x q1 b q2) (Function.update x q1 b q3) = xor (x q2) (x q3)) :
    cxPerm q3 q2 h32 * cxPerm q2 q1 h21 * cxPerm q3 q2 h32
      = flipPerm q1 (fun x => xor (x q2) (x q3)) hf := by
  apply Equiv.ext
  intro x
  funext r
  simp only [Equiv.Perm.mul_apply, cxPerm_apply, flipPerm_apply]
  by_cases hr1 : r = q1
  · rw [hr1]
    simp [h32, h21, h31, h21.symm]
  · by_cases hr2 : r = q2
    · rw [hr2]
      simp [h32, h21, h31, h21.symm]
    · simp [Function.update_apply, hr1, hr2]

/-- The base circuit on three neighbouring wires `q3, q2, q1`. -/
noncomputable def baseCirc (q3 q2 q1 : Fin N) (h32 : q3.val + 1 = q2.val)
    (h21 : q2.val + 1 = q1.val) : List (Gate N) :=
  [.one q1 hGate, .cx q3 q2 (Or.inl h32), .cx q2 q1 (Or.inl h21), .cx q3 q2 (Or.inl h32),
   .one q1 hGate]

theorem cnots_baseCirc (q3 q2 q1 : Fin N) (h32 : q3.val + 1 = q2.val)
    (h21 : q2.val + 1 = q1.val) : cnots (baseCirc q3 q2 q1 h32 h21) = 3 := rfl

theorem unitaryGates_baseCirc (q3 q2 q1 : Fin N) (h32 : q3.val + 1 = q2.val)
    (h21 : q2.val + 1 = q1.val) : UnitaryGates (baseCirc q3 q2 q1 h32 h21) :=
  unitaryGates_cons_one _ hGate_unitary (unitaryGates_cons_cx _ _ _
    (unitaryGates_cons_cx _ _ _ (unitaryGates_cons_cx _ _ _
      (unitaryGates_cons_one _ hGate_unitary unitaryGates_nil))))

/-- The base is the diagonal sign `(-1)^{x q1 ∧ (x q2 ⊕ x q3)}`. -/
theorem circMat_baseCirc (q3 q2 q1 : Fin N) (h32 : q3.val + 1 = q2.val)
    (h21 : q2.val + 1 = q1.val) :
    circMat (baseCirc q3 q2 q1 h32 h21)
      = Matrix.diagonal (fun x => if (xor (x q2) (x q3)) && x q1 then (-1 : ℂ) else 1) := by
  have n32 : q3 ≠ q2 := adj_ne (Or.inl h32)
  have n21 : q2 ≠ q1 := adj_ne (Or.inl h21)
  have n31 : q3 ≠ q1 := by
    intro hh
    rw [hh] at h32
    omega
  have hf : ∀ (x : St N) (b : Bool),
      xor (Function.update x q1 b q2) (Function.update x q1 b q3) = xor (x q2) (x q3) := by
    intro x b
    rw [Function.update_of_ne n21, Function.update_of_ne n31]
  have hmid : (Gate.cx q3 q2 (Or.inl h32)).mat * (Gate.cx q2 q1 (Or.inl h21)).mat
        * (Gate.cx q3 q2 (Or.inl h32)).mat
      = ctrlMat q1 (fun x => if xor (x q2) (x q3) then xGate else 1) := by
    simp only [Gate.mat]
    rw [mono_mul, mono_mul, cx3_perm q3 q2 q1 n32 n21 n31 hf]
    simp only [mul_one]
    exact flip_eq_ctrlMat q1 _ hf
  have hre : circMat (baseCirc q3 q2 q1 h32 h21)
      = (Gate.one q1 hGate).mat * ((Gate.cx q3 q2 (Or.inl h32)).mat
          * (Gate.cx q2 q1 (Or.inl h21)).mat * (Gate.cx q3 q2 (Or.inl h32)).mat)
        * (Gate.one q1 hGate).mat := by
    simp only [baseCirc, circMat, one_mul, Matrix.mul_assoc]
  have hg : ∀ (x : St N) (b : Bool),
      hGate * (if xor (Function.update x q1 b q2) (Function.update x q1 b q3) then xGate else 1)
        = hGate * (if xor (x q2) (x q3) then xGate else 1) := by
    intro x b
    rw [hf]
  rw [hre, hmid]
  change ctrlMat q1 (fun _ => hGate) * ctrlMat q1 _ * ctrlMat q1 (fun _ => hGate) = _
  rw [ctrlMat_mul q1 (fun _ => hGate) _ (fun _ _ => rfl),
    ctrlMat_mul q1 (fun x => hGate * (if xor (x q2) (x q3) then xGate else 1)) _ hg]
  have hb : (fun x : St N => hGate * (if xor (x q2) (x q3) then xGate else 1) * hGate)
      = fun x => Matrix.diagonal (fun b => if xor (x q2) (x q3) && b then (-1 : ℂ) else 1) :=
    funext fun x => hGate_x_hGate _
  rw [hb, ctrlMat_diagonal, mono_one_eq_diagonal]

/-! ### The controlled Hadamard with one CNOT -/

/-- The real rotation by `π/8`. -/
noncomputable def rGate : Matrix Bool Bool ℂ :=
  m2 (Real.cos (Real.pi / 8) : ℂ) (-(Real.sin (Real.pi / 8) : ℂ))
    (Real.sin (Real.pi / 8) : ℂ) (Real.cos (Real.pi / 8) : ℂ)

theorem transpose_m2 (a b c d : ℂ) : (m2 a b c d)ᵀ = m2 a c b d := by
  ext i j
  cases i <;> cases j <;> simp [m2, Matrix.transpose_apply]

theorem rGate_transpose :
    rGateᵀ = m2 (Real.cos (Real.pi / 8) : ℂ) (Real.sin (Real.pi / 8) : ℂ)
      (-(Real.sin (Real.pi / 8) : ℂ)) (Real.cos (Real.pi / 8) : ℂ) := by
  rw [rGate, transpose_m2]

theorem cos_sq_add_sin_sq_eighth :
    ((Real.cos (Real.pi / 8) : ℝ) : ℂ) ^ 2 + ((Real.sin (Real.pi / 8) : ℝ) : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq (Real.pi / 8)

theorem inv_sqrt_two : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  rw [div_eq_div_iff (Real.sqrt_ne_zero'.2 (by norm_num)) (by norm_num),
    Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem cos_sq_sub_sin_sq_eighth :
    ((Real.cos (Real.pi / 8) : ℝ) : ℂ) ^ 2 - ((Real.sin (Real.pi / 8) : ℝ) : ℂ) ^ 2
      = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h1 := Real.cos_two_mul (Real.pi / 8)
  have h2 := Real.sin_sq_add_cos_sq (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h1
  have h3 : Real.cos (Real.pi / 8) ^ 2 - Real.sin (Real.pi / 8) ^ 2 = 1 / Real.sqrt 2 := by
    rw [inv_sqrt_two]
    linarith
  exact_mod_cast h3

theorem two_sin_cos_eighth :
    2 * ((Real.sin (Real.pi / 8) : ℝ) : ℂ) * ((Real.cos (Real.pi / 8) : ℝ) : ℂ)
      = 1 / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h1 := Real.sin_two_mul (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.sin_pi_div_four] at h1
  have h3 : 2 * Real.sin (Real.pi / 8) * Real.cos (Real.pi / 8) = 1 / Real.sqrt 2 := by
    rw [inv_sqrt_two]
    linarith
  exact_mod_cast h3

/-- `Rᵀ X R = H` and `Rᵀ R = 1`. -/
theorem ch_block (p : Bool) :
    rGateᵀ * (if p then xGate else 1) * rGate = if p then hGate else 1 := by
  have hP := cos_sq_add_sin_sq_eighth
  have hC := cos_sq_sub_sin_sq_eighth
  have hS := two_sin_cos_eighth
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
    rw [rGate_transpose, rGate, m2_mul, one_eq_m2]
    congr 1
    · linear_combination hP
    · ring
    · ring
    · linear_combination hP
  · simp only [↓reduceIte]
    rw [rGate_transpose, rGate, xGate_eq_m2, m2_mul, m2_mul, hGate_eq_m2]
    congr 1
    · linear_combination hS
    · linear_combination hC
    · linear_combination hC
    · linear_combination -hS

theorem rGate_unitary : rGate ∈ Matrix.unitaryGroup Bool ℂ := by
  have hP := cos_sq_add_sin_sq_eighth
  have hs : star rGate = rGateᵀ := by
    rw [rGate_transpose, rGate, star_m2]
    simp
  rw [Matrix.mem_unitaryGroup_iff, hs, rGate_transpose, rGate, m2_mul, one_eq_m2]
  congr 1
  · linear_combination hP
  · ring
  · ring
  · linear_combination hP

theorem rGate_transpose_unitary : rGateᵀ ∈ Matrix.unitaryGroup Bool ℂ := by
  have hP := cos_sq_add_sin_sq_eighth
  have hs : star rGateᵀ = rGate := by
    rw [rGate_transpose, rGate, star_m2]
    simp
  rw [Matrix.mem_unitaryGroup_iff, hs, rGate_transpose, rGate, m2_mul, one_eq_m2]
  congr 1
  · linear_combination hP
  · ring
  · ring
  · linear_combination hP

/-- The block of the controlled Hadamard: `H` when wire `c` holds a one. -/
noncomputable def chBlk (c : Fin N) (x : St N) : Matrix Bool Bool ℂ :=
  if x c then hGate else 1

/-- The controlled Hadamard from wire `q1` onto its neighbour `q0`, with one CNOT. -/
noncomputable def chCirc (q0 q1 : Fin N) (h : q0.val + 1 = q1.val) : List (Gate N) :=
  [.one q0 rGate, .cx q1 q0 (Or.inr h), .one q0 rGateᵀ]

theorem cnots_chCirc (q0 q1 : Fin N) (h : q0.val + 1 = q1.val) :
    cnots (chCirc q0 q1 h) = 1 := rfl

theorem unitaryGates_chCirc (q0 q1 : Fin N) (h : q0.val + 1 = q1.val) :
    UnitaryGates (chCirc q0 q1 h) :=
  unitaryGates_cons_one _ rGate_unitary (unitaryGates_cons_cx _ _ _
    (unitaryGates_cons_one _ rGate_transpose_unitary unitaryGates_nil))

theorem circMat_chCirc (q0 q1 : Fin N) (h : q0.val + 1 = q1.val) :
    circMat (chCirc q0 q1 h) = ctrlMat q0 (chBlk q1) := by
  have n : q1 ≠ q0 := adj_ne (Or.inr h)
  have hu : ∀ (x : St N) (b : Bool),
      rGateᵀ * (if Function.update x q0 b q1 then xGate else 1)
        = rGateᵀ * (if x q1 then xGate else 1) := by
    intro x b
    rw [Function.update_of_ne n]
  simp only [chCirc, circMat, one_mul]
  change ctrlMat q0 (fun _ => rGateᵀ) * mono (cxPerm q1 q0 n) (fun _ => 1)
    * ctrlMat q0 (fun _ => rGate) = _
  rw [cx_eq_ctrlMat q1 q0 n, ctrlMat_mul q0 (fun _ => rGateᵀ) _ (fun _ _ => rfl),
    ctrlMat_mul q0 (fun x => rGateᵀ * (if x q1 then xGate else 1)) _ hu]
  congr 1
  funext x
  exact ch_block (x q1)

/-! ### The toggle: `CH · diagonal · CH` is a conditional flip up to phases -/

theorem diagonal_eq_ctrlMat (q : Fin N) (δ : St N → ℂ) :
    Matrix.diagonal δ
      = ctrlMat q (fun x => Matrix.diagonal (fun b => δ (Function.update x q b))) := by
  rw [ctrlMat_diagonal, mono_one_eq_diagonal]
  congr 1
  funext x
  simp

/-- The block `C · diag(±1, ±1) · C` for `C = H` (if `p`) or `1`. -/
noncomputable def togBlock (p w g : Bool) : Matrix Bool Bool ℂ :=
  (if p then hGate else 1) * Matrix.diagonal (fun b => if xor w (b && g) then (-1 : ℂ) else 1)
    * (if p then hGate else 1)

theorem togBlock_eq (p w g : Bool) :
    togBlock p w g
      = if p && g then m2 0 (if w then -1 else 1) (if w then -1 else 1) 0
        else m2 (if w then -1 else 1) 0 0 (if xor w g then -1 else 1) := by
  unfold togBlock
  rw [diagonal_eq_m2]
  cases p
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Matrix.one_mul, Matrix.mul_one]
    cases w <;> cases g <;> simp
  · simp only [↓reduceIte, Bool.true_and, hGate_mul_mul]
    cases w <;> cases g <;> norm_num

/-- The diagonal blocks of a sign `(-1)^{w ⊕ (b ∧ g)}` on one wire. -/
noncomputable def sgnBlk (w g : St N → Bool) (x : St N) : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if xor (w x) (b && g x) then (-1 : ℂ) else 1)

/-- **Controlled Hadamards turn a controlled sign into a conditional flip.**  If `w`
and `g` do not depend on wire `q0`, then `CH · diag((-1)^{w ⊕ (x q0 ∧ g)}) · CH`, with
the Hadamards controlled by wire `c`, flips wire `q0` iff `x c ∧ g x`, up to phases of
modulus one. -/
theorem toggle_core (q0 c : Fin N) (hc : c ≠ q0) (w g : St N → Bool)
    (hw : ∀ x b, w (Function.update x q0 b) = w x)
    (hg : ∀ x b, g (Function.update x q0 b) = g x)
    (hf : ∀ (x : St N) (b : Bool),
      (Function.update x q0 b c && g (Function.update x q0 b)) = (x c && g x)) :
    ∃ φ : St N → ℂ, (∀ x, star (φ x) * φ x = 1) ∧
      ctrlMat q0 (chBlk c)
          * Matrix.diagonal (fun x => if xor (w x) (x q0 && g x) then (-1 : ℂ) else 1)
          * ctrlMat q0 (chBlk c)
        = mono (flipPerm q0 (fun x => x c && g x) hf) φ := by
  have hD : Matrix.diagonal (fun x => if xor (w x) (x q0 && g x) then (-1 : ℂ) else 1)
      = ctrlMat q0 (sgnBlk w g) := by
    rw [diagonal_eq_ctrlMat q0]
    congr 1
    funext x
    simp only [sgnBlk, hw, hg, Function.update_self]
  have hA : ∀ (x : St N) (b : Bool), chBlk c (Function.update x q0 b) = chBlk c x := by
    intro x b
    simp only [chBlk, Function.update_of_ne hc]
  have hS : ∀ (x : St N) (b : Bool), sgnBlk w g (Function.update x q0 b) = sgnBlk w g x := by
    intro x b
    simp only [sgnBlk, hw, hg]
  have hB : ∀ (x : St N) (b : Bool),
      chBlk c (Function.update x q0 b) * sgnBlk w g (Function.update x q0 b)
        = chBlk c x * sgnBlk w g x := by
    intro x b
    rw [hA, hS]
  have key : ctrlMat q0 (chBlk c)
        * Matrix.diagonal (fun x => if xor (w x) (x q0 && g x) then (-1 : ℂ) else 1)
        * ctrlMat q0 (chBlk c)
      = ctrlMat q0 (fun x => togBlock (x c) (w x) (g x)) := by
    rw [hD, ctrlMat_mul q0 (chBlk c) (sgnBlk w g) hA,
      ctrlMat_mul q0 (fun x => chBlk c x * sgnBlk w g x) (chBlk c) hB]
    rfl
  have hsupp : ∀ (x : St N) (a b : Bool), a ≠ xor b (x c && g x) →
      togBlock (x c) (w x) (g x) a b = 0 := by
    intro x a b
    rw [togBlock_eq]
    cases x c <;> cases w x <;> cases g x <;> cases a <;> cases b <;> simp [m2]
  refine ⟨fun x => togBlock (x c) (w x) (g x) (xor (x q0) (x c && g x)) (x q0), ?_, ?_⟩
  · intro x
    simp only [togBlock_eq]
    cases x c <;> cases w x <;> cases g x <;> cases x q0 <;> simp [m2]
  · rw [key]
    exact ctrlMat_eq_mono q0 (fun x => x c && g x) hf _ hsupp

/-! ### The long toggle -/

/-- All odd wires below `2a` hold a one. -/
def oddOnes (a : ℕ) (x : St N) : Bool :=
  decide (∀ r : Fin N, r.val < 2 * a → r.val % 2 = 1 → x r = true)

theorem oddOnes_update (a : ℕ) (h0 : 0 < N) (x : St N) (b : Bool) :
    oddOnes a (Function.update x ⟨0, h0⟩ b) = oddOnes a x := by
  have key : ∀ r : Fin N, r.val % 2 = 1 → Function.update x ⟨0, h0⟩ b r = x r := by
    intro r hr
    apply Function.update_of_ne
    intro hh
    have h1 : r.val = 0 := congrArg Fin.val hh
    omega
  unfold oddOnes
  rw [decide_eq_decide]
  constructor
  · intro H r h1 h2
    rw [← key r h2]
    exact H r h1 h2
  · intro H r h1 h2
    rw [key r h2]
    exact H r h1 h2

/-- The part of the toggle condition that the sweep and the base contribute. -/
def markG (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) : Bool :=
  oddAll (2 * a - 3) x && x ⟨2 * a - 1, by omega⟩

/-- The sign that does not depend on wire `0`. -/
def markW (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) : Bool :=
  xor (x ⟨2 * a - 2, by omega⟩)
      (sweepPerm N (2 * a - 3) (Function.update x ⟨0, by omega⟩ false) ⟨2 * a - 3, by omega⟩)
    && x ⟨2 * a - 1, by omega⟩

theorem markG_update (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) (b : Bool) :
    markG a hN ha (Function.update x ⟨0, by omega⟩ b) = markG a hN ha x := by
  have h0 : 0 < N := by omega
  have n1 : (⟨2 * a - 1, by omega⟩ : Fin N) ≠ ⟨0, h0⟩ := fin_ne _ _ (by omega)
  unfold markG
  rw [oddAll_update, Function.update_of_ne n1]

theorem markW_update (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) (b : Bool) :
    markW a hN ha (Function.update x ⟨0, by omega⟩ b) = markW a hN ha x := by
  have h0 : 0 < N := by omega
  have n1 : (⟨2 * a - 1, by omega⟩ : Fin N) ≠ ⟨0, h0⟩ := fin_ne _ _ (by omega)
  have n2 : (⟨2 * a - 2, by omega⟩ : Fin N) ≠ ⟨0, h0⟩ := fin_ne _ _ (by omega)
  unfold markW
  rw [Function.update_idem, Function.update_of_ne n1, Function.update_of_ne n2]

theorem bool_final (A P b G u : Bool) :
    (xor A (xor P (b && G)) && u) = xor (xor A P && u) (b && (G && u)) := by
  cases A <;> cases P <;> cases b <;> cases G <;> cases u <;> rfl

/-- The base sign after the sweep: a sign independent of wire `0`, times
`(-1)^{x 0 ∧ x 3 ∧ x 5 ∧ … ∧ x (2a-1)}`. -/
theorem mark_diag (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) :
    (xor (sweepPerm N (2 * a - 3) x ⟨2 * a - 2, by omega⟩)
          (sweepPerm N (2 * a - 3) x ⟨2 * a - 3, by omega⟩)
        && sweepPerm N (2 * a - 3) x ⟨2 * a - 1, by omega⟩)
      = xor (markW a hN ha x) (x ⟨0, by omega⟩ && markG a hN ha x) := by
  rw [sweepPerm_untouched (2 * a - 3) (by omega) x ⟨2 * a - 2, by omega⟩
      (by show 2 * a - 3 < 2 * a - 2; omega),
    sweepPerm_untouched (2 * a - 3) (by omega) x ⟨2 * a - 1, by omega⟩
      (by show 2 * a - 3 < 2 * a - 1; omega),
    sweep_invariant (2 * a - 3) (by omega) x, markW, markG]
  exact bool_final _ _ _ _ _

theorem oddOnes_eq (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) (x : St N) :
    (x ⟨1, by omega⟩ && markG a hN ha x) = oddOnes a x := by
  rw [Bool.eq_iff_iff]
  simp only [markG, oddOnes, oddAll, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨H1, H2, H3⟩ r hr hodd
    by_cases h1 : r.val = 1
    · have hr' : r = ⟨1, by omega⟩ := Fin.ext h1
      rw [hr']
      exact H1
    · by_cases h3 : r.val = 2 * a - 1
      · have hr' : r = ⟨2 * a - 1, by omega⟩ := Fin.ext h3
        rw [hr']
        exact H3
      · exact H2 r (by omega) (by omega) hodd
  · intro H
    refine ⟨H _ ?_ ?_, fun r h1 h2 h3 => H r (by omega) h3, H _ ?_ ?_⟩
    · show 1 < 2 * a
      omega
    · show 1 % 2 = 1
      rfl
    · show 2 * a - 1 < 2 * a
      omega
    · show (2 * a - 1) % 2 = 1
      omega

/-- **The long relative-phase toggle** on wires `0 .. 2a-1`:
`CH ++ steps ++ base ++ invCirc steps ++ CH`. -/
noncomputable def mark (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) : List (Gate N) :=
  chCirc ⟨0, by omega⟩ ⟨1, by omega⟩ rfl ++ steps N (2 * a - 3)
    ++ baseCirc ⟨2 * a - 3, by omega⟩ ⟨2 * a - 2, by omega⟩ ⟨2 * a - 1, by omega⟩
        (by show 2 * a - 3 + 1 = 2 * a - 2; omega) (by show 2 * a - 2 + 1 = 2 * a - 1; omega)
    ++ invCirc (steps N (2 * a - 3)) ++ chCirc ⟨0, by omega⟩ ⟨1, by omega⟩ rfl

/-- The toggle has `8a - 9` CNOTs. -/
theorem cnots_mark (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) :
    cnots (mark a hN ha) = 8 * a - 9 := by
  simp only [mark, cnots_append, cnots_invCirc, cnots_chCirc, cnots_baseCirc]
  rw [cnots_steps (2 * a - 3) (by omega)]
  omega

theorem unitaryGates_mark (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) :
    UnitaryGates (mark a hN ha) :=
  unitaryGates_append (unitaryGates_append (unitaryGates_append (unitaryGates_append
    (unitaryGates_chCirc _ _ _) (unitaryGates_steps _ _)) (unitaryGates_baseCirc _ _ _ _ _))
    (unitaryGates_invCirc (unitaryGates_steps _ _))) (unitaryGates_chCirc _ _ _)

/-- **The toggle is a conditional flip up to phases.**  Its matrix flips wire `0`
exactly when all odd wires `1, 3, …, 2a-1` hold a one, up to phases of modulus one. -/
theorem circMat_mark (a : ℕ) (hN : 2 * a ≤ N) (ha : 2 ≤ a) :
    ∃ φ : St N → ℂ, (∀ x, star (φ x) * φ x = 1) ∧
      circMat (mark a hN ha)
        = mono (flipPerm ⟨0, by omega⟩ (oddOnes a) (oddOnes_update a (by omega))) φ := by
  have h0 : 0 < N := by omega
  have n10 : (⟨1, by omega⟩ : Fin N) ≠ ⟨0, h0⟩ := fin_ne _ _ (by omega)
  obtain ⟨ψ, hψ, hV⟩ := circMat_steps N (2 * a - 3)
  have hre : circMat (mark a hN ha)
      = circMat (chCirc (N := N) ⟨0, by omega⟩ ⟨1, by omega⟩ rfl)
        * ((circMat (steps N (2 * a - 3)))ᴴ
          * circMat (baseCirc (N := N) ⟨2 * a - 3, by omega⟩ ⟨2 * a - 2, by omega⟩
              ⟨2 * a - 1, by omega⟩ (by show 2 * a - 3 + 1 = 2 * a - 2; omega)
              (by show 2 * a - 2 + 1 = 2 * a - 1; omega))
          * circMat (steps N (2 * a - 3)))
        * circMat (chCirc (N := N) ⟨0, by omega⟩ ⟨1, by omega⟩ rfl) := by
    simp only [mark, circMat_append, circMat_invCirc, Matrix.mul_assoc]
  have hf : ∀ (x : St N) (b : Bool),
      (Function.update x ⟨0, h0⟩ b ⟨1, by omega⟩ && markG a hN ha (Function.update x ⟨0, h0⟩ b))
        = (x ⟨1, by omega⟩ && markG a hN ha x) := by
    intro x b
    rw [Function.update_of_ne n10, markG_update]
  obtain ⟨φ, hφ, hE⟩ := toggle_core ⟨0, h0⟩ ⟨1, by omega⟩ n10 (markW a hN ha) (markG a hN ha)
    (markW_update a hN ha) (markG_update a hN ha) hf
  refine ⟨φ, hφ, ?_⟩
  have hmid : (mono (sweepPerm N (2 * a - 3)) ψ)ᴴ
        * Matrix.diagonal (fun x : St N =>
            if (xor (x ⟨2 * a - 2, by omega⟩) (x ⟨2 * a - 3, by omega⟩))
              && x ⟨2 * a - 1, by omega⟩ then (-1 : ℂ) else 1)
        * mono (sweepPerm N (2 * a - 3)) ψ
      = Matrix.diagonal (fun x : St N =>
          if xor (markW a hN ha x) (x ⟨0, h0⟩ && markG a hN ha x) then (-1 : ℂ) else 1) := by
    rw [conj_mono_diagonal _ _ _ hψ]
    congr 1
    funext x
    exact congrArg (fun b : Bool => if b then (-1 : ℂ) else 1) (mark_diag a hN ha x)
  rw [hre, hV, circMat_baseCirc, hmid, circMat_chCirc, hE]
  congr 1
  apply Equiv.ext
  intro x
  have hfe : (x ⟨1, by omega⟩ && markG a hN ha x) = oddOnes a x := oddOnes_eq a hN ha x
  simp only [flipPerm_apply, hfe]

end Line
