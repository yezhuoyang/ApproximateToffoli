/-
Exact conditional on a line: the phase-cancellation theorem.

This file formalizes the correctness argument of the exact construction

    Inc~† · F† · Inc~ · F  =  T_N · P_b(-θ),

for ANY circuit `Inc~` that
  * is a permutation up to phases (a "monomial" matrix),
  * keeps the bit `b`, and
  * adds one to the address when `b = 1`
(what it does to the addresses when `b = 0` is arbitrary).

Basis states are indexed by `Fin (n+1) × Bool`: an address `x` with `L = n+1`
values and the bit `b`.  For `N` qubits, `L = 2^(N-1)`; the theorem does not use
that `L` is a power of two.

Not formalized here: the gate-by-gate circuit that realizes `Inc~` on a line and
its CNOT count.
-/
import Mathlib

namespace ExactLine

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A permutation up to phases: it sends the basis state `j` to `φ j` times the
basis state `σ j`. -/
def mono (σ : Equiv.Perm ι) (φ : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => if i = σ j then φ j else 0

theorem conjTranspose_mono_mul_apply (σ : Equiv.Perm ι) (φ : ι → ℂ)
    (M : Matrix ι ι ℂ) (i j : ι) :
    ((mono σ φ)ᴴ * M) i j = star (φ i) * M (σ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
  · simp [mono]
  · intro k _ hk
    simp [mono, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_mono_apply (σ : Equiv.Perm ι) (φ : ι → ℂ)
    (M : Matrix ι ι ℂ) (i j : ι) :
    (M * mono σ φ) i j = M i (σ j) * φ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [mono]
  · intro k _ hk
    simp [mono, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Wrong phases are allowed.**  If `A` is a permutation `σ` up to phases `φ`
of modulus one, then `A† D† A D` is diagonal for every diagonal `D`, and it does
not depend on `φ` at all: the phases of `A` cancel against its inverse. -/
theorem commutator_eq_diagonal (σ : Equiv.Perm ι) (φ f : ι → ℂ)
    (hφ : ∀ j, star (φ j) * φ j = 1) :
    (mono σ φ)ᴴ * (Matrix.diagonal f)ᴴ * mono σ φ * Matrix.diagonal f
      = Matrix.diagonal (fun j => star (f (σ j)) * f j) := by
  ext i j
  rw [Matrix.mul_diagonal, mul_mono_apply, conjTranspose_mono_mul_apply,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, Pi.star_apply]
    linear_combination (star (f (σ i)) * f i) * hφ i
  · have h' : σ i ≠ σ j := fun e => h (σ.injective e)
    rw [if_neg h', if_neg h]
    simp

/-! ### Phases `e^{it}` -/

/-- The phase `e^{it}`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

theorem e_zero : e 0 = 1 := by simp [e]

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  simp only [e]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem e_pi : e Real.pi = -1 := by
  simp [e, Complex.exp_pi_mul_I]

theorem star_e (t : ℝ) : star (e t) = e (-t) := by
  simp only [e]
  change (starRingEnd ℂ) (Complex.exp (t * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-! ### The increment between two phase operations -/

/-- The angle `θ = π / L` with `L = n + 1` addresses. -/
noncomputable def θ (n : ℕ) : ℝ := Real.pi / ((n : ℝ) + 1)

theorem θ_mul (n : ℕ) : θ n * ((n : ℝ) + 1) = Real.pi := by
  unfold θ
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- One step of the increment: the phase `e^{iθx}` before, the phase
`e^{-iθ(x+1 mod L)}` after.  Every address receives `e^{-iθ}`, and the address
that wraps around receives an extra minus sign. -/
theorem step_phase (n : ℕ) (x : Fin (n + 1)) :
    star (e (θ n * ((x + 1 : Fin (n + 1)).val : ℝ))) * e (θ n * (x.val : ℝ))
      = (if x = Fin.last n then (-1 : ℂ) else 1) * e (-θ n) := by
  rw [star_e, ← e_add]
  have hv := Fin.val_add_one x
  by_cases hx : x = Fin.last n
  · rw [if_pos hx] at hv
    rw [if_pos hx, hv]
    have hlast : (x.val : ℝ) = n := by rw [hx]; simp
    rw [hlast]
    have : -(θ n * ((0 : ℕ) : ℝ)) + θ n * (n : ℝ) = Real.pi + -θ n := by
      push_cast
      linear_combination θ_mul n
    rw [this, e_add, e_pi]
  · rw [if_neg hx] at hv
    rw [if_neg hx, hv, one_mul]
    congr 1
    push_cast
    ring

/-- The phase operation `F`: `e^{iθ b x}`. -/
noncomputable def fPhase (n : ℕ) (p : Fin (n + 1) × Bool) : ℂ :=
  if p.2 then e (θ n * (p.1.val : ℝ)) else 1

/-- The conditional sign `T`: minus one on the single basis state with `b = 1`
and the last address (all ones), plus one elsewhere. -/
def signT (n : ℕ) (p : Fin (n + 1) × Bool) : ℂ :=
  if p.2 then (if p.1 = Fin.last n then -1 else 1) else 1

/-- The one-qubit phase gate `P_b(t)` on the bit `b`. -/
noncomputable def pB (n : ℕ) (t : ℝ) (p : Fin (n + 1) × Bool) : ℂ :=
  if p.2 then e t else 1

/-- **It only has to work when the target qubit is one.**  The basis
permutation of the increment: add one to the address when `b = 1`; when `b = 0`
apply an arbitrary permutation `τ` of the addresses.  The bit `b` is kept. -/
def incPerm {n : ℕ} (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 1) × Bool) where
  toFun p := if p.2 then (p.1 + 1, true) else (τ p.1, false)
  invFun p := if p.2 then (p.1 - 1, true) else (τ.symm p.1, false)
  left_inv := by
    rintro ⟨x, b⟩
    cases b <;> simp
  right_inv := by
    rintro ⟨x, b⟩
    cases b <;> simp

theorem conditional_phase (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1) × Bool) :
    star (fPhase n (incPerm τ p)) * fPhase n p = signT n p * pB n (-θ n) p := by
  obtain ⟨x, b⟩ := p
  cases b
  · simp [incPerm, fPhase, signT, pB]
  · have h := step_phase n x
    simpa [incPerm, fPhase, signT, pB] using h

/-- **Main theorem.**  Let `Inc~` be any permutation up to phases whose basis
permutation keeps `b`, adds one to the address when `b = 1`, and is arbitrary
when `b = 0`.  Then

    Inc~† · F† · Inc~ · F  =  T · P_b(-θ). -/
theorem commutator_eq_conditional (n : ℕ) (τ : Equiv.Perm (Fin (n + 1)))
    (φ : Fin (n + 1) × Bool → ℂ) (hφ : ∀ p, star (φ p) * φ p = 1) :
    (mono (incPerm τ) φ)ᴴ * (Matrix.diagonal (fPhase n))ᴴ * mono (incPerm τ) φ
        * Matrix.diagonal (fPhase n)
      = Matrix.diagonal (signT n) * Matrix.diagonal (pB n (-θ n)) := by
  rw [commutator_eq_diagonal _ _ _ hφ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  exact conditional_phase n τ p

/-- **Exactness.**  One more one-qubit phase gate on `b` removes the remaining
phase: the circuit is exactly the conditional sign `T`. -/
theorem exact_conditional (n : ℕ) (τ : Equiv.Perm (Fin (n + 1)))
    (φ : Fin (n + 1) × Bool → ℂ) (hφ : ∀ p, star (φ p) * φ p = 1) :
    Matrix.diagonal (pB n (θ n)) *
        ((mono (incPerm τ) φ)ᴴ * (Matrix.diagonal (fPhase n))ᴴ * mono (incPerm τ) φ
          * Matrix.diagonal (fPhase n))
      = Matrix.diagonal (signT n) := by
  rw [commutator_eq_conditional n τ φ hφ, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  obtain ⟨x, b⟩ := p
  have h1 : e (θ n) * e (-θ n) = 1 := by rw [← e_add, add_neg_cancel, e_zero]
  cases b
  · simp [pB, signT]
  · simp only [pB, signT, if_true]
    linear_combination (if x = Fin.last n then (-1 : ℂ) else 1) * h1

/-! ### The whole-register variant: no bit `b`, a free phase gradient -/

/-- The phase gradient `G`: `e^{iθx}` on the address `x`. -/
noncomputable def gPhase (n : ℕ) (x : Fin (n + 1)) : ℂ := e (θ n * (x.val : ℝ))

/-- The whole-register increment between two phase gradients is the conditional
sign up to the global phase `e^{-iθ}`. -/
theorem whole_register (n : ℕ) (φ : Fin (n + 1) → ℂ) (hφ : ∀ x, star (φ x) * φ x = 1) :
    (mono (Equiv.addRight (1 : Fin (n + 1))) φ)ᴴ * (Matrix.diagonal (gPhase n))ᴴ
        * mono (Equiv.addRight (1 : Fin (n + 1))) φ * Matrix.diagonal (gPhase n)
      = Matrix.diagonal (fun x => (if x = Fin.last n then (-1 : ℂ) else 1) * e (-θ n)) := by
  rw [commutator_eq_diagonal _ _ _ hφ]
  congr 1
  funext x
  simpa [gPhase] using step_phase n x

/-! ### The four steps of the increment: junk that cancels

The address is split into a low half `l : Fin (a+1)` and a high half
`H : Fin (s+1)`.  The four steps are stated as maps on basis states; `h` is an
arbitrary "junk" function of the low half. -/

section FourSteps

variable {a s : ℕ}

/-- The bit `b` as a number. -/
def bit (b : Bool) : Fin (s + 1) := if b then 1 else 0

/-- `allOnes l` holds when the low half is at its last value. -/
def allOnes (l : Fin (a + 1)) : Bool := decide (l = Fin.last a)

/-- `K`: add the junk `h l` and the bit `b` to the high half. -/
def stepK (h : Fin (a + 1) → Fin (s + 1)) (p : Fin (a + 1) × Fin (s + 1) × Bool) :
    Fin (a + 1) × Fin (s + 1) × Bool :=
  (p.1, p.2.1 + h p.1 + bit p.2.2, p.2.2)

/-- `K†`: subtract the junk `h l` and the current bit `b`. -/
def stepKinv (h : Fin (a + 1) → Fin (s + 1)) (p : Fin (a + 1) × Fin (s + 1) × Bool) :
    Fin (a + 1) × Fin (s + 1) × Bool :=
  (p.1, p.2.1 - h p.1 - bit p.2.2, p.2.2)

/-- `M`: flip `b` when the low half is all ones. -/
def stepM (p : Fin (a + 1) × Fin (s + 1) × Bool) : Fin (a + 1) × Fin (s + 1) × Bool :=
  (p.1, p.2.1, xor p.2.2 (allOnes p.1))

/-- `R`: increment the low half and flip `b` when it was all ones. -/
def stepR (p : Fin (a + 1) × Fin (s + 1) × Bool) : Fin (a + 1) × Fin (s + 1) × Bool :=
  (p.1 + 1, p.2.1, xor p.2.2 (allOnes p.1))

/-- **Junk that cancels.**  For every junk function `h`, the four steps
`K, M, K†, R` applied to a state with `b = 1` increment the low half, add its
carry to the high half, and restore `b`. -/
theorem four_steps_true (h : Fin (a + 1) → Fin (s + 1)) (l : Fin (a + 1)) (H : Fin (s + 1)) :
    stepR (stepKinv h (stepM (stepK h (l, H, true))))
      = (l + 1, H + bit (allOnes l), true) := by
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show H + h l + bit true - h l - bit (xor true (allOnes l)) = H + bit (allOnes l)
    cases allOnes l
    · show H + h l + 1 - h l - 1 = H + 0
      abel
    · show H + h l + 1 - h l - 0 = H + 1
      abel
  · show xor (xor true (allOnes l)) (allOnes l) = true
    cases allOnes l <;> rfl

/-- When `b = 0` the four steps still keep `b` (they then do something else to
the address, which is allowed). -/
theorem four_steps_keep_b (h : Fin (a + 1) → Fin (s + 1)) (l : Fin (a + 1)) (H : Fin (s + 1))
    (b : Bool) :
    (stepR (stepKinv h (stepM (stepK h (l, H, b))))).2.2 = b := by
  show xor (xor b (allOnes l)) (allOnes l) = b
  cases b <;> cases allOnes l <;> rfl

/-- The pair (low half + 1, high half + carry) is the combined address plus one:
with the value `l + (a+1)·H`, the step adds one modulo `(a+1)(s+1)`. -/
theorem carry_is_increment (l : Fin (a + 1)) (H : Fin (s + 1)) :
    ((l + 1).val + (a + 1) * (H + bit (allOnes l)).val) % ((a + 1) * (s + 1))
      = (l.val + (a + 1) * H.val + 1) % ((a + 1) * (s + 1)) := by
  have hl := Fin.val_add_one l
  by_cases hx : l = Fin.last a
  · have hones : allOnes l = true := by simp [allOnes, hx]
    rw [if_pos hx] at hl
    have hla : l.val = a := by rw [hx]; simp
    have hH := Fin.val_add_one H
    rw [hones, hl, hla]
    show (0 + (a + 1) * (H + 1).val) % ((a + 1) * (s + 1)) = _
    by_cases hH' : H = Fin.last s
    · rw [if_pos hH'] at hH
      have hHs : H.val = s := by rw [hH']; simp
      rw [hH, hHs]
      have : a + (a + 1) * s + 1 = (a + 1) * (s + 1) := by ring
      rw [this, Nat.mod_self]
      simp
    · rw [if_neg hH'] at hH
      rw [hH]
      congr 1
      ring
  · have hones : allOnes l = false := by simp [allOnes, hx]
    rw [if_neg hx] at hl
    rw [hones, hl]
    show (l.val + 1 + (a + 1) * (H + 0).val) % ((a + 1) * (s + 1)) = _
    rw [add_zero]
    congr 1
    ring

end FourSteps

end ExactLine
