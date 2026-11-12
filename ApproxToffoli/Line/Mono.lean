/-
Permutations up to phases on a line of qubits: algebra of `mono`, of one-qubit gates,
and of "one target qubit with classical controls" matrices (`ctrlMat`).

The main tool is `ctrlMat_eq_mono`: a `ctrlMat` whose 2×2 blocks are diagonal or
anti-diagonal according to a Boolean `f` is a permutation up to phases.
-/
import Mathlib
import ApproxToffoli.Line.Model

namespace Line

open Matrix ExactLine

variable {N : ℕ}

/-! ### Products of permutations up to phases -/

theorem mono_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (σ τ : Equiv.Perm ι) (φ ψ : ι → ℂ) :
    mono σ φ * mono τ ψ = mono (σ * τ) (fun j => φ (τ j) * ψ j) := by
  ext i j
  rw [mul_mono_apply]
  simp [mono]

theorem mono_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    mono (1 : Equiv.Perm ι) (fun _ => (1 : ℂ)) = 1 := by
  ext i j
  simp [mono, Matrix.one_apply]

/-! ### Sums over the states that agree with `x` away from qubit `q` -/

theorem sum_agree (q : Fin N) (x : St N) (F : St N → ℂ)
    (hF : ∀ z, ¬ (∀ r, r ≠ q → z r = x r) → F z = 0) :
    ∑ z, F z = F (Function.update x q true) + F (Function.update x q false) := by
  have hne : Function.update x q true ≠ Function.update x q false := by
    intro h
    have := congrFun h q
    simp at this
  rw [← Finset.sum_pair hne]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hz
  apply hF
  intro hagree
  apply hz
  have hzu : z = Function.update x q (z q) := by
    funext r
    by_cases hr : r = q
    · subst hr
      simp
    · rw [Function.update_of_ne hr]
      exact hagree r hr
  rw [hzu]
  cases z q <;> simp

/-! ### One target qubit with classical controls -/

/-- The matrix that applies the 2×2 block `g x` to qubit `q`, where the block may
depend on the other bits of the basis state `x`. -/
def ctrlMat (q : Fin N) (g : St N → Matrix Bool Bool ℂ) : Matrix (St N) (St N) ℂ :=
  Matrix.of fun y x => if (∀ r, r ≠ q → y r = x r) then g x (y q) (x q) else 0

theorem oneMat_eq_ctrlMat (q : Fin N) (g : Matrix Bool Bool ℂ) :
    oneMat q g = ctrlMat q (fun _ => g) := rfl

theorem ctrlMat_mul (q : Fin N) (g h : St N → Matrix Bool Bool ℂ)
    (hg : ∀ x b, g (Function.update x q b) = g x) :
    ctrlMat q g * ctrlMat q h = ctrlMat q (fun x => g x * h x) := by
  ext y x
  rw [Matrix.mul_apply, sum_agree q x]
  · have h2 : ∀ b, (∀ r, r ≠ q → Function.update x q b r = x r) :=
      fun b r hr => Function.update_of_ne hr _ _
    by_cases hyx : ∀ r, r ≠ q → y r = x r
    · have h1 : ∀ b, (∀ r, r ≠ q → y r = Function.update x q b r) := by
        intro b r hr
        rw [Function.update_of_ne hr]
        exact hyx r hr
      simp only [ctrlMat, Matrix.of_apply, hg, if_pos (h1 true), if_pos (h1 false),
        if_pos (h2 true), if_pos (h2 false), if_pos hyx, Matrix.mul_apply, Fintype.sum_bool,
        Function.update_self]
    · have h1 : ∀ b, ¬ (∀ r, r ≠ q → y r = Function.update x q b r) := by
        intro b hb
        apply hyx
        intro r hr
        have := hb r hr
        rwa [Function.update_of_ne hr] at this
      simp [ctrlMat, h1, hyx]
  · intro z hz
    simp [ctrlMat, hz]

/-! ### One-qubit gates -/

theorem oneMat_mul (q : Fin N) (g h : Matrix Bool Bool ℂ) :
    oneMat q g * oneMat q h = oneMat q (g * h) := by
  rw [oneMat_eq_ctrlMat, oneMat_eq_ctrlMat, ctrlMat_mul q _ _ (fun _ _ => rfl)]
  rfl

/-! ### Blocks that are diagonal or anti-diagonal: permutations up to phases -/

/-- Flip bit `q` exactly when `f x` holds. -/
def flipFun (q : Fin N) (f : St N → Bool) (x : St N) : St N :=
  Function.update x q (xor (x q) (f x))

theorem flipFun_involutive (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) : Function.Involutive (flipFun q f) := by
  intro x
  funext r
  unfold flipFun
  rw [hf]
  by_cases hr : r = q
  · subst hr
    simp
  · simp [Function.update_of_ne hr]

/-- The basis permutation "flip bit `q` iff `f x`", for `f` that does not depend on
bit `q`. -/
def flipPerm (q : Fin N) (f : St N → Bool) (hf : ∀ x b, f (Function.update x q b) = f x) :
    Equiv.Perm (St N) :=
  (flipFun_involutive q f hf).toPerm _

theorem flipPerm_apply (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) (x : St N) :
    flipPerm q f hf x = Function.update x q (xor (x q) (f x)) := rfl

/-- **A cell is a permutation up to phases.**  If the block `g x` is supported on the
entries `(b xor f x, b)` (diagonal when `f x = false`, anti-diagonal when
`f x = true`), then `ctrlMat q g` is the permutation "flip bit `q` iff `f x`" up to
the phases `g x (x q xor f x) (x q)`. -/
theorem ctrlMat_eq_mono (q : Fin N) (f : St N → Bool)
    (hf : ∀ x b, f (Function.update x q b) = f x) (g : St N → Matrix Bool Bool ℂ)
    (hg : ∀ x a b, a ≠ xor b (f x) → g x a b = 0) :
    ctrlMat q g = mono (flipPerm q f hf) (fun x => g x (xor (x q) (f x)) (x q)) := by
  ext y x
  simp only [ctrlMat, mono, Matrix.of_apply]
  have key : (y = flipPerm q f hf x) ↔
      (y q = xor (x q) (f x)) ∧ ∀ r, r ≠ q → y r = x r := Function.eq_update_iff
  by_cases h1 : ∀ r, r ≠ q → y r = x r
  · by_cases h2 : y q = xor (x q) (f x)
    · rw [if_pos h1, if_pos (key.2 ⟨h2, h1⟩), h2]
    · rw [if_pos h1, if_neg (fun h => h2 (key.1 h).1)]
      exact hg x _ _ h2
  · rw [if_neg h1, if_neg (fun h => h1 (key.1 h).2)]

theorem flipPerm_false (q : Fin N) :
    flipPerm q (fun _ => false) (fun _ _ => rfl) = 1 := by
  ext x
  simp [flipPerm_apply]

/-- Diagonal blocks give a diagonal matrix. -/
theorem ctrlMat_diagonal (q : Fin N) (d : St N → Bool → ℂ) :
    ctrlMat q (fun x => Matrix.diagonal (d x)) = mono 1 (fun x => d x (x q)) := by
  rw [ctrlMat_eq_mono q (fun _ => false) (fun _ _ => rfl), flipPerm_false]
  · congr 1
    funext x
    simp
  · intro x a b hab
    apply Matrix.diagonal_apply_ne
    simpa using hab

theorem oneMat_one (q : Fin N) : oneMat q (1 : Matrix Bool Bool ℂ) = 1 := by
  have h := ctrlMat_diagonal q (fun _ _ => (1 : ℂ))
  rw [mono_one] at h
  rw [oneMat_eq_ctrlMat, ← h]
  congr 1

theorem oneMat_pGate (q : Fin N) (t : ℝ) :
    oneMat q (pGate t) = mono 1 (fun x => if x q then e t else 1) :=
  ctrlMat_diagonal q (fun _ b => if b then e t else 1)

/-- The CNOT with control `c` and target `q` is a controlled NOT block on qubit `q`. -/
theorem cx_eq_ctrlMat (c q : Fin N) (h : c ≠ q) :
    mono (cxPerm c q h) (fun _ => (1 : ℂ)) = ctrlMat q (fun x => if x c then xGate else 1) := by
  have hf : ∀ (x : St N) (b : Bool), (Function.update x q b) c = x c :=
    fun x b => Function.update_of_ne h _ _
  rw [ctrlMat_eq_mono q (fun x => x c) hf]
  · have hp : cxPerm c q h = flipPerm q (fun x => x c) hf := Equiv.ext fun _ => rfl
    rw [hp]
    congr 1
    funext x
    cases hc : x c <;> cases hq : x q <;> simp [xGate, Matrix.one_apply]
  · intro x a b hab
    cases hc : x c <;> cases a <;> cases b <;> simp_all [xGate]

end Line
