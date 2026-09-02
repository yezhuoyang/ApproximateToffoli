import ApproxToffoli.BlockClean

/-!
# The two-phase unitary orbit theorem

Let `E ∈ U(n)` and let `𝒟_r` be the set of unitaries with doubly-degenerate spectrum of the
shape `(λ,…,λ,μ,…,μ)` with the `λ`-eigenspace of dimension `r`:

    R = λ • P + μ • (1 - P),   |λ| = |μ| = 1,   P = Pᴴ = P²,   tr P = r.

> **THEOREM.**  `max_{R ∈ 𝒟_r} ‖1 + R E‖_*` is attained at some `R` whose spectral projection
> `P` commutes with `E`.

For `n = 4`, `r = 2` and `E` diagonal with distinct entries this says the maximiser is
**diagonal**, which is `notes/REMAINING_GAP.md` §3 — hence **(DIAGONAL TARGETS) at `k = 3`**.

## Why a first-order argument

Every method in `notes/REMAINING_GAP.md` §4 is a convexity method, and convexity points the
*wrong* way here (§4.1: `f` is convex in `P`, so torus averaging gives `f(diag P) ≤ f(P)`).
What convexity does supply is an **exact affine minorant** at each point, coming from the dual
pairing `‖M‖_* ≥ Re tr(Wᴴ M)`.  Reading that minorant at a maximiser turns the problem into a
Ky Fan eigenvalue statement, which forces `[P,Γ] = 0` and then `[P,E] = 0`.

The whole argument is finite-dimensional linear algebra plus one Cauchy–Schwarz: no Grassmannian
tangent calculus and no derivative of `tr(T^{1/2})`.  See `notes/TWO_PHASE_ORBIT_THEOREM.md`.

## Contents

| name | rôle |
|---|---|
| `nucNorm` | `tr √(Mᴴ M)` — Mathlib has no Schatten norm for matrices |
| `re_trace_mul_le` | **Lemma CS**: `Re tr(Z H) ≤ tr H` for `Z` unitary, `H ⪰ 0` |
| `unitary_conj_sqrt` | a unitary fixing `A` fixes `√A` — used twice (Step 1a and the `J`-trick) |
| `sqrt_comm` | `√((1+T)ᴴ(1+T))` commutes with the unitary `T` |
| `unitary_sqrt_of_polar` | **Step 1**: `Q := (1+T)S⁻¹` is unitary, `Q² = T`, `Q + Qᴴ = S` |
| `nucNorm_of_polar` | `‖W S‖_* = tr S` for `W` unitary, `S ⪰ 0` |
| `nucNorm_ge_re_trace` | **Step 2**: the affine minorant |
-/

namespace ApproxToffoli.TwoPhase

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **nuclear (trace) norm** `‖M‖_* = tr √(Mᴴ M)`.  Mathlib has no Schatten norm for
matrices, and this is the form the whole argument wants: Steps 1, 4, 5 become pure algebra. -/
noncomputable def nucNorm (M : Matrix n n ℂ) : ℝ := (CFC.sqrt (Mᴴ * M)).trace.re

/-! ### Lemma CS and the square-root calculus -/

/-- **Lemma CS.**  `Re tr(Z H) ≤ tr H` for `Z` unitary and `H ⪰ 0`.

The proof is one line of algebra: with `Y := 1 - Z` one has `Yᴴ Y = Y + Yᴴ` (this is exactly
unitarity), hence `2 · Re tr(Y H) = tr(Yᴴ Y H) = tr((YK)ᴴ (YK)) ≥ 0` where `K := √H`. -/
theorem re_trace_mul_le (Z H : Matrix n n ℂ) (hZ : Zᴴ * Z = 1) (hH : H.PosSemidef) :
    (Z * H).trace.re ≤ H.trace.re := by
  set K := CFC.sqrt H with hKdef
  have hKH : Kᴴ = K := (Matrix.PosSemidef.posSemidef_sqrt (A := H)).isHermitian
  have hKK : K * K = H := by have := hH.sq_sqrt; rwa [pow_two] at this
  set Y : Matrix n n ℂ := 1 - Z with hYdef
  have key : Yᴴ * Y = Y + Yᴴ := by
    simp only [hYdef, conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, one_mul, mul_one, hZ]
    abel
  have hpsd : (0:ℂ) ≤ ((Y * K)ᴴ * (Y * K)).trace :=
    (Matrix.posSemidef_conjTranspose_mul_self (Y * K)).trace_nonneg
  have e1 : ((Y * K)ᴴ * (Y * K)).trace = (Yᴴ * Y * H).trace := by
    rw [conjTranspose_mul, hKH,
      show K * Yᴴ * (Y * K) = K * (Yᴴ * Y * K) by noncomm_ring,
      Matrix.trace_mul_comm K (Yᴴ * Y * K),
      show Yᴴ * Y * K * K = Yᴴ * Y * (K * K) by noncomm_ring, hKK]
  have e2 : (Yᴴ * Y * H).trace = 2 * ((Y * H).trace.re : ℂ) := by
    rw [key, add_mul, Matrix.trace_add]
    have h3 : (Yᴴ * H).trace = (starRingEnd ℂ) ((Y * H).trace) := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, hH.isHermitian,
        Matrix.trace_mul_comm]
    rw [h3, Complex.add_conj]; push_cast; ring
  rw [e1, e2] at hpsd
  have hre : (0:ℝ) ≤ 2 * (Y * H).trace.re := by
    have := Complex.le_def.mp hpsd; simpa using this.1
  have expand : (Y * H).trace = H.trace - (Z * H).trace := by
    rw [hYdef, sub_mul, one_mul, Matrix.trace_sub]
  rw [expand] at hre
  simp only [Complex.sub_re] at hre
  linarith

/-- `tr(A B) ≥ 0` for `A`, `B` positive semidefinite. -/
theorem trace_mul_nonneg (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (0 : ℂ) ≤ (A * B).trace := by
  have hKp : (CFC.sqrt A).PosSemidef := Matrix.PosSemidef.posSemidef_sqrt
  have hKH : (CFC.sqrt A)ᴴ = CFC.sqrt A := hKp.isHermitian
  have hKK : CFC.sqrt A * CFC.sqrt A = A := by have := hA.sq_sqrt; rwa [pow_two] at this
  have hconj : ((CFC.sqrt A)ᴴ * B * CFC.sqrt A).PosSemidef := hB.conjTranspose_mul_mul_same _
  have := hconj.trace_nonneg
  rwa [hKH, show CFC.sqrt A * B * CFC.sqrt A = CFC.sqrt A * (B * CFC.sqrt A) by noncomm_ring,
    Matrix.trace_mul_comm, show B * CFC.sqrt A * CFC.sqrt A = B * (CFC.sqrt A * CFC.sqrt A) by
      noncomm_ring, hKK, Matrix.trace_mul_comm] at this

/-- **Lemma CS for contractions.**  `Re tr(Z H) ≤ tr H` whenever `1 - ZᴴZ ⪰ 0` and `H ⪰ 0`.

The unitary case is the special case `1 - ZᴴZ = 0`.  The extra slack is exactly the term
`tr((1 - ZᴴZ)H) ≥ 0`.  This version is what makes the *competitor* side of the first-order
condition work without a polar decomposition: for `ε > 0` the matrix `X(√(XᴴX) + ε)⁻¹` is a
contraction for every `X`, singular or not, whereas a unitary polar factor need not exist
constructively. -/
theorem re_trace_mul_le_contraction (Z H : Matrix n n ℂ) (hZ : (1 - Zᴴ * Z).PosSemidef)
    (hH : H.PosSemidef) : (Z * H).trace.re ≤ H.trace.re := by
  set K := CFC.sqrt H with hKdef
  have hKH : Kᴴ = K := (Matrix.PosSemidef.posSemidef_sqrt (A := H)).isHermitian
  have hKK : K * K = H := by have := hH.sq_sqrt; rwa [pow_two] at this
  set Y : Matrix n n ℂ := 1 - Z with hYdef
  have key : Y + Yᴴ = Yᴴ * Y + (1 - Zᴴ * Z) := by
    simp only [hYdef, conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, one_mul, mul_one]
    abel
  have h1 : (0:ℂ) ≤ (Yᴴ * Y * H).trace := by
    have hpsd : (0:ℂ) ≤ ((Y * K)ᴴ * (Y * K)).trace :=
      (Matrix.posSemidef_conjTranspose_mul_self (Y * K)).trace_nonneg
    rwa [conjTranspose_mul, hKH, show K * Yᴴ * (Y * K) = K * (Yᴴ * Y * K) by noncomm_ring,
      Matrix.trace_mul_comm K (Yᴴ * Y * K),
      show Yᴴ * Y * K * K = Yᴴ * Y * (K * K) by noncomm_ring, hKK] at hpsd
  have h2 : (0:ℂ) ≤ ((1 - Zᴴ * Z) * H).trace := trace_mul_nonneg _ _ hZ hH
  have hsum : (0:ℂ) ≤ ((Y + Yᴴ) * H).trace := by
    rw [key, add_mul, Matrix.trace_add]; exact add_nonneg h1 h2
  have e2 : ((Y + Yᴴ) * H).trace = 2 * ((Y * H).trace.re : ℂ) := by
    rw [add_mul, Matrix.trace_add]
    have h3 : (Yᴴ * H).trace = (starRingEnd ℂ) ((Y * H).trace) := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, hH.isHermitian,
        Matrix.trace_mul_comm]
    rw [h3, Complex.add_conj]; push_cast; ring
  rw [e2] at hsum
  have hre : (0:ℝ) ≤ 2 * (Y * H).trace.re := by
    have := Complex.le_def.mp hsum; simpa using this.1
  have expand : (Y * H).trace = H.trace - (Z * H).trace := by
    rw [hYdef, sub_mul, one_mul, Matrix.trace_sub]
  rw [expand] at hre
  simp only [Complex.sub_re] at hre
  linarith

/-- If a unitary `X` fixes a PSD matrix `A` under conjugation, it fixes `√A` too.

Used twice: to commute `√((1+T)ᴴ(1+T))` with `T` (Step 1a), and as the **`J`-trick** of Step 5.
Both times it replaces an appeal to functional calculus by uniqueness of the PSD square root. -/
theorem unitary_conj_sqrt (X A : Matrix n n ℂ) (hX : Xᴴ * X = 1)
    (hA : A.PosSemidef) (h : X * A * Xᴴ = A) : X * CFC.sqrt A * Xᴴ = CFC.sqrt A := by
  have hsp : (CFC.sqrt A).PosSemidef := Matrix.PosSemidef.posSemidef_sqrt
  have hsq : CFC.sqrt A * CFC.sqrt A = A := by have := hA.sq_sqrt; rwa [pow_two] at this
  have hBp : (X * CFC.sqrt A * Xᴴ).PosSemidef := by
    have := hsp.conjTranspose_mul_mul_same Xᴴ; rwa [conjTranspose_conjTranspose] at this
  refine (hBp.eq_sqrt_iff_sq_eq hA).mpr ?_
  rw [pow_two, show X * CFC.sqrt A * Xᴴ * (X * CFC.sqrt A * Xᴴ)
        = X * CFC.sqrt A * (Xᴴ * X) * CFC.sqrt A * Xᴴ by noncomm_ring, hX,
    show X * CFC.sqrt A * 1 * CFC.sqrt A * Xᴴ
        = X * (CFC.sqrt A * CFC.sqrt A) * Xᴴ by noncomm_ring, hsq, h]

/-- `(1+T)ᴴ(1+T) = 2 + T + Tᴴ` for `T` unitary. -/
theorem gram_eq (T : Matrix n n ℂ) (hT : Tᴴ * T = 1) : (1 + T)ᴴ * (1 + T) = 1 + 1 + T + Tᴴ := by
  rw [conjTranspose_add, conjTranspose_one,
    show (1 + Tᴴ) * (1 + T) = 1 + T + Tᴴ + Tᴴ * T by noncomm_ring, hT]
  abel

/-- **Step 1a.**  `S := √((1+T)ᴴ(1+T))` commutes with a unitary `T`. -/
theorem sqrt_comm (T : Matrix n n ℂ) (hT : Tᴴ * T = 1) (hT' : T * Tᴴ = 1) :
    T * CFC.sqrt ((1 + T)ᴴ * (1 + T)) = CFC.sqrt ((1 + T)ᴴ * (1 + T)) * T := by
  set G := (1 + T)ᴴ * (1 + T) with hG
  have hGp : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hcomm : T * G * Tᴴ = G := by
    have hGexp : G = 1 + 1 + T + Tᴴ := gram_eq T hT
    have h1 : T * G = G * T := by
      rw [hGexp, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, hT, hT']; noncomm_ring
    rw [h1, mul_assoc, hT', mul_one]
  have hfix := unitary_conj_sqrt T G hT hGp hcomm
  calc T * CFC.sqrt G = T * CFC.sqrt G * (Tᴴ * T) := by rw [hT, mul_one]
    _ = (T * CFC.sqrt G * Tᴴ) * T := by noncomm_ring
    _ = CFC.sqrt G * T := by rw [hfix]

/-- **Step 1.**  For `T` unitary with `S := √((1+T)ᴴ(1+T))` invertible, `Q := (1+T) S⁻¹` is a
*unitary square root* of `T` whose real part is `S/2 ⪰ 0`:

* `Qᴴ Q = 1`,
* `Q Q = T`,
* `Q + Qᴴ = S`.

In particular `1 + T = Q S` is a polar decomposition. -/
theorem unitary_sqrt_of_polar (T Si : Matrix n n ℂ) (hT : Tᴴ * T = 1) (hT' : T * Tᴴ = 1)
    (hSi : CFC.sqrt ((1 + T)ᴴ * (1 + T)) * Si = 1)
    (hSi' : Si * CFC.sqrt ((1 + T)ᴴ * (1 + T)) = 1) :
    ((1 + T) * Si)ᴴ * ((1 + T) * Si) = 1 ∧ ((1 + T) * Si) * ((1 + T) * Si) = T ∧
      ((1 + T) * Si) + ((1 + T) * Si)ᴴ = CFC.sqrt ((1 + T)ᴴ * (1 + T)) := by
  set G := (1 + T)ᴴ * (1 + T) with hG
  set S := CFC.sqrt G with hS
  have hGp : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hSH : Sᴴ = S := (Matrix.PosSemidef.posSemidef_sqrt (A := G)).isHermitian
  have hSS : S * S = G := by have := hGp.sq_sqrt; rwa [pow_two] at this
  have hGexp : G = 1 + 1 + T + Tᴴ := gram_eq T hT
  -- `Si` inherits hermiticity and the commutation with `T`
  have hSiH : Siᴴ = Si := by
    have h1 : Siᴴ * S = 1 := by
      have := congrArg conjTranspose hSi
      rwa [conjTranspose_mul, conjTranspose_one, hSH] at this
    calc Siᴴ = Siᴴ * (S * Si) := by rw [hSi, mul_one]
      _ = (Siᴴ * S) * Si := by noncomm_ring
      _ = Si := by rw [h1, one_mul]
  have hTS : T * S = S * T := sqrt_comm T hT hT'
  have hTSi : T * Si = Si * T := by
    calc T * Si = (Si * S) * T * Si := by rw [hSi', one_mul]
      _ = Si * (S * T) * Si := by noncomm_ring
      _ = Si * (T * S) * Si := by rw [hTS]
      _ = Si * T * (S * Si) := by noncomm_ring
      _ = Si * T := by rw [hSi, mul_one]
  have hOTSi : (1 + T) * Si = Si * (1 + T) := by
    rw [add_mul, mul_add, one_mul, mul_one, hTSi]
  refine ⟨?_, ?_, ?_⟩
  · -- unitarity
    rw [conjTranspose_mul, hSiH,
      show Si * (1 + T)ᴴ * ((1 + T) * Si) = Si * ((1 + T)ᴴ * (1 + T)) * Si by noncomm_ring,
      ← hG, ← hSS, show Si * (S * S) * Si = (Si * S) * (S * Si) by noncomm_ring, hSi, hSi',
      one_mul]
  · -- square root
    have hTG : T * G = (1 + T) * (1 + T) := by
      rw [hGexp, mul_add, mul_add, mul_add, hT']; noncomm_ring
    calc (1 + T) * Si * ((1 + T) * Si) = (1 + T) * (Si * (1 + T)) * Si := by noncomm_ring
      _ = (1 + T) * ((1 + T) * Si) * Si := by rw [← hOTSi]
      _ = ((1 + T) * (1 + T)) * (Si * Si) := by noncomm_ring
      _ = (T * G) * (Si * Si) := by rw [hTG]
      _ = T * (S * S) * (Si * Si) := by rw [← hSS]
      _ = T * (S * (S * Si)) * Si := by noncomm_ring
      _ = T * S * Si := by rw [hSi, mul_one]
      _ = T := by rw [mul_assoc, hSi, mul_one]
  · -- real part
    rw [conjTranspose_mul, hSiH, hOTSi,
      show Si * (1 + T) + Si * (1 + T)ᴴ = Si * ((1 + T) + (1 + T)ᴴ) by noncomm_ring]
    have : (1 + T) + (1 + T)ᴴ = G := by
      rw [hGexp, conjTranspose_add, conjTranspose_one]; abel
    rw [this, ← hSS, show Si * (S * S) = (Si * S) * S by noncomm_ring, hSi', one_mul]

/-- **The principal unitary square root, UNCONDITIONALLY.**  Every unitary `T` has a unitary
square root `Q` with `Q + Qᴴ = √((1+T)ᴴ(1+T)) ⪰ 0` — no invertibility hypothesis.

`unitary_sqrt_of_polar` needs `S := √((1+T)ᴴ(1+T))` invertible, because it inverts it. That is
avoided by using the **Moore–Penrose** inverse instead. Writing `Π` for the spectral projection of
`S` at `0` and `W` for the pseudo-inverse,

    Q := (1+T) W + i • Π

works: on `ran S` it is the old `(1+T)S⁻¹`, and on `ker S` — where `T = -1` — it is `i`, a square
root of `-1` with vanishing real part.

Both `Π` and `W` come from the **real** continuous functional calculus of the selfadjoint `S`,
applied to the discontinuous functions `x ↦ [x = 0]` and `x ↦ [x ≠ 0]·x⁻¹`. That is legitimate
because the spectrum of a *matrix* is **finite** (`finite_real_spectrum`), so every function on it
is `ContinuousOn` (`Set.Finite.continuousOn`). No spectral theorem for unitaries is needed. -/
theorem exists_unitary_sqrt (T : Matrix n n ℂ) (hT : Tᴴ * T = 1) (hT' : T * Tᴴ = 1) :
    ∃ Q : Matrix n n ℂ, Qᴴ * Q = 1 ∧ Q * Q = T ∧ Q + Qᴴ = CFC.sqrt ((1 + T)ᴴ * (1 + T)) := by
  obtain ⟨G, hG⟩ : ∃ M, M = (1 + T)ᴴ * (1 + T) := ⟨_, rfl⟩
  have hGp : G.PosSemidef := hG ▸ Matrix.posSemidef_conjTranspose_mul_self _
  have hGexp : G = 1 + 1 + T + Tᴴ := by rw [hG]; exact gram_eq T hT
  obtain ⟨S, hS⟩ : ∃ M, M = CFC.sqrt G := ⟨_, rfl⟩
  have hSpsd : S.PosSemidef := hS ▸ Matrix.PosSemidef.posSemidef_sqrt
  have hSH : Sᴴ = S := hSpsd.isHermitian
  have hSS : S * S = G := by rw [hS]; have := hGp.sq_sqrt; rwa [pow_two] at this
  -- the spectrum of a matrix is finite, so ANY real function may be fed to the calculus
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) :=
    fun f => Set.Finite.continuousOn finite_real_spectrum f
  have hSid : cfc (id : ℝ → ℝ) S = S := cfc_id ℝ S
  obtain ⟨P, hP⟩ : ∃ M, M = cfc (fun x : ℝ => if x = 0 then (1:ℝ) else 0) S := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ M, M = cfc (fun x : ℝ => if x = 0 then (0:ℝ) else x⁻¹) S := ⟨_, rfl⟩
  have hPsa : Pᴴ = P := by
    have h : IsSelfAdjoint P := hP ▸ cfc_predicate (R := ℝ) _ S; exact h
  have hWsa : Wᴴ = W := by
    have h : IsSelfAdjoint W := hW ▸ cfc_predicate (R := ℝ) _ S; exact h
  have hSP : S * P = 0 := by
    rw [hP]; nth_rewrite 1 [← hSid]
    rw [← cfc_mul _ _ S (hc _) (hc _),
      show (fun x : ℝ => id x * (if x = 0 then (1:ℝ) else 0)) = fun _ => (0:ℝ) by
        funext x; by_cases hx : x = 0 <;> simp [hx]]
    simp
  have hPP : P * P = P := by
    rw [hP, ← cfc_mul _ _ S (hc _) (hc _)]
    refine cfc_congr ?_; intro x _; by_cases hx : x = 0 <;> simp [hx]
  have hSW : S * W = 1 - P := by
    rw [hW, hP]; nth_rewrite 1 [← hSid]
    rw [← cfc_mul _ _ S (hc _) (hc _), ← cfc_one (R := ℝ) S, ← cfc_sub _ _ S (hc _) (hc _)]
    refine cfc_congr ?_; intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, mul_inv_cancel₀ hx]
  have hWP : W * P = 0 := by
    rw [hW, hP, ← cfc_mul _ _ S (hc _) (hc _),
      show (fun x : ℝ => (if x = 0 then (0:ℝ) else x⁻¹) * (if x = 0 then (1:ℝ) else 0))
        = fun _ => (0:ℝ) by funext x; by_cases hx : x = 0 <;> simp [hx]]
    simp
  have hWS : W * S = 1 - P := by
    have h := congrArg conjTranspose hSW
    rwa [conjTranspose_mul, hWsa, hSH, conjTranspose_sub, conjTranspose_one, hPsa] at h
  have hPS : P * S = 0 := by
    have h := congrArg conjTranspose hSP
    rwa [conjTranspose_mul, hPsa, hSH, conjTranspose_zero] at h
  have hPW : P * W = 0 := by
    have h := congrArg conjTranspose hWP
    rwa [conjTranspose_mul, hPsa, hWsa, conjTranspose_zero] at h
  -- `S` commutes with `T`, hence so do the two functions of `S`
  have hST : Commute S T := by
    have h : T * S = S * T := by rw [hS, hG]; exact sqrt_comm T hT hT'
    exact h.symm
  have hTW : T * W = W * T := (hW ▸ (Commute.cfc_real hST _ : Commute (cfc _ S) T)).symm
  have hTP : T * P = P * T := (hP ▸ (Commute.cfc_real hST _ : Commute (cfc _ S) T)).symm
  -- from here it is pure algebra
  have hGG : (1 + T)ᴴ * (1 + T) = G := hG.symm
  have h1TP : (1 + T) * P = 0 := by
    refine conjTranspose_mul_self_eq_zero.mp ?_
    rw [conjTranspose_mul, hPsa,
      show P * (1 + T)ᴴ * ((1 + T) * P) = P * ((1 + T)ᴴ * (1 + T)) * P by noncomm_ring,
      hGG, ← hSS, show P * (S * S) * P = (P * S) * (S * P) by noncomm_ring, hPS, zero_mul]
  have hTPn : T * P = -P := by
    have h := h1TP; rw [add_mul, one_mul] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  have hPTH : P * Tᴴ = -P := by
    have h := congrArg conjTranspose hTPn
    rwa [conjTranspose_mul, hPsa, conjTranspose_neg, hPsa] at h
  have hTHP : Tᴴ * P = -P := by
    have hcc : P * Tᴴ = Tᴴ * P := by
      have h := congrArg conjTranspose hTP
      rwa [conjTranspose_mul, conjTranspose_mul, hPsa] at h
    rw [← hcc, hPTH]
  have hPTn : P * T = -P := by rw [← hTP, hTPn]
  have hSWc : S * W = W * S := hSW.trans hWS.symm
  have hWcomm : (1 + T) * W = W * (1 + T) := by rw [add_mul, mul_add, one_mul, mul_one, hTW]
  have hPidem : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hPP]; noncomm_ring
  have hsq : (1 + T) * (1 + T) = T * G := by
    rw [hGexp, mul_add, mul_add, mul_add, hT']; noncomm_ring
  have hSSWW : (S * W) * (S * W) = (S * S) * (W * W) := by
    rw [show (S * W) * (S * W) = S * (W * S) * W by noncomm_ring, ← hSWc]; noncomm_ring
  have hVV : ((1 + T) * W) * ((1 + T) * W) = T + P := by
    calc ((1 + T) * W) * ((1 + T) * W)
        = (1 + T) * (W * (1 + T)) * W := by noncomm_ring
      _ = (1 + T) * ((1 + T) * W) * W := by rw [hWcomm]
      _ = ((1 + T) * (1 + T)) * (W * W) := by noncomm_ring
      _ = T * ((S * S) * (W * W)) := by rw [hsq, ← hSS]; noncomm_ring
      _ = T * ((S * W) * (S * W)) := by rw [hSSWW]
      _ = T * (1 - P) := by rw [hSW, hPidem]
      _ = T + P := by rw [mul_sub, mul_one, hTPn]; abel
  have hVN : ((1 + T) * W) * (Complex.I • P) = 0 := by
    rw [mul_smul_comm, show (1 + T) * W * P = (1 + T) * (W * P) by noncomm_ring, hWP,
      mul_zero, smul_zero]
  have hNV : (Complex.I • P) * ((1 + T) * W) = 0 := by
    rw [smul_mul_assoc, show P * ((1 + T) * W) = (P * (1 + T)) * W by noncomm_ring,
      show P * (1 + T) = 0 by rw [mul_add, mul_one, hPTn]; abel, zero_mul, smul_zero]
  have hNN : (Complex.I • P) * (Complex.I • P) = -P := by
    rw [smul_mul_smul_comm, hPP, Complex.I_mul_I, neg_one_smul]
  have hVH : ((1 + T) * W)ᴴ = W * (1 + Tᴴ) := by
    rw [conjTranspose_mul, hWsa, conjTranspose_add, conjTranspose_one]
  have hNH : (Complex.I • P)ᴴ = -(Complex.I • P) := by
    rw [conjTranspose_smul, hPsa]; simp
  have hVHV : ((1 + T) * W)ᴴ * ((1 + T) * W) = 1 - P := by
    rw [hVH, show W * (1 + Tᴴ) * ((1 + T) * W) = W * ((1 + T)ᴴ * (1 + T)) * W by
      rw [conjTranspose_add, conjTranspose_one]; noncomm_ring, hGG, ← hSS,
      show W * (S * S) * W = (W * S) * (S * W) by noncomm_ring, hWS, hSW, hPidem]
  have hVHN : ((1 + T) * W)ᴴ * (Complex.I • P) = 0 := by
    rw [hVH, mul_smul_comm, show W * (1 + Tᴴ) * P = W * ((1 + Tᴴ) * P) by noncomm_ring,
      show (1 + Tᴴ) * P = 0 by rw [add_mul, one_mul, hTHP]; abel, mul_zero, smul_zero]
  have hVVH : ((1 + T) * W) + ((1 + T) * W)ᴴ = S := by
    rw [hVH, hWcomm, show W * (1 + T) + W * (1 + Tᴴ) = W * (1 + 1 + T + Tᴴ) by noncomm_ring,
      ← hGexp, ← hSS, show W * (S * S) = (W * S) * S by noncomm_ring, hWS, sub_mul, one_mul, hPS,
      sub_zero]
  refine ⟨(1 + T) * W + Complex.I • P, ?_, ?_, ?_⟩
  · rw [conjTranspose_add, add_mul, mul_add, mul_add, hVHV, hVHN, hNH, neg_mul, hNV, neg_zero,
      neg_mul, hNN, neg_neg]
    abel
  · rw [add_mul, mul_add, mul_add, hVV, hVN, hNV, hNN]; abel
  · rw [← hG, ← hS, conjTranspose_add,
      show (1 + T) * W + Complex.I • P + (((1 + T) * W)ᴴ + (Complex.I • P)ᴴ)
        = ((1 + T) * W + ((1 + T) * W)ᴴ) + (Complex.I • P + (Complex.I • P)ᴴ) by abel,
      hVVH, hNH]
    abel

/-! ### The nuclear norm along a polar decomposition -/

/-- `‖W S‖_* = tr S` for `W` unitary and `S ⪰ 0`. -/
theorem nucNorm_of_polar (M W S : Matrix n n ℂ) (hW : Wᴴ * W = 1) (hS : S.PosSemidef)
    (hM : M = W * S) : nucNorm M = S.trace.re := by
  have hSH : Sᴴ = S := hS.isHermitian
  have hgram : Mᴴ * M = S ^ 2 := by
    rw [hM, conjTranspose_mul, hSH,
      show S * Wᴴ * (W * S) = S * (Wᴴ * W) * S by noncomm_ring, hW, mul_one, pow_two]
  have hsq : CFC.sqrt (S ^ 2) = S :=
    ((hS.eq_sqrt_iff_sq_eq (Matrix.PosSemidef.pow hS 2)).mpr rfl).symm
  rw [nucNorm, hgram, hsq]

/-- **Step 2 (the affine minorant).**  For any unitary `W`, any unitary `V` and any `S ⪰ 0`,
`Re tr(Wᴴ (V S)) ≤ ‖V S‖_*`.

This is the only inequality in the whole proof.  Applied with `V S` the polar decomposition of
`1 + R'E` at a competitor `R'`, it produces an affine function of `R'` lying below the objective
and touching it at the maximiser. -/
theorem nucNorm_ge_re_trace (W V S : Matrix n n ℂ) (hW : Wᴴ * W = 1) (hV : Vᴴ * V = 1)
    (hS : S.PosSemidef) : (Wᴴ * (V * S)).trace.re ≤ nucNorm (V * S) := by
  rw [nucNorm_of_polar (V * S) V S hV hS rfl]
  have hZ : (Wᴴ * V)ᴴ * (Wᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose,
      show Vᴴ * W * (Wᴴ * V) = Vᴴ * (W * Wᴴ) * V by noncomm_ring]
    rw [Matrix.mul_eq_one_comm.mpr hW, mul_one, hV]
  have := re_trace_mul_le (Wᴴ * V) S hZ hS
  rwa [show Wᴴ * V * S = Wᴴ * (V * S) by noncomm_ring] at this

/-- **The affine minorant, unconditionally.**  `Re tr(Wᴴ X) ≤ ‖X‖_*` for every `X` and every
unitary `W` — no polar decomposition of `X` required.

For `ε > 0` the *regularised* polar factor `X (√(XᴴX) + ε)⁻¹` is a contraction for every `X`,
singular or not (a genuine unitary polar factor would need a spectral theorem for normal
matrices, which Mathlib does not have).  Lemma CS for contractions then gives
`Re tr(WᴴX) ≤ tr √(XᴴX) + ε·n`, and `ε ↓ 0`. -/
theorem nucNorm_ge_re_trace_gen (W X : Matrix n n ℂ) (hW : Wᴴ * W = 1) :
    (Wᴴ * X).trace.re ≤ nucNorm X := by
  have hWW : W * Wᴴ = 1 := Matrix.mul_eq_one_comm.mpr hW
  obtain ⟨K, hKdef⟩ : ∃ M, M = CFC.sqrt (Xᴴ * X) := ⟨_, rfl⟩
  have hKp : K.PosSemidef := hKdef ▸ Matrix.PosSemidef.posSemidef_sqrt
  have hKK : K * K = Xᴴ * X := by
    have := (Matrix.posSemidef_conjTranspose_mul_self X).sq_sqrt
    rw [pow_two] at this; rw [hKdef]; exact this
  have key : ∀ ε : ℝ, 0 < ε → (Wᴴ * X).trace.re ≤ K.trace.re + ε * (Fintype.card n) := by
    intro ε hε
    obtain ⟨G, hG⟩ : ∃ M : Matrix n n ℂ, M = (ε:ℂ)^2 • 1 + (2*ε:ℂ) • K := ⟨_, rfl⟩
    obtain ⟨Kε, hKε⟩ : ∃ M : Matrix n n ℂ, M = (ε:ℂ) • 1 + K := ⟨_, rfl⟩
    have hKεpd : Kε.PosDef := by
      rw [hKε]
      exact (Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast hε)).add_posSemidef hKp
    obtain ⟨u, hu⟩ := hKεpd.isUnit
    obtain ⟨Kεi, hKεi⟩ : ∃ M : Matrix n n ℂ, M = ↑u⁻¹ := ⟨_, rfl⟩
    have h1 : Kε * Kεi = 1 := by rw [hKεi, ← hu]; simp
    have h2 : Kεi * Kε = 1 := by rw [hKεi, ← hu]; simp
    have hKεH : Kεᴴ = Kε := hKεpd.posSemidef.isHermitian
    have hKεiH : Kεiᴴ = Kεi := by
      have ha : Kεiᴴ * Kε = 1 := by
        have := congrArg conjTranspose h1
        rwa [conjTranspose_mul, conjTranspose_one, hKεH] at this
      calc Kεiᴴ = Kεiᴴ * (Kε * Kεi) := by rw [h1, mul_one]
        _ = (Kεiᴴ * Kε) * Kεi := by noncomm_ring
        _ = Kεi := by rw [ha, one_mul]
    obtain ⟨Z, hZ⟩ : ∃ M : Matrix n n ℂ, M = Wᴴ * (X * Kεi) := ⟨_, rfl⟩
    have hgap : G.PosSemidef := by
      rw [hG]
      refine Matrix.PosSemidef.add (Matrix.PosSemidef.smul Matrix.PosSemidef.one (by positivity))
        (Matrix.PosSemidef.smul hKp ?_)
      rw [show (2:ℂ) * (ε:ℂ) = ((2*ε : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by positivity : (0:ℝ) ≤ 2*ε)
    have hcontr : (1 - Zᴴ * Z).PosSemidef := by
      have hZZ : Zᴴ * Z = Kεi * (K * K) * Kεi := by
        rw [hZ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hKεiH, hKK,
          show Kεi * Xᴴ * W * (Wᴴ * (X * Kεi)) = Kεi * Xᴴ * (W * Wᴴ) * (X * Kεi) by noncomm_ring,
          hWW, mul_one]
        noncomm_ring
      have hone : Kεi * (Kε * Kε) * Kεi = 1 := by
        rw [show Kεi * (Kε * Kε) * Kεi = (Kεi * Kε) * (Kε * Kεi) by noncomm_ring, h1, h2, one_mul]
      have hKK' : Kε * Kε = K * K + G := by
        subst hKε hG
        have h : ((ε:ℂ) • (1:Matrix n n ℂ) + K) * ((ε:ℂ) • 1 + K)
            = ((ε:ℂ)*(ε:ℂ)) • (1:Matrix n n ℂ) + (ε:ℂ) • K + ((ε:ℂ) • K + K * K) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
            smul_smul]
        rw [h]; module
      have hsplit : (1 : Matrix n n ℂ) - Kεi * (K * K) * Kεi = Kεiᴴ * G * Kεi := by
        rw [hKεiH]
        calc (1 : Matrix n n ℂ) - Kεi * (K * K) * Kεi
            = Kεi * (Kε * Kε) * Kεi - Kεi * (K * K) * Kεi := by rw [hone]
          _ = Kεi * (K * K + G) * Kεi - Kεi * (K * K) * Kεi := by rw [hKK']
          _ = Kεi * G * Kεi := by noncomm_ring
      rw [hZZ, hsplit]
      exact hgap.conjTranspose_mul_mul_same _
    have hmain := re_trace_mul_le_contraction Z Kε hcontr hKεpd.posSemidef
    have heq : Z * Kε = Wᴴ * X := by
      rw [hZ, show Wᴴ * (X * Kεi) * Kε = Wᴴ * (X * (Kεi * Kε)) by noncomm_ring, h2, mul_one]
    rw [heq] at hmain
    refine hmain.trans_eq ?_
    rw [hKε, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Complex.add_re, smul_eq_mul]
    simp [Complex.mul_re]; ring
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0:ℝ) < (Fintype.card n : ℝ) + 1 := by positivity
  have hk := key (δ / ((Fintype.card n : ℝ) + 1)) (by positivity)
  have hb : δ / ((Fintype.card n : ℝ) + 1) * (Fintype.card n) ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card n), hδ.le]
  calc (Wᴴ * X).trace.re
      ≤ K.trace.re + δ / ((Fintype.card n : ℝ) + 1) * (Fintype.card n) := hk
    _ ≤ nucNorm X + δ := by rw [nucNorm, ← hKdef]; linarith

/-! ### Step 3: the Ky Fan first-order condition

`P` maximises `P' ↦ Re tr(Γ P')` over the projections of its own trace ⟹ `[P, Γ] = 0`.

The perturbations used are `P ↦ (1+u²)⁻¹ (1+uS) P (1-uS)` for `S` a *skew-Hermitian symmetry*
(`Sᴴ = -S`, `S² = -1`); `(1-uS)(1+uS) = (1+u²)·1` makes these projections of the same trace,
with a **polynomial** dependence on the real parameter `u`.  Maximality then reads
`u·b ≤ u²·M`, forcing `b = Re tr(Γ[S,P]) = 0`.  Taking `S = -i(1 - t·xxᴴ)` (a Householder
reflection, rescaled) turns this into the vanishing of the quadratic form of `[P,Γ]`. -/

theorem trace_mul_vecMulVec (K : Matrix n n ℂ) (x : n → ℂ) :
    (K * Matrix.vecMulVec x (star x)).trace = star x ⬝ᵥ (K *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem vecMulVec_sq (x : n → ℂ) :
    Matrix.vecMulVec x (star x) * Matrix.vecMulVec x (star x)
      = (star x ⬝ᵥ x) • Matrix.vecMulVec x (star x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply, Matrix.smul_apply,
    smul_eq_mul, dotProduct]
  rw [Finset.sum_congr rfl (fun k _ => show x i * star (x k) * (x k * star (x j))
      = (star (x k) * x k) * (x i * star (x j)) from by ring), ← Finset.sum_mul]

theorem vecMulVec_herm (x : n → ℂ) :
    (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
  ext i j; simp [Matrix.vecMulVec, Matrix.conjTranspose_apply]; ring

/-- Conjugating a projection by `1 + uS`, `S` a skew-Hermitian symmetry, again gives a
projection of the same trace, after the scalar normalisation `(1+u²)⁻¹`. -/
theorem proj_perturb (P S : Matrix n n ℂ) (hP : Pᴴ = P) (hP2 : P * P = P)
    (hS : Sᴴ = -S) (hS2 : S * S = -1) (u : ℝ) :
    (((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)))ᴴ
        = ((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)) ∧
      (((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)))
        * (((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)))
        = ((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)) ∧
      (((1 + u^2 : ℝ) : ℂ)⁻¹ • ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S))).trace = P.trace := by
  have hne : ((1 + u^2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; positivity
  have hkey : (1 - (u:ℂ) • S) * (1 + (u:ℂ) • S) = ((1 + u^2 : ℝ) : ℂ) • 1 := by
    have expand : (1 - (u:ℂ) • S) * (1 + (u:ℂ) • S) = 1 - ((u:ℂ)*(u:ℂ)) • (S * S) := by
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    rw [expand, hS2]; push_cast; module
  refine ⟨?_, ?_, ?_⟩
  · simp only [conjTranspose_smul, conjTranspose_mul, conjTranspose_sub, conjTranspose_add,
      conjTranspose_one, hP, hS, Complex.star_def, map_inv₀, Complex.conj_ofReal,
      smul_neg, sub_neg_eq_add]
    congr 1
    noncomm_ring
  · rw [smul_mul_smul_comm,
      show (1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S) * ((1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S))
        = (1 + (u:ℂ) • S) * P * ((1 - (u:ℂ) • S) * (1 + (u:ℂ) • S)) * P * (1 - (u:ℂ) • S) by
          noncomm_ring, hkey]
    rw [show (1 + (u:ℂ) • S) * P * (((1 + u^2 : ℝ) : ℂ) • (1:Matrix n n ℂ)) * P * (1 - (u:ℂ) • S)
      = ((1 + u^2 : ℝ) : ℂ) • ((1 + (u:ℂ) • S) * (P * P) * (1 - (u:ℂ) • S)) by
        simp only [mul_smul_comm, smul_mul_assoc, mul_one]; noncomm_ring, hP2, smul_smul,
      show ((1 + u^2 : ℝ) : ℂ)⁻¹ * ((1 + u^2 : ℝ) : ℂ)⁻¹ * ((1 + u^2 : ℝ) : ℂ)
        = ((1 + u^2 : ℝ) : ℂ)⁻¹ by field_simp]
  · rw [Matrix.trace_smul,
      show (1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S) = (1 + (u:ℂ) • S) * (P * (1 - (u:ℂ) • S)) by
        noncomm_ring,
      Matrix.trace_mul_comm,
      show P * (1 - (u:ℂ) • S) * (1 + (u:ℂ) • S) = P * ((1 - (u:ℂ) • S) * (1 + (u:ℂ) • S)) by
        noncomm_ring, hkey, mul_smul_comm, mul_one, Matrix.trace_smul, smul_smul,
      inv_mul_cancel₀ hne, one_smul]

/-- Maximality along the `S`-perturbation family is the vanishing of a first-order coefficient. -/
theorem stationary_of_max (Γ P S : Matrix n n ℂ) (hP : Pᴴ = P) (hP2 : P * P = P)
    (hS : Sᴴ = -S) (hS2 : S * S = -1)
    (hmax : ∀ P' : Matrix n n ℂ, P'ᴴ = P' → P' * P' = P' → P'.trace = P.trace →
        (Γ * P').trace.re ≤ (Γ * P).trace.re) :
    (Γ * (S * P - P * S)).trace.re = 0 := by
  have hre : ∀ (r : ℝ) (z : ℂ), ((r:ℂ) * z).re = r * z.re := by
    intro r z; simp [Complex.mul_re]
  obtain ⟨a, ha⟩ : ∃ t : ℝ, t = (Γ * P).trace.re := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ t : ℝ, t = (Γ * (S * P - P * S)).trace.re := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ t : ℝ, t = (Γ * (S * P * S)).trace.re := ⟨_, rfl⟩
  have hineq : ∀ u : ℝ, u * b ≤ u^2 * (a + c) := by
    intro u
    have hpos : (0:ℝ) < 1 + u^2 := by positivity
    have hpp := proj_perturb P S hP hP2 hS hS2 u
    have hle := hmax _ hpp.1 hpp.2.1 hpp.2.2
    have hMu : (1 + (u:ℂ) • S) * P * (1 - (u:ℂ) • S)
        = P + (u:ℂ) • (S * P - P * S) - ((u:ℂ)*(u:ℂ)) • (S * P * S) := by
      simp only [add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_sub]
      module
    have htr : (Γ * (P + (u:ℂ) • (S*P - P*S) - ((u:ℂ)*(u:ℂ)) • (S*P*S))).trace
        = (Γ*P).trace + (u:ℂ) * (Γ*(S*P-P*S)).trace - ((u:ℂ)*(u:ℂ)) * (Γ*(S*P*S)).trace := by
      rw [mul_sub, mul_add, mul_smul_comm, mul_smul_comm, Matrix.trace_sub, Matrix.trace_add,
        Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, hMu, htr, ← Complex.ofReal_inv, hre] at hle
    simp only [Complex.add_re, Complex.sub_re] at hle
    rw [hre, show ((u:ℂ)*(u:ℂ)) = ((u*u : ℝ) : ℂ) by push_cast; ring, hre, ← ha, ← hb, ← hc] at hle
    rw [inv_mul_le_iff₀ hpos] at hle
    nlinarith [hle]
  have hbzero : b = 0 := by
    have hall : ∀ δ : ℝ, 0 < δ → |b| ≤ δ := by
      intro δ hδ
      obtain ⟨M, hM⟩ : ∃ t : ℝ, t = a + c := ⟨_, rfl⟩
      obtain ⟨u, hu⟩ : ∃ t : ℝ, t = δ / (|M| + 1) := ⟨_, rfl⟩
      have hM1 : (0:ℝ) < |M| + 1 := by positivity
      have hupos : 0 < u := by rw [hu]; positivity
      have e1 : u * b ≤ u^2 * M := by rw [hM]; exact hineq u
      have e2 : -(u * b) ≤ u^2 * M := by
        have h := hineq (-u); rw [← hM] at h; nlinarith [h]
      have h3 : u * |b| ≤ u^2 * |M| := by
        rcases abs_cases b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          nlinarith [le_abs_self M, sq_nonneg u, e1, e2]
      have h4 : |b| ≤ u * |M| := le_of_mul_le_mul_left (by nlinarith [h3]) hupos
      calc |b| ≤ u * |M| := h4
        _ = δ * |M| / (|M| + 1) := by rw [hu]; ring
        _ ≤ δ := by rw [div_le_iff₀ hM1]; nlinarith [abs_nonneg M, hδ.le]
    have hle0 : |b| ≤ 0 := le_of_forall_pos_le_add fun δ hδ => by linarith [hall δ hδ]
    exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg b))
  rw [← hb]; exact hbzero

/-- The rescaled Householder reflection attached to a nonzero vector, as a skew-Hermitian
symmetry, together with the trace formula that exposes the quadratic form. -/
theorem householder_symm (x : n → ℂ) (hx : x ≠ 0) :
    ∃ (S : Matrix n n ℂ) (c : ℝ), c ≠ 0 ∧ Sᴴ = -S ∧ S * S = -1 ∧
      ∀ K : Matrix n n ℂ, K.trace = 0 →
        (K * S).trace = (c:ℂ) * Complex.I * (star x ⬝ᵥ (K *ᵥ x)) := by
  obtain ⟨s, hs⟩ : ∃ z, z = star x ⬝ᵥ x := ⟨_, rfl⟩
  have hsnz : s ≠ 0 := by rw [hs]; exact fun h => hx (dotProduct_star_self_eq_zero.mp h)
  have hs0 : (0:ℂ) ≤ s := by rw [hs]; exact dotProduct_star_self_nonneg x
  have hsim : s.im = 0 := ((Complex.le_def.mp hs0).2).symm
  have hsre : (s.re : ℂ) = s := by
    apply Complex.ext <;> simp [hsim]
  have hsrenz : s.re ≠ 0 := fun h => hsnz (by rw [← hsre, h]; simp)
  have hsstar : star s = s := by rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hsim
  obtain ⟨t, ht⟩ : ∃ z : ℂ, z = 2 / s := ⟨_, rfl⟩
  have htstar : star t = t := by rw [ht, star_div₀, hsstar]; norm_num
  obtain ⟨A, hA⟩ : ∃ M, M = Matrix.vecMulVec x (star x) := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by rw [hA]; exact vecMulVec_herm x
  have hAA : A * A = s • A := by rw [hA, hs]; exact vecMulVec_sq x
  obtain ⟨J, hJ⟩ : ∃ M, M = (1 : Matrix n n ℂ) - t • A := ⟨_, rfl⟩
  have hJH : Jᴴ = J := by
    rw [hJ, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hAH, htstar]
  have hJJ : J * J = 1 := by
    have hexp : J * J = 1 - (t+t) • A + (t*t) • (A*A) := by
      rw [hJ]
      simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
      module
    rw [hexp, hAA, smul_smul, show t*t*s = t + t by rw [ht]; field_simp; ring]
    abel
  refine ⟨(-Complex.I) • J, 2 / s.re, div_ne_zero two_ne_zero hsrenz, ?_, ?_, ?_⟩
  · rw [conjTranspose_smul, hJH]; simp
  · rw [smul_mul_smul_comm, hJJ]; simp [Complex.I_mul_I]
  · intro K hKtr
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, hJ, mul_sub, mul_one, Matrix.trace_sub,
      hKtr, mul_smul_comm, Matrix.trace_smul, smul_eq_mul, zero_sub, hA,
      trace_mul_vecMulVec]
    rw [show ((2 / s.re : ℝ) : ℂ) = t by
      rw [Complex.ofReal_div, hsre, ht]; norm_num]
    ring

/-- The quadratic form of a skew-Hermitian matrix is purely imaginary. -/
theorem quad_skew_re_zero (K : Matrix n n ℂ) (hKskew : Kᴴ = -K) (x : n → ℂ) :
    (star x ⬝ᵥ (K *ᵥ x)).re = 0 := by
  obtain ⟨A, hA⟩ : ∃ M, M = Matrix.vecMulVec x (star x) := ⟨_, rfl⟩
  have hAH : Aᴴ = A := by rw [hA]; exact vecMulVec_herm x
  have hq : (K * A).trace = star x ⬝ᵥ (K *ᵥ x) := by rw [hA]; exact trace_mul_vecMulVec K x
  have hconj : (starRingEnd ℂ) ((K*A).trace) = -((K*A).trace) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, hAH, hKskew,
      show A * -K = -(A*K) by noncomm_ring, Matrix.trace_neg, Matrix.trace_mul_comm]
  have hac := Complex.add_conj ((K*A).trace)
  rw [hconj, add_neg_cancel] at hac
  rw [← hq]
  simpa using hac.symm

/-- **Step 3 (Ky Fan).**  If a projection `P` maximises `P' ↦ Re tr(Γ P')` over all projections
of the same trace, then `P` commutes with the Hermitian matrix `Γ`. -/
theorem kyFan_commute (Γ P : Matrix n n ℂ) (hΓ : Γᴴ = Γ) (hP : Pᴴ = P) (hP2 : P * P = P)
    (hmax : ∀ P' : Matrix n n ℂ, P'ᴴ = P' → P' * P' = P' → P'.trace = P.trace →
        (Γ * P').trace.re ≤ (Γ * P).trace.re) :
    P * Γ = Γ * P := by
  obtain ⟨K, hK⟩ : ∃ M, M = P * Γ - Γ * P := ⟨_, rfl⟩
  have hKskew : Kᴴ = -K := by
    rw [hK, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hΓ, hP]; abel
  have hKtr : K.trace = 0 := by
    rw [hK, Matrix.trace_sub, Matrix.trace_mul_comm]; exact sub_self _
  have hKS : ∀ S : Matrix n n ℂ, Sᴴ = -S → S * S = -1 → (K * S).trace.re = 0 := by
    intro S hS hS2
    have h := stationary_of_max Γ P S hP hP2 hS hS2 hmax
    have heq : (Γ * (S * P - P * S)).trace = (K * S).trace := by
      rw [hK, sub_mul, Matrix.trace_sub, mul_sub, Matrix.trace_sub]
      congr 1
      · rw [show Γ * (S * P) = (Γ * S) * P by noncomm_ring, Matrix.trace_mul_comm,
          show P * (Γ * S) = P * Γ * S by noncomm_ring]
      · rw [show Γ * (P * S) = Γ * P * S by noncomm_ring]
    rw [← heq]; exact h
  have hquad : ∀ x : n → ℂ, star x ⬝ᵥ (K *ᵥ x) = 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨S, c, hc, hSsk, hSsq, hStr⟩ := householder_symm x hx
    have h0 := hKS S hSsk hSsq
    rw [hStr K hKtr] at h0
    have him : (star x ⬝ᵥ (K *ᵥ x)).im = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at h0
      have : c * (star x ⬝ᵥ (K *ᵥ x)).im = 0 := by linarith [h0]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hc
      · exact h
    exact Complex.ext (quad_skew_re_zero K hKskew x) him
  -- a skew-Hermitian matrix with vanishing quadratic form is zero
  obtain ⟨H, hH⟩ : ∃ M, M = Complex.I • K := ⟨_, rfl⟩
  have hHH : Hᴴ = H := by rw [hH, conjTranspose_smul, hKskew]; simp
  have hHq : ∀ x : n → ℂ, star x ⬝ᵥ (H *ᵥ x) = 0 := by
    intro x; rw [hH]; simp [Matrix.smul_mulVec, dotProduct_smul, hquad x]
  have h1 : H.PosSemidef :=
    Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHH, fun x => by rw [hHq x]⟩
  have h2 : (-H).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
    · show (-H)ᴴ = -H
      rw [conjTranspose_neg, hHH]
    · rw [Matrix.neg_mulVec, dotProduct_neg, hHq x]; simp
  have hz : H = 0 :=
    le_antisymm (neg_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr h2))
      (Matrix.nonneg_iff_posSemidef.mpr h1)
  have hKz : K = 0 := by
    have : Complex.I • K = 0 := by rw [← hH, hz]
    simpa [Complex.I_ne_zero] using this
  exact sub_eq_zero.mp (hK ▸ hKz)

/-! ### Steps 4–6: stationarity forces the commutation

Throughout, `J := 2P - 1` is the *symmetry* attached to the spectral projection `P`
(`Jᴴ = J`, `J² = 1`), and `C := (λ-μ) Rᴴ = z + wJ` with `z` purely imaginary and `w` real.
Working with `J` instead of `P` removes every block-matrix computation: "off-diagonal in the
`P`-decomposition" becomes "anticommutes with `J`", and Step 4's `Γ₁₂ = 0` becomes a one-line
cancellation. -/

/-- PSD matrices with equal squares are equal. -/
theorem psd_eq_of_sq_eq {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h : X ^ 2 = Y ^ 2) : X = Y := by
  rw [(hX.eq_sqrt_iff_sq_eq (hX.pow 2)).mpr rfl, h,
    ← (hY.eq_sqrt_iff_sq_eq (hY.pow 2)).mpr rfl]

/-- **Step 4.**  With `C = z + wJ` (`z` imaginary, `w` real) invertible and `D` anticommuting
with `J`, the relation `C D + Dᴴ Cᴴ = 0` forces `D` selfadjoint.

Blockwise, `D = JQJ - Q` is the off-diagonal part of `Q` doubled, and this says `Q₁₂ = Q₂₁ᴴ`. -/
theorem step4_selfadjoint (J D C Ci : Matrix n n ℂ) (z w : ℂ)
    (hC : C = z • (1 : Matrix n n ℂ) + w • J) (hz : star z = -z) (hw : star w = w)
    (hJ : Jᴴ = J) (hJD : J * D = -(D * J)) (hCi : Ci * C = 1)
    (h : C * D + Dᴴ * Cᴴ = 0) : Dᴴ = D := by
  have hCH : Cᴴ = -(z • (1 : Matrix n n ℂ)) + w • J := by
    rw [hC, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hJ,
      hz, hw, neg_smul]
  have hJDH : Dᴴ * J = -(J * Dᴴ) := by
    have := congrArg conjTranspose hJD
    rwa [conjTranspose_mul, conjTranspose_neg, conjTranspose_mul, hJ] at this
  have hslide : Dᴴ * Cᴴ = -(C * Dᴴ) := by
    rw [hCH, hC, mul_add, add_mul]
    simp only [mul_neg, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hJDH]
    module
  have key : C * (D - Dᴴ) = 0 := by rw [mul_sub, ← h, hslide]; abel
  calc Dᴴ = D - (D - Dᴴ) := by abel
    _ = D - 1 * (D - Dᴴ) := by rw [one_mul]
    _ = D - Ci * C * (D - Dᴴ) := by rw [hCi]
    _ = D - Ci * (C * (D - Dᴴ)) := by noncomm_ring
    _ = D := by rw [key, mul_zero, sub_zero]

/-- **Step 5 (the `J`-trick).**  A symmetry `J` fixing the *imaginary* part of a unitary `Q`
with `Q + Qᴴ ⪰ 0` fixes `Q` itself.

No functional calculus: `J(Q+Qᴴ)J` and `Q+Qᴴ` are both PSD with the *same square*, because
`(Q ± Qᴴ)² = Q² + Qᴴ² ± 2`, so uniqueness of the PSD square root identifies them. -/
theorem step5_Jtrick (J Q : Matrix n n ℂ) (hJ : Jᴴ = J) (hJ2 : J * J = 1)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) (hS : (Q + Qᴴ).PosSemidef)
    (himag : J * (Q - Qᴴ) * J = Q - Qᴴ) : J * Q * J = Q := by
  have hsqm : (Q - Qᴴ) * (Q - Qᴴ) + 1 + 1 = Q * Q + Qᴴ * Qᴴ := by
    rw [show (Q - Qᴴ) * (Q - Qᴴ) = Q * Q + Qᴴ * Qᴴ - Q * Qᴴ - Qᴴ * Q by noncomm_ring, hQ, hQ']
    abel
  have hsqp : (Q + Qᴴ) * (Q + Qᴴ) = Q * Q + Qᴴ * Qᴴ + 1 + 1 := by
    rw [show (Q + Qᴴ) * (Q + Qᴴ) = Q * Q + Qᴴ * Qᴴ + Q * Qᴴ + Qᴴ * Q by noncomm_ring, hQ, hQ']
  have hconj : ∀ X : Matrix n n ℂ, (J * X * J) * (J * X * J) = J * (X * X) * J := by
    intro X
    rw [show J * X * J * (J * X * J) = J * X * (J * J) * X * J by noncomm_ring, hJ2]
    noncomm_ring
  have hfix2 : J * (Q * Q + Qᴴ * Qᴴ) * J = Q * Q + Qᴴ * Qᴴ := by
    have h1 : J * ((Q - Qᴴ) * (Q - Qᴴ)) * J = (Q - Qᴴ) * (Q - Qᴴ) := by rw [← hconj, himag]
    calc J * (Q * Q + Qᴴ * Qᴴ) * J
        = J * ((Q - Qᴴ) * (Q - Qᴴ) + 1 + 1) * J := by rw [hsqm]
      _ = J * ((Q - Qᴴ) * (Q - Qᴴ)) * J + J * J + J * J := by noncomm_ring
      _ = (Q - Qᴴ) * (Q - Qᴴ) + 1 + 1 := by rw [h1, hJ2]
      _ = Q * Q + Qᴴ * Qᴴ := hsqm
  have hfixsq : (J * (Q + Qᴴ) * J) ^ 2 = (Q + Qᴴ) ^ 2 := by
    rw [pow_two, pow_two, hconj, hsqp]
    calc J * (Q * Q + Qᴴ * Qᴴ + 1 + 1) * J
        = J * (Q * Q + Qᴴ * Qᴴ) * J + J * J + J * J := by noncomm_ring
      _ = Q * Q + Qᴴ * Qᴴ + 1 + 1 := by rw [hfix2, hJ2]
  have hpsd : (J * (Q + Qᴴ) * J).PosSemidef := by
    have := hS.conjTranspose_mul_mul_same J; rwa [hJ] at this
  have hreal : J * (Q + Qᴴ) * J = Q + Qᴴ := psd_eq_of_sq_eq hpsd hS hfixsq
  have hdouble : (2 : ℂ) • (J * Q * J) = (2 : ℂ) • Q := by
    have hsum : J * (Q + Qᴴ) * J + J * (Q - Qᴴ) * J = (Q + Qᴴ) + (Q - Qᴴ) := by
      rw [hreal, himag]
    rw [show J * (Q + Qᴴ) * J + J * (Q - Qᴴ) * J = (2 : ℂ) • (J * Q * J) by
      rw [two_smul]; noncomm_ring,
      show (Q + Qᴴ) + (Q - Qᴴ) = (2 : ℂ) • Q by rw [two_smul]; abel] at hsum
    exact hsum
  exact smul_right_injective _ two_ne_zero hdouble

/-- **Step 6.**  `J` commutes with `Q`, hence with `Q² = R E`; as `J` commutes with `R` and `R`
is invertible, `J` commutes with `E`. -/
theorem step6_commute (E J Q R Ri : Matrix n n ℂ) (hJ2 : J * J = 1)
    (hJQ : J * Q * J = Q) (hQ2 : Q * Q = R * E) (hRJ : R * J = J * R) (hRi : Ri * R = 1) :
    J * E = E * J := by
  have hJQ' : J * Q = Q * J := by
    calc J * Q = J * Q * (J * J) := by rw [hJ2, mul_one]
      _ = (J * Q * J) * J := by noncomm_ring
      _ = Q * J := by rw [hJQ]
  have hJT : J * (R * E) = (R * E) * J := by
    rw [← hQ2]
    calc J * (Q * Q) = (J * Q) * Q := by noncomm_ring
      _ = (Q * J) * Q := by rw [hJQ']
      _ = Q * (J * Q) := by noncomm_ring
      _ = Q * (Q * J) := by rw [hJQ']
      _ = Q * Q * J := by noncomm_ring
  have h2 : R * (J * E) = R * (E * J) := by
    calc R * (J * E) = (R * J) * E := by noncomm_ring
      _ = (J * R) * E := by rw [hRJ]
      _ = J * (R * E) := by noncomm_ring
      _ = (R * E) * J := hJT
      _ = R * (E * J) := by noncomm_ring
  calc J * E = 1 * (J * E) := by rw [one_mul]
    _ = Ri * R * (J * E) := by rw [hRi]
    _ = Ri * (R * (J * E)) := by noncomm_ring
    _ = Ri * (R * (E * J)) := by rw [h2]
    _ = Ri * R * (E * J) := by noncomm_ring
    _ = E * J := by rw [hRi, one_mul]

/-- The bridge from `[J, Γ] = 0` to the hypothesis of Step 4, with `D := JQJ - Q`.
Here `Γ` appears in the doubled form `C Q + Qᴴ Cᴴ = 2 Herm(C Q)`. -/
theorem stat_to_step4 (J Q C : Matrix n n ℂ) (z w : ℂ)
    (hC : C = z • (1 : Matrix n n ℂ) + w • J) (hJ : Jᴴ = J) (hJ2 : J * J = 1)
    (hz : star z = -z) (hw : star w = w)
    (hstat : J * (C * Q + Qᴴ * Cᴴ) * J = C * Q + Qᴴ * Cᴴ) :
    C * (J * Q * J - Q) + (J * Q * J - Q)ᴴ * Cᴴ = 0 := by
  have hCH : Cᴴ = -(z • (1 : Matrix n n ℂ)) + w • J := by
    rw [hC, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hJ,
      hz, hw, neg_smul]
  have hJC : J * C = C * J := by
    rw [hC]; simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hJ2]
  have hJCH : J * Cᴴ = Cᴴ * J := by
    rw [hCH]; simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hJ2,
      mul_neg, neg_mul]
  have hQH : (J * Q * J)ᴴ = J * Qᴴ * J := by
    rw [conjTranspose_mul, conjTranspose_mul, hJ]; noncomm_ring
  have hexp : J * (C * Q + Qᴴ * Cᴴ) * J = C * (J * Q * J) + (J * Q * J)ᴴ * Cᴴ := by
    rw [hQH, mul_add, add_mul]
    congr 1
    · calc J * (C * Q) * J = (J * C) * Q * J := by noncomm_ring
        _ = (C * J) * Q * J := by rw [hJC]
        _ = C * (J * Q * J) := by noncomm_ring
    · calc J * (Qᴴ * Cᴴ) * J = J * Qᴴ * (Cᴴ * J) := by noncomm_ring
        _ = J * Qᴴ * (J * Cᴴ) := by rw [hJCH]
        _ = J * Qᴴ * J * Cᴴ := by noncomm_ring
  rw [hexp] at hstat
  rw [mul_sub, conjTranspose_sub, sub_mul,
    show C * (J * Q * J) - C * Q + ((J * Q * J)ᴴ * Cᴴ - Qᴴ * Cᴴ)
      = (C * (J * Q * J) + (J * Q * J)ᴴ * Cᴴ) - (C * Q + Qᴴ * Cᴴ) by abel, hstat, sub_self]

/-- **Steps 4–6 assembled: stationarity implies commutation.**

If the Hermitian matrix `Γ = Herm(C Q)` (in doubled form `C Q + Qᴴ Cᴴ`) commutes with the
symmetry `J`, then `J` — equivalently the projection `P = (1+J)/2` — commutes with `E`.

This is everything downstream of the first-order condition.  What remains to reach the full
theorem is to *derive* `[J, Γ] = 0` from maximality (Steps 2–3: the affine minorant
`nucNorm_ge_re_trace` followed by Ky Fan). -/
theorem stationary_implies_commute
    (E J Q C Ci R Ri : Matrix n n ℂ) (z w : ℂ)
    (hJ : Jᴴ = J) (hJ2 : J * J = 1)
    (hQ : Qᴴ * Q = 1) (hQ' : Q * Qᴴ = 1) (hSpsd : (Q + Qᴴ).PosSemidef)
    (hQ2 : Q * Q = R * E) (hRJ : R * J = J * R) (hRi : Ri * R = 1)
    (hC : C = z • (1 : Matrix n n ℂ) + w • J) (hz : star z = -z) (hw : star w = w)
    (hCi : Ci * C = 1)
    (hstat : J * (C * Q + Qᴴ * Cᴴ) * J = C * Q + Qᴴ * Cᴴ) :
    J * E = E * J := by
  set D := J * Q * J - Q with hD
  have h4in : C * D + Dᴴ * Cᴴ = 0 := stat_to_step4 J Q C z w hC hJ hJ2 hz hw hstat
  have hJD : J * D = -(D * J) := by
    rw [hD, mul_sub, sub_mul,
      show J * (J * Q * J) = (J * J) * Q * J by noncomm_ring, hJ2, one_mul,
      show (J * Q * J) * J = J * Q * (J * J) by noncomm_ring, hJ2, mul_one]
    abel
  have hDsa : Dᴴ = D := step4_selfadjoint J D C Ci z w hC hz hw hJ hJD hCi h4in
  have himag : J * (Q - Qᴴ) * J = Q - Qᴴ := by
    have hDH : Dᴴ = J * Qᴴ * J - Qᴴ := by
      rw [hD, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hJ]; noncomm_ring
    rw [hDH, hD] at hDsa
    rw [mul_sub, sub_mul,
      show J * Q * J - J * Qᴴ * J
        = (J * Q * J - Q) - (J * Qᴴ * J - Qᴴ) + (Q - Qᴴ) by abel, hDsa, sub_self, zero_add]
  exact step6_commute E J Q R Ri hJ2 (step5_Jtrick J Q hJ hJ2 hQ hQ' hSpsd himag) hQ2 hRJ hRi

/-- The same conclusion phrased for the projection `P = (1+J)/2`. -/
theorem proj_commute_of_symm_commute (E J P : Matrix n n ℂ)
    (hP : (2 : ℂ) • P = J + 1) (h : J * E = E * J) : P * E = E * P := by
  have : (2 : ℂ) • (P * E) = (2 : ℂ) • (E * P) := by
    rw [← smul_mul_assoc, ← mul_smul_comm, hP, add_mul, mul_add, one_mul, mul_one, h]
  exact smul_right_injective _ two_ne_zero this

/-! ### The theorem -/

/-- The algebra of the two-phase unitary `R = λP + μ(1-P)` in terms of `J = 2P-1`.
The last conjunct is what makes `C := (λ-μ)Rᴴ` have the shape `z + wJ` with `z` purely
imaginary and `w` real that Step 4 requires. -/
theorem twoPhase_algebra (lam mu : ℂ) (P R J : Matrix n n ℂ)
    (hlam : star lam * lam = 1) (hmu : star mu * mu = 1) (hP : Pᴴ = P) (hP2 : P * P = P)
    (hR : R = lam • P + mu • (1 - P)) (hJ : J = (2 : ℂ) • P - 1) :
    Rᴴ * R = 1 ∧ R * Rᴴ = 1 ∧ R * J = J * R ∧ Jᴴ = J ∧ J * J = 1 ∧
      (lam - mu) • Rᴴ
        = ((lam - mu) * (star lam + star mu) / 2) • (1 : Matrix n n ℂ)
          + ((lam - mu) * (star lam - star mu) / 2) • J := by
  have hRH : Rᴴ = star lam • P + star mu • (1 - P) := by
    rw [hR, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_sub,
      conjTranspose_one, hP]
  have hPc : P * (1 - P) = 0 ∧ (1 - P) * P = 0 ∧ (1 - P) * (1 - P) = 1 - P := by
    refine ⟨by rw [mul_sub, mul_one, hP2, sub_self], by rw [sub_mul, one_mul, hP2, sub_self], ?_⟩
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hP2]; abel
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRH, hR]
    simp only [add_mul, mul_add, smul_mul_smul_comm, hP2, hPc.1, hPc.2.1, hPc.2.2, hlam, hmu,
      smul_zero, add_zero, zero_add]
    module
  · rw [hRH, hR]
    simp only [add_mul, mul_add, smul_mul_smul_comm, hP2, hPc.1, hPc.2.1, hPc.2.2,
      smul_zero, add_zero, zero_add]
    rw [show lam * star lam = 1 by rw [mul_comm]; exact hlam,
      show mu * star mu = 1 by rw [mul_comm]; exact hmu]
    module
  · rw [hR, hJ]
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
      hP2]
    module
  · rw [hJ, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hP]; norm_num
  · rw [hJ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hP2]
    module
  · rw [hRH, hJ]; module

/-- **THE TWO-PHASE UNITARY ORBIT THEOREM** (maximiser form).

Let `E ∈ U(n)`, let `P` be an orthogonal projection and `λ, μ` unimodular with `λ ≠ μ`, and set
`R = λP + μ(1-P)`.  If `R` **maximises** `‖1 + R'E‖_*` over all `R' = λP' + μ(1-P')` with `P'` a
projection of the same trace as `P`, and if the positive factor
`S = √((1+RE)ᴴ(1+RE))` is invertible, then

  **`P` commutes with `E`.**

The whole proof is finite-dimensional linear algebra:

* `unitary_sqrt_of_polar` builds the unitary square root `Q = (1+RE)S⁻¹`, so `1 + RE = QS` is a
  polar decomposition and `‖1+RE‖_* = Re tr(Qᴴ(1+RE))` **exactly**;
* `nucNorm_ge_re_trace_gen` gives `‖1+R'E‖_* ≥ Re tr(Qᴴ(1+R'E))` for every competitor;
* subtracting, maximality becomes `tr(ΓP') ≤ tr(ΓP)` with `Γ = Herm((λ-μ)EQᴴ)`, a *linear*
  condition;
* `kyFan_commute` turns that into `[P,Γ] = 0`;
* `stationary_implies_commute` (Steps 4–6) upgrades `[P,Γ] = 0` to `[P,E] = 0`.

The invertibility of `S` — equivalently `-1 ∉ spec(RE)` — is the one hypothesis not yet
discharged inside Lean; see `notes/TWO_PHASE_ORBIT_THEOREM.md` §3 Step 6 for its (elementary)
proof by a common-phase perturbation. -/
theorem maximizer_commutes
    (E : Matrix n n ℂ) (hE : Eᴴ * E = 1) (hE' : E * Eᴴ = 1)
    (lam mu : ℂ) (hlam : star lam * lam = 1) (hmu : star mu * mu = 1) (hne : lam ≠ mu)
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hP2 : P * P = P)
    (hmax : ∀ P' : Matrix n n ℂ, P'ᴴ = P' → P' * P' = P' → P'.trace = P.trace →
        nucNorm (1 + (lam • P' + mu • (1 - P')) * E)
          ≤ nucNorm (1 + (lam • P + mu • (1 - P)) * E)) :
    P * E = E * P := by
  obtain ⟨R, hR⟩ : ∃ M, M = lam • P + mu • (1 - P) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ M, M = (2 : ℂ) • P - 1 := ⟨_, rfl⟩
  obtain ⟨hRu, hRu', hRJ, hJH, hJ2, hCform⟩ := twoPhase_algebra lam mu P R J hlam hmu hP hP2 hR hJ
  obtain ⟨T, hT⟩ : ∃ M, M = R * E := ⟨_, rfl⟩
  rw [← hR, ← hT] at hmax
  have hTu : Tᴴ * T = 1 := by
    rw [hT, conjTranspose_mul, show Eᴴ * Rᴴ * (R * E) = Eᴴ * (Rᴴ * R) * E by noncomm_ring,
      hRu, mul_one, hE]
  have hTu' : T * Tᴴ = 1 := by
    rw [hT, conjTranspose_mul, show R * E * (Eᴴ * Rᴴ) = R * (E * Eᴴ) * Rᴴ by noncomm_ring,
      hE', mul_one, hRu']
  obtain ⟨Q, hQu, hQ2, hQS⟩ := exists_unitary_sqrt T hTu hTu'
  obtain ⟨S, hS⟩ : ∃ M, M = CFC.sqrt ((1 + T)ᴴ * (1 + T)) := ⟨_, rfl⟩
  rw [← hS] at hQS
  have hQu' : Q * Qᴴ = 1 := Matrix.mul_eq_one_comm.mpr hQu
  have hSpsd : S.PosSemidef := hS ▸ Matrix.PosSemidef.posSemidef_sqrt
  have hQSpsd : (Q + Qᴴ).PosSemidef := hQS ▸ hSpsd
  -- `1 + T = Q S` is a polar decomposition, straight from `Q² = T` and `Q Qᴴ = 1`
  have hpolar : (1 : Matrix n n ℂ) + T = Q * S := by
    rw [← hQS, mul_add, hQ2, hQu']; abel
  have hval : nucNorm (1 + T) = S.trace.re := nucNorm_of_polar _ Q S hQu hSpsd hpolar
  have hvalQ : (Qᴴ * (1 + T)).trace.re = S.trace.re := by
    rw [hpolar, show Qᴴ * (Q * S) = (Qᴴ * Q) * S by noncomm_ring, hQu, one_mul]
  -- the Hermitian form `Γ`
  obtain ⟨X, hX⟩ : ∃ M, M = (lam - mu) • (E * Qᴴ) := ⟨_, rfl⟩
  obtain ⟨Γ, hΓ⟩ : ∃ M, M = X + Xᴴ := ⟨_, rfl⟩
  have hΓH : Γᴴ = Γ := by rw [hΓ, conjTranspose_add, conjTranspose_conjTranspose]; abel
  -- the trace pairing with a Hermitian matrix picks out twice the real part
  have hpair : ∀ D : Matrix n n ℂ, Dᴴ = D → (Γ * D).trace = 2 * ((X * D).trace.re : ℂ) := by
    intro D hD
    have hconj : (Xᴴ * D).trace = (starRingEnd ℂ) ((X * D).trace) := by
      rw [← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, hD,
        Matrix.trace_mul_comm]
    rw [hΓ, add_mul, Matrix.trace_add, hconj, Complex.add_conj]; push_cast; ring
  -- Step 2 + 3: the first-order condition, then Ky Fan
  have hkyfan : ∀ P' : Matrix n n ℂ, P'ᴴ = P' → P' * P' = P' → P'.trace = P.trace →
      (Γ * P').trace.re ≤ (Γ * P).trace.re := by
    intro P' hP'H hP'2 hP'tr
    have hmin := nucNorm_ge_re_trace_gen Q (1 + (lam • P' + mu • (1 - P')) * E) hQu
    have hchain : (Qᴴ * (1 + (lam • P' + mu • (1 - P')) * E)).trace.re
        ≤ (Qᴴ * (1 + T)).trace.re := by
      rw [hvalQ, ← hval]; exact hmin.trans (hmax P' hP'H hP'2 hP'tr)
    -- the difference is `Re tr(X (P' - P))`
    have hRdiff : (lam • P' + mu • (1 - P')) - (lam • P + mu • (1 - P))
        = (lam - mu) • (P' - P) := by module
    have hdiff : (Qᴴ * (1 + (lam • P' + mu • (1 - P')) * E)).trace - (Qᴴ * (1 + T)).trace
        = (X * (P' - P)).trace := by
      rw [hT, hR, ← Matrix.trace_sub, ← mul_sub,
        show (1 + (lam • P' + mu • (1 - P')) * E) - (1 + (lam • P + mu • (1 - P)) * E)
          = ((lam • P' + mu • (1 - P')) - (lam • P + mu • (1 - P))) * E by noncomm_ring,
        hRdiff,
        show Qᴴ * (((lam - mu) • (P' - P)) * E) = (lam - mu) • (Qᴴ * ((P' - P) * E)) by
          simp only [smul_mul_assoc, mul_smul_comm],
        Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm Qᴴ ((P' - P) * E),
        show (P' - P) * E * Qᴴ = (P' - P) * (E * Qᴴ) by noncomm_ring,
        Matrix.trace_mul_comm (P' - P) (E * Qᴴ), hX, smul_mul_assoc, Matrix.trace_smul,
        smul_eq_mul]
    have hDH : (P' - P)ᴴ = P' - P := by rw [conjTranspose_sub, hP'H, hP]
    have h2 : (Γ * (P' - P)).trace.re ≤ 0 := by
      rw [hpair _ hDH, ← hdiff]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
        Complex.im_ofNat, Complex.sub_re]
      linarith [hchain]
    rw [mul_sub, Matrix.trace_sub, Complex.sub_re] at h2
    linarith [h2]
  have hcomm : P * Γ = Γ * P := kyFan_commute Γ P hΓH hP hP2 hkyfan
  -- Step 4: `Γ` in the form `C Q + Qᴴ Cᴴ`
  obtain ⟨C, hC⟩ : ∃ M, M = (lam - mu) • Rᴴ := ⟨_, rfl⟩
  have hEQ : E * Qᴴ = Rᴴ * Q := by
    have hEeq : E = Rᴴ * (Q * Q) := by rw [hQ2, hT, ← mul_assoc, hRu, one_mul]
    calc E * Qᴴ = Rᴴ * (Q * Q) * Qᴴ := by rw [← hEeq]
      _ = Rᴴ * Q * (Q * Qᴴ) := by noncomm_ring
      _ = Rᴴ * Q := by rw [hQu', mul_one]
  have hXC : X = C * Q := by rw [hX, hC, hEQ, smul_mul_assoc]
  have hΓC : Γ = C * Q + Qᴴ * Cᴴ := by rw [hΓ, hXC, conjTranspose_mul]
  -- Step 5: transfer `[P,Γ] = 0` to the symmetry `J`
  have hstat : J * (C * Q + Qᴴ * Cᴴ) * J = C * Q + Qᴴ * Cᴴ := by
    rw [← hΓC]
    have hJΓ : J * Γ = Γ * J := by
      rw [hJ, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hcomm, one_mul, mul_one]
    rw [hJΓ, mul_assoc, hJ2, mul_one]
  -- Step 6: apply the rigidity theorem
  have hJE : J * E = E * J := by
    refine stationary_implies_commute E J Q C ((lam - mu)⁻¹ • R) R Rᴴ
      ((lam - mu) * (star lam + star mu) / 2) ((lam - mu) * (star lam - star mu) / 2)
      hJH hJ2 hQu hQu' hQSpsd (by rw [hQ2, hT]) hRJ hRu (by rw [hC, hCform]) ?_ ?_ ?_ hstat
    · -- `z` is purely imaginary: `(λ-μ)(λ̄+μ̄) = λμ̄ - μλ̄` when `|λ| = |μ| = 1`
      have h1 : star ((lam - mu) * (star lam + star mu) / 2)
          = (star lam - star mu) * (lam + mu) / 2 := by
        simp only [star_div₀, star_mul', star_add, star_sub, star_star]
        norm_num
      rw [h1]
      linear_combination hlam - hmu
    · -- `w = |λ-μ|²/2` is real
      simp only [star_div₀, star_mul', star_sub, star_star]
      norm_num
      ring
    · -- `C` is invertible
      rw [hC, smul_mul_smul_comm, hRu', inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
  exact proj_commute_of_symm_commute E J P (by rw [hJ]; abel) hJE

end ApproxToffoli.TwoPhase
