/-
  ApproxToffoli.CutBound

  The analytic half of `cut_trace_bound`, and the `m = 2` assembly.

  After `CutNormalForm.lean` the problem is purely about `Mat4` traces: R5 turned
  the objective into `2^(m+1)` terms, and the substitution

      K := M₀ M₁ M₂ ,   Q := M₀ Ẑ M₀ᴴ ,   P := M₂ᴴ Ẑ M₂

  (Lean's gate order — see `CutNormalForm`'s docstring; the notes have `P` and `Q`
  the other way round, and copying them verbatim would give a FALSE lemma) turns the
  eight `Mat4` traces into `Tr(Z'ⁱ Qᵃ K Pᵇ)`, with `P`, `Q` rank-2 reflections and
  `K` unitary.

  `cut2_bound_of_PQK` — PROVED here — shows that the whole `m = 2` case follows from
  exactly two inequalities, neither of which mentions circuits:

  * **`bridge_ineq`** (gap_proof.py steps 1–4). A statement about eight FREE complex
    numbers and three `U(2)` matrices — no 4×4 matrices at all. Unitarity forces the
    weights on the two C-blocks to be SWAPPED (`u2_diag_eq`, `u2_offdiag_eq`), which
    pairs `σ₁, σ₂, τ₁, τ₂` into two instances of one shape.
  * **`core_psi_bound`** (steps 5–9). `ψ(K)² + ψ(QK)² ≤ 32 + 16√2` for `K` unitary
    and `P`, `Q` rank-2 reflections, `ψ(X) = |Tr X| + |Tr(Z' Q X P)|`. Route:
    Minkowski → AM–QM → a rank-2 Cauchy–Schwarz in `ℂ⁸` → **Lemma T1**.

  Both are TIGHT — `32 + 16√2 = (8cos(π/8))²` is attained — so any step with
  multiplicative slack is a bug rather than an inefficiency. The ONE exception is
  `cut_trace_bound_one` (`F(1)² = 40` against a budget of `54.627`), where a lossy
  argument is deliberate.

  STATUS (iter 1058). **This file is `sorry`-free**, and with it the whole cut chain
  and `ApproxToffoli` itself. `core_psi_bound` closed when `gap_proof.py`'s step 7 —
  a Cauchy–Schwarz against an orthonormal basis of `ran Π±`, i.e. eigenvector
  machinery this Mathlib does not have — was replaced by the ONB-free
  `proj_trace_bound`, whose proof is three explicit matrices in the Hilbert–Schmidt
  inner product. `cut_trace_bound_one` reuses the same lemma one gate shorter; note it
  is NOT an instance of `core_psi_bound` (the `m = 1` case is the `P = 1` degeneration
  and `IsRefl4 1` is false).

  Falsity-checks by adversarial optimisation, all in the repo's own index conventions
  (random sampling is worthless for these inequalities and has already fooled two
  agents): `bridge_ineq` over `c₀,c₁,c₂ ∈ U(2)` and eight free complex numbers
  (`PyScript/cut_bridge_lean_order.py`); `proj_trace_bound` at `n = 4` and `n = 8`,
  max violation `0.0000000000`, attained (`PyScript/cut_step7_falsity.py`); the `m = 1`
  route and objective, max `24` and `40` against budgets `27.314` and `54.627`
  (`PyScript/cut_f1_route_check.py`).
-/

import ApproxToffoli.CutNormalForm
import ApproxToffoli.LemmaT1

open Matrix Complex

noncomputable section

/-! ## Rank-2 reflections -/

/-- A rank-2 reflection: Hermitian, involutive, traceless — hence spectrum
    `{+1,+1,-1,-1}`. These are exactly the `P`, `Q` that Lemma T1 consumes. -/
def IsRefl4 (P : Mat4) : Prop := Pᴴ = P ∧ P * P = 1 ∧ Matrix.trace P = 0

lemma isRefl4_zhat4 : IsRefl4 Zhat4 :=
  ⟨zhat4_conjTranspose, zhat4_mul_self, trace_zhat4⟩

lemma isRefl4_isUnitary {P : Mat4} (h : IsRefl4 P) : IsUnitary4 P := by
  rw [IsUnitary4, h.1]; exact h.2.1

/-- Conjugating `Ẑ` by a unitary gives a rank-2 reflection. -/
lemma isRefl4_conj {M : Mat4} (hM : IsUnitary4 M) : IsRefl4 (Mᴴ * Zhat4 * M) := by
  have hMM : Mᴴ * M = 1 := hM
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hMM
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, zhat4_conjTranspose, Matrix.mul_assoc]
  · calc Mᴴ * Zhat4 * M * (Mᴴ * Zhat4 * M)
        = Mᴴ * Zhat4 * (M * Mᴴ) * Zhat4 * M := by noncomm_ring
      _ = Mᴴ * (Zhat4 * Zhat4) * M := by rw [hMM']; noncomm_ring
      _ = 1 := by rw [zhat4_mul_self, Matrix.mul_one, hMM]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hMM', Matrix.one_mul, trace_zhat4]

/-- The other orientation. -/
lemma isRefl4_conj' {M : Mat4} (hM : IsUnitary4 M) : IsRefl4 (M * Zhat4 * Mᴴ) := by
  have hMM : Mᴴ * M = 1 := hM
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hMM
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, zhat4_conjTranspose, Matrix.mul_assoc]
  · calc M * Zhat4 * Mᴴ * (M * Zhat4 * Mᴴ)
        = M * Zhat4 * (Mᴴ * M) * Zhat4 * Mᴴ := by noncomm_ring
      _ = M * (Zhat4 * Zhat4) * Mᴴ := by rw [hMM]; noncomm_ring
      _ = 1 := by rw [zhat4_mul_self, Matrix.mul_one, hMM']
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hMM, Matrix.one_mul, trace_zhat4]

/-! ## Lemma T1, in the repository's vocabulary

`ApproxToffoli/LemmaT1.lean` states T1 over the unbundled hypotheses and its own
namespaced copy of `Z'`. That copy is definitionally this file's `Zp4`
(`T1Bridge.Zp4 = Zp4` is `rfl`), so T1 is directly consumable; these two wrappers are
the forms `core_psi_bound` will actually use. -/

/-- **Lemma T1.** For rank-2 reflections `P`, `Q`:
    `|Tr(P Z')|² + |Tr(Q P Z')| ² ≤ 8`. TIGHT — `P = Q = Ẑ` attains exactly 8. -/
theorem T1_repo {P Q : Mat4} (hP : IsRefl4 P) (hQ : IsRefl4 Q) :
    Complex.normSq (Matrix.trace (P * Zp4))
      + Complex.normSq (Matrix.trace (Q * P * Zp4)) ≤ 8 :=
  T1Bridge.T1 P Q hP.1 hP.2.1 hP.2.2 hQ.1 hQ.2.1 hQ.2.2

/-- T1 in the `‖·‖` form that `psiF` uses. -/
theorem T1_norm {P Q : Mat4} (hP : IsRefl4 P) (hQ : IsRefl4 Q) :
    ‖Matrix.trace (P * Zp4)‖ ^ 2 + ‖Matrix.trace (Q * P * Zp4)‖ ^ 2 ≤ 8 := by
  rw [Complex.sq_norm, Complex.sq_norm]; exact T1_repo hP hQ

/-! ## The rank-2 Cauchy–Schwarz, without an orthonormal basis

`gap_proof.py`'s step 7 is a Cauchy–Schwarz in `ℂ⁸` performed against an orthonormal
basis of `ran Π±` — i.e. exactly the eigenvector machinery this Mathlib does not have.
It is replaced here by an ONB-FREE equivalent:

    Π a rank-2 orthogonal projection, `K`, `R` unitary
      ⟹ |Tr(Π K)|² + |Tr(Π K R)|² ≤ 2 (2 + |Tr(Π R)|).                  (`proj_trace_bound`)

TIGHT: at `K = R = 1` both sides are 8. The proof is three vectors in the
Hilbert–Schmidt space of `4×4` matrices,

    X = Kᴴ Π ,   Y = Π ,   Z = R Π ,

for which `⟪Y,X⟫ = conj (Tr(ΠK))`, `⟪Z,X⟫ = conj (Tr(ΠKR))`, `⟪Y,Z⟫ = Tr(ΠR)` and
`‖X‖² = ‖Y‖² = ‖Z‖² = Tr Π = 2` — all by `Π² = Π`, `Πᴴ = Π` and unitarity alone.
No basis, no spectral theorem. The inequality is then the elementary three-vector
bound below.

Adversarial optimisation (`PyScript/cut_step7_falsity.py`, L-BFGS-B + Nelder–Mead,
many restarts, `n = 4` and `n = 8`) puts the maximum violation at `0.0000000000`, i.e.
true and attained — consistent with tightness. -/

/-- Matrices as vectors under the Hilbert–Schmidt inner product `⟪A,B⟫ = Tr(Aᴴ B)`.
    Mathlib has no inner-product instance on `Matrix`, so we transport along the
    obvious bijection with `ℂ^(4×4)`. -/
def matToEuc (A : Mat4) : EuclideanSpace ℂ (Fin 4 × Fin 4) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

lemma inner_matToEuc (A B : Mat4) :
    (inner ℂ (matToEuc A) (matToEuc B) : ℂ) = Matrix.trace (Aᴴ * B) := by
  rw [PiLp.inner_apply]
  simp only [matToEuc, WithLp.ofLp_toLp, RCLike.inner_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp; ring

lemma norm_matToEuc_sq (A : Mat4) :
    ‖matToEuc A‖ ^ 2 = RCLike.re (Matrix.trace (Aᴴ * A)) := by
  rw [← inner_matToEuc A A, inner_self_eq_norm_sq]

/-- **The three-vector bound.** For `X, Y, Z` in any complex inner product space with
    `‖X‖², ‖Y‖², ‖Z‖² ≤ τ`,

        |⟪Y,X⟫|² + |⟪Z,X⟫|² ≤ τ (τ + |⟪Y,Z⟫|).

    This is `‖ |Y⟩⟨Y| + |Z⟩⟨Z| ‖ = ‖Y‖² + |⟪Y,Z⟫|` in disguise, but proved without any
    operator-norm or eigenvalue machinery: test against `W = ⟪Y,X⟫ • Y + ⟪Z,X⟫ • Z`,
    for which `⟪W,X⟫` is exactly the real number `N = |⟪Y,X⟫|² + |⟪Z,X⟫|²` while
    `‖W‖² ≤ N(τ + |⟪Y,Z⟫|)` by `2|u||v| ≤ |u|² + |v|²`. Cauchy–Schwarz then gives
    `N² ≤ N(τ+g)τ`, and `N > 0` divides out — so no optimal direction has to be
    normalised and no division appears in the proof. -/
theorem three_vector_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (X Y Z : E) (τ g : ℝ) (hg0 : 0 ≤ g)
    (hX : ‖X‖ ^ 2 ≤ τ) (hY : ‖Y‖ ^ 2 ≤ τ) (hZ : ‖Z‖ ^ 2 ≤ τ)
    (hg : ‖(inner ℂ Y Z : ℂ)‖ ≤ g) :
    ‖(inner ℂ Y X : ℂ)‖ ^ 2 + ‖(inner ℂ Z X : ℂ)‖ ^ 2 ≤ τ * (τ + g) := by
  have hτ0 : (0:ℝ) ≤ τ := le_trans (sq_nonneg _) hX
  have key : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    intro z
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  set u : ℂ := inner ℂ Y X with hu
  set v : ℂ := inner ℂ Z X with hv
  set N : ℝ := ‖u‖ ^ 2 + ‖v‖ ^ 2 with hNdef
  have hN0 : 0 ≤ N := by positivity
  rcases eq_or_lt_of_le hN0 with h0 | hpos
  · rw [← h0]; positivity
  · set W : E := u • Y + v • Z with hW
    have hWX : (inner ℂ W X : ℂ) = (N : ℂ) := by
      rw [hW, inner_add_left, inner_smul_left, inner_smul_left, ← hu, ← hv, hNdef,
        key u, key v]
      push_cast
      ring
    have hYZ : ‖(inner ℂ (u • Y) (v • Z) : ℂ)‖ ≤ ‖u‖ * ‖v‖ * g := by
      rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj,
        ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hg (by positivity)
    have hWnorm : ‖W‖ ^ 2 ≤ N * (τ + g) := by
      rw [hW, norm_add_sq (𝕜 := ℂ)]
      have h1 : ‖u • Y‖ ^ 2 ≤ ‖u‖ ^ 2 * τ := by
        rw [norm_smul, mul_pow]; exact mul_le_mul_of_nonneg_left hY (sq_nonneg _)
      have h2 : ‖v • Z‖ ^ 2 ≤ ‖v‖ ^ 2 * τ := by
        rw [norm_smul, mul_pow]; exact mul_le_mul_of_nonneg_left hZ (sq_nonneg _)
      have h3 : RCLike.re (inner ℂ (u • Y) (v • Z) : ℂ) ≤ ‖u‖ * ‖v‖ * g :=
        le_trans (RCLike.re_le_norm _) hYZ
      have h4 : 2 * (‖u‖ * ‖v‖) ≤ N := by rw [hNdef]; nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
      nlinarith [h1, h2, h3, h4, hg0, norm_nonneg u, norm_nonneg v]
    have hcs : ‖(inner ℂ W X : ℂ)‖ ≤ ‖W‖ * ‖X‖ := norm_inner_le_norm _ _
    rw [hWX] at hcs
    have hNnorm : ‖((N:ℝ) : ℂ)‖ = N := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN0]
    rw [hNnorm] at hcs
    have hsq : N ^ 2 ≤ (‖W‖ ^ 2) * (‖X‖ ^ 2) := by
      nlinarith [hcs, norm_nonneg W, norm_nonneg X, hN0]
    have hfin : N ^ 2 ≤ (N * (τ + g)) * τ := by
      nlinarith [hsq, hWnorm, hX, sq_nonneg ‖W‖, sq_nonneg ‖X‖, hτ0, hN0, hg0]
    nlinarith [hfin, hpos]

/-- **Step 7, ONB-free.** For `Π` a rank-2 orthogonal projection and `K`, `R` unitary:
    `|Tr(Π K)|² + |Tr(Π K R)|² ≤ 2 (2 + |Tr(Π R)|)`. TIGHT at `K = R = 1`. -/
theorem proj_trace_bound {Pi K R : Mat4}
    (hh : Piᴴ = Pi) (hi : Pi * Pi = Pi) (ht : Matrix.trace Pi = 2)
    (hK : IsUnitary4 K) (hR : IsUnitary4 R) :
    ‖Matrix.trace (Pi * K)‖ ^ 2 + ‖Matrix.trace (Pi * K * R)‖ ^ 2
      ≤ 2 * (2 + ‖Matrix.trace (Pi * R)‖) := by
  have hKK : K * Kᴴ = 1 := mul_eq_one_comm.mp hK
  have hRR : Rᴴ * R = 1 := hR
  set X : EuclideanSpace ℂ (Fin 4 × Fin 4) := matToEuc (Kᴴ * Pi) with hXd
  set Y : EuclideanSpace ℂ (Fin 4 × Fin 4) := matToEuc Pi with hYd
  set Z : EuclideanSpace ℂ (Fin 4 × Fin 4) := matToEuc (R * Pi) with hZd
  have nX : ‖X‖ ^ 2 = 2 := by
    rw [hXd, norm_matToEuc_sq]
    have e : (Kᴴ * Pi)ᴴ * (Kᴴ * Pi) = Pi := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh]
      calc Pi * K * (Kᴴ * Pi) = Pi * (K * Kᴴ) * Pi := by noncomm_ring
        _ = Pi := by rw [hKK, Matrix.mul_one, hi]
    rw [e, ht]; simp
  have nY : ‖Y‖ ^ 2 = 2 := by rw [hYd, norm_matToEuc_sq, hh, hi, ht]; simp
  have nZ : ‖Z‖ ^ 2 = 2 := by
    rw [hZd, norm_matToEuc_sq]
    have e : (R * Pi)ᴴ * (R * Pi) = Pi := by
      rw [Matrix.conjTranspose_mul, hh]
      calc Pi * Rᴴ * (R * Pi) = Pi * (Rᴴ * R) * Pi := by noncomm_ring
        _ = Pi := by rw [hRR, Matrix.mul_one, hi]
    rw [e, ht]; simp
  have iYX : (inner ℂ Y X : ℂ) = star (Matrix.trace (Pi * K)) := by
    have e1 : Matrix.trace (Piᴴ * (Kᴴ * Pi)) = Matrix.trace (Kᴴ * Pi) := by
      rw [hh]
      calc Matrix.trace (Pi * (Kᴴ * Pi))
          = Matrix.trace ((Kᴴ * Pi) * Pi) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Kᴴ * (Pi * Pi)) := by rw [Matrix.mul_assoc]
        _ = Matrix.trace (Kᴴ * Pi) := by rw [hi]
    have e2 : star (Matrix.trace (Pi * K)) = Matrix.trace (Kᴴ * Pi) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hh]
    rw [hYd, hXd, inner_matToEuc, e1, e2]
  have iZX : (inner ℂ Z X : ℂ) = star (Matrix.trace (Pi * K * R)) := by
    have e1 : Matrix.trace ((R * Pi)ᴴ * (Kᴴ * Pi)) = Matrix.trace (Rᴴ * Kᴴ * Pi) := by
      rw [Matrix.conjTranspose_mul, hh]
      calc Matrix.trace (Pi * Rᴴ * (Kᴴ * Pi))
          = Matrix.trace ((Pi * Rᴴ * Kᴴ) * Pi) := by
            rw [show Pi * Rᴴ * (Kᴴ * Pi) = (Pi * Rᴴ * Kᴴ) * Pi by noncomm_ring]
        _ = Matrix.trace (Pi * (Pi * Rᴴ * Kᴴ)) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace ((Pi * Pi) * (Rᴴ * Kᴴ)) := by
            rw [show Pi * (Pi * Rᴴ * Kᴴ) = (Pi * Pi) * (Rᴴ * Kᴴ) by noncomm_ring]
        _ = Matrix.trace (Pi * (Rᴴ * Kᴴ)) := by rw [hi]
        _ = Matrix.trace ((Rᴴ * Kᴴ) * Pi) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (Rᴴ * Kᴴ * Pi) := by rw [Matrix.mul_assoc]
    have e2 : star (Matrix.trace (Pi * K * R)) = Matrix.trace (Rᴴ * Kᴴ * Pi) := by
      rw [← Matrix.trace_conjTranspose]
      congr 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hh]
      noncomm_ring
    rw [hZd, hXd, inner_matToEuc, e1, e2]
  have iYZ : (inner ℂ Y Z : ℂ) = Matrix.trace (Pi * R) := by
    rw [hYd, hZd, inner_matToEuc, hh]
    calc Matrix.trace (Pi * (R * Pi))
        = Matrix.trace ((Pi * R) * Pi) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Pi * (Pi * R)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Pi * Pi) * R) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (Pi * R) := by rw [hi]
  have hmain := three_vector_bound X Y Z 2 ‖Matrix.trace (Pi * R)‖ (norm_nonneg _)
    (le_of_eq nX) (le_of_eq nY) (le_of_eq nZ) (by rw [iYZ])
  rw [iYX, iZX] at hmain
  simpa [norm_star] using hmain

/-! ## The spectral projections of a rank-2 reflection

`Π± = ½(1 ± Q)` — polynomials in `Q`, so nothing has to be diagonalised. -/

/-- `Π₊ = ½(1 + Q)`. -/
def piPlus (Q : Mat4) : Mat4 := (2 : ℂ)⁻¹ • ((1 : Mat4) + Q)

/-- `Π₋ = ½(1 - Q)`. -/
def piMinus (Q : Mat4) : Mat4 := (2 : ℂ)⁻¹ • ((1 : Mat4) - Q)

section PiPM
variable {Q : Mat4}

lemma piPlus_herm (hQ : IsRefl4 Q) : (piPlus Q)ᴴ = piPlus Q := by
  rw [piPlus, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, hQ.1]
  norm_num

lemma piMinus_herm (hQ : IsRefl4 Q) : (piMinus Q)ᴴ = piMinus Q := by
  rw [piMinus, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hQ.1]
  norm_num

lemma piPlus_idem (hQ : IsRefl4 Q) : piPlus Q * piPlus Q = piPlus Q := by
  have h2 : Q * Q = 1 := hQ.2.1
  rw [piPlus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show ((1 : Mat4) + Q) * (1 + Q) = 1 + Q + Q + Q * Q by noncomm_ring, h2]
  module

lemma piMinus_idem (hQ : IsRefl4 Q) : piMinus Q * piMinus Q = piMinus Q := by
  have h2 : Q * Q = 1 := hQ.2.1
  rw [piMinus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show ((1 : Mat4) - Q) * (1 - Q) = 1 - Q - Q + Q * Q by noncomm_ring, h2]
  module

/-- Rank 2: `Tr Π± = ½(4 ± 0) = 2`. This is where tracelessness of `Q` enters. -/
lemma piPlus_trace (hQ : IsRefl4 Q) : Matrix.trace (piPlus Q) = 2 := by
  rw [piPlus, Matrix.trace_smul, Matrix.trace_add, hQ.2.2, Matrix.trace_one]
  norm_num

lemma piMinus_trace (hQ : IsRefl4 Q) : Matrix.trace (piMinus Q) = 2 := by
  rw [piMinus, Matrix.trace_smul, Matrix.trace_sub, hQ.2.2, Matrix.trace_one]
  norm_num

end PiPM

lemma piPlus_trace_mul (Q X : Mat4) :
    Matrix.trace (piPlus Q * X) = (2:ℂ)⁻¹ * (Matrix.trace X + Matrix.trace (Q * X)) := by
  rw [piPlus, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add,
    Matrix.one_mul]
  simp

lemma piMinus_trace_mul (Q X : Mat4) :
    Matrix.trace (piMinus Q * X) = (2:ℂ)⁻¹ * (Matrix.trace X - Matrix.trace (Q * X)) := by
  rw [piMinus, Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.one_mul]
  simp

/-- The parallelogram law in the form the `Π±` split produces it: passing from the
    pair `(Tr X, Tr(QX))` to the pair `(Tr(Π₊X), Tr(Π₋X))` halves the sum of squares. -/
lemma half_parallelogram (x y : ℂ) :
    ‖(2:ℂ)⁻¹ * (x + y)‖ ^ 2 + ‖(2:ℂ)⁻¹ * (x - y)‖ ^ 2 = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_mul, Complex.normSq_mul]
  have h := parallelogram_normSq x y
  have h2 : Complex.normSq (2:ℂ)⁻¹ = 1/4 := by simp; norm_num
  rw [h2]; linarith

/-- `Z'` is unitary. -/
lemma isUnitary4_zp4 : IsUnitary4 Zp4 := by
  rw [IsUnitary4, zp4_conjTranspose]; exact zp4_mul_self

/-! ## The core inequality -/

/-- `ψ(X) = |Tr X| + |Tr(Z' Q X P)|`, the diagonal-`c` objective. -/
def psiF (P Q X : Mat4) : ℝ :=
  ‖Matrix.trace X‖ + ‖Matrix.trace (Zp4 * Q * X * P)‖

/-! ### The bridge inequality (gap_proof.py steps 1–4) — PROVED -/

/-- The real kernel of the bridge: two nested Cauchy–Schwarz steps against the unit
    vectors `(w,w')`, `(v,v')`, `(u,u')`, then `u² + u'² = 1` to turn a convex
    combination into a `max`. -/
theorem bridge_real (v v' u u' w w' s1 s2 t1 t2 : ℝ)
    (hv : 0 ≤ v) (hv' : 0 ≤ v') (hu : 0 ≤ u) (hu' : 0 ≤ u')
    (hvv : v ^ 2 + v' ^ 2 = 1) (huu : u ^ 2 + u' ^ 2 = 1) (hww : w ^ 2 + w' ^ 2 = 1)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) :
    (w * (v * u * s1 + v' * u' * s2) + w' * (v * u' * t1 + v' * u * t2)) ^ 2
      ≤ max (s1 ^ 2 + t2 ^ 2) (s2 ^ 2 + t1 ^ 2) := by
  set A := v * u * s1 + v' * u' * s2 with hA
  set B := v * u' * t1 + v' * u * t2 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have h1 : (w * A + w' * B) ^ 2 ≤ A ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (w * B - w' * A), hww, sq_nonneg (w * A + w' * B)]
  have h2 : A ^ 2 ≤ u ^ 2 * s1 ^ 2 + u' ^ 2 * s2 ^ 2 := by
    nlinarith [sq_nonneg (v * (u' * s2) - v' * (u * s1)), hvv]
  have h3 : B ^ 2 ≤ u' ^ 2 * t1 ^ 2 + u ^ 2 * t2 ^ 2 := by
    nlinarith [sq_nonneg (v * (u * t2) - v' * (u' * t1)), hvv]
  have hle1 : s1 ^ 2 + t2 ^ 2 ≤ max (s1 ^ 2 + t2 ^ 2) (s2 ^ 2 + t1 ^ 2) := le_max_left _ _
  have hle2 : s2 ^ 2 + t1 ^ 2 ≤ max (s1 ^ 2 + t2 ^ 2) (s2 ^ 2 + t1 ^ 2) := le_max_right _ _
  nlinarith [sq_nonneg u, sq_nonneg u', huu]

lemma norm_of_normSq_eq {x y : ℂ} (h : Complex.normSq x = Complex.normSq y) :
    ‖x‖ = ‖y‖ := by
  have hx : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by rw [Complex.sq_norm, Complex.sq_norm, h]
  nlinarith [norm_nonneg x, norm_nonneg y]

lemma u2_diag_norm {c : Mat2} (h : IsUnitary2 c) : ‖c 0 0‖ = ‖c 1 1‖ :=
  norm_of_normSq_eq (u2_diag_eq h)

lemma u2_offdiag_norm {c : Mat2} (h : IsUnitary2 c) : ‖c 0 1‖ = ‖c 1 0‖ :=
  norm_of_normSq_eq (u2_offdiag_eq h)

lemma u2_row_norm {c : Mat2} (h : IsUnitary2 c) : ‖c 0 0‖ ^ 2 + ‖c 0 1‖ ^ 2 = 1 := by
  rw [Complex.sq_norm, Complex.sq_norm]; exact u2_row0 h

private lemma norm_add4_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
    _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _

/-- **The bridge inequality** (gap_proof.py steps 1–4). PROVED.

Purely a statement about eight FREE complex numbers and three `U(2)` matrices — no
4×4 matrices appear. With `σ₁ = |T₀₀₀|+|T₁₁₁|`, `σ₂ = |T₁₀₀|+|T₀₁₁|`,
`τ₁ = |T₀₀₁|+|T₁₁₀|`, `τ₂ = |T₁₀₁|+|T₀₁₀|`:

    |Σ (c₀)_{ia}(c₁)_{ab}(c₂)_{bi} T_{iab}|² ≤ max(σ₁² + τ₂², σ₂² + τ₁²).

Regroup by the `c₁` factor into `Θ₀₀, Θ₀₁, Θ₁₀, Θ₁₁`; the anti-correlation
`|c₀₀| = |c₁₁|`, `|c₀₁| = |c₁₀|` (`u2_diag_norm`, `u2_offdiag_norm`) then makes the
weights on the two C-blocks SWAP, which is exactly what pairs `σ₁` with `τ₂` and
`σ₂` with `τ₁`. The rest is `bridge_real`. -/
theorem bridge_ineq (c0 c1 c2 : Mat2)
    (h0 : IsUnitary2 c0) (h1 : IsUnitary2 c1) (h2 : IsUnitary2 c2)
    (T000 T001 T010 T011 T100 T101 T110 T111 : ℂ) :
    Complex.normSq
        (c0 0 0 * c1 0 0 * c2 0 0 * T000 + c0 0 0 * c1 0 1 * c2 1 0 * T001
        + c0 0 1 * c1 1 0 * c2 0 0 * T010 + c0 0 1 * c1 1 1 * c2 1 0 * T011
        + c0 1 0 * c1 0 0 * c2 0 1 * T100 + c0 1 0 * c1 0 1 * c2 1 1 * T101
        + c0 1 1 * c1 1 0 * c2 0 1 * T110 + c0 1 1 * c1 1 1 * c2 1 1 * T111)
      ≤ max ((‖T000‖ + ‖T111‖) ^ 2 + (‖T101‖ + ‖T010‖) ^ 2)
            ((‖T100‖ + ‖T011‖) ^ 2 + (‖T001‖ + ‖T110‖) ^ 2) := by
  have e1 : ‖c0 1 0‖ = ‖c0 0 1‖ := (u2_offdiag_norm h0).symm
  have e2 : ‖c0 1 1‖ = ‖c0 0 0‖ := (u2_diag_norm h0).symm
  have e3 : ‖c2 1 0‖ = ‖c2 0 1‖ := (u2_offdiag_norm h2).symm
  have e4 : ‖c2 1 1‖ = ‖c2 0 0‖ := (u2_diag_norm h2).symm
  have e5 : ‖c1 1 0‖ = ‖c1 0 1‖ := (u2_offdiag_norm h1).symm
  have e6 : ‖c1 1 1‖ = ‖c1 0 0‖ := (u2_diag_norm h1).symm
  have b00 : ‖c0 0 0 * c2 0 0 * T000 + c0 1 0 * c2 0 1 * T100‖
      ≤ ‖c0 0 0‖ * ‖c2 0 0‖ * ‖T000‖ + ‖c0 0 1‖ * ‖c2 0 1‖ * ‖T100‖ :=
    le_trans (norm_add_le _ _) (le_of_eq (by simp only [norm_mul, e1]))
  have b01 : ‖c0 0 0 * c2 1 0 * T001 + c0 1 0 * c2 1 1 * T101‖
      ≤ ‖c0 0 0‖ * ‖c2 0 1‖ * ‖T001‖ + ‖c0 0 1‖ * ‖c2 0 0‖ * ‖T101‖ :=
    le_trans (norm_add_le _ _) (le_of_eq (by simp only [norm_mul, e1, e3, e4]))
  have b10 : ‖c0 0 1 * c2 0 0 * T010 + c0 1 1 * c2 0 1 * T110‖
      ≤ ‖c0 0 1‖ * ‖c2 0 0‖ * ‖T010‖ + ‖c0 0 0‖ * ‖c2 0 1‖ * ‖T110‖ :=
    le_trans (norm_add_le _ _) (le_of_eq (by simp only [norm_mul, e2]))
  have b11 : ‖c0 0 1 * c2 1 0 * T011 + c0 1 1 * c2 1 1 * T111‖
      ≤ ‖c0 0 1‖ * ‖c2 0 1‖ * ‖T011‖ + ‖c0 0 0‖ * ‖c2 0 0‖ * ‖T111‖ :=
    le_trans (norm_add_le _ _) (le_of_eq (by simp only [norm_mul, e2, e3, e4]))
  have hnorm : ‖c0 0 0 * c1 0 0 * c2 0 0 * T000 + c0 0 0 * c1 0 1 * c2 1 0 * T001
      + c0 0 1 * c1 1 0 * c2 0 0 * T010 + c0 0 1 * c1 1 1 * c2 1 0 * T011
      + c0 1 0 * c1 0 0 * c2 0 1 * T100 + c0 1 0 * c1 0 1 * c2 1 1 * T101
      + c0 1 1 * c1 1 0 * c2 0 1 * T110 + c0 1 1 * c1 1 1 * c2 1 1 * T111‖
      ≤ ‖c1 0 0‖ * (‖c0 0 0‖ * ‖c2 0 0‖ * (‖T000‖ + ‖T111‖)
                    + ‖c0 0 1‖ * ‖c2 0 1‖ * (‖T100‖ + ‖T011‖))
        + ‖c1 0 1‖ * (‖c0 0 0‖ * ‖c2 0 1‖ * (‖T001‖ + ‖T110‖)
                    + ‖c0 0 1‖ * ‖c2 0 0‖ * (‖T101‖ + ‖T010‖)) := by
    have hgroup : c0 0 0 * c1 0 0 * c2 0 0 * T000 + c0 0 0 * c1 0 1 * c2 1 0 * T001
        + c0 0 1 * c1 1 0 * c2 0 0 * T010 + c0 0 1 * c1 1 1 * c2 1 0 * T011
        + c0 1 0 * c1 0 0 * c2 0 1 * T100 + c0 1 0 * c1 0 1 * c2 1 1 * T101
        + c0 1 1 * c1 1 0 * c2 0 1 * T110 + c0 1 1 * c1 1 1 * c2 1 1 * T111
        = c1 0 0 * (c0 0 0 * c2 0 0 * T000 + c0 1 0 * c2 0 1 * T100)
        + c1 0 1 * (c0 0 0 * c2 1 0 * T001 + c0 1 0 * c2 1 1 * T101)
        + c1 1 0 * (c0 0 1 * c2 0 0 * T010 + c0 1 1 * c2 0 1 * T110)
        + c1 1 1 * (c0 0 1 * c2 1 0 * T011 + c0 1 1 * c2 1 1 * T111) := by ring
    rw [hgroup]
    refine le_trans (norm_add4_le _ _ _ _) ?_
    simp only [norm_mul, e5, e6]
    nlinarith [b00, b01, b10, b11, norm_nonneg (c1 0 0), norm_nonneg (c1 0 1)]
  have hmain := bridge_real ‖c0 0 0‖ ‖c0 0 1‖ ‖c2 0 0‖ ‖c2 0 1‖ ‖c1 0 0‖ ‖c1 0 1‖
    (‖T000‖ + ‖T111‖) (‖T100‖ + ‖T011‖) (‖T001‖ + ‖T110‖) (‖T101‖ + ‖T010‖)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (u2_row_norm h0) (u2_row_norm h2) (u2_row_norm h1)
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [← Complex.sq_norm]
  refine le_trans ?_ hmain
  have hnn := norm_nonneg (c0 0 0 * c1 0 0 * c2 0 0 * T000
      + c0 0 0 * c1 0 1 * c2 1 0 * T001
      + c0 0 1 * c1 1 0 * c2 0 0 * T010 + c0 0 1 * c1 1 1 * c2 1 0 * T011
      + c0 1 0 * c1 0 0 * c2 0 1 * T100 + c0 1 0 * c1 0 1 * c2 1 1 * T101
      + c0 1 1 * c1 1 0 * c2 0 1 * T110 + c0 1 1 * c1 1 1 * c2 1 1 * T111)
  nlinarith [hnorm, hnn]

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: the `set`-heavy body carries a dozen `Mat4` trace atoms through
-- three parallelogram rewrites and two `nlinarith` calls.
/-- **The core inequality** (gap_proof.py steps 5–9, resting on Lemma T1). PROVED.

`ψ(K)² + ψ(QK)² ≤ 32 + 16√2 = (8cos(π/8))²`, TIGHT. With `R = P Z'` (unitary) and
`p = |Tr K|`, `q = |Tr(R Q K)|`, `r = |Tr(QK)|`, `s = |Tr(RK)|` the goal is
`(p+q)² + (r+s)² ≤ 32 + 16√2`, and the route is:

* **steps 5–6** collapse: `(p+q)² + (r+s)² ≤ 2(p²+q²+r²+s²)`, plain AM–QM twice.
  (The write-up routes this through `α = √(p²+r²)`, `β = √(q²+s²)`, Minkowski and
  then `α+β ≤ √(2(α²+β²))`; the composite is the same constant, with no square
  roots to carry.)
* **step 7** `proj_trace_bound` at `Π₊` and at `Π₋`, whose two left-hand sides are —
  by the parallelogram law — exactly `½(p²+r²)` and `½(s²+q²)`. This gives
  `p²+q²+r²+s² ≤ 16 + 4(g₊+g₋)`, `g± = |Tr(Π± R)|`.
* **step 8 = Lemma T1** `|Tr(PZ')|² + |Tr(QPZ')|² ≤ 8` is `g₊² + g₋² ≤ 4`, again by
  the parallelogram law, so `g₊+g₋ ≤ 2√2`.
* **step 9** `p²+q²+r²+s² ≤ 16 + 8√2`, hence the goal. `2√(8+4√2) = 8cos(π/8)` is an
  IDENTITY (`two_sqrt_eight_add`), which is why no slack is lost at the endpoint. -/
theorem core_psi_bound {P Q K : Mat4}
    (hP : IsRefl4 P) (hQ : IsRefl4 Q) (hK : IsUnitary4 K) :
    psiF P Q K ^ 2 + psiF P Q (Q * K) ^ 2 ≤ 32 + 16 * Real.sqrt 2 := by
  set R : Mat4 := P * Zp4 with hRdef
  have hR : IsUnitary4 R := isUnitary4_mul (isRefl4_isUnitary hP) isUnitary4_zp4
  have hQ2 : Q * Q = 1 := hQ.2.1
  -- ψ, rewritten with `R` in front by cyclicity
  have e1 : Matrix.trace (Zp4 * Q * K * P) = Matrix.trace (R * (Q * K)) := by
    rw [Matrix.trace_mul_comm (Zp4 * Q * K) P, hRdef]; congr 1; noncomm_ring
  have e2 : Matrix.trace (Zp4 * Q * (Q * K) * P) = Matrix.trace (R * K) := by
    rw [show Zp4 * Q * (Q * K) * P = (Zp4 * (Q * Q) * K) * P by noncomm_ring, hQ2,
      Matrix.trace_mul_comm (Zp4 * 1 * K) P, hRdef]
    congr 1; noncomm_ring
  have hA : psiF P Q K = ‖Matrix.trace K‖ + ‖Matrix.trace (R * (Q * K))‖ := by
    rw [psiF, e1]
  have hB : psiF P Q (Q * K) = ‖Matrix.trace (Q * K)‖ + ‖Matrix.trace (R * K)‖ := by
    rw [psiF, e2]
  rw [hA, hB]
  set p := ‖Matrix.trace K‖ with hp
  set q := ‖Matrix.trace (R * (Q * K))‖ with hq
  set r := ‖Matrix.trace (Q * K)‖ with hr
  set s := ‖Matrix.trace (R * K)‖ with hs
  set g0 := ‖Matrix.trace (piPlus Q * R)‖ with hg0
  set g1 := ‖Matrix.trace (piMinus Q * R)‖ with hg1
  -- step 7, at each spectral projection of Q
  have bP := proj_trace_bound (piPlus_herm hQ) (piPlus_idem hQ) (piPlus_trace hQ) hK hR
  have bM := proj_trace_bound (piMinus_herm hQ) (piMinus_idem hQ) (piMinus_trace hQ) hK hR
  have parK : ‖Matrix.trace (piPlus Q * K)‖ ^ 2 + ‖Matrix.trace (piMinus Q * K)‖ ^ 2
      = (p ^ 2 + r ^ 2) / 2 := by
    rw [piPlus_trace_mul, piMinus_trace_mul, half_parallelogram]
  have hKR1 : Matrix.trace (K * R) = Matrix.trace (R * K) := Matrix.trace_mul_comm _ _
  have hKR2 : Matrix.trace (Q * (K * R)) = Matrix.trace (R * (Q * K)) := by
    rw [show Q * (K * R) = (Q * K) * R by noncomm_ring]; exact Matrix.trace_mul_comm _ _
  have parKR : ‖Matrix.trace (piPlus Q * K * R)‖ ^ 2
      + ‖Matrix.trace (piMinus Q * K * R)‖ ^ 2 = (s ^ 2 + q ^ 2) / 2 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, piPlus_trace_mul, piMinus_trace_mul,
      half_parallelogram, hKR1, hKR2]
  -- step 8: the same parallelogram identity turns T1 into a cap on g₊ + g₋
  have parR : g0 ^ 2 + g1 ^ 2
      = (‖Matrix.trace R‖ ^ 2 + ‖Matrix.trace (Q * R)‖ ^ 2) / 2 := by
    rw [hg0, hg1, piPlus_trace_mul, piMinus_trace_mul, half_parallelogram]
  have hT1 : ‖Matrix.trace R‖ ^ 2 + ‖Matrix.trace (Q * R)‖ ^ 2 ≤ 8 := by
    have h := T1_norm hP hQ
    rw [hRdef, show Q * (P * Zp4) = Q * P * Zp4 by noncomm_ring]
    exact h
  have hgsum : g0 + g1 ≤ 2 * Real.sqrt 2 := by
    have hsq : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    have hgg : g0 ^ 2 + g1 ^ 2 ≤ 4 := by rw [parR]; linarith
    nlinarith [sq_nonneg (g0 - g1), norm_nonneg (Matrix.trace (piPlus Q * R)),
      norm_nonneg (Matrix.trace (piMinus Q * R)), Real.sqrt_nonneg 2, hsq, hgg]
  -- step 9
  have hsum : p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 ≤ 16 + 8 * Real.sqrt 2 := by
    linarith [bP, bM, parK, parKR]
  nlinarith [sq_nonneg (p - q), sq_nonneg (r - s), hsum]

/-! ## The `m = 2` bound -/

/-- **`F(2) ≤ 8cos(π/8)`, abstractly.** All circuit structure has been eliminated:
    a bound on eight `Mat4` traces given only that `P`, `Q` are rank-2 reflections,
    `K` is unitary and `c₀, c₁, c₂` are `U(2)`.

    PROVED from `bridge_ineq` and `core_psi_bound` — i.e. those two statements really
    do suffice, which is the point of writing the assembly first. -/
theorem cut2_bound_of_PQK {P Q K : Mat4} {c0 c1 c2 : Mat2}
    (hP : IsRefl4 P) (hQ : IsRefl4 Q) (hK : IsUnitary4 K)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1) (k2 : IsUnitary2 c2) :
    Complex.normSq
        (c0 0 0 * c1 0 0 * c2 0 0 * Matrix.trace K
        + c0 0 0 * c1 0 1 * c2 1 0 * Matrix.trace (K * P)
        + c0 0 1 * c1 1 0 * c2 0 0 * Matrix.trace (Q * K)
        + c0 0 1 * c1 1 1 * c2 1 0 * Matrix.trace (Q * K * P)
        + c0 1 0 * c1 0 0 * c2 0 1 * Matrix.trace (Zp4 * K)
        + c0 1 0 * c1 0 1 * c2 1 1 * Matrix.trace (Zp4 * (K * P))
        + c0 1 1 * c1 1 0 * c2 0 1 * Matrix.trace (Zp4 * Q * K)
        + c0 1 1 * c1 1 1 * c2 1 1 * Matrix.trace (Zp4 * Q * K * P))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  have hQ2 : Q * Q = 1 := hQ.2.1
  have hP2 : P * P = 1 := hP.2.1
  have s1 : Zp4 * Q * (Q * K) * P = Zp4 * (K * P) := by
    calc Zp4 * Q * (Q * K) * P = Zp4 * (Q * Q) * K * P := by noncomm_ring
      _ = Zp4 * (K * P) := by rw [hQ2, Matrix.mul_one]; noncomm_ring
  have s2 : Zp4 * Q * (K * P) * P = Zp4 * Q * K := by
    calc Zp4 * Q * (K * P) * P = Zp4 * Q * K * (P * P) := by noncomm_ring
      _ = Zp4 * Q * K := by rw [hP2, Matrix.mul_one]
  have s3 : Q * (K * P) = Q * K * P := by noncomm_ring
  have s4 : Zp4 * Q * (Q * (K * P)) * P = Zp4 * K := by
    calc Zp4 * Q * (Q * (K * P)) * P = Zp4 * (Q * Q) * K * (P * P) := by noncomm_ring
      _ = Zp4 * K := by rw [hQ2, hP2, Matrix.mul_one, Matrix.mul_one]
  have pA : psiF P Q K = ‖Matrix.trace K‖ + ‖Matrix.trace (Zp4 * Q * K * P)‖ := rfl
  have pB : psiF P Q (Q * K)
      = ‖Matrix.trace (Q * K)‖ + ‖Matrix.trace (Zp4 * (K * P))‖ := by rw [psiF, s1]
  have pC : psiF P Q (K * P)
      = ‖Matrix.trace (K * P)‖ + ‖Matrix.trace (Zp4 * Q * K)‖ := by rw [psiF, s2]
  have pD : psiF P Q (Q * (K * P))
      = ‖Matrix.trace (Q * K * P)‖ + ‖Matrix.trace (Zp4 * K)‖ := by rw [psiF, s4, s3]
  refine le_trans (bridge_ineq c0 c1 c2 k0 k1 k2 _ _ _ _ _ _ _ _) ?_
  have hA := core_psi_bound hP hQ hK
  have hB := core_psi_bound hP hQ (isUnitary4_mul hK (isRefl4_isUnitary hP))
  rw [pA, pB] at hA
  rw [pC, pD] at hB
  rw [sixtyfour_cos_sq]
  refine max_le ?_ ?_
  · calc (‖Matrix.trace K‖ + ‖Matrix.trace (Zp4 * Q * K * P)‖) ^ 2
          + (‖Matrix.trace (Zp4 * (K * P))‖ + ‖Matrix.trace (Q * K)‖) ^ 2
        = (‖Matrix.trace K‖ + ‖Matrix.trace (Zp4 * Q * K * P)‖) ^ 2
          + (‖Matrix.trace (Q * K)‖ + ‖Matrix.trace (Zp4 * (K * P))‖) ^ 2 := by
            rw [add_comm (‖Matrix.trace (Zp4 * (K * P))‖)]
      _ ≤ 32 + 16 * Real.sqrt 2 := hA
  · calc (‖Matrix.trace (Zp4 * K)‖ + ‖Matrix.trace (Q * K * P)‖) ^ 2
          + (‖Matrix.trace (K * P)‖ + ‖Matrix.trace (Zp4 * Q * K)‖) ^ 2
        = (‖Matrix.trace (K * P)‖ + ‖Matrix.trace (Zp4 * Q * K)‖) ^ 2
          + (‖Matrix.trace (Q * K * P)‖ + ‖Matrix.trace (Zp4 * K)‖) ^ 2 := by
            rw [add_comm (‖Matrix.trace (Zp4 * K)‖)]; ring
      _ ≤ 32 + 16 * Real.sqrt 2 := hB

/-! ## Identifying the eight traces with `Z'ⁱ Qᵃ K Pᵇ` -/

section PQK
variable {M0 M1 M2 : Mat4}

/-- `K P = M₀ M₁ Ẑ M₂`. -/
lemma kp_eq (h2 : IsUnitary4 M2) :
    (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2) = M0 * M1 * Zhat4 * M2 := by
  have h : M2 * M2ᴴ = 1 := mul_eq_one_comm.mp h2
  calc (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2)
      = M0 * M1 * (M2 * M2ᴴ) * Zhat4 * M2 := by noncomm_ring
    _ = M0 * M1 * Zhat4 * M2 := by rw [h, Matrix.mul_one]

/-- `Q K = M₀ Ẑ M₁ M₂`. -/
lemma qk_eq (h0 : IsUnitary4 M0) :
    (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) = M0 * Zhat4 * M1 * M2 := by
  have h : M0ᴴ * M0 = 1 := h0
  calc (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2)
      = M0 * Zhat4 * (M0ᴴ * M0) * M1 * M2 := by noncomm_ring
    _ = M0 * Zhat4 * M1 * M2 := by rw [h, Matrix.mul_one]

/-- `Q K P = M₀ Ẑ M₁ Ẑ M₂`. -/
lemma qkp_eq (h0 : IsUnitary4 M0) (h2 : IsUnitary4 M2) :
    (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2)
      = M0 * Zhat4 * M1 * Zhat4 * M2 := by
  have ha : M0ᴴ * M0 = 1 := h0
  have hb : M2 * M2ᴴ = 1 := mul_eq_one_comm.mp h2
  calc (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2)
      = M0 * Zhat4 * (M0ᴴ * M0) * M1 * (M2 * M2ᴴ) * Zhat4 * M2 := by noncomm_ring
    _ = M0 * Zhat4 * M1 * Zhat4 * M2 := by
        rw [ha, hb, Matrix.mul_one, Matrix.mul_one]

end PQK

/-! ## The `m = 0` bound

`F(0) = √40 = 6.3247 < 8cos(π/8) = 7.3910`, so this case has room to spare
(`40 ≤ 54.627`). It reduces to the repo's already-proved `cnot_trace_bound`, but
that lemma is stated for `CNOT_BC_4`, not for `Z'`; the bridge is `Z' = CZ` and
`CZ = (I ⊗ H) CNOT (I ⊗ H)`. -/

/-- `I₂` written out entrywise. Needed because `simp` turns `I₂` into `1` and then
    stalls on `Matrix.one_apply` at `Fin`-division indices such as `⟨i.val / 2, _⟩`. -/
lemma I2_eq : I₂ = Matrix.of !![(1 : ℂ), 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [I₂]

set_option maxHeartbeats 1600000 in
-- Heartbeat bump: 16-case `fin_cases × fin_cases` over `Fin 4 × Fin 4` with a
-- triple 4×4 matrix product expanded by `Fin.sum_univ_four`.
/-- **`CZ = (I ⊗ H) · CNOT · (I ⊗ H)`**, in this repository's `kron2` convention
    (`i = 2*b + c`, so the Hadamard sits in the SECOND slot — on the CNOT target
    qubit — matching `CNOT_BC_4` from `BlockDecomp.lean`). This is the bridge that
    lets `cnot_trace_bound` be applied to `Z'`. -/
lemma zp4_eq_conj_cnot : Zp4 = kron2 I₂ Hgate * CNOT_BC_4 * kron2 I₂ Hgate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Zp4, kron2, CNOT_BC_4, Hgate, I2_eq, pauliX, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.diagonal] <;>
    norm_num [invSqrt2_sq]

/-- `(I ⊗ H)² = I` at the 4×4 level. -/
lemma kron2_IH_sq : kron2 I₂ Hgate * kron2 I₂ Hgate = (1 : Mat4) := by
  rw [kron2_mul, hgate_sq]
  have h : I₂ * I₂ = I₂ := by simp [I₂]
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kron2, I2_eq, Matrix.one_apply]

/-- **`cnot_trace_bound` transported along the CZ ↔ CNOT bridge.**
    `|Tr M|² + |Tr (Z' · M)|² ≤ 20` for every 4×4 unitary `M`. Apply
    `cnot_trace_bound` to `M' = (I⊗H) M (I⊗H)`, which is unitary, has the same
    trace as `M` (cyclicity plus `(I⊗H)² = I`), and satisfies
    `Tr (CNOT_BC_4 · M') = Tr (Z' · M)`. -/
lemma zp4_trace_bound (M : Mat4) (hM : IsUnitary4 M) :
    Complex.normSq (Matrix.trace M)
      + Complex.normSq (Matrix.trace (Zp4 * M)) ≤ 20 := by
  have hAu : IsUnitary4 (kron2 I₂ Hgate) := isUnitary4_kron2 isUnitary2_I2 hgate_unitary
  have hAA : kron2 I₂ Hgate * kron2 I₂ Hgate = 1 := kron2_IH_sq
  have hM'u : IsUnitary4 (kron2 I₂ Hgate * M * kron2 I₂ Hgate) :=
    isUnitary4_mul (isUnitary4_mul hAu hM) hAu
  have htr : Matrix.trace (kron2 I₂ Hgate * M * kron2 I₂ Hgate) = Matrix.trace M := by
    rw [Matrix.trace_mul_comm (kron2 I₂ Hgate * M) (kron2 I₂ Hgate), ← Matrix.mul_assoc,
      hAA, Matrix.one_mul]
  have htr2 : Matrix.trace (Zp4 * M)
      = Matrix.trace (CNOT_BC_4 * (kron2 I₂ Hgate * M * kron2 I₂ Hgate)) := by
    rw [zp4_eq_conj_cnot, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.trace_mul_comm (kron2 I₂ Hgate) (CNOT_BC_4 * (kron2 I₂ Hgate * M))]
    simp [Matrix.mul_assoc]
  have hcb := cnot_trace_bound _ hM'u
  rw [htr] at hcb
  rw [htr2]
  exact hcb

/-- **`F(0) ≤ 8cos(π/8)`.** A `BCCut 0` circuit is `kronABC M c`. Splitting the
    `CCZ8` overlap along the C-cut (`trace_ccz_cut0`), Cauchy–Schwarz on the two
    terms, `|c₀₀|² + |c₁₁|² ≤ 2` and `zp4_trace_bound` give
    `|Tr (CCZ8 · U)|² ≤ 2 · 20 = 40 ≤ 32 + 16√2 = 64 cos²(π/8)`. -/
theorem cut_trace_bound_zero {U : Mat8} (h : BCCut 0 U) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  cases h with
  | base M c hM hc =>
    rw [trace_ccz_cut0]
    have hcs := cauchy_schwarz_two (c 0 0) (c 1 1) (Matrix.trace M)
      (Matrix.trace (Zp4 * M))
    have hc0 : Complex.normSq (c 0 0) ≤ 1 := by
      have := unitary2_col0_norm c hc
      nlinarith [Complex.normSq_nonneg (c 1 0)]
    have hc1 : Complex.normSq (c 1 1) ≤ 1 := by
      have := unitary2_col1_norm c hc
      nlinarith [Complex.normSq_nonneg (c 0 1)]
    have hM20 := zp4_trace_bound M hM
    have hnn0 := Complex.normSq_nonneg (Matrix.trace M)
    have hnn1 := Complex.normSq_nonneg (Matrix.trace (Zp4 * M))
    have hsq : (64 : ℝ) * Real.cos (Real.pi / 8) ^ 2 = 32 + 16 * Real.sqrt 2 :=
      sixtyfour_cos_sq
    have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2]
    nlinarith [hcs, hc0, hc1, hM20, hnn0, hnn1]

/-! ## Remaining assembly -/

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: a dozen `Mat4` trace atoms carried through three parallelogram
-- rewrites, a `T1_repo` instantiation and two `nlinarith` calls.
/-- **The `m = 1` analytic core.** For `Q` a rank-2 reflection and `K` unitary,

    `|Tr K|² + |Tr(QK)|² + |Tr(Z'K)|² + |Tr(Z'QK)|² ≤ 16 + 8√2`.

Same machinery as `core_psi_bound`, one gate shorter: `proj_trace_bound` at the two
spectral projections `Π± = ½(1 ± Q)` with the `R` slot instantiated at `Z'`, then the
parallelogram law to convert each `Π±` pair back into the corresponding `(1, Q)` pair.
The residual `g± = |Tr(Π± Z')|` is capped by Lemma T1 at `P = Q`, where the second
summand degenerates to `|Tr Z'|² = 4` because `Q² = 1`; this leaves
`|Tr(Q Z')|² ≤ 4`, hence `g₊² + g₋² ≤ 4` and `g₊ + g₋ ≤ 2√2`.

Not tight: adversarial optimisation (`PyScript/cut_f1_route_check.py`) puts the true
maximum of the left side at exactly 24, against the 27.3137 proved here. That slack is
affordable — see `cut_trace_bound_one`. -/
theorem four_trace_bound_of_refl {Q K : Mat4} (hQ : IsRefl4 Q) (hK : IsUnitary4 K) :
    ‖Matrix.trace K‖ ^ 2 + ‖Matrix.trace (Q * K)‖ ^ 2
      + ‖Matrix.trace (Zp4 * K)‖ ^ 2 + ‖Matrix.trace (Zp4 * (Q * K))‖ ^ 2
      ≤ 16 + 8 * Real.sqrt 2 := by
  have htrZ : Matrix.trace Zp4 = 2 := by
    simp [Zp4, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]; norm_num
  have hnsq2 : Complex.normSq (2 : ℂ) = 4 := by simp; norm_num
  set g0 := ‖Matrix.trace (piPlus Q * Zp4)‖ with hg0
  set g1 := ‖Matrix.trace (piMinus Q * Zp4)‖ with hg1
  -- step 7, at each spectral projection of `Q`, with `R = Z'`
  have bP := proj_trace_bound (piPlus_herm hQ) (piPlus_idem hQ) (piPlus_trace hQ) hK
    isUnitary4_zp4
  have bM := proj_trace_bound (piMinus_herm hQ) (piMinus_idem hQ) (piMinus_trace hQ) hK
    isUnitary4_zp4
  have parK : ‖Matrix.trace (piPlus Q * K)‖ ^ 2 + ‖Matrix.trace (piMinus Q * K)‖ ^ 2
      = (‖Matrix.trace K‖ ^ 2 + ‖Matrix.trace (Q * K)‖ ^ 2) / 2 := by
    rw [piPlus_trace_mul, piMinus_trace_mul, half_parallelogram]
  have hKZ1 : Matrix.trace (K * Zp4) = Matrix.trace (Zp4 * K) := Matrix.trace_mul_comm _ _
  have hKZ2 : Matrix.trace (Q * (K * Zp4)) = Matrix.trace (Zp4 * (Q * K)) := by
    rw [show Q * (K * Zp4) = (Q * K) * Zp4 by noncomm_ring]
    exact Matrix.trace_mul_comm _ _
  have parKZ : ‖Matrix.trace (piPlus Q * K * Zp4)‖ ^ 2
      + ‖Matrix.trace (piMinus Q * K * Zp4)‖ ^ 2
      = (‖Matrix.trace (Zp4 * K)‖ ^ 2 + ‖Matrix.trace (Zp4 * (Q * K))‖ ^ 2) / 2 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, piPlus_trace_mul, piMinus_trace_mul,
      half_parallelogram, hKZ1, hKZ2]
  -- step 8 = Lemma T1 at `P = Q`
  have parR : g0 ^ 2 + g1 ^ 2
      = (‖Matrix.trace Zp4‖ ^ 2 + ‖Matrix.trace (Q * Zp4)‖ ^ 2) / 2 := by
    rw [hg0, hg1, piPlus_trace_mul, piMinus_trace_mul, half_parallelogram]
  have hT1 := T1_repo hQ hQ
  rw [hQ.2.1, Matrix.one_mul, htrZ, hnsq2] at hT1
  have hQZ : ‖Matrix.trace (Q * Zp4)‖ ^ 2 ≤ 4 := by rw [Complex.sq_norm]; linarith
  have hZ4 : ‖Matrix.trace Zp4‖ ^ 2 = 4 := by rw [Complex.sq_norm, htrZ, hnsq2]
  have hgg : g0 ^ 2 + g1 ^ 2 ≤ 4 := by rw [parR, hZ4]; linarith
  have hgsum : g0 + g1 ≤ 2 * Real.sqrt 2 := by
    have hsq : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    nlinarith [sq_nonneg (g0 - g1), norm_nonneg (Matrix.trace (piPlus Q * Zp4)),
      norm_nonneg (Matrix.trace (piMinus Q * Zp4)), Real.sqrt_nonneg 2, hsq, hgg]
  linarith [bP, bM, parK, parKZ]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: four `Mat4` trace atoms plus a four-term Cauchy–Schwarz.
/-- **`F(1) ≤ 8cos(π/8)`.** PROVED.

`trace_ccz_cut1` turns the objective into the four-term sum
`Σ_{i,a} (c₀)_{ia}(c₁)_{ai} Tr(Z'ⁱ Qᵃ K)` with `K = M₀M₁` unitary and
`Q = M₀ Ẑ M₀ᴴ` a rank-2 reflection (`isRefl4_conj'`); the two-factor analogue of
`qk_eq` identifies `Q K = M₀ Ẑ M₁`, so the four `Mat4` traces really are
`Tr K`, `Tr(QK)`, `Tr(Z'K)`, `Tr(Z'QK)`.

`four_trace_bound_of_refl` caps their squared moduli by `16 + 8√2`. For the weights,
unitarity of `c₀`, `c₁` gives `|c₀₀| = |c₁₁|`, `|c₀₁| = |c₁₀|`, so the four
coefficients have moduli `au, bv, bv, au` with `a²+b² = u²+v² = 1`; the triangle
inequality and a four-term Cauchy–Schwarz then give
`|Σ|² ≤ 2(a²u² + b²v²)(16 + 8√2) ≤ 32 + 16√2 = 64cos²(π/8)` (`sixtyfour_cos_sq`).

LOSSY, deliberately: `F(1) = √40 = 6.3246` against a budget of `8cos(π/8) = 7.3910`.
This is the one step of the problem with slack, so the crude
`a²u² + b²v² ≤ a² + b² = 1` costs nothing.

Note that this is NOT an instance of `core_psi_bound`: the `m = 1` case is the `P = 1`
degeneration, and `IsRefl4 1` is FALSE (`Tr 1 = 4 ≠ 0`), so `core_psi_bound` cannot be
instantiated here at all. It reuses `proj_trace_bound`, not `core_psi_bound`. -/
theorem cut_trace_bound_one {M0 M1 : Mat4} {c0 c1 : Mat2}
    (h0 : IsUnitary4 M0) (h1 : IsUnitary4 M1)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1) :
    Complex.normSq (Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  -- `K = M₀M₁` unitary, `Q = M₀ Ẑ M₀ᴴ` a rank-2 reflection
  have hK : IsUnitary4 (M0 * M1) := isUnitary4_mul h0 h1
  have hQ : IsRefl4 (M0 * Zhat4 * M0ᴴ) := isRefl4_conj' h0
  -- the two-factor analogue of `qk_eq`
  have eQK : (M0 * Zhat4 * M0ᴴ) * (M0 * M1) = M0 * Zhat4 * M1 := by
    have h : M0ᴴ * M0 = 1 := h0
    calc (M0 * Zhat4 * M0ᴴ) * (M0 * M1) = M0 * Zhat4 * (M0ᴴ * M0) * M1 := by noncomm_ring
      _ = M0 * Zhat4 * M1 := by rw [h, Matrix.mul_one]
  have hcore := four_trace_bound_of_refl hQ hK
  rw [eQK, show Zp4 * (M0 * M1) = Zp4 * M0 * M1 by noncomm_ring,
    show Zp4 * (M0 * Zhat4 * M1) = Zp4 * M0 * Zhat4 * M1 by noncomm_ring] at hcore
  rw [trace_ccz_cut1, ← Complex.sq_norm, sixtyfour_cos_sq]
  set n1 := ‖Matrix.trace (M0 * M1)‖ with hn1
  set n2 := ‖Matrix.trace (M0 * Zhat4 * M1)‖ with hn2
  set n3 := ‖Matrix.trace (Zp4 * M0 * M1)‖ with hn3
  set n4 := ‖Matrix.trace (Zp4 * M0 * Zhat4 * M1)‖ with hn4
  have e1 : ‖c0 1 0‖ = ‖c0 0 1‖ := (u2_offdiag_norm k0).symm
  have e2 : ‖c0 1 1‖ = ‖c0 0 0‖ := (u2_diag_norm k0).symm
  have e3 : ‖c1 1 0‖ = ‖c1 0 1‖ := (u2_offdiag_norm k1).symm
  have e4 : ‖c1 1 1‖ = ‖c1 0 0‖ := (u2_diag_norm k1).symm
  have hbound : ‖c0 0 0 * c1 0 0 * Matrix.trace (M0 * M1)
      + c0 0 1 * c1 1 0 * Matrix.trace (M0 * Zhat4 * M1)
      + c0 1 0 * c1 0 1 * Matrix.trace (Zp4 * M0 * M1)
      + c0 1 1 * c1 1 1 * Matrix.trace (Zp4 * M0 * Zhat4 * M1)‖
      ≤ ‖c0 0 0‖ * ‖c1 0 0‖ * n1 + ‖c0 0 1‖ * ‖c1 0 1‖ * n2
        + ‖c0 0 1‖ * ‖c1 0 1‖ * n3 + ‖c0 0 0‖ * ‖c1 0 0‖ * n4 := by
    refine le_trans (norm_add4_le _ _ _ _) (le_of_eq ?_)
    simp only [norm_mul, e1, e2, e3, e4, hn1, hn2, hn3, hn4]
  have key : ∀ x : ℝ, 0 ≤ x →
      x ≤ ‖c0 0 0‖ * ‖c1 0 0‖ * n1 + ‖c0 0 1‖ * ‖c1 0 1‖ * n2
        + ‖c0 0 1‖ * ‖c1 0 1‖ * n3 + ‖c0 0 0‖ * ‖c1 0 0‖ * n4 →
      x ^ 2 ≤ 32 + 16 * Real.sqrt 2 := by
    intro x hx hxle
    have ha0 : (0:ℝ) ≤ ‖c0 0 0‖ := norm_nonneg _
    have hb0 : (0:ℝ) ≤ ‖c0 0 1‖ := norm_nonneg _
    have hu0 : (0:ℝ) ≤ ‖c1 0 0‖ := norm_nonneg _
    have hv0 : (0:ℝ) ≤ ‖c1 0 1‖ := norm_nonneg _
    have hab : ‖c0 0 0‖ ^ 2 + ‖c0 0 1‖ ^ 2 = 1 := u2_row_norm k0
    have huv : ‖c1 0 0‖ ^ 2 + ‖c1 0 1‖ ^ 2 = 1 := u2_row_norm k1
    set a := ‖c0 0 0‖
    set b := ‖c0 0 1‖
    set u := ‖c1 0 0‖
    set v := ‖c1 0 1‖
    have h1 : x ^ 2 ≤ (a * u * n1 + b * v * n2 + b * v * n3 + a * u * n4) ^ 2 := by
      nlinarith [hxle, hx]
    have hcs : (a * u * n1 + b * v * n2 + b * v * n3 + a * u * n4) ^ 2
        ≤ ((a*u)^2 + (b*v)^2 + (b*v)^2 + (a*u)^2) * (n1^2 + n2^2 + n3^2 + n4^2) := by
      nlinarith [sq_nonneg (a*u*n2 - b*v*n1), sq_nonneg (a*u*n3 - b*v*n1),
        sq_nonneg (a*u*n4 - a*u*n1), sq_nonneg (b*v*n3 - b*v*n2),
        sq_nonneg (b*v*n4 - a*u*n2), sq_nonneg (b*v*n4 - a*u*n3)]
    have hw : (a*u)^2 + (b*v)^2 + (b*v)^2 + (a*u)^2 ≤ 2 := by
      nlinarith [hab, huv, mul_nonneg (sq_nonneg a) (sq_nonneg v),
        mul_nonneg (sq_nonneg b) (sq_nonneg u)]
    have hN0 : (0:ℝ) ≤ n1^2 + n2^2 + n3^2 + n4^2 := by positivity
    have h2 : ((a*u)^2 + (b*v)^2 + (b*v)^2 + (a*u)^2) * (n1^2 + n2^2 + n3^2 + n4^2)
        ≤ 2 * (n1^2 + n2^2 + n3^2 + n4^2) := by nlinarith [hw, hN0]
    linarith [h1, hcs, h2, hcore]
  exact key _ (norm_nonneg _) hbound

/-- **The cut trace bound.** `F(m) ≤ 8cos(π/8)` for `m ≤ 2`. Case analysis on the
    `CZCut` inductive: `m = 0` is `cut_trace_bound_zero` (via `BCCut.base`), `m = 1`
    is `cut_trace_bound_one`, `m = 2` is `trace_ccz_cut2` followed by
    `cut2_bound_of_PQK` at `K = M₀M₁M₂`, `Q = M₀ Ẑ M₀ᴴ`, `P = M₂ᴴ Ẑ M₂` (the eight
    trace identifications are `kp_eq`/`qk_eq`/`qkp_eq` and their `Z'`-prefixed
    reassociations), and `m ≥ 3` contradicts `hm`. -/
theorem cut_trace_bound_cz {m : ℕ} {U : Mat8} (h : CZCut m U) (hm : m ≤ 2) :
    Complex.normSq (Matrix.trace (CCZ8 * U)) ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  cases h with
  | base M c hM hc =>
      exact cut_trace_bound_zero (BCCut.base M c hM hc)
  | step h1 M2 c2 hM2 hc2 =>
      cases h1 with
      | base M0 c0 hM0 hc0 =>
          -- `m = 1` : `U = (M₀ ⊗ c₀) · CZ_BC · (M₂ ⊗ c₂)`.
          have e : CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M2 c2)
              = CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M2 c2 := by noncomm_ring
          rw [e]
          exact cut_trace_bound_one hM0 hM2 hc0 hc2
      | step h2 M1 c1 hM1 hc1 =>
          cases h2 with
          | base M0 c0 hM0 hc0 =>
              -- `m = 2` : `U = (M₀ ⊗ c₀) · CZ · (M₁ ⊗ c₁) · CZ · (M₂ ⊗ c₂)`.
              have e : CCZ8 * (kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
                    * kronABC M2 c2)
                  = CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1 * CZBC8
                    * kronABC M2 c2 := by noncomm_ring
              rw [e, trace_ccz_cut2]
              -- identify the eight `Mat4` traces with `Tr(Z'ⁱ Qᵃ K Pᵇ)`
              have e2 : M0 * M1 * Zhat4 * M2
                  = (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2) := (kp_eq hM2).symm
              have e3 : M0 * Zhat4 * M1 * M2
                  = (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) := (qk_eq hM0).symm
              have e4 : M0 * Zhat4 * M1 * Zhat4 * M2
                  = (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2) :=
                (qkp_eq hM0 hM2).symm
              have e5 : Zp4 * M0 * M1 * M2 = Zp4 * (M0 * M1 * M2) := by noncomm_ring
              have e6 : Zp4 * M0 * M1 * Zhat4 * M2
                  = Zp4 * ((M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2)) := by
                calc Zp4 * M0 * M1 * Zhat4 * M2
                    = Zp4 * (M0 * M1 * Zhat4 * M2) := by noncomm_ring
                  _ = Zp4 * ((M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2)) := by rw [kp_eq hM2]
              have e7 : Zp4 * M0 * Zhat4 * M1 * M2
                  = Zp4 * (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) := by
                calc Zp4 * M0 * Zhat4 * M1 * M2
                    = Zp4 * (M0 * Zhat4 * M1 * M2) := by noncomm_ring
                  _ = Zp4 * ((M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2)) := by rw [qk_eq hM0]
                  _ = Zp4 * (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) := by noncomm_ring
              have e8 : Zp4 * M0 * Zhat4 * M1 * Zhat4 * M2
                  = Zp4 * (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2) * (M2ᴴ * Zhat4 * M2) := by
                calc Zp4 * M0 * Zhat4 * M1 * Zhat4 * M2
                    = Zp4 * (M0 * Zhat4 * M1 * Zhat4 * M2) := by noncomm_ring
                  _ = Zp4 * ((M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2)
                        * (M2ᴴ * Zhat4 * M2)) := by rw [qkp_eq hM0 hM2]
                  _ = Zp4 * (M0 * Zhat4 * M0ᴴ) * (M0 * M1 * M2)
                        * (M2ᴴ * Zhat4 * M2) := by noncomm_ring
              rw [e2, e3, e4, e5, e6, e7, e8]
              exact cut2_bound_of_PQK (isRefl4_conj hM2) (isRefl4_conj' hM0)
                (isUnitary4_mul (isUnitary4_mul hM0 hM1) hM2) hc0 hc1 hc2
          | step h3 _ _ _ _ =>
              -- `m ≥ 3` contradicts `hm : m ≤ 2`.
              omega

end
