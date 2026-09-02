import ApproxToffoli.SharpBounds
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin

open Matrix Complex

noncomputable section

namespace Key2

/-! ## Part A : a `±1` eigenvector pair of `Q` inside the hyperplane `x 3 = 0` -/

lemma trace_mulVecLin (M : Mat4) :
    LinearMap.trace ℂ (Fin 4 → ℂ) (Matrix.mulVecLin M) = M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 4))]
  congr 1
  exact (LinearEquiv.eq_symm_apply
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin 4)) (Pi.basisFun ℂ (Fin 4)))).mp rfl

lemma finrank_range_of_idem (P : Mat4) (hi : P * P = P) (ht : Matrix.trace P = 2) :
    Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin P)) = 2 := by
  set f := Matrix.mulVecLin P with hf
  have hff : f ∘ₗ f = f := by rw [hf, ← Matrix.mulVecLin_mul, hi]
  have hproj : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x; exact LinearMap.mem_range_self _ _
    · rintro x ⟨y, rfl⟩; exact congrArg (fun g => g y) hff
  have h := hproj.trace
  rw [trace_mulVecLin, ht] at h
  exact_mod_cast h.symm

lemma finrank_ker_proj3 : Module.finrank ℂ
    (LinearMap.ker (LinearMap.proj (3 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ)) = 3 := by
  have hs : Function.Surjective (LinearMap.proj (3 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) :=
    fun c => ⟨fun _ => c, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (3 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ)
  rw [LinearMap.range_eq_top.mpr hs, Module.finrank_fin_fun ℂ] at h
  simp [Module.finrank_self] at h
  omega

lemma inter_ne_bot (S T : Submodule ℂ (Fin 4 → ℂ)) (hS : Module.finrank ℂ S = 2)
    (hT : Module.finrank ℂ T = 3) : S ⊓ T ≠ ⊥ := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hle : Module.finrank ℂ (S ⊔ T : Submodule ℂ (Fin 4 → ℂ)) ≤ 4 := by
    have h2 := Submodule.finrank_le (S ⊔ T)
    rwa [Module.finrank_fin_fun ℂ] at h2
  intro hbot
  rw [hbot] at h
  simp [hS, hT] at h
  omega

lemma dot_self_eq (u : Fin 4 → ℂ) :
    star u ⬝ᵥ u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

lemma dot_smul_self (c : ℝ) (u : Fin 4 → ℂ) :
    star ((c : ℂ) • u) ⬝ᵥ ((c : ℂ) • u)
      = ((c ^ 2 * ∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  rw [star_smul, dotProduct_smul, smul_dotProduct, dot_self_eq]
  simp only [RCLike.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast; ring

lemma dot_self_pos (u : Fin 4 → ℂ) (h : u ≠ 0) : 0 < ∑ i, Complex.normSq (u i) := by
  rcases Function.ne_iff.mp h with ⟨i, hi⟩
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  simpa using hi

lemma normalize_exists (u : Fin 4 → ℂ) (h : u ≠ 0) :
    ∃ c : ℝ, star ((c : ℂ) • u) ⬝ᵥ ((c : ℂ) • u) = 1 := by
  set t : ℝ := ∑ i, Complex.normSq (u i) with htdef
  have htp : 0 < t := dot_self_pos u h
  refine ⟨(Real.sqrt t)⁻¹, ?_⟩
  rw [dot_smul_self, ← htdef]
  have hc2 : ((Real.sqrt t)⁻¹) ^ 2 * t = 1 := by
    rw [inv_pow, Real.sq_sqrt htp.le]; field_simp
  rw [hc2]; norm_num

/-- A trace-2 idempotent `4×4` matrix has a unit fixed vector with vanishing last
    coordinate.  `2 + 3 > 4` is the whole content; `trace = rank` for an idempotent
    (`LinearMap.IsProj.trace`) is what turns `trace P = 2` into `dim (ran P) = 2`. -/
theorem exists_unit_eigvec (P : Mat4) (hi : P * P = P) (ht : Matrix.trace P = 2) :
    ∃ u : Fin 4 → ℂ, star u ⬝ᵥ u = 1 ∧ u 3 = 0 ∧ P *ᵥ u = u := by
  have h := inter_ne_bot (LinearMap.range (Matrix.mulVecLin P))
    (LinearMap.ker (LinearMap.proj (3 : Fin 4) : (Fin 4 → ℂ) →ₗ[ℂ] ℂ))
    (finrank_range_of_idem P hi ht) finrank_ker_proj3
  rw [Submodule.ne_bot_iff] at h
  obtain ⟨u, hu, hu0⟩ := h
  rw [Submodule.mem_inf] at hu
  have hu3 : u 3 = 0 := LinearMap.mem_ker.mp hu.2
  have hfix : P *ᵥ u = u := by
    obtain ⟨y, hy⟩ := hu.1
    rw [show (Matrix.mulVecLin P) y = P *ᵥ y from rfl] at hy
    rw [← hy, Matrix.mulVec_mulVec, hi]
  obtain ⟨c, hc⟩ := normalize_exists u hu0
  exact ⟨(c : ℂ) • u, hc, by simp [hu3], by rw [Matrix.mulVec_smul, hfix]⟩

lemma Q_mul_piPlus {Q : Mat4} (hQ : IsRefl4 Q) : Q * piPlus Q = piPlus Q := by
  rw [piPlus, Matrix.mul_smul, show Q * ((1:Mat4) + Q) = Q + Q * Q by noncomm_ring, hQ.2.1]
  module

lemma Q_mul_piMinus {Q : Mat4} (hQ : IsRefl4 Q) : Q * piMinus Q = - piMinus Q := by
  rw [piMinus, Matrix.mul_smul, show Q * ((1:Mat4) - Q) = Q - Q * Q by noncomm_ring, hQ.2.1]
  module

/-- **The eigenvector pair.**  For a rank-2 reflection `Q` there are orthonormal `u`, `v`
    with vanishing last coordinate such that `Q u = u`, `Q v = -v`.  Tracelessness of `Q`
    is exactly what makes both spectral projections have rank 2, hence both meet the
    3-dimensional hyperplane `x 3 = 0`. -/
theorem exists_eig_pair {Q : Mat4} (hQ : IsRefl4 Q) :
    ∃ u v : Fin 4 → ℂ, star u ⬝ᵥ u = 1 ∧ star v ⬝ᵥ v = 1 ∧ star u ⬝ᵥ v = 0 ∧
      u 3 = 0 ∧ v 3 = 0 ∧ Q *ᵥ u = u ∧ Q *ᵥ v = -v := by
  obtain ⟨u, hu1, hu3, huP⟩ :=
    exists_unit_eigvec (piPlus Q) (piPlus_idem hQ) (piPlus_trace hQ)
  obtain ⟨v, hv1, hv3, hvP⟩ :=
    exists_unit_eigvec (piMinus Q) (piMinus_idem hQ) (piMinus_trace hQ)
  have hQu : Q *ᵥ u = u := by
    conv_lhs => rw [← huP]
    rw [Matrix.mulVec_mulVec, Q_mul_piPlus hQ, huP]
  have hQv : Q *ᵥ v = -v := by
    conv_lhs => rw [← hvP]
    rw [Matrix.mulVec_mulVec, Q_mul_piMinus hQ, Matrix.neg_mulVec, hvP]
  refine ⟨u, v, hu1, hv1, ?_, hu3, hv3, hQu, hQv⟩
  have h1 : star u ⬝ᵥ (Q *ᵥ v) = (star u ᵥ* Q) ⬝ᵥ v := by rw [Matrix.dotProduct_mulVec]
  have h2 : star u ᵥ* Q = star u := by
    have h3 : star (Qᴴ *ᵥ u) = star u ᵥ* Q := by rw [Matrix.star_mulVec]; simp
    rw [← h3, hQ.1, hQu]
  rw [hQv, h2, dotProduct_neg] at h1
  linear_combination -h1 / 2

/-! ## Part B : the rank-one projections `|u⟩⟨u|`, `|v⟩⟨v|` -/

/-- `|u⟩⟨u|`. -/
def rk1 (u : Fin 4 → ℂ) : Mat4 := Matrix.vecMulVec u (star u)

lemma rk1_herm (u : Fin 4 → ℂ) : (rk1 u)ᴴ = rk1 u := by
  ext i j
  simp [rk1, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

lemma trace_rk1 (u : Fin 4 → ℂ) : Matrix.trace (rk1 u) = star u ⬝ᵥ u := by
  simp [rk1, Matrix.trace, Matrix.vecMulVec_apply, dotProduct, mul_comm]

lemma rk1_mul_rk1 (u v : Fin 4 → ℂ) :
    rk1 u * rk1 v = (star u ⬝ᵥ v) • Matrix.vecMulVec u (star v) := by
  ext i j
  simp only [rk1, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.smul_apply,
    Pi.star_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma mul_vecMulVec (M : Mat4) (u w : Fin 4 → ℂ) :
    M * Matrix.vecMulVec u w = Matrix.vecMulVec (M *ᵥ u) w := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma mul_rk1_self (M : Mat4) (u : Fin 4 → ℂ) (h : M *ᵥ u = u) : M * rk1 u = rk1 u := by
  rw [rk1, mul_vecMulVec, h]

lemma mul_rk1_neg (M : Mat4) (u : Fin 4 → ℂ) (h : M *ᵥ u = -u) : M * rk1 u = - rk1 u := by
  rw [rk1, mul_vecMulVec, h]
  ext i j; simp [Matrix.vecMulVec_apply]

lemma zp4_mulVec (u : Fin 4 → ℂ) (h : u 3 = 0) : Zp4 *ᵥ u = u := by
  ext i
  fin_cases i <;> simp [Zp4, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, h]

/-! ## Part C : the elementary endgame -/

/-- `p + q + s ≤ √20` when `p² = 1+2x`, `q² = 1−2x` and `s² ≤ 4 + 4gx` with `|g| ≤ 2`.

    `s ≤ 2·max(p,q)` because `4 + 4gx ≤ 4 + 8|x| = 4·max(p,q)²`; then
    `3M + m ≤ √(10(M²+m²)) = √20` is `(M − 3m)² ≥ 0`.  TIGHT at `(M,m) ∝ (3,1)`. -/
theorem real_core (p q s g x : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hp2 : p ^ 2 = 1 + 2 * x) (hq2 : q ^ 2 = 1 - 2 * x)
    (hs2 : s ^ 2 ≤ 4 + 4 * g * x) (hg1 : -2 ≤ g) (hg2 : g ≤ 2) :
    p + q + s ≤ Real.sqrt 20 := by
  have key : (p + q + s) ^ 2 ≤ 20 := by
    rcases le_total 0 x with hx | hx
    · have hsp : s ≤ 2 * p := by nlinarith [sq_nonneg (s - 2 * p), sq_nonneg (s + 2 * p)]
      nlinarith [sq_nonneg (p - 3 * q), sq_nonneg (p - q)]
    · have hsq : s ≤ 2 * q := by nlinarith [sq_nonneg (s - 2 * q), sq_nonneg (s + 2 * q)]
      nlinarith [sq_nonneg (q - 3 * p), sq_nonneg (p - q)]
  have h0 : 0 ≤ p + q + s := by linarith
  rw [show (20:ℝ) = Real.sqrt 20 ^ 2 by rw [Real.sq_sqrt]; norm_num] at key
  nlinarith [Real.sqrt_nonneg (20:ℝ), key, h0]

/-- The complex packaging of `real_core`.  `p = ‖a+b‖`, `q = ‖a−b‖`, and the two unit
    scalars `A`, `B` are the diagonal matrix elements at the `±1` eigenvectors. -/
theorem analytic_core (a b A B C D : ℂ) (g : ℝ)
    (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hg1 : -2 ≤ g) (hg2 : g ≤ 2)
    (hCD : ‖a * C + b * D‖ ^ 2 ≤ 4 + 4 * g * (a * (starRingEnd ℂ) b).re) :
    ‖a * (A - B + C) + b * (A + B + D)‖ ≤ Real.sqrt 20 := by
  set x : ℝ := (a * (starRingEnd ℂ) b).re with hxd
  have hp2 : ‖a + b‖ ^ 2 = 1 + 2 * x := by
    rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm, ← Complex.sq_norm, hab]
  have hq2 : ‖a - b‖ ^ 2 = 1 - 2 * x := by
    rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, ← Complex.sq_norm, hab]
  have m1 : ‖(a + b) * A‖ ≤ ‖a + b‖ := by
    rw [norm_mul]; nlinarith [norm_nonneg (a + b), hA]
  have m2 : ‖(b - a) * B‖ ≤ ‖a - b‖ := by
    rw [norm_mul, norm_sub_rev b a]; nlinarith [norm_nonneg (a - b), hB]
  have hsplit : a * (A - B + C) + b * (A + B + D)
      = (a + b) * A + (b - a) * B + (a * C + b * D) := by ring
  have h1 : ‖(a + b) * A + (b - a) * B + (a * C + b * D)‖
      ≤ ‖a + b‖ + ‖a - b‖ + ‖a * C + b * D‖ := by
    have t1 := norm_add_le ((a + b) * A + (b - a) * B) (a * C + b * D)
    have t2 := norm_add_le ((a + b) * A) ((b - a) * B)
    linarith
  rw [hsplit]
  exact le_trans h1 (real_core _ _ _ g x (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hp2 hq2 hCD hg1 hg2)

/-- Two-variable duality: an upper bound on every unit combination bounds the sum of
    squares.  The optimal `(a,b) = (conj T₁, conj T₂)/r` is written down explicitly. -/
theorem duality (T1 T2 : ℂ)
    (h : ∀ a b : ℂ, ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 → ‖a * T1 + b * T2‖ ≤ Real.sqrt 20) :
    ‖T1‖ ^ 2 + ‖T2‖ ^ 2 ≤ 20 := by
  set R : ℝ := ‖T1‖ ^ 2 + ‖T2‖ ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  rcases eq_or_lt_of_le hR0 with h0 | hpos
  · rw [← h0]; norm_num
  · set r : ℝ := Real.sqrt R with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = R := Real.sq_sqrt hR0
    have hrne : (r : ℂ) ≠ 0 := by simpa using hrpos.ne'
    have hnr : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
    set a : ℂ := (starRingEnd ℂ) T1 / (r : ℂ) with ha
    set b : ℂ := (starRingEnd ℂ) T2 / (r : ℂ) with hb
    have hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
      rw [ha, hb, norm_div, norm_div, RCLike.norm_conj, RCLike.norm_conj, hnr,
        div_pow, div_pow, ← add_div, ← hR, hr2]
      field_simp
    have e1 : (starRingEnd ℂ) T1 * T1 = ((‖T1‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    have e2 : (starRingEnd ℂ) T2 * T2 = ((‖T2‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    have hval : a * T1 + b * T2 = (r : ℂ) := by
      rw [ha, hb, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, e1, e2,
        ← Complex.ofReal_add, ← hR, div_eq_iff hrne, ← hr2]
      push_cast; ring
    have hfin := h a b hab
    rw [hval, hnr] at hfin
    have h20 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
    nlinarith [hfin, hrpos, hr2, h20, Real.sqrt_nonneg (20:ℝ)]

/-! ## Part D : the Hilbert–Schmidt Cauchy–Schwarz steps -/

/-- `|⟪Y,X⟫ a + ⟪Z,X⟫ b|² ≤ 4 + 4g·Re(a b̄)` when `‖X‖²=‖Y‖²=‖Z‖²=2` and `⟪Y,Z⟫ = g`
    is real.  A single Cauchy–Schwarz against `ā•Y + b̄•Z`. -/
theorem cs_combo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (X Y Z : E) (a b : ℂ) (g : ℝ)
    (hY : ‖Y‖ ^ 2 = 2) (hZ : ‖Z‖ ^ 2 = 2) (hX : ‖X‖ ^ 2 = 2)
    (hYZ : (inner ℂ Y Z : ℂ) = (g : ℂ)) (hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖a * (inner ℂ Y X : ℂ) + b * (inner ℂ Z X : ℂ)‖ ^ 2
      ≤ 4 + 4 * g * (a * (starRingEnd ℂ) b).re := by
  set V : E := ((starRingEnd ℂ) a) • Y + ((starRingEnd ℂ) b) • Z with hV
  have hVX : (inner ℂ V X : ℂ) = a * (inner ℂ Y X : ℂ) + b * (inner ℂ Z X : ℂ) := by
    rw [hV, inner_add_left, inner_smul_left, inner_smul_left]; simp
  have hVn : ‖V‖ ^ 2 = 2 + 2 * g * (a * (starRingEnd ℂ) b).re := by
    rw [hV, norm_add_pow_two (𝕜 := ℂ), norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, hYZ]
    simp only [RCLike.norm_conj, mul_pow]
    rw [hY, hZ]
    have h3 : ((starRingEnd ℂ) ((starRingEnd ℂ) a) * ((starRingEnd ℂ) b * (g : ℂ)))
        = (a * (starRingEnd ℂ) b) * (g : ℂ) := by simp; ring
    rw [h3]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, RCLike.re_to_complex]
    nlinarith [hab]
  have hcs : ‖(inner ℂ V X : ℂ)‖ ≤ ‖V‖ * ‖X‖ := norm_inner_le_norm _ _
  have h2 : ‖(inner ℂ V X : ℂ)‖ ^ 2 ≤ (‖V‖ * ‖X‖) ^ 2 := by
    have h4 := norm_nonneg ((inner ℂ V X : ℂ))
    nlinarith [mul_nonneg (norm_nonneg V) (norm_nonneg X)]
  rw [hVX] at h2
  rw [mul_pow, hVn, hX] at h2
  linarith

/-- `|Tr(F N)| ≤ 1` for `F` a rank-one orthogonal projection and `N` unitary. -/
theorem rk1_trace_le_one {N F : Mat4} (hN : IsUnitary4 N)
    (hFh : Fᴴ = F) (hFi : F * F = F) (hFt : Matrix.trace F = 1) :
    ‖Matrix.trace (F * N)‖ ≤ 1 := by
  have hNN : Nᴴ * N = 1 := hN
  have hin : (inner ℂ (matToEuc F) (matToEuc (N * F)) : ℂ) = Matrix.trace (F * N) := by
    rw [inner_matToEuc, hFh, show F * (N * F) = (F * N) * F by noncomm_ring,
      Matrix.trace_mul_comm, show F * (F * N) = (F * F) * N by noncomm_ring, hFi]
  have n1 : ‖matToEuc F‖ ^ 2 = 1 := by rw [norm_matToEuc_sq, hFh, hFi, hFt]; simp
  have n2 : ‖matToEuc (N * F)‖ ^ 2 = 1 := by
    rw [norm_matToEuc_sq, Matrix.conjTranspose_mul, hFh,
      show F * Nᴴ * (N * F) = F * (Nᴴ * N) * F by noncomm_ring, hNN, Matrix.mul_one,
      hFi, hFt]
    simp
  have hcs : ‖(inner ℂ (matToEuc F) (matToEuc (N * F)) : ℂ)‖
      ≤ ‖matToEuc F‖ * ‖matToEuc (N * F)‖ := norm_inner_le_norm _ _
  rw [hin] at hcs
  have e1 : ‖matToEuc F‖ = 1 := by nlinarith [n1, norm_nonneg (matToEuc F)]
  have e2 : ‖matToEuc (N * F)‖ = 1 := by nlinarith [n2, norm_nonneg (matToEuc (N * F))]
  rw [e1, e2] at hcs
  linarith

/-! ## Part E : the matrix-level core -/

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: ~20 matrix rewrites plus four Cauchy–Schwarz steps in one proof.
/-- **`key2`, with the eigen-decomposition supplied.**  `Fu = |u⟩⟨u|`, `Fv = |v⟩⟨v|` are
    the rank-one projections onto the `±1` eigenvectors of `Q` inside `ker e₃*`; both are
    fixed by `Z'`.  Splitting `1 = Fu + Fv + W` turns `Tr(QN)` into `A − B + C` and
    `Tr(Z'N)` into `A + B + D`, and the pair `(C,D)` is controlled by one Cauchy–Schwarz
    in the Hilbert–Schmidt space against `W`, whose trace is 2. -/
theorem key2_split {Q N Fu Fv : Mat4}
    (hQh : Qᴴ = Q) (hQ2 : Q * Q = 1) (hN : IsUnitary4 N)
    (hFuh : Fuᴴ = Fu) (hFui : Fu * Fu = Fu) (hFut : Matrix.trace Fu = 1)
    (hFvh : Fvᴴ = Fv) (hFvi : Fv * Fv = Fv) (hFvt : Matrix.trace Fv = 1)
    (huv : Fu * Fv = 0) (hvu : Fv * Fu = 0)
    (hQu : Q * Fu = Fu) (hQv : Q * Fv = -Fv)
    (hZu : Zp4 * Fu = Fu) (hZv : Zp4 * Fv = Fv) :
    ‖Matrix.trace (Q * N)‖ ^ 2 + ‖Matrix.trace (Zp4 * N)‖ ^ 2 ≤ 20 := by
  have hNN : Nᴴ * N = 1 := hN
  set W : Mat4 := 1 - Fu - Fv with hWdef
  -- `W` is a trace-2 projection commuting with both `Q` and `Z'`
  have hWh : Wᴴ = W := by
    rw [hWdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hFuh, hFvh]
  have hWi : W * W = W := by
    rw [hWdef, show ((1:Mat4) - Fu - Fv) * ((1:Mat4) - Fu - Fv)
      = 1 - Fu - Fv - Fu - Fv + Fu * Fu + Fu * Fv + Fv * Fu + Fv * Fv by noncomm_ring,
      hFui, hFvi, huv, hvu]
    abel
  have hWt : Matrix.trace W = 2 := by
    rw [hWdef, Matrix.trace_sub, Matrix.trace_sub, hFut, hFvt, Matrix.trace_one]
    norm_num
  have hFuQ : Fu * Q = Fu := by
    have h := congrArg Matrix.conjTranspose hQu
    rwa [Matrix.conjTranspose_mul, hQh, hFuh] at h
  have hFvQ : Fv * Q = -Fv := by
    have h := congrArg Matrix.conjTranspose hQv
    rwa [Matrix.conjTranspose_mul, hQh, hFvh, Matrix.conjTranspose_neg, hFvh] at h
  have hFuZ : Fu * Zp4 = Fu := by
    have h := congrArg Matrix.conjTranspose hZu
    rwa [Matrix.conjTranspose_mul, zp4_conjTranspose, hFuh] at h
  have hFvZ : Fv * Zp4 = Fv := by
    have h := congrArg Matrix.conjTranspose hZv
    rwa [Matrix.conjTranspose_mul, zp4_conjTranspose, hFvh] at h
  have hQW : Q * W = W * Q := by
    rw [hWdef, show Q * ((1:Mat4) - Fu - Fv) = Q - Q * Fu - Q * Fv by noncomm_ring,
      show ((1:Mat4) - Fu - Fv) * Q = Q - Fu * Q - Fv * Q by noncomm_ring,
      hQu, hQv, hFuQ, hFvQ]
  have hZW : Zp4 * W = W * Zp4 := by
    rw [hWdef, show Zp4 * ((1:Mat4) - Fu - Fv) = Zp4 - Zp4 * Fu - Zp4 * Fv by noncomm_ring,
      show ((1:Mat4) - Fu - Fv) * Zp4 = Zp4 - Fu * Zp4 - Fv * Zp4 by noncomm_ring,
      hZu, hZv, hFuZ, hFvZ]
  -- the two trace decompositions
  have eQ : Matrix.trace (Q * N)
      = Matrix.trace (Fu * N) - Matrix.trace (Fv * N) + Matrix.trace (Q * W * N) := by
    have e : Q * W * N = Q * N - (Q * Fu) * N - (Q * Fv) * N := by
      rw [hWdef]; noncomm_ring
    rw [e, hQu, hQv]
    simp only [Matrix.neg_mul, Matrix.trace_sub, Matrix.trace_neg]
    ring
  have eZ : Matrix.trace (Zp4 * N)
      = Matrix.trace (Fu * N) + Matrix.trace (Fv * N) + Matrix.trace (Zp4 * W * N) := by
    have e : Zp4 * W * N = Zp4 * N - (Zp4 * Fu) * N - (Zp4 * Fv) * N := by
      rw [hWdef]; noncomm_ring
    rw [e, hZu, hZv]
    simp only [Matrix.trace_sub]
    ring
  -- the three Hilbert–Schmidt vectors
  have nX : ‖matToEuc (N * W)‖ ^ 2 = 2 := by
    rw [norm_matToEuc_sq, Matrix.conjTranspose_mul, hWh,
      show W * Nᴴ * (N * W) = W * (Nᴴ * N) * W by noncomm_ring, hNN, Matrix.mul_one,
      hWi, hWt]
    simp
  have nY : ‖matToEuc (W * Q)‖ ^ 2 = 2 := by
    rw [norm_matToEuc_sq,
      show (W * Q)ᴴ * (W * Q) = Q * (W * W) * Q by
        rw [Matrix.conjTranspose_mul, hWh, hQh]; noncomm_ring,
      hWi, Matrix.trace_mul_comm, show Q * (Q * W) = (Q * Q) * W by noncomm_ring, hQ2,
      Matrix.one_mul, hWt]
    simp
  have nZ : ‖matToEuc (W * Zp4)‖ ^ 2 = 2 := by
    rw [norm_matToEuc_sq,
      show (W * Zp4)ᴴ * (W * Zp4) = Zp4 * (W * W) * Zp4 by
        rw [Matrix.conjTranspose_mul, hWh, zp4_conjTranspose]; noncomm_ring,
      hWi, Matrix.trace_mul_comm,
      show Zp4 * (Zp4 * W) = (Zp4 * Zp4) * W by noncomm_ring, zp4_mul_self,
      Matrix.one_mul, hWt]
    simp
  have iYX : (inner ℂ (matToEuc (W * Q)) (matToEuc (N * W)) : ℂ)
      = Matrix.trace (Q * W * N) := by
    rw [inner_matToEuc,
      show (W * Q)ᴴ * (N * W) = (Q * W * N) * W by
        rw [Matrix.conjTranspose_mul, hWh, hQh]; noncomm_ring,
      Matrix.trace_mul_comm, show W * (Q * W * N) = (W * Q) * W * N by noncomm_ring,
      ← hQW, show Q * W * W * N = Q * (W * W) * N by noncomm_ring, hWi]
  have iZX : (inner ℂ (matToEuc (W * Zp4)) (matToEuc (N * W)) : ℂ)
      = Matrix.trace (Zp4 * W * N) := by
    rw [inner_matToEuc,
      show (W * Zp4)ᴴ * (N * W) = (Zp4 * W * N) * W by
        rw [Matrix.conjTranspose_mul, hWh, zp4_conjTranspose]; noncomm_ring,
      Matrix.trace_mul_comm, show W * (Zp4 * W * N) = (W * Zp4) * W * N by noncomm_ring,
      ← hZW, show Zp4 * W * W * N = Zp4 * (W * W) * N by noncomm_ring, hWi]
  have iYZ : (inner ℂ (matToEuc (W * Q)) (matToEuc (W * Zp4)) : ℂ)
      = Matrix.trace (Q * W * Zp4) := by
    rw [inner_matToEuc,
      show (W * Q)ᴴ * (W * Zp4) = Q * (W * W) * Zp4 by
        rw [Matrix.conjTranspose_mul, hWh, hQh]; noncomm_ring,
      hWi]
  -- `⟪Y,Z⟫ = Tr(Q W Z')` is real, with modulus ≤ 2
  have hgconj : (starRingEnd ℂ) (Matrix.trace (Q * W * Zp4))
      = Matrix.trace (Q * W * Zp4) := by
    have h : ((Q * W * Zp4)ᴴ).trace = star ((Q * W * Zp4).trace) :=
      Matrix.trace_conjTranspose _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh, hWh,
      zp4_conjTranspose] at h
    rw [starRingEnd_apply, ← h, show Zp4 * (W * Q) = (Zp4 * W) * Q by noncomm_ring, hZW,
      Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have hgre : (((Matrix.trace (Q * W * Zp4)).re : ℝ) : ℂ) = Matrix.trace (Q * W * Zp4) :=
    Complex.conj_eq_iff_re.mp hgconj
  have hgbd : |(Matrix.trace (Q * W * Zp4)).re| ≤ 2 := by
    have h1 : ‖(inner ℂ (matToEuc (W * Q)) (matToEuc (W * Zp4)) : ℂ)‖
        ≤ ‖matToEuc (W * Q)‖ * ‖matToEuc (W * Zp4)‖ := norm_inner_le_norm _ _
    rw [iYZ] at h1
    have h2 : ‖matToEuc (W * Q)‖ * ‖matToEuc (W * Zp4)‖ ≤ 2 := by
      nlinarith [nY, nZ, norm_nonneg (matToEuc (W * Q)), norm_nonneg (matToEuc (W * Zp4)),
        mul_nonneg (norm_nonneg (matToEuc (W * Q))) (norm_nonneg (matToEuc (W * Zp4)))]
    exact le_trans (Complex.abs_re_le_norm _) (by linarith)
  obtain ⟨hg1, hg2⟩ := abs_le.mp hgbd
  have hA : ‖Matrix.trace (Fu * N)‖ ≤ 1 := rk1_trace_le_one hN hFuh hFui hFut
  have hB : ‖Matrix.trace (Fv * N)‖ ≤ 1 := rk1_trace_le_one hN hFvh hFvi hFvt
  rw [eQ, eZ]
  refine duality _ _ (fun a b hab => ?_)
  have hcs := cs_combo (matToEuc (N * W)) (matToEuc (W * Q)) (matToEuc (W * Zp4)) a b
    (Matrix.trace (Q * W * Zp4)).re nY nZ nX (by rw [iYZ, hgre]) hab
  rw [iYX, iZX] at hcs
  exact analytic_core a b _ _ _ _ _ hab hA hB (by linarith) (by linarith) hcs

/-! ## Part F : `key2` -/

/-- **`key2`.**  For a rank-2 reflection `Q` (Hermitian, involutive, traceless) and a
    unitary `N`,

        ‖Tr(Q N)‖² + ‖Tr(Z' N)‖² ≤ 20 ,      `Z' = diag(1,1,1,−1)`.

    TIGHT: `20` is attained.  This is the `Q`-twisted analogue of `zp4_trace_bound`, and
    is strictly sharper than what the plain Hilbert–Schmidt three-vector bound gives
    (`16 + 4‖Tr(Q Z')‖`, whose maximum is 24). -/
theorem key2 (Q N : Mat4) (hQ : IsRefl4 Q) (hN : IsUnitary4 N) :
    ‖Matrix.trace (Q * N)‖ ^ 2 + ‖Matrix.trace (Zp4 * N)‖ ^ 2 ≤ 20 := by
  obtain ⟨u, v, hu1, hv1, huv0, hu3, hv3, hQu, hQv⟩ := exists_eig_pair hQ
  have hFui : rk1 u * rk1 u = rk1 u := by rw [rk1_mul_rk1, hu1, one_smul, rk1]
  have hFvi : rk1 v * rk1 v = rk1 v := by rw [rk1_mul_rk1, hv1, one_smul, rk1]
  have huv : rk1 u * rk1 v = 0 := by rw [rk1_mul_rk1, huv0, zero_smul]
  have hvu : rk1 v * rk1 u = 0 := by
    have h := congrArg Matrix.conjTranspose huv
    rwa [Matrix.conjTranspose_mul, rk1_herm, rk1_herm, Matrix.conjTranspose_zero] at h
  exact key2_split hQ.1 hQ.2.1 hN
    (rk1_herm u) hFui (by rw [trace_rk1, hu1])
    (rk1_herm v) hFvi (by rw [trace_rk1, hv1])
    huv hvu
    (mul_rk1_self Q u hQu) (mul_rk1_neg Q v hQv)
    (mul_rk1_self Zp4 u (zp4_mulVec u hu3)) (mul_rk1_self Zp4 v (zp4_mulVec v hv3))

/-- **`F(1) ≤ √40`, unconditionally.**  `SharpBounds.cut_trace_bound_one_sharp` with its
    hypothesis `key2` discharged. -/
theorem cut_trace_bound_one_sharp' {M0 M1 : Mat4} {c0 c1 : Mat2}
    (h0 : IsUnitary4 M0) (h1 : IsUnitary4 M1)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1) :
    Complex.normSq (Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1))
      ≤ 40 :=
  SharpBounds.cut_trace_bound_one_sharp h0 h1 k0 k1 (fun Q N hQ hN => key2 Q N hQ hN)

end Key2
