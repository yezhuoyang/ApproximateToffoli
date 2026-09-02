/-
  ApproxToffoli.OneGate

  **`M(1) ≤ 6`, hence `d(0) = d(1) = √7/4`.**

  `M(n) = max |Tr(CCX† U)|` over `U` built from at most `n` CX gates on the line
  A–B–C.  This file closes `n = 0` and `n = 1`:

      M(0) = M(1) = 6 ,     d(0) = d(1) = √(1 − 36/64) = √7/4 = √28/8 ≈ 0.66144 .

  (NOT `√7/(2√2)` — that is `√(7/8) ≈ 0.935`.  The closed form of `√(1−36/64)`
  is `√(28/64) = √(7/16) = √7/4`.)

  ## Why the generic cut machinery is not enough

  `CutForm`/`CutBound` relax the AB-side block of a `BCCut 0` circuit to an
  ARBITRARY `U(4)`, and over that relaxation the maximum is `F(0) = √40 > 6`.
  So for `n ≤ 1` the CX-cost of the 4×4 block has to be tracked; that is the
  predicate `Cost1U4` below.

  ## The chain

  * `achievable_le_one_form` — for `n ≤ 1` one of the two cuts has NO crossing
    gate, so `U = kronABC M c` or `U = kronA_BC c M` with `Cost1U4 M`.
    (No `swapMatAC` mirror is needed: `CCZ8` is A↔C symmetric, so
    `trace_ccz_kronA_BC` is literally the same formula as `trace_ccz_cut0`.)
  * `phi_cost1` — `Φ(M) := ‖Tr M‖ + ‖Tr(CZ·M)‖ ≤ 6` for every `Cost1U4 M`.
    Cost 0 is `SharpBounds.phi_local_le_six`; cost 1 is `cost1_matrix`, proved
    here from scratch.
  * `weighted_six` — the free `U(2)` layer on the third wire contributes weights
    `|c₀₀| = |c₁₁| ≤ 1`, so the objective is at most `Φ(M) ≤ 6`.
  * `achievable_le_one_trace_bound` — `normSq (Tr(U† CCX)) ≤ 36`.
  * `approxToffoli_lower_bound_one`, `d_zero_isLeast`, `d_one_isLeast`.

  ## The cost-1 case

  With `M = (x⊗y)·CZ·(z⊗w)` and, for i = 1,2,
      `wᵢ = aᵢ₁₁bᵢ₁₁`,  `vᵢ = −aᵢ₁₀bᵢ₀₁`,  `δᵢ = det aᵢ · det bᵢ`,
  unitarity gives `(bᵢaᵢ)₀₀ = δᵢ w̄ᵢ − vᵢ`, `(bᵢaᵢ)₁₁ = wᵢ − δᵢ v̄ᵢ` and
  `‖wᵢ‖ + ‖vᵢ‖ ≤ 1` (Cauchy–Schwarz between row 1 of `aᵢ` and column 1 of `bᵢ`).
  Dividing out a square root `εᵢ² = δᵢ` (`exists_unit_sqrt`) puts the objective in
  the `δ = 1` normal form

      T  = 4·Re(w₁−v₁)·Re(w₂−v₂) − 2(w₁−v̄₁)(w₂−v̄₂)          (`Tw`)
      κ  = (w₁−v₁)(w₂−v₂) − 2w₁w₂                            (`Kp`)
      Tr M = ε₁ε₂ T ,   Tr(CZ·M) = ε₁ε₂ (T − 2κ) .

  `T` and `T − 2κ` are ℝ-BILINEAR in `((w₁,v₁),(w₂,v₂))`, so the triangle
  inequality splits the objective into the four "pure" blocks `(w,w)`, `(w,v)`,
  `(v,w)`, `(v,v)` with weights summing to `(‖w₁‖+‖v₁‖)(‖w₂‖+‖v₂‖) ≤ 1.  Each
  block is bounded by `6‖·‖‖·‖` (`blockA`…`blockD`), and all four reduce to the
  single real inequality `core_real`, i.e. `√(P² + n² − Q²) + |P| + |Q| ≤ 3n`.
  Equality holds exactly at `M = CZ`, so `M(1) = 6` is sharp.

  Everything below was checked with `lean_run_code` against the built
  `ApproxToffoli.CutMain` / `.SharpBounds` / `.CurveWitnesses`; the tree itself was
  not edited and `lake build` was not run.
-/

import ApproxToffoli.CutMain
import ApproxToffoli.SharpBounds
import ApproxToffoli.CurveWitnesses

open Matrix Complex

noncomputable section

namespace Cost1

/-! ## §1  The real core

`F + 2|P| + 2|Q| ≤ 6n` whenever `F² ≤ 4(P² + n² − Q²)` and `|P|, |Q| ≤ n`.
Equality at `|P| = |Q| = n`, `F = 2n`, which is the configuration `M = CZ`. -/

theorem core_real {F P Q n : ℝ} (hn : 0 ≤ n)
    (hF2 : F ^ 2 ≤ 4 * (P ^ 2 + n ^ 2 - Q ^ 2)) (hP : |P| ≤ n) (hQ : |Q| ≤ n) :
    F + 2 * |P| + 2 * |Q| ≤ 6 * n := by
  have hp0 : 0 ≤ |P| := abs_nonneg _
  have hq0 : 0 ≤ |Q| := abs_nonneg _
  have hpp : P ^ 2 = |P| ^ 2 := (sq_abs P).symm
  have hqq : Q ^ 2 = |Q| ^ 2 := (sq_abs Q).symm
  have hR : 0 ≤ 6 * n - 2 * |P| - 2 * |Q| := by linarith
  have key : F ^ 2 ≤ (6 * n - 2 * |P| - 2 * |Q|) ^ 2 := by
    rw [hpp, hqq] at hF2
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (by linarith : (0:ℝ) ≤ 6 * n - 2 * |Q|),
      sq_nonneg (n - |Q|), hp0, hq0, hn]
  nlinarith [key, hR]

/-! ## §2  The bilinear kernel and the four blocks

`Fst a b = 4·Re(a)·Re(b) − 2ab` is the value of `Tw` on a pure block; its modulus
squared is `4(Re(a b̄)² + Im(ab)²)`, which is what feeds `core_real`. -/

def Fst (a b : ℂ) : ℂ := 4 * (a.re : ℂ) * (b.re : ℂ) - 2 * a * b

lemma normSq_Fst (a b : ℂ) :
    ‖Fst a b‖ ^ 2 = 4 * ((a * (starRingEnd ℂ) b).re ^ 2 + (a * b).im ^ 2) := by
  rw [Complex.sq_norm]
  simp [Fst, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im]
  ring

lemma norm_mul_conj (a b : ℂ) : ‖a * (starRingEnd ℂ) b‖ = ‖a‖ * ‖b‖ := by
  rw [norm_mul, norm_conj]

lemma nsq_mul (a b : ℂ) : (‖a‖ * ‖b‖) ^ 2 = (a * b).re ^ 2 + (a * b).im ^ 2 := by
  rw [← norm_mul, Complex.sq_norm, Complex.normSq_apply]; ring

lemma nsq_mul_conj (a b : ℂ) :
    (‖a‖ * ‖b‖) ^ 2 = (a * (starRingEnd ℂ) b).re ^ 2 + (a * (starRingEnd ℂ) b).im ^ 2 := by
  rw [← norm_mul_conj, Complex.sq_norm, Complex.normSq_apply]; ring

/-- `core_real` with `(P, Q) = (Re(a b̄), Re(ab))`. -/
theorem block1 (a b : ℂ) :
    ‖Fst a b‖ + 2 * |(a * (starRingEnd ℂ) b).re| + 2 * |(a * b).re| ≤ 6 * (‖a‖ * ‖b‖) := by
  refine core_real (by positivity) ?_ ?_ ?_
  · rw [normSq_Fst]; nlinarith [nsq_mul a b]
  · rw [← norm_mul_conj a b]; exact Complex.abs_re_le_norm _
  · rw [← norm_mul]; exact Complex.abs_re_le_norm _

/-- `core_real` with `(P, Q) = (Im(ab), Im(a b̄))`. -/
theorem block2 (a b : ℂ) :
    ‖Fst a b‖ + 2 * |(a * b).im| + 2 * |(a * (starRingEnd ℂ) b).im| ≤ 6 * (‖a‖ * ‖b‖) := by
  refine core_real (by positivity) ?_ ?_ ?_
  · rw [normSq_Fst]; nlinarith [nsq_mul_conj a b]
  · rw [← norm_mul]; exact Complex.abs_im_le_norm _
  · rw [← norm_mul_conj a b]; exact Complex.abs_im_le_norm _

lemma abs_add2 (x y : ℝ) : |2 * (x + y)| ≤ 2 * |x| + 2 * |y| :=
  abs_le.mpr ⟨by linarith [neg_abs_le x, neg_abs_le y],
    by linarith [le_abs_self x, le_abs_self y]⟩

lemma abs_sub2 (x y : ℝ) : |2 * (x - y)| ≤ 2 * |x| + 2 * |y| :=
  abs_le.mpr ⟨by linarith [neg_abs_le x, le_abs_self y],
    by linarith [le_abs_self x, neg_abs_le y]⟩

lemma abs_neg2 (x y : ℝ) : |(-(2 * (x + y)))| ≤ 2 * |x| + 2 * |y| :=
  abs_le.mpr ⟨by linarith [le_abs_self x, le_abs_self y],
    by linarith [neg_abs_le x, neg_abs_le y]⟩

lemma abs_negsub2 (x y : ℝ) : |(-(2 * (x - y)))| ≤ 2 * |x| + 2 * |y| :=
  abs_le.mpr ⟨by linarith [le_abs_self x, neg_abs_le y],
    by linarith [neg_abs_le x, le_abs_self y]⟩

lemma eqA (a b : ℂ) :
    Fst a b + 2 * a * b = ((2 * ((a * (starRingEnd ℂ) b).re + (a * b).re) : ℝ) : ℂ) := by
  simp only [Fst, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.add_re, Complex.add_im]
  constructor <;> ring

lemma eqD (a b : ℂ) :
    Fst a b - 2 * (starRingEnd ℂ) a * (starRingEnd ℂ) b
      = ((2 * ((a * (starRingEnd ℂ) b).re - (a * b).re) : ℝ) : ℂ) := by
  simp only [Fst, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat]
  constructor <;> ring

lemma eqB (a b : ℂ) :
    Fst a b - 2 * a * (starRingEnd ℂ) b
      = ((-(2 * ((a * b).im + (a * (starRingEnd ℂ) b).im)) : ℝ) : ℂ) * Complex.I := by
  simp only [Fst, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im]
  constructor <;> ring

lemma eqC (a b : ℂ) :
    Fst a b - 2 * (starRingEnd ℂ) a * b
      = ((-(2 * ((a * b).im - (a * (starRingEnd ℂ) b).im)) : ℝ) : ℂ) * Complex.I := by
  simp only [Fst, Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im]
  constructor <;> ring

/-- Block `(w, w)`. -/
theorem blockA (a b : ℂ) : ‖Fst a b‖ + ‖Fst a b + 2 * a * b‖ ≤ 6 * (‖a‖ * ‖b‖) := by
  have h : ‖Fst a b + 2 * a * b‖ ≤ 2 * |(a * (starRingEnd ℂ) b).re| + 2 * |(a * b).re| := by
    rw [eqA, Complex.norm_real, Real.norm_eq_abs]
    exact abs_add2 _ _
  linarith [block1 a b, h]

/-- Block `(v, v)`. -/
theorem blockD (a b : ℂ) :
    ‖Fst a b‖ + ‖Fst a b - 2 * (starRingEnd ℂ) a * (starRingEnd ℂ) b‖ ≤ 6 * (‖a‖ * ‖b‖) := by
  have h : ‖Fst a b - 2 * (starRingEnd ℂ) a * (starRingEnd ℂ) b‖
      ≤ 2 * |(a * (starRingEnd ℂ) b).re| + 2 * |(a * b).re| := by
    rw [eqD, Complex.norm_real, Real.norm_eq_abs]
    exact abs_sub2 _ _
  linarith [block1 a b, h]

/-- Block `(w, v)`. -/
theorem blockB (a b : ℂ) :
    ‖Fst a b‖ + ‖Fst a b - 2 * a * (starRingEnd ℂ) b‖ ≤ 6 * (‖a‖ * ‖b‖) := by
  have h : ‖Fst a b - 2 * a * (starRingEnd ℂ) b‖
      ≤ 2 * |(a * b).im| + 2 * |(a * (starRingEnd ℂ) b).im| := by
    rw [eqB, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_neg2 _ _
  linarith [block2 a b, h]

/-- Block `(v, w)`. -/
theorem blockC (a b : ℂ) :
    ‖Fst a b‖ + ‖Fst a b - 2 * (starRingEnd ℂ) a * b‖ ≤ 6 * (‖a‖ * ‖b‖) := by
  have h : ‖Fst a b - 2 * (starRingEnd ℂ) a * b‖
      ≤ 2 * |(a * b).im| + 2 * |(a * (starRingEnd ℂ) b).im| := by
    rw [eqC, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_negsub2 _ _
  linarith [block2 a b, h]

/-! ## §3  The scalar cost-1 bound

`Tw` is `Tr M` and `Tw − 2·Kp` is `Tr(CZ·M)`, in the normalised coordinates. -/

def Tw (w1 v1 w2 v2 : ℂ) : ℂ :=
  4 * (((w1 - v1).re : ℝ) : ℂ) * (((w2 - v2).re : ℝ) : ℂ)
    - 2 * (w1 - (starRingEnd ℂ) v1) * (w2 - (starRingEnd ℂ) v2)

def Kp (w1 v1 w2 v2 : ℂ) : ℂ := (w1 - v1) * (w2 - v2) - 2 * w1 * w2

lemma Tw_split (w1 v1 w2 v2 : ℂ) :
    Tw w1 v1 w2 v2 = Fst w1 w2 + (-Fst w1 ((starRingEnd ℂ) v2))
      + (-Fst ((starRingEnd ℂ) v1) w2) + Fst ((starRingEnd ℂ) v1) ((starRingEnd ℂ) v2) := by
  simp only [Tw, Fst, Complex.sub_re, Complex.conj_re, Complex.ofReal_sub]
  ring

lemma T2_split (w1 v1 w2 v2 : ℂ) :
    Tw w1 v1 w2 v2 - 2 * Kp w1 v1 w2 v2
      = (Fst w1 w2 + 2 * w1 * w2)
        + (-(Fst w1 ((starRingEnd ℂ) v2) - 2 * w1 * v2))
        + (-(Fst ((starRingEnd ℂ) v1) w2 - 2 * v1 * w2))
        + (Fst ((starRingEnd ℂ) v1) ((starRingEnd ℂ) v2) - 2 * v1 * v2) := by
  simp only [Tw, Kp, Fst, Complex.sub_re, Complex.conj_re, Complex.ofReal_sub]
  ring

/-- **The cost-1 scalar bound.**  Sharp: equality at `w₁ = w₂ = 1`, `v = 0`
    (i.e. `M = CZ`), where `‖Tw‖ = 2` and `‖Tw − 2Kp‖ = 4`. -/
theorem cost1_scalar (w1 v1 w2 v2 : ℂ) (h1 : ‖w1‖ + ‖v1‖ ≤ 1) (h2 : ‖w2‖ + ‖v2‖ ≤ 1) :
    ‖Tw w1 v1 w2 v2‖ + ‖Tw w1 v1 w2 v2 - 2 * Kp w1 v1 w2 v2‖ ≤ 6 := by
  have hc1 : ‖(starRingEnd ℂ) v1‖ = ‖v1‖ := norm_conj v1
  have hc2 : ‖(starRingEnd ℂ) v2‖ = ‖v2‖ := norm_conj v2
  have hA := blockA w1 w2
  have hB := blockB w1 ((starRingEnd ℂ) v2)
  have hC := blockC ((starRingEnd ℂ) v1) w2
  have hD := blockD ((starRingEnd ℂ) v1) ((starRingEnd ℂ) v2)
  simp only [Complex.conj_conj] at hB hC hD
  rw [hc2] at hB
  rw [hc1] at hC
  rw [hc1, hc2] at hD
  have e1 : ‖Tw w1 v1 w2 v2‖
      ≤ ‖Fst w1 w2‖ + ‖Fst w1 ((starRingEnd ℂ) v2)‖
        + ‖Fst ((starRingEnd ℂ) v1) w2‖
        + ‖Fst ((starRingEnd ℂ) v1) ((starRingEnd ℂ) v2)‖ := by
    rw [Tw_split]
    refine le_trans (SharpBounds.norm_add4_le' _ _ _ _) ?_
    simp only [norm_neg]
    exact le_rfl
  have e2 : ‖Tw w1 v1 w2 v2 - 2 * Kp w1 v1 w2 v2‖
      ≤ ‖Fst w1 w2 + 2 * w1 * w2‖
        + ‖Fst w1 ((starRingEnd ℂ) v2) - 2 * w1 * v2‖
        + ‖Fst ((starRingEnd ℂ) v1) w2 - 2 * v1 * w2‖
        + ‖Fst ((starRingEnd ℂ) v1) ((starRingEnd ℂ) v2) - 2 * v1 * v2‖ := by
    rw [T2_split]
    refine le_trans (SharpBounds.norm_add4_le' _ _ _ _) ?_
    simp only [norm_neg]
    exact le_rfl
  have hprod : ‖w1‖ * ‖w2‖ + ‖w1‖ * ‖v2‖ + ‖v1‖ * ‖w2‖ + ‖v1‖ * ‖v2‖ ≤ 1 := by
    nlinarith [norm_nonneg w1, norm_nonneg v1, norm_nonneg w2, norm_nonneg v2, h1, h2]
  linarith [e1, e2, hA, hB, hC, hD, hprod]

/-! ## §4  A unit square root

Needed to divide out `δ = det a · det b`; Mathlib has no `Matrix` polar
decomposition and no ready-made unit square root, so here is the explicit
`(1+z)/‖1+z‖` construction (with `z = −1` handled by `i`). -/

theorem exists_unit_sqrt {z : ℂ} (hz : ‖z‖ = 1) : ∃ e : ℂ, e ^ 2 = z ∧ ‖e‖ = 1 := by
  by_cases h : z = -1
  · exact ⟨Complex.I, by rw [h]; simp [Complex.I_sq], Complex.norm_I⟩
  · have h1 : (1 : ℂ) + z ≠ 0 := by
      intro hc; apply h; linear_combination hc
    have hn : ((‖(1 : ℂ) + z‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using norm_ne_zero_iff.mpr h1
    have hzz : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj]; norm_cast; rw [← Complex.sq_norm, hz]; norm_num
    have hsq : ((‖(1 : ℂ) + z‖ : ℝ) : ℂ) ^ 2 = (1 + z) * (1 + (starRingEnd ℂ) z) := by
      rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
      rw [map_add, map_one]
      ring
    refine ⟨(1 + z) / ((‖(1 : ℂ) + z‖ : ℝ) : ℂ), ?_, ?_⟩
    · rw [div_pow, hsq, div_eq_iff (by rw [← hsq]; exact pow_ne_zero 2 hn)]
      linear_combination (-(1 + z)) * hzz
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h1)]

lemma mul_conj_unit {z : ℂ} (h : ‖z‖ = 1) : z * (starRingEnd ℂ) z = 1 := by
  rw [Complex.mul_conj]
  have : Complex.normSq z = 1 := by rw [← Complex.sq_norm, h]; norm_num
  exact_mod_cast this

/-! ## §5  Entries of a `2×2` unitary, and the normalised per-index data -/

lemma u2_comm {a : Mat2} (h : IsUnitary2 a) : a * aᴴ = 1 := mul_eq_one_comm.mp h

lemma u2_row1_sq {a : Mat2} (h : IsUnitary2 a) :
    a 1 0 * (starRingEnd ℂ) (a 1 0) + a 1 1 * (starRingEnd ℂ) (a 1 1) = 1 := by
  have h1 : (a * aᴴ) 1 1 = 1 := by rw [u2_comm h]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simpa [Matrix.conjTranspose_apply] using h1

lemma u2_offdiag {a : Mat2} (h : IsUnitary2 a) :
    a 1 0 * (starRingEnd ℂ) (a 0 0) + a 1 1 * (starRingEnd ℂ) (a 0 1) = 0 := by
  have h1 : (a * aᴴ) 1 0 = 0 := by rw [u2_comm h]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h1
  simpa [Matrix.conjTranspose_apply] using h1

/-- `U(2) = {[[p, −δq̄], [q, δp̄]] : |p|²+|q|² = 1, |δ| = 1}`, entry `(0,0)` half. -/
lemma u2_a00 {a : Mat2} (h : IsUnitary2 a) : a 0 0 = a.det * (starRingEnd ℂ) (a 1 1) := by
  have r1 := u2_row1_sq h
  have r2 := congrArg (starRingEnd ℂ) (u2_offdiag h)
  simp only [map_add, map_mul, Complex.conj_conj, map_zero] at r2
  rw [Matrix.det_fin_two]
  linear_combination (-(a 0 0)) * r1 + (a 1 0) * r2

lemma u2_det_norm {a : Mat2} (h : IsUnitary2 a) : ‖a.det‖ = 1 := by
  have hd : (aᴴ * a).det = 1 := by rw [h]; simp
  rw [Matrix.det_mul, Matrix.det_conjTranspose] at hd
  have hns : Complex.normSq a.det = 1 := by
    have hc : ((Complex.normSq a.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact hd
    exact_mod_cast hc
  have h2 : ‖a.det‖ ^ 2 = 1 := by rw [Complex.sq_norm]; exact hns
  nlinarith [norm_nonneg a.det, h2]

lemma isUnitary2_mul' {a b : Mat2} (ha : IsUnitary2 a) (hb : IsUnitary2 b) :
    IsUnitary2 (b * a) := by
  unfold IsUnitary2 at *
  rw [Matrix.conjTranspose_mul]
  calc aᴴ * bᴴ * (b * a) = aᴴ * (bᴴ * b) * a := by noncomm_ring
    _ = 1 := by rw [hb, Matrix.mul_one, ha]

lemma u2_row1_norm {a : Mat2} (h : IsUnitary2 a) : ‖a 1 0‖ ^ 2 + ‖a 1 1‖ ^ 2 = 1 := by
  have hs := u2_row1_sq h
  simp only [Complex.sq_norm]
  have hc : ((Complex.normSq (a 1 0) + Complex.normSq (a 1 1) : ℝ) : ℂ) = 1 := by
    push_cast
    simp only [Complex.normSq_eq_conj_mul_self]
    linear_combination hs
  exact_mod_cast hc

lemma u2_col1_norm {a : Mat2} (h : IsUnitary2 a) : ‖a 0 1‖ ^ 2 + ‖a 1 1‖ ^ 2 = 1 := by
  simp only [Complex.sq_norm]; exact u2_col1 h

/-- `(b·a)₀₀ = δ·w̄ − v` with `w = a₁₁b₁₁`, `v = −a₁₀b₀₁`, `δ = det a · det b`. -/
lemma cornerG {a b : Mat2} (ha : IsUnitary2 a) (hb : IsUnitary2 b) :
    (b * a) 0 0
      = (a.det * b.det) * (starRingEnd ℂ) (a 1 1 * b 1 1) - (-(a 1 0 * b 0 1)) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, u2_a00 ha, u2_a00 hb]
  simp only [map_mul]
  ring

/-- `(b·a)₁₁ = w − δ·v̄`, obtained from `cornerG` applied to the unitary `b·a`. -/
lemma cornerH {a b : Mat2} (ha : IsUnitary2 a) (hb : IsUnitary2 b) :
    (b * a) 1 1
      = a 1 1 * b 1 1 - (a.det * b.det) * (starRingEnd ℂ) (-(a 1 0 * b 0 1)) := by
  have hG := cornerG ha hb
  have hcu := isUnitary2_mul' ha hb
  have hdet : (b * a).det = a.det * b.det := by rw [Matrix.det_mul]; ring
  have hGH := u2_a00 hcu
  rw [hdet] at hGH
  have hd1 : ‖a.det * b.det‖ = 1 := by rw [norm_mul, u2_det_norm ha, u2_det_norm hb]; norm_num
  have hdd := mul_conj_unit hd1
  simp only [map_mul] at hdd
  have hconj := congrArg (starRingEnd ℂ) hGH
  simp only [map_mul, Complex.conj_conj] at hconj
  have hH : (b * a) 1 1 = (a.det * b.det) * (starRingEnd ℂ) ((b * a) 0 0) := by
    linear_combination (-(a.det * b.det)) * hconj - ((b * a) 1 1) * hdd
  rw [hH, hG]
  simp only [map_sub, map_mul, map_neg, Complex.conj_conj]
  linear_combination (a 1 1 * b 1 1) * hdd

/-- **Per-index normalised data.**  The unit `e` is a square root of
    `det a · det b`; after dividing it out the two corner entries of `b·a` are
    `w̄ − v` and `w − v̄`, and `‖w‖ + ‖v‖ ≤ 1` by Cauchy–Schwarz between row 1 of
    `a` and column 1 of `b`. -/
lemma index_data {a b : Mat2} (ha : IsUnitary2 a) (hb : IsUnitary2 b) :
    ∃ e w v : ℂ, ‖e‖ = 1 ∧ ‖w‖ + ‖v‖ ≤ 1 ∧
      (b * a) 0 0 = e * ((starRingEnd ℂ) w - v) ∧
      (b * a) 1 1 = e * (w - (starRingEnd ℂ) v) ∧
      a 1 1 * b 1 1 = e * w ∧ a 1 0 * b 0 1 = -(e * v) := by
  have hd : ‖a.det * b.det‖ = 1 := by
    rw [norm_mul, u2_det_norm ha, u2_det_norm hb]; norm_num
  obtain ⟨ε, hε2, hεn⟩ := exists_unit_sqrt hd
  have hεc : ε * (starRingEnd ℂ) ε = 1 := mul_conj_unit hεn
  refine ⟨ε, (starRingEnd ℂ) ε * (a 1 1 * b 1 1), (starRingEnd ℂ) ε * (-(a 1 0 * b 0 1)),
    hεn, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : ‖(starRingEnd ℂ) ε * (a 1 1 * b 1 1)‖ = ‖a 1 1‖ * ‖b 1 1‖ := by
      rw [norm_mul, norm_conj, hεn, one_mul, norm_mul]
    have e2 : ‖(starRingEnd ℂ) ε * (-(a 1 0 * b 0 1))‖ = ‖a 1 0‖ * ‖b 0 1‖ := by
      rw [norm_mul, norm_conj, hεn, one_mul, norm_neg, norm_mul]
    rw [e1, e2]
    exact SharpBounds.weights_le_one _ _ _ _ (by linarith [u2_row1_norm ha])
      (by linarith [u2_col1_norm hb])
  · rw [cornerG ha hb]
    simp only [map_mul, Complex.conj_conj]
    linear_combination (-((starRingEnd ℂ) (a 1 1) * (starRingEnd ℂ) (b 1 1))) * hε2
      - (a 1 0 * b 0 1) * hεc
  · rw [cornerH ha hb]
    simp only [map_mul, Complex.conj_conj, map_neg]
    linear_combination (-(a 1 1 * b 1 1)) * hεc
      - ((starRingEnd ℂ) (a 1 0) * (starRingEnd ℂ) (b 0 1)) * hε2
  · linear_combination (-(a 1 1 * b 1 1)) * hεc
  · linear_combination (-(a 1 0 * b 0 1)) * hεc

/-! ## §6  The cost-1 matrix bound -/

lemma quad_re (z1 z2 : ℂ) :
    (starRingEnd ℂ) z1 * (starRingEnd ℂ) z2 + (starRingEnd ℂ) z1 * z2
      + z1 * (starRingEnd ℂ) z2 - z1 * z2
      = 4 * ((z1.re : ℝ) : ℂ) * ((z2.re : ℝ) : ℂ) - 2 * (z1 * z2) := by
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  constructor <;> ring

lemma re_conj_sub (w v : ℂ) : (w - v).re = (w - (starRingEnd ℂ) v).re := by
  simp [Complex.sub_re, Complex.conj_re]

lemma trace_zp4_mul (M : Mat4) : (Zp4 * M).trace = M.trace - 2 * M 3 3 := by
  simp [Zp4, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Fin.sum_univ_four]
  ring

lemma trace_zp4_kron2 (d1 d2 : Mat2) :
    (Zp4 * kron2 d1 d2).trace
      = d1 0 0 * d2 0 0 + d1 0 0 * d2 1 1 + d1 1 1 * d2 0 0 - d1 1 1 * d2 1 1 := by
  simp [Zp4, kron2, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.of_apply, Fin.sum_univ_four]
  ring

lemma entry33 (a1 a2 b1 b2 : Mat2) :
    (kron2 a1 a2 * Zp4 * kron2 b1 b2) 3 3
      = a1 1 0 * b1 0 1 * (a2 1 0 * b2 0 1) + a1 1 0 * b1 0 1 * (a2 1 1 * b2 1 1)
        + a1 1 1 * b1 1 1 * (a2 1 0 * b2 0 1) - a1 1 1 * b1 1 1 * (a2 1 1 * b2 1 1) := by
  simp [Zp4, kron2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Fin.sum_univ_four]
  ring

lemma trace_cz_prod (a1 a2 b1 b2 : Mat2) :
    (kron2 a1 a2 * Zp4 * kron2 b1 b2).trace = (Zp4 * kron2 (b1 * a1) (b2 * a2)).trace := by
  rw [← kron2_mul, Matrix.trace_mul_comm (kron2 a1 a2 * Zp4) (kron2 b1 b2),
    ← Matrix.mul_assoc, Matrix.trace_mul_comm (kron2 b1 b2 * kron2 a1 a2) Zp4]

/-- **`Φ(M) ≤ 6` for `M = (x⊗y)·CZ·(z⊗w)`.**  Sharp: equality at `M = CZ`. -/
theorem cost1_matrix {a1 a2 b1 b2 : Mat2}
    (ha1 : IsUnitary2 a1) (ha2 : IsUnitary2 a2) (hb1 : IsUnitary2 b1) (hb2 : IsUnitary2 b2) :
    ‖(kron2 a1 a2 * Zp4 * kron2 b1 b2).trace‖
      + ‖(Zp4 * (kron2 a1 a2 * Zp4 * kron2 b1 b2)).trace‖ ≤ 6 := by
  obtain ⟨e1, w1, v1, he1, hn1, hG1, hH1, hW1, hV1⟩ := index_data ha1 hb1
  obtain ⟨e2, w2, v2, he2, hn2, hG2, hH2, hW2, hV2⟩ := index_data ha2 hb2
  have hq := quad_re (w1 - (starRingEnd ℂ) v1) (w2 - (starRingEnd ℂ) v2)
  simp only [map_sub, Complex.conj_conj] at hq
  have hT : (kron2 a1 a2 * Zp4 * kron2 b1 b2).trace = e1 * e2 * Tw w1 v1 w2 v2 := by
    rw [trace_cz_prod, trace_zp4_kron2, hG1, hG2, hH1, hH2, Tw,
      re_conj_sub w1 v1, re_conj_sub w2 v2]
    linear_combination (e1 * e2) * hq
  have hK : (kron2 a1 a2 * Zp4 * kron2 b1 b2) 3 3 = e1 * e2 * Kp w1 v1 w2 v2 := by
    rw [entry33, hW1, hW2, hV1, hV2, Kp]; ring
  have hT2 : (Zp4 * (kron2 a1 a2 * Zp4 * kron2 b1 b2)).trace
      = e1 * e2 * (Tw w1 v1 w2 v2 - 2 * Kp w1 v1 w2 v2) := by
    rw [trace_zp4_mul, hT, hK]; ring
  have hnorm : ∀ z : ℂ, ‖e1 * e2 * z‖ = ‖z‖ := by
    intro z; rw [norm_mul, norm_mul, he1, he2]; ring
  rw [hT, hT2, hnorm, hnorm]
  exact cost1_scalar w1 v1 w2 v2 hn1 hn2

/-! ## §7  Two-qubit unitaries of CX-cost at most one -/

/-- Two-qubit unitaries reachable with at most one CX gate on the pair.  `Zp4` is
    `CZ`; `CNOT = (1⊗H)·CZ·(1⊗H)` and `CNOT_BA = (H⊗1)·CZ·(H⊗1)`, so no
    generality is lost by taking the crossing gate to be `CZ`. -/
inductive Cost1U4 : Mat4 → Prop where
  | zero (x y : Mat2) (hx : IsUnitary2 x) (hy : IsUnitary2 y) : Cost1U4 (kron2 x y)
  | one (x y z w : Mat2) (hx : IsUnitary2 x) (hy : IsUnitary2 y)
      (hz : IsUnitary2 z) (hw : IsUnitary2 w) :
      Cost1U4 (kron2 x y * Zp4 * kron2 z w)

lemma Cost1U4_mul_left {M : Mat4} (h : Cost1U4 M) {x y : Mat2}
    (hx : IsUnitary2 x) (hy : IsUnitary2 y) : Cost1U4 (kron2 x y * M) := by
  cases h with
  | zero x' y' hx' hy' =>
      rw [kron2_mul]
      exact Cost1U4.zero _ _ (isUnitary2_mul hx hx') (isUnitary2_mul hy hy')
  | one x' y' z' w' hx' hy' hz' hw' =>
      have e : kron2 x y * (kron2 x' y' * Zp4 * kron2 z' w')
          = kron2 (x * x') (y * y') * Zp4 * kron2 z' w' := by
        rw [← kron2_mul]; noncomm_ring
      rw [e]
      exact Cost1U4.one _ _ _ _ (isUnitary2_mul hx hx') (isUnitary2_mul hy hy') hz' hw'

lemma Cost1U4_mul_right {M : Mat4} (h : Cost1U4 M) {x y : Mat2}
    (hx : IsUnitary2 x) (hy : IsUnitary2 y) : Cost1U4 (M * kron2 x y) := by
  cases h with
  | zero x' y' hx' hy' =>
      rw [kron2_mul]
      exact Cost1U4.zero _ _ (isUnitary2_mul hx' hx) (isUnitary2_mul hy' hy)
  | one x' y' z' w' hx' hy' hz' hw' =>
      have e : kron2 x' y' * Zp4 * kron2 z' w' * kron2 x y
          = kron2 x' y' * Zp4 * kron2 (z' * x) (w' * y) := by
        rw [← kron2_mul]; noncomm_ring
      rw [e]
      exact Cost1U4.one _ _ _ _ hx' hy' (isUnitary2_mul hz' hx) (isUnitary2_mul hw' hy)

set_option maxHeartbeats 800000 in
-- Heartbeat bump: 16-case `fin_cases × fin_cases` on `Fin 4` with a triple
-- 4×4 product and `1/√2` arithmetic.
lemma cnotAB_eq_cz : cutCNOT_AB_4 = kron2 1 Hgate * Zp4 * kron2 1 Hgate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutCNOT_AB_4, kron2, Zp4, Hgate, proj0, proj1, I₂, pauliX, Matrix.mul_apply,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2]

set_option maxHeartbeats 800000 in
-- Heartbeat bump: as `cnotAB_eq_cz`.
lemma cnotBA_eq_cz : CNOT_BA_4 = kron2 Hgate 1 * Zp4 * kron2 Hgate 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CNOT_BA_4, kron2, Zp4, Hgate, proj0, proj1, I₂, pauliX, Matrix.mul_apply,
      Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.of_apply,
      Fin.sum_univ_four] <;>
    ring_nf <;>
    norm_num [invSqrt2_pow2]

lemma cost1_cnotAB : Cost1U4 cutCNOT_AB_4 := by
  rw [cnotAB_eq_cz]
  exact Cost1U4.one 1 Hgate 1 Hgate isUnitary2_one hgate_unitary isUnitary2_one hgate_unitary

lemma cost1_cnotBA : Cost1U4 CNOT_BA_4 := by
  rw [cnotBA_eq_cz]
  exact Cost1U4.one Hgate 1 Hgate 1 hgate_unitary isUnitary2_one hgate_unitary isUnitary2_one

lemma norm_diag_le_one {c : Mat2} (h : IsUnitary2 c) : ‖c 0 0‖ ≤ 1 := by
  have := u2_row_norm h
  nlinarith [norm_nonneg (c 0 0), norm_nonneg (c 0 1)]

/-- Cost-0 case: this IS `SharpBounds.phi_local_le_six`. -/
theorem phi_zero {x y : Mat2} (hx : IsUnitary2 x) (hy : IsUnitary2 y) :
    ‖(kron2 x y).trace‖ + ‖(Zp4 * kron2 x y).trace‖ ≤ 6 := by
  rw [trace_kron2, trace_zp4_kron2,
    show x 0 0 * y 0 0 + x 0 0 * y 1 1 + x 1 1 * y 0 0 - x 1 1 * y 1 1
      = x 0 0 * (y 0 0 + y 1 1) + x 1 1 * (y 0 0 - y 1 1) by ring]
  exact SharpBounds.phi_local_le_six (u2_diag_norm hx) (norm_diag_le_one hx)
    (u2_diag_norm hy) (norm_diag_le_one hy)

/-- **`Φ(M) ≤ 6` for every two-qubit unitary of CX-cost at most one.** -/
theorem phi_cost1 {M : Mat4} (h : Cost1U4 M) : ‖M.trace‖ + ‖(Zp4 * M).trace‖ ≤ 6 := by
  cases h with
  | zero x y hx hy => exact phi_zero hx hy
  | one x y z w hx hy hz hw => exact cost1_matrix hx hy hz hw

/-! ## §8  Circuit normal form for `n ≤ 1`, and the trace bound -/

lemma trace_kronA_BC (c : Mat2) (M : Mat4) :
    Matrix.trace (kronA_BC c M) = (c 0 0 + c 1 1) * Matrix.trace M := by
  simp [kronA_BC, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Fin.sum_univ_eight,
    Fin.sum_univ_four]
  ring

/-- The A|BC mirror of `trace_ccz_cut0`.  Identical formula, because `CCZ8` is
    symmetric under A↔C and its odd block is `Zp4` in both cuts. -/
lemma trace_ccz_kronA_BC (c : Mat2) (M : Mat4) :
    Matrix.trace (CCZ8 * kronA_BC c M)
      = c 0 0 * Matrix.trace M + c 1 1 * Matrix.trace (Zp4 * M) := by
  simp [CCZ8, Zp4, kronA_BC, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.of_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
  ring

lemma achievable_zero_form {U : Mat8} (h : AchievableCircuit 0 U) :
    ∃ a b c : Mat2, IsUnitary2 a ∧ IsUnitary2 b ∧ IsUnitary2 c ∧
      U = singleQubitLayer a b c := by
  cases h with
  | single_layer a b c ha hb hc => exact ⟨a, b, c, ha, hb, hc, rfl⟩

/-- **Normal form for `n ≤ 1`.**  With at most one CX gate one of the two cuts has
    NO crossing gate, and the 4×4 block on the other side has CX-cost ≤ 1. -/
theorem achievable_le_one_form {n : ℕ} {U : Mat8} (hn : n ≤ 1) (h : AchievableCircuit n U) :
    (∃ M c, Cost1U4 M ∧ IsUnitary2 c ∧ U = kronABC M c) ∨
    (∃ c M, Cost1U4 M ∧ IsUnitary2 c ∧ U = kronA_BC c M) := by
  interval_cases n
  · obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := achievable_zero_form h
    exact Or.inl ⟨kron2 a b, c, Cost1U4.zero a b ha hb, hc,
      singleQubitLayer_eq_kronABC a b c⟩
  · cases h with
    | weaken h0 =>
        obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := achievable_zero_form h0
        exact Or.inl ⟨kron2 a b, c, Cost1U4.zero a b ha hb, hc,
          singleQubitLayer_eq_kronABC a b c⟩
    | compose uA uB uC hA hB hC hCX rest =>
        obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := achievable_zero_form rest
        rcases hCX with rfl | rfl | rfl | rfl
        · refine Or.inl ⟨kron2 a b * cutCNOT_AB_4 * kron2 uA uB, c * I₂ * uC, ?_, ?_, ?_⟩
          · exact Cost1U4_mul_right (Cost1U4_mul_left cost1_cnotAB ha hb) hA hB
          · exact isUnitary2_mul (isUnitary2_mul hc isUnitary2_I2) hC
          · rw [singleQubitLayer_eq_kronABC, cx_ab_eq_kronABC, singleQubitLayer_eq_kronABC,
              kronABC_mul, kronABC_mul]
        · refine Or.inl ⟨kron2 a b * CNOT_BA_4 * kron2 uA uB, c * I₂ * uC, ?_, ?_, ?_⟩
          · exact Cost1U4_mul_right (Cost1U4_mul_left cost1_cnotBA ha hb) hA hB
          · exact isUnitary2_mul (isUnitary2_mul hc isUnitary2_I2) hC
          · rw [singleQubitLayer_eq_kronABC, cx_ba_eq_kronABC, singleQubitLayer_eq_kronABC,
              kronABC_mul, kronABC_mul]
        · refine Or.inr ⟨a * I₂ * uA, kron2 b c * cutCNOT_AB_4 * kron2 uB uC, ?_, ?_, ?_⟩
          · exact Cost1U4_mul_right (Cost1U4_mul_left cost1_cnotAB hb hc) hB hC
          · exact isUnitary2_mul (isUnitary2_mul ha isUnitary2_I2) hA
          · rw [singleQubitLayer_eq_kronA_BC, cx_bc_eq_kronA_BC, singleQubitLayer_eq_kronA_BC,
              kronA_BC_mul, kronA_BC_mul]
        · refine Or.inr ⟨a * I₂ * uA, kron2 b c * CNOT_BA_4 * kron2 uB uC, ?_, ?_, ?_⟩
          · exact Cost1U4_mul_right (Cost1U4_mul_left cost1_cnotBA hb hc) hB hC
          · exact isUnitary2_mul (isUnitary2_mul ha isUnitary2_I2) hA
          · rw [singleQubitLayer_eq_kronA_BC, cx_cb_eq_kronA_BC, singleQubitLayer_eq_kronA_BC,
              kronA_BC_mul, kronA_BC_mul]

/-- The free `U(2)` layer on the remaining wire has `|c₀₀| = |c₁₁| ≤ 1`, so it
    cannot amplify `Φ`. -/
lemma weighted_six {M : Mat4} {c : Mat2} (hM : Cost1U4 M) (hc : IsUnitary2 c) :
    ‖c 0 0 * M.trace + c 1 1 * (Zp4 * M).trace‖ ≤ 6 := by
  have hphi := phi_cost1 hM
  have hd : ‖c 0 0‖ = ‖c 1 1‖ := u2_diag_norm hc
  calc ‖c 0 0 * M.trace + c 1 1 * (Zp4 * M).trace‖
      ≤ ‖c 0 0 * M.trace‖ + ‖c 1 1 * (Zp4 * M).trace‖ := norm_add_le _ _
    _ = ‖c 0 0‖ * (‖M.trace‖ + ‖(Zp4 * M).trace‖) := by rw [norm_mul, norm_mul, ← hd]; ring
    _ ≤ 1 * 6 := mul_le_mul (norm_diag_le_one hc) hphi (by positivity) zero_le_one
    _ = 6 := by norm_num

lemma normSq_le_36 {z : ℂ} (h : ‖z‖ ≤ 6) : Complex.normSq z ≤ 36 := by
  rw [← Complex.sq_norm]; nlinarith [norm_nonneg z, h]

theorem ccz_bound_cut0 {M : Mat4} {c : Mat2} (hM : Cost1U4 M) (hc : IsUnitary2 c) :
    Complex.normSq (Matrix.trace (CCZ8 * kronABC M c)) ≤ 36 := by
  rw [trace_ccz_cut0]; exact normSq_le_36 (weighted_six hM hc)

theorem ccz_bound_cutA0 {M : Mat4} {c : Mat2} (hM : Cost1U4 M) (hc : IsUnitary2 c) :
    Complex.normSq (Matrix.trace (CCZ8 * kronA_BC c M)) ≤ 36 := by
  rw [trace_ccz_kronA_BC]; exact normSq_le_36 (weighted_six hM hc)

/-- **`M(1) ≤ 6`.**  Sharp: `Curve.witness0` (the identity circuit) attains 6. -/
theorem achievable_le_one_trace_bound {n : ℕ} {U : Mat8} (hn : n ≤ 1)
    (h : AchievableCircuit n U) : Complex.normSq (Matrix.trace (Uᴴ * CCX)) ≤ 36 := by
  rw [normSq_trace_ccx_eq]
  rcases achievable_le_one_form hn h with ⟨M, c, hM, hc, rfl⟩ | ⟨c, M, hM, hc, rfl⟩
  · have e : kron3 1 1 Hgate * kronABC M c * kron3 1 1 Hgate
        = kronABC M (Hgate * c * Hgate) := by
      rw [hC_eq_kronABC, kronABC_mul, kronABC_mul, Matrix.one_mul, Matrix.mul_one]
    rw [e]
    exact ccz_bound_cut0 hM
      (isUnitary2_mul (isUnitary2_mul hgate_unitary hc) hgate_unitary)
  · have e : kron3 1 1 Hgate * kronA_BC c M * kron3 1 1 Hgate
        = kronA_BC c (kron2 1 Hgate * M * kron2 1 Hgate) := by
      rw [hC_eq_kronA_BC, kronA_BC_mul, kronA_BC_mul, one_mul, mul_one]
    rw [e]
    exact ccz_bound_cutA0
      (Cost1U4_mul_right (Cost1U4_mul_left hM isUnitary2_one hgate_unitary)
        isUnitary2_one hgate_unitary) hc

/-- `M(1) ≤ 6` in the form the curve `M(n)` is stated in. -/
theorem trace_norm_le_six {n : ℕ} {U : Mat8} (hn : n ≤ 1) (h : AchievableCircuit n U) :
    ‖Matrix.trace (Uᴴ * CCX)‖ ≤ 6 := by
  have h1 := achievable_le_one_trace_bound hn h
  rw [← Complex.sq_norm] at h1
  nlinarith [norm_nonneg (Matrix.trace (Uᴴ * CCX)), h1]

/-! ## §9  `d(0) = d(1) = √7/4` -/

/-- `√(1 − 36/64) = √(7/16) = √7/4 = √28/8 ≈ 0.66144`. -/
lemma sqrt_seven_quarter : Real.sqrt (1 - 36 / 64) = Real.sqrt 7 / 4 := by
  rw [show (1 : ℝ) - 36 / 64 = (Real.sqrt 7 / 4) ^ 2 by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-- **`d(0) = d(1) = √7/4`, lower half.** -/
theorem approxToffoli_lower_bound_one {n : ℕ} (hn : n ≤ 1) (U : Mat8)
    (h : AchievableCircuit n U) : hsDistance U CCX ≥ Real.sqrt 7 / 4 := by
  rw [← sqrt_seven_quarter]
  exact hsDistance_ge_of_normSq_le U CCX (achievable_le_one_trace_bound hn h)

/-- **`d(0) = √7/4`**, attained by the identity circuit. -/
theorem d_zero_isLeast :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 0 U ∧ hsDistance U CCX = d}
      (Real.sqrt 7 / 4) := by
  constructor
  · exact ⟨Curve.witness0, Curve.witness0_achievable, Curve.witness0_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact approxToffoli_lower_bound_one (by omega) U hU

/-- **`d(1) = √7/4`**: one CX gate buys nothing. -/
theorem d_one_isLeast :
    IsLeast {d : ℝ | ∃ U : Mat8, AchievableCircuit 1 U ∧ hsDistance U CCX = d}
      (Real.sqrt 7 / 4) := by
  constructor
  · exact ⟨Curve.witness0, AchievableCircuit.weaken Curve.witness0_achievable,
      Curve.witness0_distance⟩
  · rintro d ⟨U, hU, rfl⟩
    exact approxToffoli_lower_bound_one (by omega) U hU

end Cost1

end
