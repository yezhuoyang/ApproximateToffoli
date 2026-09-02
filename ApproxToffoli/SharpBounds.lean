/-
  SharpBounds.lean  —  (T1) k = 0  and  (T2) F(1) ≤ √40.

  Both halves below were checked with `lean_run_code` against the built
  `ApproxToffoli.CutBound`; the tree itself was NOT edited and `lake build` was not run.

  * `phi_local_le_six`          : (T1), case k = 0.  Φ(a ⊗ b) ≤ 6.   PROVED, no hypotheses.
  * `cut_trace_bound_one_sharp` : (T2).  F(1)² ≤ 40, i.e. F(1) ≤ √40. PROVED from `key2`.

  `key2` is the one open input; see the module note at `cut_trace_bound_one_sharp`.
-/
import ApproxToffoli.CutBound

open Matrix Complex

noncomputable section

namespace SharpBounds

/-! ## Shared elementary real lemmas -/

theorem sq_le_sq_imp {a b : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [h, ha, hb]

theorem prod_le_of_abs {x y X Y : ℝ} (h1 : x ≤ X) (h2 : -x ≤ X) (h3 : y ≤ Y) (h4 : -y ≤ Y) :
    x * y ≤ X * Y := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ X - x) (by linarith : (0:ℝ) ≤ Y + y),
    mul_nonneg (by linarith : (0:ℝ) ≤ X + x) (by linarith : (0:ℝ) ≤ Y - y)]

theorem norm_add4_le' (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
    _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by gcongr; exact norm_add_le _ _

/-! ## (T1), case k = 0 :  `Φ(a ⊗ b) ≤ 6` for local `a ⊗ b`

`α, α'` are the diagonal entries of `a`, `β, β'` those of `b`; unitarity of a `2×2`
gives exactly `‖α‖ = ‖α'‖ ≤ 1`, `‖β‖ = ‖β'‖ ≤ 1`.  Then

    Tr (a ⊗ b)      = (α+α')(β+β')
    Tr (CZ (a ⊗ b)) = α(β+β') + α'(β−β')

so `Φ = ‖(α+α')(β+β')‖ + ‖α(β+β') + α'(β−β')‖`.

The proof is entirely elementary.  With `A± = ‖α ± α'‖`, `B± = ‖β ± β'‖`,
`c = ‖α‖`, `d = ‖β‖`:

* parallelogram        `A₊² + A₋² = 4c²`,  `B₊² + B₋² = 4d²`;
* an exact expansion   `T² = 4c²d² + 4·Im(α ᾱ')·Im(β β̄')`;
* the exact identity   `(A₊A₋)² = (2 Im(α ᾱ'))²`, likewise for `B`;
  hence `T² ≤ 4c²d² + (A₊B₊)(A₋B₋)`;
* Cauchy–Schwarz       `A₊B₊ + A₋B₋ ≤ 4cd ≤ 4`;
* so with `P = A₊B₊`,  `T² ≤ 4 + 4P − P²` and `P + T ≤ 6` reduces to `2(P−4)² ≥ 0`.

TIGHT, with equality exactly at `P = 4`, i.e. `a ⊗ b = (phase)·1`.
-/

/-- The real core of (T1) k = 0. -/
theorem local_core (Ap Am Bp Bm c d T : ℝ)
    (hAp : 0 ≤ Ap) (hAm : 0 ≤ Am) (hBp : 0 ≤ Bp) (hBm : 0 ≤ Bm) (hT : 0 ≤ T)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hA : Ap ^ 2 + Am ^ 2 = 4 * c ^ 2) (hB : Bp ^ 2 + Bm ^ 2 = 4 * d ^ 2)
    (hT2 : T ^ 2 ≤ 4 * c ^ 2 * d ^ 2 + (Ap * Bp) * (Am * Bm)) :
    Ap * Bp + T ≤ 6 := by
  have hP0 : 0 ≤ Ap * Bp := mul_nonneg hAp hBp
  have hQ0 : 0 ≤ Am * Bm := mul_nonneg hAm hBm
  have hcd : 0 ≤ c * d := mul_nonneg hc hd
  have h1 : (Ap * Bp + Am * Bm) ^ 2 ≤ (4 * (c * d)) ^ 2 := by
    have e : (Ap * Bp + Am * Bm) ^ 2 ≤ (Ap ^ 2 + Am ^ 2) * (Bp ^ 2 + Bm ^ 2) := by
      nlinarith [sq_nonneg (Ap * Bm - Am * Bp)]
    rw [hA, hB] at e
    nlinarith [e]
  have hCS : Ap * Bp + Am * Bm ≤ 4 * (c * d) :=
    sq_le_sq_imp (by linarith) (by linarith) h1
  have hm4 : 4 * (c * d) ≤ 4 := by nlinarith
  have hPle : Ap * Bp ≤ 4 := by linarith
  have step1 : T ^ 2 ≤ 4 * (c * d) ^ 2 + (Ap * Bp) * (4 * (c * d) - Ap * Bp) := by
    have h2 : (Ap * Bp) * (Am * Bm) ≤ (Ap * Bp) * (4 * (c * d) - Ap * Bp) :=
      mul_le_mul_of_nonneg_left (by linarith) hP0
    nlinarith [hT2, h2]
  have step2 : 4 * (c * d) ^ 2 + (Ap * Bp) * (4 * (c * d) - Ap * Bp)
      ≤ 4 + 4 * (Ap * Bp) - (Ap * Bp) ^ 2 := by nlinarith [hm4, hcd, hP0]
  nlinarith [step1, step2, hT, hP0, hPle, sq_nonneg (Ap * Bp - 4)]

set_option maxHeartbeats 1000000 in
-- Heartbeat bump: four `linear_combination`s over eight real coordinates of `ℂ⁴`.
/-- **(T1), case k = 0.**  `|Tr M| + |Tr(CZ·M)| ≤ 6` for `M = a ⊗ b` local. -/
theorem phi_local_le_six {α α' β β' : ℂ}
    (ha : ‖α‖ = ‖α'‖) (ha1 : ‖α‖ ≤ 1) (hb : ‖β‖ = ‖β'‖) (hb1 : ‖β‖ ≤ 1) :
    ‖(α + α') * (β + β')‖ + ‖α * (β + β') + α' * (β - β')‖ ≤ 6 := by
  have hnsa : Complex.normSq α = Complex.normSq α' := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, ha]
  have hnsb : Complex.normSq β = Complex.normSq β' := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, hb]
  have hA : ‖α + α'‖ ^ 2 + ‖α - α'‖ ^ 2 = 4 * ‖α‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    simp only [Complex.normSq_apply] at hnsa
    linear_combination (-2 : ℝ) * hnsa
  have hB : ‖β + β'‖ ^ 2 + ‖β - β'‖ ^ 2 = 4 * ‖β‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    simp only [Complex.normSq_apply] at hnsb
    linear_combination (-2 : ℝ) * hnsb
  have hpa : ‖α + α'‖ ^ 2 * ‖α - α'‖ ^ 2 = 4 * (α.im * α'.re - α.re * α'.im) ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    simp only [Complex.normSq_apply] at hnsa
    linear_combination (α.re * α.re + α.im * α.im - α'.re * α'.re - α'.im * α'.im) * hnsa
  have hpb : ‖β + β'‖ ^ 2 * ‖β - β'‖ ^ 2 = 4 * (β.im * β'.re - β.re * β'.im) ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    simp only [Complex.normSq_apply] at hnsb
    linear_combination (β.re * β.re + β.im * β.im - β'.re * β'.re - β'.im * β'.im) * hnsb
  have hT2 : ‖α * (β + β') + α' * (β - β')‖ ^ 2
      = 4 * ‖α‖ ^ 2 * ‖β‖ ^ 2
        + 4 * (α.im * α'.re - α.re * α'.im) * (β.im * β'.re - β.re * β'.im) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    simp only [Complex.normSq_apply] at hnsa hnsb
    linear_combination
      (-(β.re * β.re + β.im * β.im) - (β'.re * β'.re + β'.im * β'.im)
        + 2 * (β.re * β'.re + β.im * β'.im)) * hnsa
      + (-2 * (α.re * α.re + α.im * α.im) + 2 * (α.re * α'.re + α.im * α'.im)) * hnsb
  set Ia := α.im * α'.re - α.re * α'.im with hIa
  set Ib := β.im * β'.re - β.re * β'.im with hIb
  have hAA : 0 ≤ ‖α + α'‖ * ‖α - α'‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hBB : 0 ≤ ‖β + β'‖ * ‖β - β'‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hqa : (‖α + α'‖ * ‖α - α'‖) ^ 2 = (2 * Ia) ^ 2 := by rw [mul_pow, hpa]; ring
  have hqb : (‖β + β'‖ * ‖β - β'‖) ^ 2 = (2 * Ib) ^ 2 := by rw [mul_pow, hpb]; ring
  have ha2 : 2 * Ia ≤ ‖α + α'‖ * ‖α - α'‖ := by nlinarith [hqa, hAA]
  have ha3 : -(2 * Ia) ≤ ‖α + α'‖ * ‖α - α'‖ := by nlinarith [hqa, hAA]
  have hb2 : 2 * Ib ≤ ‖β + β'‖ * ‖β - β'‖ := by nlinarith [hqb, hBB]
  have hb3 : -(2 * Ib) ≤ ‖β + β'‖ * ‖β - β'‖ := by nlinarith [hqb, hBB]
  have hcross : 4 * Ia * Ib ≤ (‖α + α'‖ * ‖β + β'‖) * (‖α - α'‖ * ‖β - β'‖) := by
    calc 4 * Ia * Ib = (2 * Ia) * (2 * Ib) := by ring
      _ ≤ (‖α + α'‖ * ‖α - α'‖) * (‖β + β'‖ * ‖β - β'‖) := prod_le_of_abs ha2 ha3 hb2 hb3
      _ = (‖α + α'‖ * ‖β + β'‖) * (‖α - α'‖ * ‖β - β'‖) := by ring
  have hfin : ‖α * (β + β') + α' * (β - β')‖ ^ 2
      ≤ 4 * ‖α‖ ^ 2 * ‖β‖ ^ 2
        + (‖α + α'‖ * ‖β + β'‖) * (‖α - α'‖ * ‖β - β'‖) := by
    rw [hT2]; linarith [hcross]
  rw [norm_mul]
  exact local_core _ _ _ _ ‖α‖ ‖β‖ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) ha1 (norm_nonneg _) hb1 hA hB hfin

/-! ## (T2) : `F(1) ≤ √40` -/

/-- `w₁,w₂ ≥ 0`, `w₁+w₂ ≤ 1`, `x² ≤ 40`, `y² ≤ 40` ⟹ `(w₁x+w₂y)² ≤ 40`.
    The identity `(w₁x+w₂y)² = (w₁+w₂)(w₁x²+w₂y²) − w₁w₂(x−y)²` does all the work. -/
theorem weighted_max_sq (w1 w2 x y : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hw : w1 + w2 ≤ 1) (hx2 : x ^ 2 ≤ 40) (hy2 : y ^ 2 ≤ 40) :
    (w1 * x + w2 * y) ^ 2 ≤ 40 := by
  have hs : 0 ≤ w1 + w2 := by linarith
  have h1 : w1 * x ^ 2 + w2 * y ^ 2 ≤ 40 * (w1 + w2) := by nlinarith
  have h2 : (w1 + w2) * (w1 * x ^ 2 + w2 * y ^ 2) ≤ (w1 + w2) * (40 * (w1 + w2)) :=
    mul_le_mul_of_nonneg_left h1 hs
  nlinarith [mul_nonneg (mul_nonneg hw1 hw2) (sq_nonneg (x - y)), h2, sq_nonneg (w1 + w2)]

/-- **The ℓ¹ weight constraint.**  `(a,b)` and `(u,v)` unit vectors ⟹ `au + bv ≤ 1`.
    This is what turns the four-term cut sum into a CONVEX COMBINATION of the two
    pair-sums, so that only `max(Φ₁,Φ₂) ≤ √40` is needed. -/
theorem weights_le_one (a b u v : ℝ)
    (h1 : a ^ 2 + b ^ 2 = 1) (h2 : u ^ 2 + v ^ 2 = 1) : a * u + b * v ≤ 1 := by
  nlinarith [sq_nonneg (a * v - b * u), sq_nonneg (a * u + b * v - 1),
    sq_nonneg (a * u + b * v + 1)]

theorem sum_sq_of_sq_sum (x y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 20) : (x + y) ^ 2 ≤ 40 := by
  nlinarith [sq_nonneg (x - y)]

theorem refl_mul_mul {Q K : Mat4} (hQ : IsRefl4 Q) : Q * (Q * K) = K := by
  rw [← Matrix.mul_assoc, hQ.2.1, Matrix.one_mul]

/-- **`F(1) ≤ √40`, sharp.**  Compare `cut_trace_bound_one`, which proves only the
(deliberately lossy) `≤ 8cos(π/8)`, i.e. `normSq ≤ 54.627`.  `√40 = 6.32455…` is the
TRUE value of `F(1)` (adversarial Gauss–Seidel on the circuit form: `6.324555320337`).

The hypothesis

    key2 :  ‖Tr (Q N)‖² + ‖Tr (Z' N)‖² ≤ 20   for `N` unitary, `Q` a rank-2 reflection

is the `Q`-twisted analogue of `zp4_trace_bound` (the `Q = 1` case), and is TIGHT —
adversarial optimisation attains exactly `20.000000000000`, at `Q = Ẑ` with `N` the
polar factor of `1 + e^{2i·arctan(1/3)} Z'Q`.  It is NOT implied by
`four_trace_bound_of_refl`, whose true maximum is `24 > 20`.

Proof of `key2` (mathematically complete, not yet formalised — see the report):
with `θ = Q₃₃ ∈ [−1,1]` and `G = Z'Q`, purely algebraically `Tr G = −2θ`,
`Tr(G²) = (Tr G)²`, `det G = −1` and `(G²−1)(G²+2θG+1) = 0`; hence
`spec G = {1,−1,e^{iφ},e^{−iφ}}` with `cos φ = −θ`, and
`‖αQ+βZ'‖_* = ‖αI+βG‖_* = Σ_j |α+βz_j| ≤ 3x+y ≤ √20` where `x,y` are `|α±β|` sorted.
The Lean blocker is the last step: nuclear-norm duality `|Tr(AN)| ≤ ‖A‖_*`, which this
Mathlib does not have for `Matrix`. -/
theorem cut_trace_bound_one_sharp {M0 M1 : Mat4} {c0 c1 : Mat2}
    (h0 : IsUnitary4 M0) (h1 : IsUnitary4 M1)
    (k0 : IsUnitary2 c0) (k1 : IsUnitary2 c1)
    (key2 : ∀ Q N : Mat4, IsRefl4 Q → IsUnitary4 N →
      ‖Matrix.trace (Q * N)‖ ^ 2 + ‖Matrix.trace (Zp4 * N)‖ ^ 2 ≤ 20) :
    Complex.normSq (Matrix.trace (CCZ8 * kronABC M0 c0 * CZBC8 * kronABC M1 c1))
      ≤ 40 := by
  have hK : IsUnitary4 (M0 * M1) := isUnitary4_mul h0 h1
  have hQ : IsRefl4 (M0 * Zhat4 * M0ᴴ) := isRefl4_conj' h0
  have hQu : IsUnitary4 (M0 * Zhat4 * M0ᴴ) := isRefl4_isUnitary hQ
  have eQK : (M0 * Zhat4 * M0ᴴ) * (M0 * M1) = M0 * Zhat4 * M1 := by
    have h : M0ᴴ * M0 = 1 := h0
    calc (M0 * Zhat4 * M0ᴴ) * (M0 * M1) = M0 * Zhat4 * (M0ᴴ * M0) * M1 := by noncomm_ring
      _ = M0 * Zhat4 * M1 := by rw [h, Matrix.mul_one]
  have hQK : IsUnitary4 (M0 * Zhat4 * M1) := by
    rw [← eQK]; exact isUnitary4_mul hQu hK
  -- Φ₂ : `key2` at `N = K`
  have b2 := key2 _ _ hQ hK
  rw [eQK, show Zp4 * (M0 * M1) = Zp4 * M0 * M1 by noncomm_ring] at b2
  -- Φ₁ : `key2` at `N = QK`, using `Q(QK) = K`
  have b1 := key2 _ _ hQ hQK
  rw [← eQK, refl_mul_mul hQ, eQK,
    show Zp4 * (M0 * Zhat4 * M1) = Zp4 * M0 * Zhat4 * M1 by noncomm_ring] at b1
  set n1 := ‖Matrix.trace (M0 * M1)‖ with hn1
  set n2 := ‖Matrix.trace (M0 * Zhat4 * M1)‖ with hn2
  set n3 := ‖Matrix.trace (Zp4 * M0 * M1)‖ with hn3
  set n4 := ‖Matrix.trace (Zp4 * M0 * Zhat4 * M1)‖ with hn4
  have P1 : (n1 + n4) ^ 2 ≤ 40 := sum_sq_of_sq_sum _ _ b1
  have P2 : (n2 + n3) ^ 2 ≤ 40 := sum_sq_of_sq_sum _ _ b2
  have e1 : ‖c0 1 0‖ = ‖c0 0 1‖ := (u2_offdiag_norm k0).symm
  have e2 : ‖c0 1 1‖ = ‖c0 0 0‖ := (u2_diag_norm k0).symm
  have e3 : ‖c1 1 0‖ = ‖c1 0 1‖ := (u2_offdiag_norm k1).symm
  have e4 : ‖c1 1 1‖ = ‖c1 0 0‖ := (u2_diag_norm k1).symm
  have hbound : ‖c0 0 0 * c1 0 0 * Matrix.trace (M0 * M1)
      + c0 0 1 * c1 1 0 * Matrix.trace (M0 * Zhat4 * M1)
      + c0 1 0 * c1 0 1 * Matrix.trace (Zp4 * M0 * M1)
      + c0 1 1 * c1 1 1 * Matrix.trace (Zp4 * M0 * Zhat4 * M1)‖
      ≤ ‖c0 0 0‖ * ‖c1 0 0‖ * (n1 + n4) + ‖c0 0 1‖ * ‖c1 0 1‖ * (n2 + n3) := by
    refine le_trans (norm_add4_le' _ _ _ _) (le_of_eq ?_)
    simp only [norm_mul, e1, e2, e3, e4, hn1, hn2, hn3, hn4]
    ring
  have hw : ‖c0 0 0‖ * ‖c1 0 0‖ + ‖c0 0 1‖ * ‖c1 0 1‖ ≤ 1 :=
    weights_le_one _ _ _ _ (u2_row_norm k0) (u2_row_norm k1)
  have hfin : (‖c0 0 0‖ * ‖c1 0 0‖ * (n1 + n4) + ‖c0 0 1‖ * ‖c1 0 1‖ * (n2 + n3)) ^ 2
      ≤ 40 :=
    weighted_max_sq _ _ _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hw P1 P2
  rw [trace_ccz_cut1, ← Complex.sq_norm]
  nlinarith [hbound, hfin, norm_nonneg (c0 0 0 * c1 0 0 * Matrix.trace (M0 * M1)
      + c0 0 1 * c1 1 0 * Matrix.trace (M0 * Zhat4 * M1)
      + c0 1 0 * c1 0 1 * Matrix.trace (Zp4 * M0 * M1)
      + c0 1 1 * c1 1 1 * Matrix.trace (Zp4 * M0 * Zhat4 * M1))]

end SharpBounds
