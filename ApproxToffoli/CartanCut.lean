/-
  ApproxToffoli.CartanCut  (candidate new module — NOT yet added to the tree)

  **PhiFive via the Cartan normal form of the crossings.**

  Five alternating arbitrary neighbour blocks split 3/2 across the two pairs, so on
  the AB|C cut there are exactly TWO crossings and three far-side blocks:

      U = (M₀ ⊗ c₀) V₁ (M₁ ⊗ c₁) V₂ (M₂ ⊗ c₂),   Mᵢ ∈ U(4) on AB, Vᵢ ∈ U(4) on BC.

  Cartan (KAK): every `V ∈ U(4)` on BC is `(β⊗γ) N(t) (β'⊗γ')` with
  `N(t) = exp(i(t₁ XX + t₂ YY + t₃ ZZ))`; the `β` factors act on B and absorb into the
  adjacent `Mᵢ`, the `γ` factors act on C and merge with the `cᵢ`.  Expanding,

      N(t) = a₀·(I⊗I) + a₁·(X⊗X) + a₂·(Y⊗Y) + a₃·(Z⊗Z),
      a₀ = c₁c₂c₃ + i s₁s₂s₃,   a₁ = i s₁c₂c₃ + c₁s₂s₃,
      a₂ = i c₁s₂c₃ + s₁c₂s₃,   a₃ = i c₁c₂s₃ + s₁s₂c₃      (cₖ = cos tₖ, sₖ = sin tₖ)

  with `Σ|aᵢ|² = 1`; equivalently `N` is DIAGONAL IN THE BELL BASIS, with eigenvalues
  `e = χᵀ a` all of modulus one (χ the ±1 character table of {I,XX,YY,ZZ}).
  For `CZ`, `t = (0,0,π/4)`, so `a₁ = a₂ = 0` — that degeneration is exactly the
  hypothesis "`P`, `Q` rank-2 reflections" of `cut2_bound_of_PQK`.

  **What this file establishes.**  The whole `bridge_ineq` + AM–QM front end of
  `CutBound.lean` generalises to arbitrary crossings, and COLLAPSES to a single
  Cauchy–Schwarz (`u2_frob_bridge`) whose only input is `‖c₁‖_F² = 2`.  Everything
  else in the two-crossing bound is then packaged as the single residual statement
  `CoreG`, the general-crossing replacement of `core_psi_bound`'s step 9
  (`p²+q²+r²+s² ≤ 16+8√2`).  Note that `CoreG` mentions no Cartan data at all: the
  local factors absorb into the free `Vᵢ`, so KAK is NOT needed downstream of the
  bridge.

  **Numerical status** (Gauss–Seidel with exact nuclear-norm block updates, plus an
  independent optimiser in the exact Lean index/ordering convention):
    * `CoreG` max = 27.313708498985  vs  `16 + 8√2` = 27.313708498985  — TRUE, TIGHT.
    * the three-crossing analogue maxes at 32, so the two-crossing budget is
      load-bearing.
    * `Φ(k)` over `UnitaryNeighborCircuit k`: 6, 4+2√2, 4+2√2, 8cos(π/8), 8cos(π/8),
      8, 8 for k = 1..7 — the threshold really is at two crossings.
  Refuted relaxations (do not retry): dropping the Bell-phase constraint down to
  `‖a‖₂ = 1` (equivalently `4·σ_max(G)`) reaches 8; the entrywise ℓ¹ bound
  `Σ_{kl}|G_{kl}| ≤ 8cos(π/8)` already fails AT the optimum (7.414331 vs 7.391036).
-/
import ApproxToffoli.Block

open Matrix Complex

noncomputable section
namespace Cartan

/-! ## 1.  The Frobenius bridge

`bridge_ineq` extracts from `c ∈ U(2)` the modulus anti-correlation `|c₀₀| = |c₁₁|`,
`|c₀₁| = |c₁₀|`, which pairs the eight `CZ`-crossing traces into two `ψ`'s.  With four
Pauli branches per crossing the C-side factors are no longer single entries `c_{ab}`
and that pairing has no analogue.  What DOES survive — and is enough — is the weaker
statement that a `U(2)` matrix has Frobenius mass exactly 2. -/

lemma u2_frob_sq {c : Mat2} (hc : IsUnitary2 c) :
    Complex.normSq (c 0 0) + Complex.normSq (c 0 1)
      + Complex.normSq (c 1 0) + Complex.normSq (c 1 1) = 2 := by
  have h : cᴴ * c = 1 := hc
  have h00 := congrArg (fun M => M 0 0) h
  have h11 := congrArg (fun M => M 1 1) h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.one_apply_eq, Complex.star_def, ← Complex.normSq_eq_conj_mul_self] at h00 h11
  have r0 : Complex.normSq (c 0 0) + Complex.normSq (c 1 0) = 1 := by exact_mod_cast h00
  have r1 : Complex.normSq (c 0 1) + Complex.normSq (c 1 1) = 1 := by exact_mod_cast h11
  linarith

private lemma cs4 (x0 x1 x2 x3 y0 y1 y2 y3 : ℝ) :
    (x0*y0 + x1*y1 + x2*y2 + x3*y3)^2
      ≤ (x0^2+x1^2+x2^2+x3^2) * (y0^2+y1^2+y2^2+y3^2) := by
  nlinarith [sq_nonneg (x0*y1 - x1*y0), sq_nonneg (x0*y2 - x2*y0), sq_nonneg (x0*y3 - x3*y0),
    sq_nonneg (x1*y2 - x2*y1), sq_nonneg (x1*y3 - x3*y1), sq_nonneg (x2*y3 - x3*y2)]

/-- **The Frobenius bridge.**  `|Σ_{μν} c_{μν} Θ_{μν}|² ≤ 2 · Σ_{μν} |Θ_{μν}|²` for
`c ∈ U(2)`.  This single Cauchy–Schwarz replaces `bridge_ineq` + `bridge_real` + the
AM–QM collapse (`core_psi_bound` steps 5–6) of the `CZ`-crossing proof, and — unlike
`bridge_ineq` — it is not lossy for general crossings: relaxing `c₁` from `U(2)` to the
Frobenius ball of radius `√2` leaves the maximum at exactly `8cos(π/8)`. -/
theorem u2_frob_bridge {c : Mat2} (hc : IsUnitary2 c) (T00 T01 T10 T11 : ℂ) :
    Complex.normSq (c 0 0 * T00 + c 0 1 * T01 + c 1 0 * T10 + c 1 1 * T11)
      ≤ 2 * (Complex.normSq T00 + Complex.normSq T01
              + Complex.normSq T10 + Complex.normSq T11) := by
  have htri : ‖c 0 0 * T00 + c 0 1 * T01 + c 1 0 * T10 + c 1 1 * T11‖
      ≤ ‖c 0 0‖*‖T00‖ + ‖c 0 1‖*‖T01‖ + ‖c 1 0‖*‖T10‖ + ‖c 1 1‖*‖T11‖ := by
    calc ‖c 0 0 * T00 + c 0 1 * T01 + c 1 0 * T10 + c 1 1 * T11‖
        ≤ ‖c 0 0 * T00 + c 0 1 * T01 + c 1 0 * T10‖ + ‖c 1 1 * T11‖ := norm_add_le _ _
      _ ≤ (‖c 0 0 * T00 + c 0 1 * T01‖ + ‖c 1 0 * T10‖) + ‖c 1 1 * T11‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ((‖c 0 0 * T00‖ + ‖c 0 1 * T01‖) + ‖c 1 0 * T10‖) + ‖c 1 1 * T11‖ := by
          gcongr; exact norm_add_le _ _
      _ = ‖c 0 0‖*‖T00‖ + ‖c 0 1‖*‖T01‖ + ‖c 1 0‖*‖T10‖ + ‖c 1 1‖*‖T11‖ := by simp
  have hcs := cs4 ‖c 0 0‖ ‖c 0 1‖ ‖c 1 0‖ ‖c 1 1‖ ‖T00‖ ‖T01‖ ‖T10‖ ‖T11‖
  have hfrob : ‖c 0 0‖^2 + ‖c 0 1‖^2 + ‖c 1 0‖^2 + ‖c 1 1‖^2 = 2 := by
    simp only [Complex.sq_norm]; exact u2_frob_sq hc
  have hnn : 0 ≤ ‖c 0 0 * T00 + c 0 1 * T01 + c 1 0 * T10 + c 1 1 * T11‖ := norm_nonneg _
  simp only [← Complex.sq_norm]
  nlinarith [htri, hnn, hcs, hfrob]

/-! ## 2.  The four matrix units of the C factor -/

def e2 : Fin 2 → Fin 2 → Mat2
  | 0, 0 => Matrix.of !![1, 0; 0, 0]
  | 0, 1 => Matrix.of !![0, 1; 0, 0]
  | 1, 0 => Matrix.of !![0, 0; 1, 0]
  | 1, 1 => Matrix.of !![0, 0; 0, 1]

lemma kronABC_add_right (M : Mat4) (b c : Mat2) :
    kronABC M (b + c) = kronABC M b + kronABC M c := by
  ext i j; simp [kronABC, Matrix.add_apply, Matrix.of_apply, mul_add]

lemma kronABC_smul_right (a : ℂ) (M : Mat4) (c : Mat2) :
    kronABC M (a • c) = a • kronABC M c := by
  ext i j; simp [kronABC, Matrix.smul_apply, Matrix.of_apply]; ring

lemma mat2_units (c : Mat2) :
    c = c 0 0 • e2 0 0 + c 0 1 • e2 0 1 + c 1 0 • e2 1 0 + c 1 1 • e2 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2, Matrix.add_apply, Matrix.of_apply]

lemma kronABC_units (M : Mat4) (c : Mat2) :
    kronABC M c = c 0 0 • kronABC M (e2 0 0) + c 0 1 • kronABC M (e2 0 1)
                + c 1 0 • kronABC M (e2 1 0) + c 1 1 • kronABC M (e2 1 1) := by
  conv_lhs => rw [mat2_units c]
  rw [kronABC_add_right, kronABC_add_right, kronABC_add_right,
      kronABC_smul_right, kronABC_smul_right, kronABC_smul_right, kronABC_smul_right]

/-! ## 3.  `CoreG` : the residual inequality -/

/-- `Θ_{μν}` : the two-crossing objective with the MIDDLE C factor replaced by the
matrix unit `E_{μν}`.  Equivalently `Θ_{μν} = Tr(M₁ · W^{νμ})` for the four C-blocks
`W^{st}` of the unitary `W = embedBC V₁ · (M₀⊗c₀) · CCZ8 · (M₂⊗c₂) · embedBC V₂`,
so that `Σ_{μν}|Θ_{μν}|² = ‖Tr_{AB}[(M₁⊗I) W]‖_F²` — the squared Frobenius mass of the
C-marginal.  (For a completely free `8×8` unitary that mass can reach 32.) -/
def coreTheta (M0 M1 M2 V1 V2 : Mat4) (c0 c2 : Mat2) (μ ν : Fin 2) : ℂ :=
  Matrix.trace (CCZ8 * (kronABC M0 c0 * embedBC V1 * kronABC M1 (e2 μ ν)
                        * embedBC V2 * kronABC M2 c2))

/-- **CORE-G** — the general-crossing replacement for `core_psi_bound` step 9
(`p²+q²+r²+s² ≤ 16+8√2`).  `V₁, V₂` are ARBITRARY two-qubit unitaries on BC, not
`CNOT`/`CZ`; `c₀, c₂` are absorbable into them, so this is really a statement about
five free `U(4)`'s.

Equivalent phrasings:
* `‖Tr_{AB}[(M₁⊗I) · V̂₁ · (M₀⊗I) · CCZ · (M₂⊗I) · V̂₂]‖_F² ≤ 16 + 8√2`;
* `Σ_{τ ∈ {I,X,Y,Z}} |Tr((I₄⊗τ)·K)|² ≤ 32 + 16√2` for that same `K`.

NUMERICALLY TRUE AND TIGHT: max `27.313708498985` = `16+8√2` (violation `5e-14`),
attained with `Tr_{AB}K = 4cos(π/8)·(unitary)`.  The three-crossing analogue maxes at
`32`, i.e. gives only the vacuous `Φ ≤ 8`. -/
def CoreG : Prop :=
  ∀ (M0 M1 M2 V1 V2 : Mat4) (c0 c2 : Mat2),
    IsUnitary4 M0 → IsUnitary4 M1 → IsUnitary4 M2 → IsUnitary4 V1 → IsUnitary4 V2 →
    IsUnitary2 c0 → IsUnitary2 c2 →
      Complex.normSq (coreTheta M0 M1 M2 V1 V2 c0 c2 0 0)
      + Complex.normSq (coreTheta M0 M1 M2 V1 V2 c0 c2 0 1)
      + Complex.normSq (coreTheta M0 M1 M2 V1 V2 c0 c2 1 0)
      + Complex.normSq (coreTheta M0 M1 M2 V1 V2 c0 c2 1 1)
      ≤ 16 + 8 * Real.sqrt 2

theorem theta_expansion (M0 M1 M2 V1 V2 : Mat4) (c0 c1 c2 : Mat2) :
    Matrix.trace (CCZ8 * (kronABC M0 c0 * embedBC V1 * kronABC M1 c1
        * embedBC V2 * kronABC M2 c2))
      = c1 0 0 * coreTheta M0 M1 M2 V1 V2 c0 c2 0 0
      + c1 0 1 * coreTheta M0 M1 M2 V1 V2 c0 c2 0 1
      + c1 1 0 * coreTheta M0 M1 M2 V1 V2 c0 c2 1 0
      + c1 1 1 * coreTheta M0 M1 M2 V1 V2 c0 c2 1 1 := by
  simp only [coreTheta]
  rw [kronABC_units M1 c1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]

/-- **The general two-crossing bound, reduced to `CoreG`.**  Exact analogue of
`cut2_bound_of_PQK`, with the crossings ARBITRARY BC unitaries instead of `CZ`.
`bridge_ineq` + `bridge_real` + `core_psi_bound` steps 5–6 collapse into the single
`u2_frob_bridge`; `CoreG` is everything that is left. -/
theorem cut2_general_of_coreG (h : CoreG) {M0 M1 M2 V1 V2 : Mat4} {c0 c1 c2 : Mat2}
    (hM0 : IsUnitary4 M0) (hM1 : IsUnitary4 M1) (hM2 : IsUnitary4 M2)
    (hV1 : IsUnitary4 V1) (hV2 : IsUnitary4 V2)
    (hc0 : IsUnitary2 c0) (hc1 : IsUnitary2 c1) (hc2 : IsUnitary2 c2) :
    Complex.normSq (Matrix.trace (CCZ8 * (kronABC M0 c0 * embedBC V1 * kronABC M1 c1
        * embedBC V2 * kronABC M2 c2)))
      ≤ 64 * Real.cos (Real.pi / 8) ^ 2 := by
  rw [theta_expansion, sixtyfour_cos_sq]
  refine le_trans (u2_frob_bridge hc1 _ _ _ _) ?_
  have hc := h M0 M1 M2 V1 V2 c0 c2 hM0 hM1 hM2 hV1 hV2 hc0 hc2
  linarith

/-! ## 4.  What a general crossing supplies on the AB side

The `CZ` crossing contributes the single reflection `Ẑ = I_A ⊗ Z_B` (`Zhat4`), so
`cut2_bound_of_PQK` sees exactly one pair `(P, Q)` of rank-2 reflections.  A general
Cartan crossing contributes `I` together with ALL THREE of `I_A ⊗ X_B`, `I_A ⊗ Y_B`,
`I_A ⊗ Z_B`, weighted by `a₁, a₂, a₃`.  Each is still a rank-2 reflection — so the
hypothesis of `cut2_bound_of_PQK` is not what breaks — but they mutually ANTI-commute,
so no single `Q` has spectral projections `Π±` splitting the objective, which is what
`core_psi_bound` step 7 (`proj_trace_bound` at `Π±(Q)`) consumes. -/

def pauliY : Mat2 := Matrix.of !![0, -Complex.I; Complex.I, 0]

def Xhat4 : Mat4 := kron2 1 pauliX
def Yhat4 : Mat4 := kron2 1 pauliY
def Zhat4' : Mat4 := kron2 1 pauliZ

lemma zhat4'_eq : Zhat4' = Zhat4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Zhat4', Zhat4, kron2, pauliZ, Matrix.of_apply, Matrix.one_apply]

lemma isRefl4_Xhat : IsRefl4 Xhat4 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Xhat4, kron2, pauliX, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Xhat4, kron2, pauliX, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four,
        Matrix.one_apply]
  · simp [Xhat4, kron2, pauliX, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four,
      Matrix.of_apply]

lemma isRefl4_Yhat : IsRefl4 Yhat4 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Yhat4, kron2, pauliY, Matrix.conjTranspose_apply, Matrix.of_apply,
        Matrix.one_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Yhat4, kron2, pauliY, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four,
        Matrix.one_apply, Complex.I_mul_I]
  · simp [Yhat4, kron2, pauliY, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four,
      Matrix.of_apply]

/-- The triple ANTI-commutes — this is why one `Q` cannot organise the objective. -/
lemma xhat_zhat_anticomm : Xhat4 * Zhat4 = - (Zhat4 * Xhat4) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Xhat4, Zhat4, kron2, pauliX, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]

/-- `isRefl4_conj` for an ARBITRARY rank-2 reflection (the repo only had `Zhat4`). -/
lemma isRefl4_conj_gen {P M : Mat4} (hP : IsRefl4 P) (hM : IsUnitary4 M) :
    IsRefl4 (Mᴴ * P * M) := by
  have hMM : Mᴴ * M = 1 := hM
  have hMM' : M * Mᴴ = 1 := mul_eq_one_comm.mp hMM
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.1, Matrix.mul_assoc]
  · calc Mᴴ * P * M * (Mᴴ * P * M)
        = Mᴴ * P * (M * Mᴴ) * P * M := by noncomm_ring
      _ = Mᴴ * (P * P) * M := by rw [hMM']; noncomm_ring
      _ = 1 := by rw [hP.2.1, Matrix.mul_one, hMM]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hMM', Matrix.one_mul, hP.2.2]

end Cartan
