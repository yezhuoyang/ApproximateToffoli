/-
  ApproxToffoli.CurveWitnesses

  **The constructive half of the curve `d(n)`**: explicit ≤ n-CX circuits on the line
  A–B–C attaining

      n = 0 : d = √7/4      (= √28/8)      |Tr(Uᴴ CCX)| = 6
      n = 2 : d = √6/4      (= √(3/8))     |Tr(Uᴴ CCX)| = √40
      n = 4 : d = sin(π/8)                 |Tr(Uᴴ CCX)| = 8cos(π/8)
      n = 8 : d = 0                        U = CCX exactly

  Every witness is a **CNOT + diagonal-phase** circuit, built from the parity picture

      CCZ = exp(i(π/4)[a + b + c − (a⊕b) − (a⊕c) − (b⊕c) + (a⊕b⊕c)]),

  i.e. `CCZ` carries ±π/4 on each of the seven non-zero parities of `𝔽₂³`.  A CNOT is
  an elementary row operation on the 3×3 `GF(2)` matrix of parities held by the wires;
  a network that RETURNS TO THE IDENTITY, with a phase gate inserted the first time a
  new parity appears on a wire, is a DIAGONAL unitary whose phase is any real
  combination of the visited parities.  So:

  * `n = 8`, word `(BC·AB)⁴`, visits ALL SEVEN parities → the circuit is `CCZ` on the
    nose, and `H_C · CCZ · H_C = CCX`.  (Exhaustive `GF(2)` search: exactly four
    8-CNOT LNN networks return to the identity and cover all seven parities, namely
    `(AB·BC)⁴`, `(BA·CB)⁴`, `(BC·AB)⁴`, `(CB·BA)⁴`.)
  * `n = 4`, word `BC·AB·BC·AB` (as `CX_CB, CX_AB, CX_CB, CX_AB`), visits the six
    parities `a, b, c, a⊕b, a⊕b⊕c, b⊕c` — everything but `a⊕c`, the parity of the two
    NON-ADJACENT qubits.  Keeping the six `CCZ` phases it can reach and DELETING the
    seventh gives `|Tr| = |4 + 4e^{-iπ/4}| = 8cos(π/8)`.
  * `n = 2`, word `AB·AB` (as `CX_BA` twice), visits `a, b, c, a⊕b`; the surviving
    phases give `CS_AB`, and the still-free single-qubit phase on C is tuned to
    `τ = (4+3i)/5` (i.e. `e^{2i·arctan(1/3)}`), which aligns `(3+i) + (3−i)τ` into
    `6 + 2i`, of modulus `√40`.
  * `n = 0` is the identity, `Tr CCX = 6`.

  **Proof technique.**  Every factor is a MONOMIAL matrix (CNOTs are permutations,
  phase layers are diagonal), so the running product is monomial and each step
  `Wₖ · CX · diag = Wₖ₊₁` is a 64-case entrywise check whose scalar residue is a
  single product of eighth roots of unity.  No 8×8 matrix is ever expanded through a
  multi-factor product.  The Hadamards that convert the `CCZ` target into `CCX` are
  absorbed into the (free) outer single-qubit layers, so the `AchievableCircuit`
  gate count is exactly the CNOT count.

  Everything lives in `namespace Curve` — `Pg`, `wp`, `wm`, `W1…W7`, `Z1…Z3`, `Y1`
  are deliberately short names and MUST stay namespaced (cf. the historical
  `cutCNOT_AB_4` vs `HP.CNOT_AB_4` and `swapMatAC` vs `HP.swapAC` collisions).
-/

import ApproxToffoli.CutAlgebra
import ApproxToffoli.TraceReduction

open Matrix Complex

noncomputable section
namespace Curve

/-! ## §1  Diagonal phase gates and the eighth root of unity -/

/-- `P(z) = diag(1, z)`; unitary exactly when `|z| = 1`. -/
def Pg (z : ℂ) : Mat2 := Matrix.of !![1, 0; 0, z]

lemma Pg_unitary {z : ℂ} (hz : Complex.normSq z = 1) : IsUnitary2 (Pg z) := by
  have h : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj]; exact_mod_cast hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pg, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, h]

lemma Pg_one_unitary : IsUnitary2 (Pg 1) := Pg_unitary (by simp)

/-- `e^{iπ/4}`, the `T` phase. -/
def wp : ℂ := invSqrt2 * (1 + Complex.I)
/-- `e^{-iπ/4} = conj wp`, the `T†` phase. -/
def wm : ℂ := invSqrt2 * (1 - Complex.I)
/-- `e^{2i·arctan(1/3)} = (4+3i)/5`, the free `C`-phase of the `n = 2` witness. -/
def tau : ℂ := (4 + 3 * Complex.I) / 5

lemma wp_mul_wm : wp * wm = 1 := by
  have h : invSqrt2 * invSqrt2 = 2⁻¹ := invSqrt2_sq
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [wp, wm]; linear_combination (2 : ℂ) * h - invSqrt2 * invSqrt2 * hI

lemma wm_mul_wp : wm * wp = 1 := by rw [mul_comm]; exact wp_mul_wm

lemma wp_mul_wp : wp * wp = Complex.I := by
  have h : invSqrt2 * invSqrt2 = 2⁻¹ := invSqrt2_sq
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [wp]; linear_combination (2 * Complex.I) * h + invSqrt2 * invSqrt2 * hI

lemma wm_mul_wm : wm * wm = -Complex.I := by
  have h : invSqrt2 * invSqrt2 = 2⁻¹ := invSqrt2_sq
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [wm]; linear_combination (-2 * Complex.I) * h + invSqrt2 * invSqrt2 * hI

lemma I_mul_wp : Complex.I * wp = -wm := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [wp, wm]; linear_combination invSqrt2 * hI

lemma wm_mul_I : wm * Complex.I = wp := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [wp, wm]; linear_combination (-invSqrt2) * hI

lemma wm_wp_assoc (z : ℂ) : wm * (wp * z) = z := by rw [← mul_assoc, wm_mul_wp, one_mul]

lemma star_wp : star wp = wm := by
  have hs : star Complex.I = -Complex.I := by simp
  simp only [wp, wm, star_mul', star_invSqrt2, star_add, star_one, hs]; ring

lemma star_wm : star wm = wp := by
  have hs : star Complex.I = -Complex.I := by simp
  simp only [wp, wm, star_mul', star_invSqrt2, star_sub, star_one, hs]; ring

lemma normSq_wp : Complex.normSq wp = 1 := by
  have h : wp * (starRingEnd ℂ) wp = 1 := by
    rw [show (starRingEnd ℂ) wp = star wp from rfl, star_wp]; exact wp_mul_wm
  rw [Complex.mul_conj] at h; exact_mod_cast h

lemma normSq_wm : Complex.normSq wm = 1 := by
  have h : wm * (starRingEnd ℂ) wm = 1 := by
    rw [show (starRingEnd ℂ) wm = star wm from rfl, star_wm]; exact wm_mul_wp
  rw [Complex.mul_conj] at h; exact_mod_cast h

lemma normSq_tau : Complex.normSq tau = 1 := by
  simp [tau, Complex.normSq_apply]; norm_num

/-! ## §2  Literal (monomial) forms of the four allowed CNOTs and of a phase layer

Index convention (from `TensorProduct.lean`): `Fin 8` is `|abc⟩ ↦ 4a + 2b + c`. -/

def CXABlit : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0;
  0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,1; 0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0]

def CXBAlit : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,1;
  0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0; 0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0]

def CXBClit : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,0,1,0,0,0,0; 0,0,1,0,0,0,0,0;
  0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,1; 0,0,0,0,0,0,1,0]

def CXCBlit : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0; 0,0,1,0,0,0,0,0; 0,1,0,0,0,0,0,0;
  0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,1; 0,0,0,0,0,0,1,0; 0,0,0,0,0,1,0,0]

lemma CX_AB_lit : CX_AB = CXABlit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_AB, CXABlit, kron3, decode3, proj0, proj1, pauliX, I₂, Matrix.one_apply]

lemma CX_BA_lit : CX_BA = CXBAlit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_BA, CXBAlit, kron3, decode3, proj0, proj1, pauliX, I₂, Matrix.one_apply]

lemma CX_BC_lit : CX_BC = CXBClit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_BC, CXBClit, kron3, decode3, proj0, proj1, pauliX, I₂, Matrix.one_apply]

lemma CX_CB_lit : CX_CB = CXCBlit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CX_CB, CXCBlit, kron3, decode3, proj0, proj1, pauliX, I₂, Matrix.one_apply]

/-- A product layer of phase gates is the diagonal of all products of its entries. -/
lemma layerP_diag (x y z : ℂ) :
    singleQubitLayer (Pg x) (Pg y) (Pg z)
      = Matrix.diagonal ![1, z, y, y*z, x, x*z, x*y, x*y*z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singleQubitLayer, kron3, decode3, Pg, Matrix.diagonal]

/-! ## §3  Trace helpers -/

/-- `H_C` conjugation is an involution. -/
lemma hc_conj_involutive (V : Mat8) :
    kron3 1 1 Hgate * (kron3 1 1 Hgate * V * kron3 1 1 Hgate) * kron3 1 1 Hgate = V := by
  calc kron3 1 1 Hgate * (kron3 1 1 Hgate * V * kron3 1 1 Hgate) * kron3 1 1 Hgate
      = (kron3 1 1 Hgate * kron3 1 1 Hgate) * V * (kron3 1 1 Hgate * kron3 1 1 Hgate) := by
        noncomm_ring
    _ = V := by rw [h8_mul_self, one_mul, mul_one]

/-- **The R1 bridge, in the direction the witnesses need.**  The `CCX` overlap of
    `H_C V H_C` is the `CCZ` overlap of `V`.  This is what lets every witness be
    designed against `CCZ` (whose phase polynomial is the whole point) and scored
    against `CCX`. -/
lemma trace_conjH_ccx (V : Mat8) :
    Matrix.trace ((kron3 1 1 Hgate * V * kron3 1 1 Hgate)ᴴ * CCX)
      = Matrix.trace (Vᴴ * CCZ8) := by
  rw [trace_ccx_conj, hc_conj_involutive]

/-- `Tr(D† CCZ)` for a diagonal `D`: alternate the sign on `|111⟩`. -/
lemma trace_diag_ccz (d : Fin 8 → ℂ) :
    Matrix.trace ((Matrix.diagonal d)ᴴ * CCZ8)
      = star (d 0) + star (d 1) + star (d 2) + star (d 3) + star (d 4) + star (d 5)
        + star (d 6) - star (d 7) := by
  simp [CCZ8, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Fin.sum_univ_eight]
  ring

/-- Splitting the trailing Hadamard on qubit C out of the last layer. -/
lemma conj_layer_last (x y z : ℂ) :
    singleQubitLayer (Pg x) (Pg y) (Pg z * Hgate)
      = singleQubitLayer (Pg x) (Pg y) (Pg z) * kron3 1 1 Hgate := by
  simp only [singleQubitLayer, kron3_mul, mul_one]

/-! ## §4  `n = 0` : the identity circuit, `d = √7/4` -/

def witness0 : Mat8 := singleQubitLayer I₂ I₂ I₂

lemma witness0_eq_one : witness0 = 1 := by
  rw [witness0, singleQubitLayer, I₂, kron3_one]

theorem witness0_achievable : AchievableCircuit 0 witness0 := by
  have hI : IsUnitary2 I₂ := by rw [IsUnitary2, I₂]; simp
  exact AchievableCircuit.single_layer I₂ I₂ I₂ hI hI hI

theorem witness0_trace : Matrix.trace (witness0ᴴ * CCX) = 6 := by
  rw [witness0_eq_one, Matrix.conjTranspose_one, one_mul]
  simp [Matrix.trace, Matrix.diag, CCX, decode3, pauliX, Fin.sum_univ_eight]
  norm_num

theorem witness0_normSq : Complex.normSq (Matrix.trace (witness0ᴴ * CCX)) = 36 := by
  rw [witness0_trace]; norm_num [Complex.normSq_apply]

theorem witness0_distance : hsDistance witness0 CCX = Real.sqrt 7 / 4 := by
  rw [hsDistance, hsFidelity, witness0_normSq]
  rw [show (1 : ℝ) - 36 / 64 = (Real.sqrt 7 / 4) ^ 2 by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-! ## §5  `n = 2` : `CS_AB ⊗ P_C(τ)`, `d = √6/4 = √(3/8)`

Word `AB·AB` (two `CX_BA`).  The parity network puts `a⊕b` on wire A between the two
CNOTs; the phases `+π/4` on `a`, `+π/4` on `b`, `−π/4` on `a⊕b` reconstruct
`i^{ab} = CS_AB`, and the free C-phase `τ` maximises `|(3+i) + (3−i)τ| = √40`. -/

def ccz2Circuit : Mat8 :=
  CX_BA * singleQubitLayer (Pg wm) (Pg 1) (Pg 1)
  * CX_BA * singleQubitLayer (Pg wp) (Pg wp) (Pg tau)

def witness2 : Mat8 :=
  singleQubitLayer I₂ I₂ Hgate
  * CX_BA * singleQubitLayer (Pg wm) (Pg 1) (Pg 1)
  * CX_BA * singleQubitLayer (Pg wp) (Pg wp) (Pg tau * Hgate)

def Y1 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,0,0,0,0,wm,0; 0,0,0,0,0,0,0,wm;
  0,0,0,0,wm,0,0,0; 0,0,0,0,0,wm,0,0; 0,0,1,0,0,0,0,0; 0,0,0,1,0,0,0,0]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: 64 entrywise cases of an 8×8 monomial product, each an
-- eight-term `Fin.sum_univ_eight` expansion.
lemma y1 : CXBAlit * Matrix.diagonal ![1,1,1,1,wm,wm,wm,wm] = Y1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CXBAlit, Y1, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `y1`.
lemma y2 : Y1 * CXBAlit
    * Matrix.diagonal ![1, tau, wp, wp*tau, wp, wp*tau, wp*wp, wp*wp*tau]
    = Matrix.diagonal ![1, tau, 1, tau, 1, tau, Complex.I, Complex.I*tau] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Y1, CXBAlit, Matrix.mul_apply, Fin.sum_univ_eight, Matrix.diagonal_apply,
      wm_mul_wp, wp_mul_wp, wm_wp_assoc]

lemma ccz2Circuit_eq :
    ccz2Circuit = Matrix.diagonal ![1, tau, 1, tau, 1, tau, Complex.I, Complex.I*tau] := by
  rw [ccz2Circuit]
  simp only [CX_BA_lit, layerP_diag, one_mul, mul_one]
  rw [y1, y2]

lemma witness2_conj : witness2 = kron3 1 1 Hgate * ccz2Circuit * kron3 1 1 Hgate := by
  rw [witness2, conj_layer_last, ccz2Circuit]
  simp only [singleQubitLayer, I₂, ← mul_assoc]

theorem witness2_achievable : AchievableCircuit 2 witness2 := by
  have hI : IsUnitary2 I₂ := by rw [IsUnitary2, I₂]; simp
  have hBA : AllowedCX CX_BA := Or.inr (Or.inl rfl)
  exact AchievableCircuit.compose (Pg wp) (Pg wp) (Pg tau * Hgate)
    (Pg_unitary normSq_wp) (Pg_unitary normSq_wp)
    (isUnitary2_mul (Pg_unitary normSq_tau) hgate_unitary) hBA
    (AchievableCircuit.compose (Pg wm) (Pg 1) (Pg 1)
      (Pg_unitary normSq_wm) Pg_one_unitary Pg_one_unitary hBA
      (AchievableCircuit.single_layer I₂ I₂ Hgate hI hI hgate_unitary))

theorem witness2_trace : Matrix.trace (witness2ᴴ * CCX) = 6 - 2 * Complex.I := by
  rw [witness2_conj, trace_conjH_ccx, ccz2Circuit_eq, trace_diag_ccz]
  simp [tau, Complex.ext_iff]
  norm_num

theorem witness2_normSq : Complex.normSq (Matrix.trace (witness2ᴴ * CCX)) = 40 := by
  rw [witness2_trace]; norm_num [Complex.normSq_apply]

theorem witness2_distance : hsDistance witness2 CCX = Real.sqrt 6 / 4 := by
  rw [hsDistance, hsFidelity, witness2_normSq]
  rw [show (1 : ℝ) - 40 / 64 = (Real.sqrt 6 / 4) ^ 2 by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]; norm_num]
  exact Real.sqrt_sq (by positivity)

/-! ## §6  `n = 4` : the six-parity circuit, `d = sin(π/8)`

Word `BC·AB·BC·AB` (`CX_CB, CX_AB, CX_CB, CX_AB`).  Wire B successively holds
`b, a⊕b, a⊕b⊕c, b⊕c, b`; the network returns to the identity and covers six of the
seven parities, missing exactly `a⊕c` — the parity of the two NON-ADJACENT qubits.
The `CCZ` phase polynomial with that one term deleted has
`Tr = 4 + 4e^{-iπ/4}`, `|Tr|² = 32 + 16√2 = 64cos²(π/8)`.

This is a DIFFERENT circuit from `Attainment.witnessU` (which is `AB·BC·AB·BC` with
non-diagonal Clifford+T layers); it attains the same value. -/

def ccz4Circuit : Mat8 :=
  CX_CB * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg wp) (Pg 1)
  * CX_CB * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg wp) (Pg wp) (Pg wp)

def witness4 : Mat8 :=
  singleQubitLayer I₂ I₂ Hgate
  * CX_CB * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg wp) (Pg 1)
  * CX_CB * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg wp) (Pg wp) (Pg wp * Hgate)

def Z1 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,0,0,wm,0,0,0,0; 0,0,wm,0,0,0,0,0; 0,1,0,0,0,0,0,0;
  0,0,0,0,1,0,0,0; 0,0,0,0,0,0,0,wm; 0,0,0,0,0,0,wm,0; 0,0,0,0,0,1,0,0]

def Z2 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,0,0,1,0,0,0,0; 0,0,1,0,0,0,0,0; 0,1,0,0,0,0,0,0;
  0,0,0,0,0,0,wp,0; 0,0,0,0,0,wm,0,0; 0,0,0,0,wm,0,0,0; 0,0,0,0,0,0,0,wp]

def Z3 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,wm,0,0,0,0,0; 0,0,0,wm,0,0,0,0;
  0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,-Complex.I; 0,0,0,0,wm,0,0,0;
  0,0,0,0,0,wp,0,0]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: 64 entrywise cases of an 8×8 monomial product.
lemma z1 : CXCBlit * Matrix.diagonal ![1,1,wm,wm,1,1,wm,wm] = Z1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CXCBlit, Z1, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `z1`.
lemma z2 : Z1 * CXABlit * Matrix.diagonal ![1,1,wp,wp,1,1,wp,wp] = Z2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z1, CXABlit, Z2, Matrix.mul_apply, Fin.sum_univ_eight, wm_mul_wp]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `z1`.
lemma z3 : Z2 * CXCBlit * Matrix.diagonal ![1,1,wm,wm,1,1,wm,wm] = Z3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z2, CXCBlit, Z3, Matrix.mul_apply, Fin.sum_univ_eight, wp_mul_wm, wm_mul_wm]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `z1`.
lemma z4 : Z3 * CXABlit
    * Matrix.diagonal ![1, wp, wp, wp*wp, wp, wp*wp, wp*wp, wp*wp*wp]
    = Matrix.diagonal ![1, wp, 1, wp, wp, 1, wp, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Z3, CXABlit, Matrix.mul_apply, Fin.sum_univ_eight, Matrix.diagonal_apply,
      wp_mul_wp, wm_mul_I, wm_mul_wp, I_mul_wp, wp_mul_wm]

lemma ccz4Circuit_eq :
    ccz4Circuit = Matrix.diagonal ![1, wp, 1, wp, wp, 1, wp, -1] := by
  rw [ccz4Circuit]
  simp only [CX_AB_lit, CX_CB_lit, layerP_diag, one_mul, mul_one]
  rw [z1, z2, z3, z4]

lemma witness4_conj : witness4 = kron3 1 1 Hgate * ccz4Circuit * kron3 1 1 Hgate := by
  rw [witness4, conj_layer_last, ccz4Circuit]
  simp only [singleQubitLayer, I₂, ← mul_assoc]

theorem witness4_achievable : AchievableCircuit 4 witness4 := by
  have hI : IsUnitary2 I₂ := by rw [IsUnitary2, I₂]; simp
  have hAB : AllowedCX CX_AB := Or.inl rfl
  have hCB : AllowedCX CX_CB := Or.inr (Or.inr (Or.inr rfl))
  have hp : IsUnitary2 (Pg wp) := Pg_unitary normSq_wp
  have hm : IsUnitary2 (Pg wm) := Pg_unitary normSq_wm
  exact AchievableCircuit.compose (Pg wp) (Pg wp) (Pg wp * Hgate) hp hp
    (isUnitary2_mul hp hgate_unitary) hAB
    (AchievableCircuit.compose (Pg 1) (Pg wm) (Pg 1) Pg_one_unitary hm Pg_one_unitary hCB
      (AchievableCircuit.compose (Pg 1) (Pg wp) (Pg 1) Pg_one_unitary hp Pg_one_unitary hAB
        (AchievableCircuit.compose (Pg 1) (Pg wm) (Pg 1) Pg_one_unitary hm Pg_one_unitary hCB
          (AchievableCircuit.single_layer I₂ I₂ Hgate hI hI hgate_unitary))))

theorem witness4_trace :
    Matrix.trace (witness4ᴴ * CCX) = 4 + 4 * invSqrt2 - 4 * invSqrt2 * Complex.I := by
  rw [witness4_conj, trace_conjH_ccx, ccz4Circuit_eq, trace_diag_ccz]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    star_one, star_wp, star_neg, Fin.isValue]
  simp only [wm]
  ring

theorem witness4_normSq :
    Complex.normSq (Matrix.trace (witness4ᴴ * CCX)) = 32 + 16 * Real.sqrt 2 := by
  have hr : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hcast : invSqrt2 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
    rw [invSqrt2, Complex.ofReal_inv]
  rw [witness4_trace, hcast,
    show (4 : ℂ) + 4 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        - 4 * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * Complex.I
      = (((4 + 4 * (Real.sqrt 2)⁻¹ : ℝ) : ℂ))
        + (((-(4 * (Real.sqrt 2)⁻¹) : ℝ) : ℂ)) * Complex.I by push_cast; ring,
    Complex.normSq_add_mul_I]
  field_simp
  nlinarith [hsq, hr]

/-- `sin²(π/8) = ½ − √2/4`.  (Local copy; `Attainment.sin_pi_eight_sq` is the same
    statement, but this file deliberately does not import `Attainment`.) -/
lemma sin_pi_eight_sq' : Real.sin (Real.pi / 8) ^ 2 = 1/2 - Real.sqrt 2 / 4 := by
  have h2 : Real.cos (2 * (Real.pi/8)) = 2 * Real.cos (Real.pi/8) ^ 2 - 1 :=
    Real.cos_two_mul _
  rw [show 2 * (Real.pi/8) = Real.pi/4 by ring, Real.cos_pi_div_four] at h2
  have hpy := Real.sin_sq_add_cos_sq (Real.pi/8)
  linarith

theorem witness4_distance : hsDistance witness4 CCX = Real.sin (Real.pi / 8) := by
  rw [hsDistance, hsFidelity, witness4_normSq]
  rw [show (1 : ℝ) - (32 + 16 * Real.sqrt 2)/64 = Real.sin (Real.pi/8) ^ 2 by
    rw [sin_pi_eight_sq']; ring]
  exact Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by nlinarith [Real.pi_pos]))

/-! ## §7  `n = 8` : the exact Toffoli, `d = 0`

Word `BC·AB·BC·AB·BC·AB·BC·AB` reading the matrix product left to right (i.e.
`(AB·BC)⁴` in time order).  The network returns to the identity and visits ALL SEVEN
parities, so the seven `CCZ` phases can all be placed and the circuit IS `CCZ`;
conjugating by `H_C` gives `CCX` on the nose. -/

def W1 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,1,0,0,0,0,0,0; 0,0,0,1,0,0,0,0; 0,0,1,0,0,0,0,0;
  0,0,0,0,1,0,0,0; 0,0,0,0,0,1,0,0; 0,0,0,0,0,0,0,1; 0,0,0,0,0,0,1,0]

def W2 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,wm,0,0,0,0,0,0; 0,0,0,wm,0,0,0,0; 0,0,1,0,0,0,0,0;
  0,0,0,0,0,0,1,0; 0,0,0,0,0,0,0,wm; 0,0,0,0,0,wm,0,0; 0,0,0,0,1,0,0,0]

def W3 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,wm,0,0,0,0,0,0; 0,0,wm,0,0,0,0,0; 0,0,0,1,0,0,0,0;
  0,0,0,0,0,0,0,1; 0,0,0,0,0,0,wm,0; 0,0,0,0,0,wm,0,0; 0,0,0,0,1,0,0,0]

def W4 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,-Complex.I,0,0,0,0,0,0; 0,0,wm,0,0,0,0,0; 0,0,0,wm,0,0,0,0;
  0,0,0,0,0,wm,0,0; 0,0,0,0,wm,0,0,0; 0,0,0,0,0,0,0,-Complex.I; 0,0,0,0,0,0,1,0]

def W5 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,-Complex.I,0,0,0,0,0,0; 0,0,0,wm,0,0,0,0; 0,0,wm,0,0,0,0,0;
  0,0,0,0,0,wm,0,0; 0,0,0,0,wm,0,0,0; 0,0,0,0,0,0,-Complex.I,0; 0,0,0,0,0,0,0,1]

def W6 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,wm,0,0,0,0,0,0; 0,0,0,1,0,0,0,0; 0,0,wm,0,0,0,0,0;
  0,0,0,0,0,0,0,1; 0,0,0,0,0,0,wm,0; 0,0,0,0,-Complex.I,0,0,0; 0,0,0,0,0,wp,0,0]

def W7 : Mat8 := Matrix.of !![
  1,0,0,0,0,0,0,0; 0,wm,0,0,0,0,0,0; 0,0,wm,0,0,0,0,0; 0,0,0,-Complex.I,0,0,0,0;
  0,0,0,0,0,0,wm,0; 0,0,0,0,0,0,0,-Complex.I; 0,0,0,0,-Complex.I,0,0,0;
  0,0,0,0,0,wp,0,0]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: 64 entrywise cases of an 8×8 monomial product.
lemma st1 : CXBClit * Matrix.diagonal ![1,1,1,1,1,1,1,1] = W1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [CXBClit, W1, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st2 : W1 * CXABlit * Matrix.diagonal ![1,wm,1,wm,1,wm,1,wm] = W2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W1, CXABlit, W2, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st3 : W2 * CXBClit * Matrix.diagonal ![1,1,1,1,1,1,1,1] = W3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W2, CXBClit, W3, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st4 : W3 * CXABlit * Matrix.diagonal ![1,wm,1,wm,1,wm,1,wm] = W4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W3, CXABlit, W4, Matrix.mul_apply, Fin.sum_univ_eight, wm_mul_wm]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st5 : W4 * CXBClit * Matrix.diagonal ![1,1,1,1,1,1,1,1] = W5 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W4, CXBClit, W5, Matrix.mul_apply, Fin.sum_univ_eight]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st6 : W5 * CXABlit * Matrix.diagonal ![1,wp,1,wp,1,wp,1,wp] = W6 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W5, CXABlit, W6, Matrix.mul_apply, Fin.sum_univ_eight, wm_mul_wp, I_mul_wp]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st7 : W6 * CXBClit * Matrix.diagonal ![1,1,wm,wm,1,1,wm,wm] = W7 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W6, CXBClit, W7, Matrix.mul_apply, Fin.sum_univ_eight, wm_mul_wm]

set_option maxHeartbeats 2000000 in
-- Heartbeat bump: as `st1`.
lemma st8 : W7 * CXABlit
    * Matrix.diagonal ![1, wp, wp, wp*wp, wp, wp*wp, wp*wp, wp*wp*wp] = CCZ8 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [W7, CXABlit, CCZ8, Matrix.mul_apply, Fin.sum_univ_eight,
      Matrix.diagonal_apply, wm_mul_wp, wp_mul_wp, I_mul_wp, wp_mul_wm]

def ccz8Circuit : Mat8 :=
  CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wm)
  * CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wm)
  * CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wp)
  * CX_BC * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg wp) (Pg wp) (Pg wp)

/-- **The eight-CNOT LNN circuit IS `CCZ`.** -/
theorem ccz8Circuit_eq : ccz8Circuit = CCZ8 := by
  rw [ccz8Circuit]
  simp only [CX_AB_lit, CX_BC_lit, layerP_diag, one_mul, mul_one]
  rw [st1, st2, st3, st4, st5, st6, st7, st8]

def witness8 : Mat8 :=
  singleQubitLayer I₂ I₂ Hgate
  * CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wm)
  * CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wm)
  * CX_BC * singleQubitLayer (Pg 1) (Pg 1) (Pg 1)
  * CX_AB * singleQubitLayer (Pg 1) (Pg 1) (Pg wp)
  * CX_BC * singleQubitLayer (Pg 1) (Pg wm) (Pg 1)
  * CX_AB * singleQubitLayer (Pg wp) (Pg wp) (Pg wp * Hgate)

lemma witness8_conj : witness8 = kron3 1 1 Hgate * ccz8Circuit * kron3 1 1 Hgate := by
  rw [witness8, conj_layer_last, ccz8Circuit]
  simp only [singleQubitLayer, I₂, ← mul_assoc]

/-- **`d(8) = 0`: the explicit eight-CNOT line circuit EQUALS the Toffoli gate.**
    A finite matrix identity — no approximation, no global phase. -/
theorem witness8_eq_CCX : witness8 = CCX := by
  rw [witness8_conj, ccz8Circuit_eq, ← ccx_eq_ccz_conj]

theorem witness8_achievable : AchievableCircuit 8 witness8 := by
  have hI : IsUnitary2 I₂ := by rw [IsUnitary2, I₂]; simp
  have hp : IsUnitary2 (Pg wp) := Pg_unitary normSq_wp
  have hm : IsUnitary2 (Pg wm) := Pg_unitary normSq_wm
  have h1 : IsUnitary2 (Pg 1) := Pg_one_unitary
  have hAB : AllowedCX CX_AB := Or.inl rfl
  have hBC : AllowedCX CX_BC := Or.inr (Or.inr (Or.inl rfl))
  exact AchievableCircuit.compose (Pg wp) (Pg wp) (Pg wp * Hgate) hp hp
    (isUnitary2_mul hp hgate_unitary) hAB
    (AchievableCircuit.compose (Pg 1) (Pg wm) (Pg 1) h1 hm h1 hBC
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg wp) h1 h1 hp hAB
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg 1) h1 h1 h1 hBC
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg wm) h1 h1 hm hAB
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg 1) h1 h1 h1 hBC
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg wm) h1 h1 hm hAB
    (AchievableCircuit.compose (Pg 1) (Pg 1) (Pg 1) h1 h1 h1 hBC
    (AchievableCircuit.single_layer I₂ I₂ Hgate hI hI hgate_unitary))))))))

lemma trace_ccx_ccx : Matrix.trace (CCXᴴ * CCX) = 8 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    CCX, decode3, pauliX, Fin.sum_univ_eight]
  norm_num

theorem witness8_trace : Matrix.trace (witness8ᴴ * CCX) = 8 := by
  rw [witness8_eq_CCX, trace_ccx_ccx]

theorem witness8_normSq : Complex.normSq (Matrix.trace (witness8ᴴ * CCX)) = 64 := by
  rw [witness8_trace]; norm_num [Complex.normSq_apply]

theorem witness8_distance : hsDistance witness8 CCX = 0 := by
  rw [hsDistance, hsFidelity, witness8_normSq]
  norm_num

/-! ## §8  The curve, assembled -/

/-- **The constructive half of the curve `d(n)`.**  Combined with
    `Basic.approxToffoli_lower_bound` (which gives `d ≥ sin(π/8)` for `n ≤ 5`), the
    `n = 4` line re-proves `d(4) = d(5) = sin(π/8)` with a purely CNOT+phase witness. -/
theorem curve_attained :
    (∃ U : Mat8, AchievableCircuit 0 U ∧ hsDistance U CCX = Real.sqrt 7 / 4) ∧
    (∃ U : Mat8, AchievableCircuit 2 U ∧ hsDistance U CCX = Real.sqrt 6 / 4) ∧
    (∃ U : Mat8, AchievableCircuit 4 U ∧ hsDistance U CCX = Real.sin (Real.pi / 8)) ∧
    (∃ U : Mat8, AchievableCircuit 8 U ∧ hsDistance U CCX = 0) :=
  ⟨⟨witness0, witness0_achievable, witness0_distance⟩,
   ⟨witness2, witness2_achievable, witness2_distance⟩,
   ⟨witness4, witness4_achievable, witness4_distance⟩,
   ⟨witness8, witness8_achievable, witness8_distance⟩⟩

/-! The same four points obtained uniformly through the generalised reduction of
`TraceReduction.lean`, showing the interface is the intended one. -/

theorem curve0_gen : hsDistance witness0 CCX = Real.sqrt (1 - 36 / 64) :=
  trace_eq_implies_distance_gen witness0 witness0_normSq

theorem curve2_gen : hsDistance witness2 CCX = Real.sqrt (1 - 40 / 64) :=
  trace_eq_implies_distance_gen witness2 witness2_normSq

theorem curve4_gen :
    hsDistance witness4 CCX = Real.sqrt (1 - (32 + 16 * Real.sqrt 2) / 64) :=
  trace_eq_implies_distance_gen witness4 witness4_normSq

theorem curve8_gen : hsDistance witness8 CCX = Real.sqrt (1 - 64 / 64) :=
  trace_eq_implies_distance_gen witness8 witness8_normSq

end Curve
end
