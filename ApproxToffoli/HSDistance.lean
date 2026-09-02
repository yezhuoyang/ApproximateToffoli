/-
  ApproxToffoli.HSDistance
  Hilbert-Schmidt fidelity and distance for 8×8 complex matrices.
-/

import ApproxToffoli.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Sqrt

open Matrix Complex Real

noncomputable section

/-! ## Hilbert-Schmidt fidelity and distance -/

/-- HS fidelity: `|Tr(U† V)|² / dim²`; for 8×8 matrices (3 qubits), `/ 64`. -/
def hsFidelity (U V : Mat8) : ℝ :=
  Complex.normSq (Matrix.trace (U.conjTranspose * V)) / 64

/-- `d(U,V) = √(1 − |Tr(U† V)|² / 64)`. This is the source preprint's Eq. (3)
    (`ApproxToffoli.pdf` §2, `√(1 − |Tr(U†V)|²/2^{2n})` at `n = 3`) implemented verbatim.

    **What it is, despite the name.** This is NOT the Hilbert–Schmidt (Frobenius)
    distance `‖U−V‖_F`; for 8×8 unitaries `‖U−V‖_F² = 16 − 2 Re Tr(U†V)`, which is a
    different quantity. Writing `cos θ = |Tr(U†V)|/8`, this is `sin θ` — the sine of the
    ray (Fubini–Study) angle between `U` and `V`, equivalently `√(1 − F_process)`. Unlike
    `‖U−V‖_F` it is invariant under a global phase on either argument, which is the right
    behaviour when comparing quantum gates. The name follows the preprint's usage.

    Note `Real.sqrt` returns 0 on negative input, so `hsDistance` is only meaningful when
    `hsFidelity ≤ 1` — automatic for unitary arguments, which is all this development
    ever applies it to. -/
def hsDistance (U V : Mat8) : ℝ :=
  Real.sqrt (1 - hsFidelity U V)

end
