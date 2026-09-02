/-
  ApproxToffoli.TraceBound
  Core trace inequality: |Tr(U† CCX)|² ≤ 64 · cos²(π/8) for achievable circuits
  with at most 5 CX gates (AB/BC connectivity only).

  IMPORTANT: The bound does NOT hold for arbitrary n. With ~12 AB/BC CX gates,
  one can build CCX exactly (via CNOT_AC simulation), giving |Tr|² = 64 > 64cos²(π/8).
  The bound is specific to n ≤ 5.

  **The proof is the CUT-FORM argument** (`CutAlgebra` → `CutForm` → `CutNormalForm` →
  `LemmaT1`/`CutBound` → `CutMain`), and this file is now only the adapter that gives
  it its historical name. In outline: an `AchievableCircuit n` circuit admits BOTH an
  AB|C and an A|BC cut with `m_BC + m_AB ≤ n`, so for `n ≤ 5` — and here it matters
  that 5 is ODD — one of the two cuts has at most 2 crossing gates; the A|BC branch is
  mirrored onto the AB|C one by the A↔C relabelling, which fixes `CCZ`. Bounding
  `F(m)` for `m ≤ 2` is then a statement about 4×4 traces with no circuits in it.

  **Why the old induction-on-gate-count proof was abandoned.** It went by induction on
  `n` with a `compose` step appending one CX gate and one product layer. That step
  (`compose_trace_bound`, four case sorries, one per CX type) is not fixable: the
  induction hypothesis tracks a single scalar `|Tr(rest† CCX)|²`, while the compose
  step needs the product numerical radius `pnr(CX · rest† · CCX)`, an optimisation over
  ALL product layers. Roughly fifteen approaches died there. It was DELETED, not
  filled, when the cut proof landed. The `m ≤ 2` bound is TIGHT — `F(2)² = 64cos²(π/8)`
  is attained — whereas `F(3) = F(4) = 8`, so no gate-count induction can work without
  already knowing the cut structure.
-/

import ApproxToffoli.Circuit
import ApproxToffoli.Gates
import ApproxToffoli.HSDistance
import ApproxToffoli.BaseCase
import ApproxToffoli.Helpers
import ApproxToffoli.CutMain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix Complex Real

noncomputable section

/-! ## Main theorem

`compose_trace_bound` — the four-case `sorry` that stood here from iter 234 to
iter 1058 — has been DELETED. It was the compose step of an induction on gate count,
and that architecture cannot be repaired: see the module docstring. The bound is now
`CutMain.achievable_trace_bound_cut`, which is not an induction on gate count at all,
and this is the adapter that presents it under the name the rest of the development
uses. -/

/-- The bound holds for achievable circuits with at most 5 CX gates. -/
theorem achievable_trace_bound
    (U : Mat8) (hU : AchievableCircuit 5 U) :
    Complex.normSq (Matrix.trace (U.conjTranspose * CCX)) ≤
      64 * Real.cos (Real.pi / 8) ^ 2 :=
  achievable_trace_bound_cut (le_refl 5) hU

end
