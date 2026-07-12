import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Derivation Manifold
open TopologicalSpace

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this recall-only
-- notation item was matched directly against mathlib's smooth-function derivation owner
-- `Derivation.evalAt_apply`, the smooth-function restriction owner
-- `ContMDiffMap.restrictRingHom`, and the adjacent chapter bridge
-- `ContMDiffSection.toDerivation` from `Notation_8_56_extra_3`.

/- Notation 8.56-extra-1 is recall-only.
Source-facing layer: the textbook operator `Xf` and restriction of smooth functions to open
subsets.
Core owners: `Derivation.evalAt_apply` and `ContMDiffMap.restrictRingHom`.
Derived API: pointwise evaluation of `Xf` and restriction maps on rings of smooth functions. -/

/- The textbook operator `Xf` is the canonical application of a smooth derivation to a smooth
function, and `Derivation.evalAt_apply` is the owner theorem for the pointwise identity
`(Xf)(p) = Xₚ f`. -/
recall Derivation.evalAt_apply

/- Restriction of smooth real-valued functions to an open subset is the canonical owner
`ContMDiffMap.restrictRingHom`, which realizes equation (8.4) by precomposition with the subset
inclusion. -/
recall ContMDiffMap.restrictRingHom

/-- Notation 8.56-extra-1: the textbook operator `Xf` is evaluated pointwise by the canonical
owner theorem `Derivation.evalAt_apply`, while restriction to open subsets is handled by the
recalled owner `ContMDiffMap.restrictRingHom`. -/
theorem Notation_8_56_extra_1
    (X : Derivation ℝ SmoothFunction SmoothFunction) (f : SmoothFunction) (p : M) :
    Derivation.evalAt p X f = (X f) p := by
  rfl

end
