import Mathlib.Geometry.Manifold.DerivationBundle

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Derivation Manifold

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

local notation "SmoothFunction" => C^∞⟮I, M; ℝ⟯
local notation "SmoothDerivation" => Derivation ℝ SmoothFunction SmoothFunction

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item is
-- matched directly against mathlib's generic `Derivation` specialized to smooth real-valued
-- functions on a manifold.

/- Definition 8.56-extra-2: Lee's notion of a derivation of `C^∞(M)` is the canonical mathlib
type of `ℝ`-derivations of the algebra of smooth real-valued functions on `M`. -/
#check (SmoothDerivation : Type _)

/- The linearity requirement in the definition is the underlying `ℝ`-linear map of a derivation. -/
#check
  (Derivation.toLinearMap :
    SmoothDerivation → SmoothFunction →ₗ[ℝ] SmoothFunction)

/- Equation (8.5) is the canonical Leibniz rule `Derivation.leibniz`; in the algebra API, the
factors `f` and `g` act on `X g` and `X f` by scalar multiplication, i.e. pointwise
multiplication. -/
#check
  (Derivation.leibniz :
    ∀ (X : SmoothDerivation) (f g : SmoothFunction),
      X (f * g) = f • X g + g • X f)

end
