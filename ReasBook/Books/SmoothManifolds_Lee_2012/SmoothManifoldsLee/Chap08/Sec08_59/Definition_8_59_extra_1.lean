import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

noncomputable section

section

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item is
-- matched directly against mathlib's manifold Lie-bracket owner.

/- Definition 8.59-extra-1: Lee's Lie bracket `[X, Y]` of vector fields on a smooth manifold is
the canonical manifold Lie bracket `VectorField.mlieBracket I X Y`, and we expose it through the
standard bracket notation `⁅X, Y⁆`. -/
recall VectorField.mlieBracket

namespace VectorField

instance : Bracket (Π p : M, TangentSpace I p) (Π p : M, TangentSpace I p) where
  bracket := mlieBracket I

@[simp] theorem bracket_eq_mlieBracket (X Y : Π p : M, TangentSpace I p) :
    ⁅X, Y⁆ = mlieBracket I X Y := rfl

end VectorField

variable (I : ModelWithCorners 𝕜 E H) (X Y : Π p : M, TangentSpace I p) (p : M)

/- The value of the Lie bracket at a point is a tangent vector at that point. -/
#check ⁅X, Y⁆ p

end
