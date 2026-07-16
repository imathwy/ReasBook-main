import StacksProject_2024.stacks_project.Chap10.Lemma_10_157_5
import StacksProject_2024.stacks_project.Chap28.Definition_28_7_1
import StacksProject_2024.stacks_project.Chap28.Definition_28_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local precedent: Chapter 28 already owns regularity via `Scheme.Regular` and
-- normality via `Scheme.isNormalAt` / `Scheme.isNormal`, while Lemma `10.157.5` supplies the
-- ring-theoretic bridge from regular to normal. The source-facing scheme statement should
-- therefore center the canonical owner `Regular X`, with the stalkwise formulation kept only as a
-- bridge.

variable {X : Scheme.{u}}

/-- If the stalk of `X` at `x` is a regular local ring, then `X` is normal at `x`. -/
theorem isNormalAt_of_isRegularLocalRing_stalk (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    X.isNormalAt x := by
  letI : IsRegularLocalRing (X.presheaf.stalk x) := hx
  simpa using (isNormalRing_of_isRegularRing : IsNormalRing (X.presheaf.stalk x))

/-- A regular scheme is normal at each point. -/
theorem Regular.isNormalAt (hX : Regular X) (x : X) :
    X.isNormalAt x := by
  letI : Regular X := hX
  exact isNormalAt_of_isRegularLocalRing_stalk x (isRegularLocalRing_stalk X x)

@[stacks 0569]
/-- Lemma 28.9.4: a regular scheme is normal. -/
theorem Regular.isNormal (hX : Regular X) :
    X.isNormal := fun x ↦ hX.isNormalAt x

/-- If every stalk of `X` is a regular local ring, then `X` is normal. -/
theorem isNormal_of_isRegularLocalRing_stalk
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    X.isNormal := fun x ↦
  isNormalAt_of_isRegularLocalRing_stalk x (hX x)

end AlgebraicGeometry.Scheme
