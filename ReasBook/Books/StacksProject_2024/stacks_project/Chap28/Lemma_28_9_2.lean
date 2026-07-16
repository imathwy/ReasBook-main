import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import StacksProject_2024.stacks_project.Chap28.Definition_28_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical scheme-side owner `AlgebraicGeometry.IsLocallyNoetherian`
-- and the closed-point API, while local Chapter 28 precedent already packages regularity via
-- `Regular` together with stalkwise `IsRegularLocalRing`.
-- The source three-way equivalence is therefore recorded as two source-faithful equivalences with
-- the existing owner `Regular X` on the left.

variable (X : Scheme.{u})

/-- Lemma 28.9.2 (1): a scheme `X` is regular if and only if `X` is locally Noetherian and every
local ring `\mathcal O_{X, x}` is a regular local ring. -/
@[stacks 02IT]
theorem regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk :
    Regular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := sorry

/-- Lemma 28.9.2 (2): a scheme `X` is regular if and only if `X` is locally Noetherian and every
closed point `x ∈ X` has regular local ring `\mathcal O_{X, x}`. -/
@[stacks 02IT]
theorem regular_iff_isLocallyNoetherian_and_forall_closedPoint_isRegularLocalRing_stalk :
    Regular X ↔
      IsLocallyNoetherian X ∧
        ∀ x : X, x ∈ closedPoints X → IsRegularLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
