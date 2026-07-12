import Mathlib
import StacksProject_2024.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical open-preimage API
-- `TopologicalSpace.Opens.map` / `Scheme.Hom.preimage`; nearby Chapter 31 precedent uses
-- `IsAdmissibleBlowup` as the owner for admissible blowups.

/-- Lemma 31.34.2: let `X` be a quasi-compact and quasi-separated scheme, let `U ⊆ X` be a
quasi-compact open subscheme, let `b : X' ⟶ X` be a `U`-admissible blowup, and let
`b' : X'' ⟶ X'` be admissible over the inverse-image open of `U` on `X'`. Then the composite
`X'' ⟶ X` is a `U`-admissible blowup. -/
@[stacks 080L]
theorem isAdmissibleBlowup_comp
    {X X' X'' : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U : X.Opens) (hU : QuasiCompact U.ι)
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (b ⁻¹ᵁ U) b') :
    IsAdmissibleBlowup U (b' ≫ b) := sorry

end AlgebraicGeometry
