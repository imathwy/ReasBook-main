import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced `morphismRestrict` / `Scheme.Hom.resLE` for
-- restricting a scheme morphism to an open subscheme, and local Chapter 31 precedent supplies
-- `IsAdmissibleBlowup` as the owner for admissible blowups.

/-- Lemma 31.34.3: let `X` be a quasi-compact and quasi-separated scheme, let `U, V ⊆ X` be
quasi-compact open subschemes, and let `b : V' ⟶ V` be a `(U ∩ V)`-admissible blowup. Then there
exists a `U`-admissible blowup `π : X' ⟶ X` whose restriction to `V` is isomorphic to `b` over
`V`. The open `U ∩ V` is represented as the preimage of `U` along `V.ι`. -/
@[stacks 080M]
theorem exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter
    {X V' : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U V : X.Opens) (hU : QuasiCompact U.ι) (hV : QuasiCompact V.ι)
    (b : V' ⟶ V.toScheme)
    (hb : IsAdmissibleBlowup ((TopologicalSpace.Opens.map V.ι.base).obj U) b) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      IsAdmissibleBlowup U π ∧ Nonempty (Over.mk (π ∣_ V) ≅ Over.mk b) := sorry

end AlgebraicGeometry
