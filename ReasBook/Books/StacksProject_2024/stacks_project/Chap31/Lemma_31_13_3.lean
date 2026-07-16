import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed `Scheme.Opens.ι` as the canonical inclusion of an
-- open subscheme. For the source complement `S \ Z`, the relevant owner is the explicit open
-- subset complementary to the set-theoretic image of the closed immersion.

variable {S Z : Scheme.{u}}

/-- The open complement of the image of a closed immersion of schemes. -/
def closedImmersionComplement (i : Z ⟶ S) [IsClosedImmersion i] : S.Opens :=
  ⟨(Set.range ⇑(CategoryTheory.ConcreteCategory.hom i.base))ᶜ,
    (isOpen_compl_iff).2 (IsClosedImmersion.isClosedEmbedding i).isClosed_range⟩

/-- Lemma 31.13.3: if `i : Z ⟶ S` is a locally principal closed subscheme of a scheme `S`, then
the inclusion of the open complement `S \ Z`, formalized as
`(closedImmersionComplement i).ι`, is an affine morphism. -/
theorem isAffineHom_closedImmersionComplement_ι_of_isLocallyPrincipalClosedSubscheme
    (i : Z ⟶ S) [IsLocallyPrincipalClosedSubscheme i] :
    IsAffineHom (closedImmersionComplement i).ι := sorry

end AlgebraicGeometry
