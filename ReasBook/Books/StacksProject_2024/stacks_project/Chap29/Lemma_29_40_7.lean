import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_37_6
import StacksProject_2024.stacks_project.Chap29.Definition_29_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical finite-type and quasi-affine
-- scheme-morphism owners; local Chapter 29 files provide `Scheme.Hom.FiniteType`,
-- `QuasiAffineHom`, Lemma 29.37.6 as the structure-sheaf relative-ampleness bridge, and the
-- section definition `QuasiProjective`. The Stacks tag evidence is consistent: item tag and
-- source URL both give `0B3H`.

/-- Lemma 29.40.7: A quasi-affine morphism of finite type is quasi-projective. -/
@[stacks 0B3H]
theorem QuasiAffineHom.quasiProjective_of_finiteType
    {X S : Scheme.{u}} {f : X ⟶ S} [Scheme.Hom.FiniteType f]
    (hf : QuasiAffineHom f) :
    QuasiProjective f := sorry

end AlgebraicGeometry
