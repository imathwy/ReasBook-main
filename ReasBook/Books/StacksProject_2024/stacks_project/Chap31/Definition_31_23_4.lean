import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` did not surface a dedicated owner for the Stacks-project
-- subsheaf of regular sections `𝒮_X`, so the source-facing owner is the nonzerodivisor set in
-- the ring of regular sections on each open subset.

variable (X : LocallyRingedSpace.{u})

/-- The regular meromorphic functions on an open subset, formalized as the nonzerodivisors in its
ring of regular sections. -/
abbrev regularMeromorphicSections (U : Opens X) : Set (X.presheaf.obj (op U)) :=
  nonZeroDivisors (X.presheaf.obj (op U))

namespace Hom

-- Semantic recall: `lean_leansearch` did not surface a dedicated owner for the Stacks-project
-- subsheaf of regular sections `𝒮_X`; the existing local owner for section pullback on ringed
-- spaces is the structure-sheaf morphism `f.toShHom.hom.c`, together with restriction along
-- `homOfLE e : U ⟶ (TopologicalSpace.Opens.map f.base).obj V`.

variable {X Y : LocallyRingedSpace.{u}}

/-- Pull a section on `V` back along `f` to `f⁻¹(V)` and then restrict it to `U ⊆ f⁻¹(V)`. -/
private abbrev pullbackSection
    (f : X ⟶ Y)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V) :
    Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op U) :=
  f.c.app (op V) ≫ X.presheaf.map (homOfLE e).op

/-- Definition 31.23.4: pullbacks of meromorphic functions are defined for a morphism
`f : X ⟶ Y` of locally ringed spaces if every section of the regular-section subsheaf on an open
`V ⊆ Y` pulls back to a section of the regular-section subsheaf on every open
`U ⊆ f⁻¹(V)`. -/
def pullbacksMeromorphicFunctionsDefined
    (f : X ⟶ Y)
    (regularSectionsX :
      ∀ U : Opens X, Set (X.presheaf.obj (op U)))
    (regularSectionsY :
      ∀ V : Opens Y, Set (Y.presheaf.obj (op V))) : Prop :=
  ∀ ⦃U : Opens X⦄ ⦃V : Opens Y⦄
    (e : U ≤ (Opens.map f.base).obj V)
    ⦃s : Y.presheaf.obj (op V)⦄,
      s ∈ regularSectionsY V →
        pullbackSection f e s ∈ regularSectionsX U

/-- Definition 31.23.4 specialized to the standard Chapter 31 regular-section subsheaves given by
nonzerodivisors on rings of sections. -/
abbrev pullbacksRegularMeromorphicFunctionsDefined (f : X ⟶ Y) : Prop :=
  pullbacksMeromorphicFunctionsDefined f X.regularMeromorphicSections Y.regularMeromorphicSections

/-- Apply Definition 31.23.4 to a specified regular section on `V`. -/
theorem pullbackSection_mem_regularSections
    {f : X ⟶ Y}
    {regularSectionsX :
      ∀ U : Opens X, Set (X.presheaf.obj (op U))}
    {regularSectionsY :
      ∀ V : Opens Y, Set (Y.presheaf.obj (op V))}
    (hf : pullbacksMeromorphicFunctionsDefined f regularSectionsX regularSectionsY)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V)
    {s : Y.presheaf.obj (op V)}
    (hs : s ∈ regularSectionsY V) :
    X.presheaf.map (homOfLE e).op ((f.c.app (op V)) s) ∈ regularSectionsX U :=
  hf e hs

/-- Apply the standard nonzerodivisor specialization of Definition 31.23.4 to a specified regular
meromorphic section on `V`. -/
theorem pullbackSection_mem_regularMeromorphicSections
    {f : X ⟶ Y}
    (hf : pullbacksRegularMeromorphicFunctionsDefined f)
    {U : Opens X} {V : Opens Y}
    (e : U ≤ (Opens.map f.base).obj V)
    {s : Y.presheaf.obj (op V)}
    (hs : s ∈ Y.regularMeromorphicSections V) :
    X.presheaf.map (homOfLE e).op ((f.c.app (op V)) s) ∈ X.regularMeromorphicSections U :=
  hf e hs

end Hom
end AlgebraicGeometry.LocallyRingedSpace
