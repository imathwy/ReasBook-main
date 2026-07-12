import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.CommSq

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall note: mathlib already owns the canonical composition and descent API for
-- `LocallyOfFiniteType`, `UniversallyClosed`, and `IsSeparated`. The source item here is the
-- square-shaped bridge specialized to a projective comparison morphism `P ⟶ S`, so the public
-- surface remains a `CommSq` theorem while delegating the actual descent steps to those canonical
-- owners.

/-- 32.14.3.1: in a commutative square
`X' ⟶ P`, `X' ⟶ X`, `P ⟶ S`, `X ⟶ S` with `π` surjective and proper, the bottom morphism is
proper as soon as the top and right morphisms are proper. -/
theorem isProper_of_surjective_commSq
    {S X P X' : Scheme.{u}} {f : X ⟶ S} {p : P ⟶ S}
    (toP : X' ⟶ P) (π : X' ⟶ X)
    (hcomm : CommSq toP π p f)
    [Surjective π] [IsProper π] [IsProper toP] [IsProper p] : IsProper f := by
  have hcomp : IsProper (π ≫ f) := by
    simpa [hcomm.w] using (inferInstance : IsProper (toP ≫ p))
  letI : IsProper (π ≫ f) := hcomp
  letI : IsSeparated f := IsSeparated.of_comp π f
  letI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp π f
  letI : UniversallyClosed f := UniversallyClosed.of_comp_surjective π f
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
