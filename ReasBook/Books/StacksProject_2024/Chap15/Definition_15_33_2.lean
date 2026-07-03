import Mathlib
import StacksProject_2024.Chap15.Definition_15_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/- Domain triage:
- primary domain: commutative algebra of local complete intersection ring maps via finite
  polynomial presentations;
- sampled owner declarations: `Ideal.IsKoszulRegularIdeal`, `Algebra.Generators`,
  `RingHom.Syntomic`, and Chapter 10's field-fiber owner `IsLocalCompleteIntersection`;
- layer: `source-facing`; this file owns the general ring-hom notion, while `RingHom.Syntomic`
  is the flatter/fiberwise core notion used later and the Chapter 10 field-algebra definition
  controls fibers only;
- primitive vs derived split: the primitive data are a finite generator presentation together with
  Koszul-regularity of its kernel ideal, while finite type is derived API and should not be stored
  as primitive owner data. -/

/-- Definition 15.33.2: a ring map `f : A →+* B` is a local complete intersection if for some
finite family of generators of `B` over `A`, the kernel ideal of the induced polynomial
presentation `A[x₁, …, xₙ] → B` is Koszul-regular. This is the Stacks-project presentation
criterion, whose finite generation of variables already encodes the finite-type hypothesis. -/
class IsLocalCompleteIntersection (f : A →+* B) : Prop where
  exists_generators_ker_isKoszulRegular :
    let _ : Algebra A B := f.toAlgebra
    ∃ n : ℕ, ∃ P : Algebra.Generators A B (Fin n),
      P.ker.IsKoszulRegularIdeal

namespace IsLocalCompleteIntersection

/-- A local complete intersection ring map is of finite type. -/
theorem finiteType {f : A →+* B} (h : f.IsLocalCompleteIntersection) : f.FiniteType := by
  let _ : Algebra A B := f.toAlgebra
  rcases h.exists_generators_ker_isKoszulRegular with ⟨n, P, _⟩
  simpa [RingHom.FiniteType] using (P.finiteType : Algebra.FiniteType A B)

instance {f : A →+* B} [h : f.IsLocalCompleteIntersection] : f.FiniteType :=
  h.finiteType

/-- The identity ring map is a local complete intersection. -/
@[instance] theorem id :
    (RingHom.id A).IsLocalCompleteIntersection := sorry

end IsLocalCompleteIntersection

end

end RingHom
