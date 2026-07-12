import StacksProject_2024.Chap31.Definition_31_19_5
import StacksProject_2024.Chap31.«31_19_1_2»

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for 31.19.5.1:
- `source-facing`: the canonical morphism `C_{Z/X} → N_{Z/X}` for an immersion `i : Z ⟶ X`;
- `core/canonical`: on an affine chart cut out by an ideal `I ⊆ R`, the ring map
  `idealConormalAlgebraQuotient I :
    SymmetricAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I] idealAssociatedGradedRing I`;
- `bridge/view`: the affine geometric morphism obtained from that ring map by `Spec.map`.

Chapter 31 already exposes the source-facing owners `NormalCone` and `NormalBundle` in
`Definition_31_19_5.lean`. The public surface here is therefore kept at the affine bridge/view
layer used by the current repository, rather than introducing a second packaged owner for the same
canonical comparison morphism. -/

noncomputable section

universe u

open CommRingCat
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "grI" => idealAssociatedGradedRing I

/-- 31.19.5.1 / tag `0637`: on an affine chart cut out by `I ⊆ R`, the canonical morphism
`C_{Z/X} → N_{Z/X}` is the scheme morphism obtained by applying `Spec.map` to the canonical
conormal-algebra quotient `idealConormalAlgebraQuotient I`. -/
@[stacks 0637]
abbrev affineChartNormalConeToNormalBundle :
    Spec (of grI) ⟶ Spec (of (SymmetricAlgebra (R ⧸ I) I.Cotangent)) :=
  Spec.map (ofHom (idealConormalAlgebraQuotient I).toRingHom)

/-- The affine chart model of the canonical morphism from the normal cone to the normal bundle is
a closed immersion. -/
theorem affineChartNormalConeToNormalBundle_isClosedImmersion :
    IsClosedImmersion (affineChartNormalConeToNormalBundle I) := by
  sorry

end

end AlgebraicGeometry
