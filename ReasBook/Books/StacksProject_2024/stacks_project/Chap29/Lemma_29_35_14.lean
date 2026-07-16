import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_32_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the ring-level criterion
  `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq` and the scheme fiber owner
  `Scheme.Hom.fiberOverSpecResidueField`.
- Local Chapter 29 precedent fixes pointwise unramifiedness as `Scheme.Hom.UnramifiedAt`
  and `Scheme.Hom.GUnramifiedAt`, fibers as `f.fiberToSpecResidueField s` with point
  `f.asFiber x`, and the relative differential sheaf as `Ω[f.toShHom]`.
- The source tag evidence is consistent: Stacks tag `02GF` is the URL tag for
  `Lemma 29.35.14`.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The maximal-ideal and residue-field criterion for unramifiedness at a point. -/
class MaximalIdealResidueFieldUnramifiedAtCriterion (f : X ⟶ S) (x : X) : Prop where
  maximalIdeal :
    Ideal.map (CommRingCat.Hom.hom (f.stalkMap x))
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  finiteDimensional :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (S.residueField (f x)) (X.residueField x)
  isSeparable :
    letI : Algebra (S.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (S.residueField (f x)) (X.residueField x)

/-- Lemma 29.35.14 (1): for a locally finite type morphism of schemes `f : X ⟶ S`
and a point `x : X`, the following conditions are equivalent: `f` is unramified at `x`;
the fibre over `f x` is unramified at the corresponding point; the stalks of
`Ω_{X/S}` and of the fibre differential sheaf vanish; the corresponding cotangent
vector spaces over the residue fields vanish; and
`𝔪_{f x} 𝒪_{X,x} = 𝔪_x` with finite separable residue-field extension `κ(x)/κ(f x)`. -/
@[stacks 02GF]
theorem unramifiedAt_tfae_differentials_fiber_residueField
    [LocallyOfFiniteType f] :
    List.TFAE [
      f.UnramifiedAt x,
      (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
      IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
      IsZero
        (RingedSpace.stalkModuleCat
          (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
      (Subsingleton
        ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
          (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x))),
      (Subsingleton
        ((IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ⊗[
            ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
          (RingedSpace.stalkModuleCat
            (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)))),
      MaximalIdealResidueFieldUnramifiedAtCriterion f x] := sorry

/-- Lemma 29.35.14 (2): for a locally finite presentation morphism of schemes `f : X ⟶ S`
and a point `x : X`, the `f.GUnramifiedAt x` version of the same list of equivalent
conditions holds: the fibre over `f x` is unramified at the corresponding point, the two
stalks of relative differentials vanish, the residue-field cotangent vector spaces vanish,
and the maximal-ideal plus finite-separable residue-field criterion holds. -/
@[stacks 02GF]
theorem gUnramifiedAt_tfae_differentials_fiber_residueField
    [LocallyOfFinitePresentation f] :
    List.TFAE [
      f.GUnramifiedAt x,
      (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
      IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
      IsZero
        (RingedSpace.stalkModuleCat
          (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
      (Subsingleton
        ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
          (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x))),
      (Subsingleton
        ((IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) ⊗[
            ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
          (RingedSpace.stalkModuleCat
            (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)))),
      MaximalIdealResidueFieldUnramifiedAtCriterion f x] := sorry

end AlgebraicGeometry
