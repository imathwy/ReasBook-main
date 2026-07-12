import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits
open IsLocalRing
open Scheme.Pullback

universe u

namespace AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.17.5:
- `source-facing`: points of `X ×_S Y` together with the residue-field prime lying over the common
  image in `S`;
- `core/canonical`: `Scheme.Pullback.carrierEquiv` for part (1), and the canonical morphism
  `Scheme.Pullback.ofPointTensor_SpecTensorTo` for the factorization in part (2);
- `bridge/view`: the residue-field comparison map attached to `Scheme.Pullback.SpecOfPoint z`. -/

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Pullback.Triplet.ofPoint`,
-- `Scheme.Pullback.SpecOfPoint`, and `Scheme.Pullback.SpecTensorTo_SpecOfPoint` as the canonical
-- owner/API for points of a scheme pullback and the corresponding prime of the tensor product of
-- residue fields.

variable {X Y S : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S)

/- Lemma 26.17.5 (1): for morphisms `f : X ⟶ S` and `g : Y ⟶ S`, points of the fiber product
`X ×_S Y` are in bijective correspondence with quadruples `(x, y, s, 𝔭)` where
`x : X`, `y : Y`, and `s : S` satisfy `f x = s` and `g y = s`, and `𝔭` is a prime ideal of
`κ(x) ⊗[κ(s)] κ(y)`. The canonical owner is the imported equivalence
`Scheme.Pullback.carrierEquiv`, which packages the quadruple as
`Scheme.Pullback.Triplet f g` together with a prime of its tensor product ring `T.tensor`.
-/
#check (Scheme.Pullback.carrierEquiv :
  (pullback f g : Scheme) ≃ Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor)

/-- Lemma 26.17.5 (2), canonical factorization form: the map from `Spec κ(z)` to the affine
scheme `Spec (κ(x) ⊗[κ(s)] κ(y))` defined by `ofPointTensor z` lands over `z` under the canonical
map from that affine scheme to `X ×_S Y`. This is the source-facing bridge behind the associated
prime `Scheme.Pullback.SpecOfPoint z`. -/
@[stacks 01JT]
theorem pullbackPoint_specOfPoint_factorization
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    CommSq
      (Spec.map (ofPointTensor z))
      ((pullback f g : Scheme).fromSpecResidueField z)
      (Triplet.ofPoint z).SpecTensorTo
      (𝟙 _) := by
  refine CommSq.mk ?_
  simpa using Scheme.Pullback.ofPointTensor_SpecTensorTo z

/-- The prime `Scheme.Pullback.SpecOfPoint z` is the image of the closed point of `Spec κ(z)` under
the affine map induced by `Scheme.Pullback.ofPointTensor z`. -/
private lemma pullbackPoint_specOfPoint_eq_image_closedPoint
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    SpecOfPoint z =
      Spec.map (ofPointTensor z) (closedPoint ((pullback f g : Scheme).residueField z)) := by
  change
    Spec.map (ofPointTensor z) (⊥ : PrimeSpectrum ((pullback f g : Scheme).residueField z)) =
      Spec.map (ofPointTensor z) (closedPoint ((pullback f g : Scheme).residueField z))
  congr
  exact Subsingleton.elim _ _

/-- Lemma 26.17.5 (2), canonical comparison map at the scheme-residue-field level: the residue
field of the point `Scheme.Pullback.SpecOfPoint z` of the affine scheme
`Spec (κ(x) ⊗[κ(s)] κ(y))` maps to the residue field `κ(z)` of the pullback point `z`. -/
@[stacks 01JT]
noncomputable def pullbackPoint_specOfPoint_residueFieldMap
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    (Spec (Triplet.ofPoint z).tensor).residueField (SpecOfPoint z) →+*
      (pullback f g : Scheme).residueField z :=
  let inst : IsLocalHom (Scheme.stalkClosedPointTo (Spec.map (ofPointTensor z))).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (Spec.map (ofPointTensor z))
  ((@Scheme.descResidueField
      ((pullback f g : Scheme).residueField z)
      inferInstance
      (Spec (Triplet.ofPoint z).tensor)
      (Spec.map (ofPointTensor z) (closedPoint ((pullback f g : Scheme).residueField z)))
      (Scheme.stalkClosedPointTo (Spec.map (ofPointTensor z)))
      inst).hom).comp
    ((Scheme.residueFieldCongr (pullbackPoint_specOfPoint_eq_image_closedPoint f g z)).hom).hom

/-- Lemma 26.17.5 (2), source-facing comparison map: the residue field of the prime ideal
`Scheme.Pullback.SpecOfPoint z` maps to the residue field `κ(z)` of the pullback point `z`, via
the canonical affine-scheme identification `Scheme.Spec.residueFieldIso`. -/
@[stacks 01JT]
noncomputable def pullbackPoint_associatedPrime_residueFieldMap
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    (SpecOfPoint z).asIdeal.ResidueField →+* (pullback f g : Scheme).residueField z :=
  (pullbackPoint_specOfPoint_residueFieldMap f g z).comp
    (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).inv.hom

/-- Companion factorization theorem for the scheme-residue-field comparison map attached to
`Scheme.Pullback.SpecOfPoint z`. -/
theorem pullbackPoint_specOfPoint_residueFieldMap_spec
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    CommSq
      (Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)))
      (Spec.map (ofPointTensor z))
      ((Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z))
      (𝟙 _) := by
  refine CommSq.mk ?_
  simpa [pullbackPoint_specOfPoint_residueFieldMap,
    pullbackPoint_specOfPoint_eq_image_closedPoint]
    using
      (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
        ((pullback f g : Scheme).residueField z)
        (Spec (Triplet.ofPoint z).tensor)
        (Spec.map (ofPointTensor z)))

/-- Lemma 26.17.5 (2): if `z` corresponds to the prime
`Scheme.Pullback.SpecOfPoint z` of `κ(x) ⊗[κ(s)] κ(y)`, then the canonical map from the residue
field of that prime ideal to the residue field `κ(z)` recovers `Spec.map (ofPointTensor z)` after
passing to `Spec` and the canonical bridge `Scheme.Spec.residueFieldIso`. -/
@[stacks 01JT]
theorem pullbackPoint_associatedPrime_residueFieldMap_spec
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme)) :
    CommSq
      (Spec.map (CommRingCat.ofHom (pullbackPoint_associatedPrime_residueFieldMap f g z)))
      (Spec.map (ofPointTensor z))
      (Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom ≫
        (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z))
      (𝟙 _) := by
  refine CommSq.mk ?_
  calc
    Spec.map (CommRingCat.ofHom (pullbackPoint_associatedPrime_residueFieldMap f g z)) ≫
        (Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom ≫
          (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z))
      = Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)) ≫
          Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).inv ≫
            Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom ≫
              (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z) := by
                simp [pullbackPoint_associatedPrime_residueFieldMap, Category.assoc, Spec.map_comp]
    _ = Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)) ≫
          (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z) := by
            have hresidueFieldIso :
                Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).inv ≫
                  Spec.map
                    (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom =
                  𝟙 _ := by
              rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
            calc
              Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)) ≫
                  Spec.map
                    (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).inv ≫
                    Spec.map
                      (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom ≫
                      (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z)
                =
                  Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)) ≫
                    (Spec.map
                      (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).inv ≫
                        Spec.map
                          (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom) ≫
                      (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z) := by
                        simp [Category.assoc]
              _ = Spec.map (CommRingCat.ofHom (pullbackPoint_specOfPoint_residueFieldMap f g z)) ≫
                    (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z) := by
                      simp [hresidueFieldIso]
    _ = Spec.map (ofPointTensor z) := (pullbackPoint_specOfPoint_residueFieldMap_spec f g z).w

end AlgebraicGeometry
