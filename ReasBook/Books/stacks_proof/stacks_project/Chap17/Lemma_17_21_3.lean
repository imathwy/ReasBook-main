import Mathlib
import stacks_proof.stacks_project.Chap06.Definition_6_26_1
import stacks_proof.stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item are implemented directly here because the former owner wrapper
-- imported a broken module state.

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.21.3:
- primary domain: pullback of module sheaves on ringed spaces and the comparison maps for tensor,
  exterior, and symmetric algebra sheaf constructions;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `PresheafOfModules.sheafificationAdjunction`;
- best owner abstraction: the source-facing content is an isomorphism in `X.Modules`
  obtained from the canonical pullback/pushforward adjunction, while the pushforward comparison
  morphism is auxiliary implementation data;
- primitive data: the objectwise algebra presheaf and the induced morphism into the pushforward of
  the pulled-back algebra sheaf;
- derived API: the three pullback comparison isomorphisms.

Source/core/bridge triage:
- `source-facing`: the three isomorphisms asserting that pullback commutes with tensor, exterior,
  and symmetric algebra sheaves;
- `core/canonical`: `f^*`, `f _*`, and `SheafOfModules.pullbackPushforwardAdjunction`;
- `bridge/view`: the auxiliary pushforward-side comparison morphisms constructed before applying
  the adjunction.

The public API should therefore expose only the `≅` statements as the owner declarations and keep
the raw comparison morphisms private.
-/

/-- The objectwise tensor algebra module on an open set of a ringed space. -/
private abbrev tensorAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (TensorAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the tensor algebra presheaf. -/
private def tensorAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        TensorAlgebra.ι (X.presheaf.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · -- Restriction commutes with addition before applying the tensor-algebra generator map.
    intro m n
    rw [show (ℱ.val.map i).hom (m + n) =
        (show ℱ.val.obj V from (ℱ.val.map i).hom m) +
          (show ℱ.val.obj V from (ℱ.val.map i).hom n) by
      simpa using (ℱ.val.map i).hom.map_add m n]
    exact
      (TensorAlgebra.ι (X.presheaf.obj V)).map_add
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)
        (show ℱ.val.obj V from (ℱ.val.map i).hom n)
  · -- Restriction is semilinear with respect to the structure-sheaf restriction map.
    intro r m
    rw [show (ℱ.val.map i).hom (r • m) =
        (X.presheaf.map i).hom r • (show ℱ.val.obj V from (ℱ.val.map i).hom m) by
      simpa using (ℱ.val.map i).hom.map_smulₛₗ r m]
    exact
      (TensorAlgebra.ι (X.presheaf.obj V)).map_smul
        ((X.presheaf.map i).hom r)
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)

/-- The restriction map for the tensor algebra presheaf. -/
private noncomputable def tensorAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    tensorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (tensorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show tensorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (TensorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((TensorAlgebra.lift (X.presheaf.obj U)
          (tensorAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- Helper for Lemma 17.21.3: restricting sections along a composite equals iterated restriction
on each element. -/
private theorem sectionMapCompApply
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (m : ℱ.val.obj U) :
    (ℱ.val.map (i ≫ j)).hom m = (ℱ.val.map j).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: evaluate the presheaf composition law on the chosen section.
  simpa using congrArg (fun h => (ModuleCat.Hom.hom h) m) (ℱ.val.map_comp i j)

/-- Helper for Lemma 17.21.3: the inverse identity restriction-of-scalars transport is pointwise
the identity on module sections. -/
private theorem sectionMapIdTransportApply
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        ((ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
          (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
          (ℱ.val.obj U))) m = m := by
  -- Proof comment: the identity restriction-of-scalars isomorphism acts as the identity on each
  -- underlying section.
  simpa using
    (ModuleCat.restrictScalarsId'App_inv_apply (X.presheaf.map (𝟙 U)).hom
      (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U)) (ℱ.val.obj U) m)

/-- Helper for Lemma 17.21.3: the inverse composite restriction-of-scalars transport evaluates to
the expected iterated restriction on sections. -/
private theorem sectionMapCompTransportApply
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (m : ℱ.val.obj U) :
    (ModuleCat.Hom.hom
        (ℱ.val.map i ≫
          (ModuleCat.restrictScalars _).map (ℱ.val.map j) ≫
            (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
              (X.presheaf.map j).hom
              (X.presheaf.map (i ≫ j)).hom
              (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
              (ℱ.val.obj W))) m =
      (ℱ.val.map j).hom ((ℱ.val.map i).hom m) := by
  -- Proof comment: expand the restriction-of-scalars comparison and then apply the presheaf
  -- composition law on the chosen section.
  simpa [ModuleCat.restrictScalarsComp'App_inv_apply] using sectionMapCompApply ℱ i j m

/-- The tensor algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
-- Route correction: compare the two `ModuleCat` maps pointwise on tensor generators and avoid
-- non-definitional transport through the identity restriction-of-scalars isomorphism.
private theorem tensorAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    tensorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (tensorAlgebraPresheafObj ℱ U) := by
  -- Proof comment: after passing to underlying module maps, tensor-algebra induction reduces the
  -- coherence check to scalars, generators, addition, and multiplication.
  ext x
  refine TensorAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- The identity transport fixes scalar elements.
    intro r
    simp [tensorAlgebraPresheafMap]
  · -- On generators, the restriction map is just the identity section map transported back.
    intro m
    simp [tensorAlgebraPresheafMap, tensorAlgebraRestrictionLinear, sectionMapIdTransportApply]
  · -- Multiplicative compatibility propagates the pointwise equality through products.
    intro a b ha hb
    simp [ha, hb]
  · -- Additive compatibility propagates the pointwise equality through sums.
    intro a b ha hb
    simp [ha, hb]

/-- The tensor algebra restriction maps satisfy the composition axiom of a presheaf of modules. -/
-- Route correction: compare the direct and iterated `ModuleCat` maps pointwise on tensor
-- generators and avoid brittle algebra-hom transport through `restrictScalarsComp'`.
private theorem tensorAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    tensorAlgebraPresheafMap ℱ (i ≫ j) =
      tensorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (tensorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (tensorAlgebraPresheafObj ℱ W) := by
  -- Proof comment: compare the direct and iterated tensor-algebra restriction maps by induction
  -- on tensor expressions and use the transport-aware section-composition lemma on generators.
  ext x
  refine TensorAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- The composite restriction transport also fixes scalar elements.
    intro r
    simp [tensorAlgebraPresheafMap]
  · -- Generators are sent to the twice-restricted section on both sides.
    intro m
    simp [tensorAlgebraPresheafMap, tensorAlgebraRestrictionLinear, sectionMapCompTransportApply]
  · -- Multiplication is preserved by both tensor-algebra lifts.
    intro a b ha hb
    simp [ha, hb]
  · -- Addition is preserved by both tensor-algebra lifts.
    intro a b ha hb
    simp [ha, hb]

/-- The presheaf `U ↦ \mathrm{T}_{\mathcal O_X(U)}(\mathcal F(U))` whose sheafification is the
tensor algebra sheaf `T(ℱ)`. This bridge/view owner is reused by stalk and pullback comparisons. -/
noncomputable def tensorAlgebraPresheaf
    (ℱ : X.Modules) : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj := tensorAlgebraPresheafObj ℱ
  map := tensorAlgebraPresheafMap ℱ
  map_id := tensorAlgebraPresheaf_map_id ℱ
  map_comp := tensorAlgebraPresheaf_map_comp ℱ

/-- The tensor algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleTensorAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (tensorAlgebraPresheaf ℱ)

/-- The objectwise symmetric algebra module on an open set of a ringed space. -/
private abbrev symmetricAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (SymmetricAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the symmetric algebra presheaf. -/
private def symmetricAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        SymmetricAlgebra.ι (X.presheaf.obj V) (ℱ.val.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · -- Restriction commutes with addition before applying the symmetric generator map.
    intro m n
    rw [show (ℱ.val.map i).hom (m + n) =
        (show ℱ.val.obj V from (ℱ.val.map i).hom m) +
          (show ℱ.val.obj V from (ℱ.val.map i).hom n) by
      simpa using (ℱ.val.map i).hom.map_add m n]
    exact
      (SymmetricAlgebra.ι (X.presheaf.obj V) (ℱ.val.obj V)).map_add
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)
        (show ℱ.val.obj V from (ℱ.val.map i).hom n)
  · -- Restriction is semilinear with respect to the structure-sheaf restriction map.
    intro r m
    rw [show (ℱ.val.map i).hom (r • m) =
        (X.presheaf.map i).hom r • (show ℱ.val.obj V from (ℱ.val.map i).hom m) by
      simpa using (ℱ.val.map i).hom.map_smulₛₗ r m]
    exact
      (SymmetricAlgebra.ι (X.presheaf.obj V) (ℱ.val.obj V)).map_smul
        ((X.presheaf.map i).hom r)
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)

/-- The restriction map for the symmetric algebra presheaf. -/
private noncomputable def symmetricAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    symmetricAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (symmetricAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show symmetricAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (SymmetricAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((SymmetricAlgebra.lift (symmetricAlgebraRestrictionLinear ℱ i)).toLinearMap))

/-- The symmetric algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
-- Route correction: prove the identity coherence by comparing the induced symmetric-algebra
-- endomorphism with the identity on generators, then transport that equality to `ModuleCat`.
private theorem symmetricAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    symmetricAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (symmetricAlgebraPresheafObj ℱ U) := by
  -- Proof comment: symmetric-algebra induction reduces the identity coherence to the generator
  -- formula and the fact that the transport is pointwise trivial.
  ext x
  refine SymmetricAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- Scalar elements are unchanged by the identity transport.
    intro r
    simp [symmetricAlgebraPresheafMap]
  · -- On generators, both sides evaluate to the same restricted section.
    intro m
    simp [symmetricAlgebraPresheafMap, symmetricAlgebraRestrictionLinear,
      sectionMapIdTransportApply]
  · -- Multiplicative compatibility extends the equality from generators.
    intro a b ha hb
    simp [ha, hb]
  · -- Additive compatibility extends the equality from generators.
    intro a b ha hb
    simp [ha, hb]

/-- The symmetric algebra restriction maps satisfy the composition axiom of a presheaf of
modules. -/
-- Route correction: compare the direct and iterated symmetric-algebra lifts on generators and
-- then transport the algebra-morphism equality through `restrictScalarsComp'`.
private theorem symmetricAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    symmetricAlgebraPresheafMap ℱ (i ≫ j) =
      symmetricAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (symmetricAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (symmetricAlgebraPresheafObj ℱ W) := by
  -- Proof comment: the direct and iterated symmetric-algebra restrictions agree on generators,
  -- and symmetric-algebra induction propagates that equality to every section.
  ext x
  refine SymmetricAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- Scalars are fixed by the composite restriction-of-scalars comparison.
    intro r
    simp [symmetricAlgebraPresheafMap]
  · -- Generator sections restrict twice on the composite side and directly on the left.
    intro m
    simp [symmetricAlgebraPresheafMap, symmetricAlgebraRestrictionLinear,
      sectionMapCompTransportApply]
  · -- Multiplication is preserved by both symmetric-algebra lifts.
    intro a b ha hb
    simp [ha, hb]
  · -- Addition is preserved by both symmetric-algebra lifts.
    intro a b ha hb
    simp [ha, hb]

/-- The presheaf `U ↦ \operatorname{Sym}_{\mathcal O_X(U)}(\mathcal F(U))` whose sheafification is
the symmetric algebra sheaf `Symm(ℱ)`. This bridge/view owner is reused by stalk and pullback
comparisons. -/
noncomputable def symmetricAlgebraPresheaf
    (ℱ : X.Modules) : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj := symmetricAlgebraPresheafObj ℱ
  map := symmetricAlgebraPresheafMap ℱ
  map_id := symmetricAlgebraPresheaf_map_id ℱ
  map_comp := symmetricAlgebraPresheaf_map_comp ℱ

/-- The symmetric algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleSymmetricAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (symmetricAlgebraPresheaf ℱ)

/-- The objectwise exterior algebra module on an open set of a ringed space. -/
private abbrev exteriorAlgebraPresheafObj
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  ModuleCat.of (X.presheaf.obj U)
    (ExteriorAlgebra (X.presheaf.obj U) (ℱ.val.obj U))

/-- The linear map on sections induced by restriction for the exterior algebra presheaf. -/
private def exteriorAlgebraRestrictionLinear
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    let _ :
        Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
      Algebra.compHom
        (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
        (X.presheaf.map i).hom
    ℱ.val.obj U →ₗ[X.presheaf.obj U] ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V) := by
  let _ :
      Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  refine
    { toFun := fun m ↦
        ExteriorAlgebra.ι (X.presheaf.obj V)
          (show ℱ.val.obj V from (ℱ.val.map i).hom m)
      map_add' := ?_
      map_smul' := ?_ }
  · -- Restriction commutes with addition before applying the exterior generator map.
    intro m n
    rw [show (ℱ.val.map i).hom (m + n) =
        (show ℱ.val.obj V from (ℱ.val.map i).hom m) +
          (show ℱ.val.obj V from (ℱ.val.map i).hom n) by
      simpa using (ℱ.val.map i).hom.map_add m n]
    exact
      (ExteriorAlgebra.ι (X.presheaf.obj V)).map_add
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)
        (show ℱ.val.obj V from (ℱ.val.map i).hom n)
  · -- Restriction is semilinear with respect to the structure-sheaf restriction map.
    intro r m
    rw [show (ℱ.val.map i).hom (r • m) =
        (X.presheaf.map i).hom r • (show ℱ.val.obj V from (ℱ.val.map i).hom m) by
      simpa using (ℱ.val.map i).hom.map_smulₛₗ r m]
    exact
      (ExteriorAlgebra.ι (X.presheaf.obj V)).map_smul
        ((X.presheaf.map i).hom r)
        (show ℱ.val.obj V from (ℱ.val.map i).hom m)

/-- The exterior restriction map squares to zero on generators. -/
private theorem exteriorAlgebraRestrictionLinear_sq_zero
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    ∀ m : ℱ.val.obj U,
      exteriorAlgebraRestrictionLinear ℱ i m *
        exteriorAlgebraRestrictionLinear ℱ i m = 0 := by
  -- Exterior generators square to zero after restricting sections.
  intro m
  simpa [exteriorAlgebraRestrictionLinear] using
    (ExteriorAlgebra.ι_sq_zero (show ℱ.val.obj V from (ℱ.val.map i).hom m))

/-- The restriction map for the exterior algebra presheaf. -/
private noncomputable def exteriorAlgebraPresheafMap
    (ℱ : X.Modules) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    exteriorAlgebraPresheafObj ℱ U ⟶
      (ModuleCat.restrictScalars (X.presheaf.map i).hom).obj
        (exteriorAlgebraPresheafObj ℱ V) := by
  let _ :
      Algebra (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) :=
    Algebra.compHom
      (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V))
      (X.presheaf.map i).hom
  exact
    (show exteriorAlgebraPresheafObj ℱ U ⟶
        ModuleCat.of (X.presheaf.obj U) (ExteriorAlgebra (X.presheaf.obj V) (ℱ.val.obj V)) from
      ModuleCat.ofHom
        ((ExteriorAlgebra.lift (X.presheaf.obj U)
          ⟨exteriorAlgebraRestrictionLinear ℱ i,
            exteriorAlgebraRestrictionLinear_sq_zero ℱ i⟩).toLinearMap))

/-- The exterior algebra restriction maps satisfy the identity axiom of a presheaf of modules. -/
-- Route correction: prove the identity coherence by comparing the induced exterior-algebra
-- endomorphism with the identity on generators, then transport that equality to `ModuleCat`.
private theorem exteriorAlgebraPresheaf_map_id
    (ℱ : X.Modules) (U : (Opens X)ᵒᵖ) :
    exteriorAlgebraPresheafMap ℱ (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.presheaf.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (X.presheaf.map_id U))).inv.app
        (exteriorAlgebraPresheafObj ℱ U) := by
  -- Proof comment: exterior-algebra induction reduces the identity coherence to scalar and
  -- generator computations, with the transport helper handling the only wrapper mismatch.
  ext x
  refine ExteriorAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- The identity restriction transport fixes scalar elements.
    intro r
    simp [exteriorAlgebraPresheafMap]
  · -- On generators, the restriction map is the identity section map after transport.
    intro m
    simp [exteriorAlgebraPresheafMap, exteriorAlgebraRestrictionLinear,
      sectionMapIdTransportApply]
  · -- Multiplicativity extends the equality from generators to wedge products.
    intro a b ha hb
    simp [ha, hb]
  · -- Additivity extends the equality from generators to sums.
    intro a b ha hb
    simp [ha, hb]

/-- The exterior algebra restriction maps satisfy the composition axiom of a presheaf of
modules. -/
-- Route correction: compare the direct and iterated exterior-algebra lifts on generators and
-- then transport the algebra-morphism equality through `restrictScalarsComp'`.
private theorem exteriorAlgebraPresheaf_map_comp
    (ℱ : X.Modules) {U V W : (Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    exteriorAlgebraPresheafMap ℱ (i ≫ j) =
      exteriorAlgebraPresheafMap ℱ i ≫
        (ModuleCat.restrictScalars _).map (exteriorAlgebraPresheafMap ℱ j) ≫
          (ModuleCat.restrictScalarsComp' (X.presheaf.map i).hom
            (X.presheaf.map j).hom
            (X.presheaf.map (i ≫ j)).hom
            (congrArg CommRingCat.Hom.hom <| X.presheaf.map_comp i j)).inv.app
            (exteriorAlgebraPresheafObj ℱ W) := by
  -- Proof comment: the direct and iterated exterior-algebra restrictions agree on generators,
  -- and exterior-algebra induction propagates that comparison through the algebra structure.
  ext x
  refine ExteriorAlgebra.induction ?_ ?_ ?_ ?_ x
  · -- Scalars are fixed by the composite restriction-of-scalars comparison.
    intro r
    simp [exteriorAlgebraPresheafMap]
  · -- Generator sections match after using the pointwise composite transport formula.
    intro m
    simp [exteriorAlgebraPresheafMap, exteriorAlgebraRestrictionLinear,
      sectionMapCompTransportApply]
  · -- Multiplication is preserved by both exterior-algebra lifts.
    intro a b ha hb
    simp [ha, hb]
  · -- Addition is preserved by both exterior-algebra lifts.
    intro a b ha hb
    simp [ha, hb]

/-- The presheaf `U ↦ \bigwedge_{\mathcal O_X(U)} \mathcal F(U)` whose sheafification is the
exterior algebra sheaf `Λ(ℱ)`. This is the bridge/view owner used to construct morphisms on
`Λ(ℱ)` by sheafifying natural transformations on sections. -/
noncomputable def exteriorAlgebraPresheaf
    (ℱ : X.Modules) : PresheafOfModules.{u} X.ringCatSheaf.obj where
  obj := exteriorAlgebraPresheafObj ℱ
  map := exteriorAlgebraPresheafMap ℱ
  map_id := exteriorAlgebraPresheaf_map_id ℱ
  map_comp := exteriorAlgebraPresheaf_map_comp ℱ

/-- The exterior algebra sheaf associated to an `\mathcal O_X`-module. -/
noncomputable abbrev moduleExteriorAlgebra
    (ℱ : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (exteriorAlgebraPresheaf ℱ)

end AlgebraicGeometry.RingedSpace

scoped[AlgebraicGeometry] notation3:max "T(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleTensorAlgebra ℱ
scoped[AlgebraicGeometry] notation3:max "Λ(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleExteriorAlgebra ℱ
scoped[AlgebraicGeometry] notation3:max "Symm(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.moduleSymmetricAlgebra ℱ
