import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_32_1 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Source/core/bridge triage for Definition 7.32.1:
- source-facing notion: a point of the topos `Sh(C)`, i.e.
  `MorphismOfTopoiIn J typesGrothendieckTopology`
- core/canonical owner: the source-facing owner
  `MorphismOfTopoiIn J typesGrothendieckTopology`, viewed internally as the specialization
  `LeftExactAdjunction (Sheaf typesGrothendieckTopology (Type w)) (Sheaf J (Type w))`, of which
  `MorphismOfTopoiIn J typesGrothendieckTopology` is the site-presented specialization already
  chosen upstream in Chapter 7
- bridge/view: the canonical equivalence `typeEquiv` identifies sheaves on the terminal site of
  sets with `Type`, so the inverse and direct image functors of a topos point may be viewed as
  the `Type`-valued functors `p.typeInverseImage` and `p.typePushforward`
- primitive data: the inverse-image functor `p⁻¹`, the direct-image functor `p _*`, and their
  adjunction, already packaged by `MorphismOfTopoiIn`
- derived API: the bridge functors `p.typeInverseImage`, `p.typePushforward`, the `Type`-valued
  adjunction `p.typeAdjunction`, and the right-adjoint instance on `p.typePushforward`
-/
/- Definition 7.32.1: a point of the topos `Sh(C)` is a morphism from the terminal topos,
identified canonically with `Sh(typesGrothendieckTopology)`, to `Sh(C)`. -/
#check (MorphismOfTopoiIn J typesGrothendieckTopology.{w})

variable {J}

namespace MorphismOfTopoiIn

/-- The inverse-image functor of a topos point, viewed as a `Type`-valued functor via
`typeEquiv`. -/
abbrev typeInverseImage (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Sheaf J (Type w) ⥤ Type w :=
  p⁻¹ ⋙ typeEquiv.{w}.inverse

/-- The direct-image functor of a topos point, viewed as a functor out of `Type` via
`typeEquiv`. -/
abbrev typePushforward (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    Type w ⥤ Sheaf J (Type w) :=
  typeEquiv.{w}.functor ⋙ (p _*)

/-- The `Type`-valued inverse and direct images of a topos point form the adjunction obtained by
transporting `p.adjunction` across `typeEquiv`. -/
abbrev typeAdjunction (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typeInverseImage ⊣ p.typePushforward :=
  p.adjunction.comp typeEquiv.{w}.symm.toAdjunction

instance (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    (p.typePushforward).IsRightAdjoint :=
  p.typeAdjunction.isRightAdjoint

end MorphismOfTopoiIn

end CategoryTheory

/-! ### Definition_7_32_2 (from Chap07) -/
universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Domain-style sampling and source/core/bridge triage for Definition 7.32.2:
- primary domain: points of Grothendieck sites and their associated stalk/fiber functors;
- sampled owner API:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.toToposPoint`;
- source-facing notion: a point of the site `(C, J)`;
- core/canonical owner: `GrothendieckTopology.Point`, instantiated at the topology `J` as `J.Point`;
- bridge/view: the textbook clauses are the owner fields, while the associated presheaf and sheaf
  fiber functors and the induced topos point are downstream derived API.

Primitive data are the fields `fiber`, `isCofiltered`, `initiallySmall`, and
`jointly_surjective`. The functors `presheafFiber` and `sheafFiber`, together with their
exactness/comparison lemmas, are derived from that owner abstraction and should not be repackaged
locally.
-/
/- Definition 7.32.2: a point of the site `(C, J)` is the canonical mathlib owner `J.Point`.
This owner already packages exactly the textbook fiber functor, cofiltered-neighborhood, and
covering-surjectivity data. -/
#check J.Point

end CategoryTheory

/-! ### Lemma_7_32_3 (from Chap07) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable (Φ : GrothendieckTopology.Point.{v} J)

/- Source/core/bridge triage for Lemma 7.32.3:
- primary domain: point fibers of representable presheaves on a site;
- sampled owner API:
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.fiber`,
  `GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso`,
  `shrinkYonedaIsoYoneda`;
- source-facing statement: `yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber`
- core/canonical owner: `Φ.shrinkYonedaCompPresheafFiberIso`
- bridge/view: transport along `shrinkYonedaIsoYoneda`
- primitive data: the point `Φ`, its functor `Φ.fiber`, and the derived functor
  `Φ.presheafFiber`;
- derived API kept here: only the change-of-owner comparison from `shrinkYoneda` to `yoneda`.
-/
/- Lemma 7.32.3: the point fiber of the representable presheaf `h_U` is functorially
isomorphic to the fiber value `Φ(U)`. This is the canonical point comparison
`Φ.shrinkYonedaCompPresheafFiberIso`, rewritten from `shrinkYoneda` to `yoneda` via
`shrinkYonedaIsoYoneda`. -/
#check
  ((Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm Φ.presheafFiber) ≪≫
    Φ.shrinkYonedaCompPresheafFiberIso :
      CategoryTheory.yoneda ⋙ Φ.presheafFiber ≅ Φ.fiber)

end GrothendieckTopology.Point

end CategoryTheory

/-! ### Lemma_7_32_4 (from Chap07) -/
open CategoryTheory Limits Opposite

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Functor
open scoped PresheafCostalk

/-- The value of `u^p E` at `X` is the set of maps from `u.obj X` to `E`. -/
theorem presheafCostalk_obj_obj (u : C ⥤ Type w) (E : Type w) (X : C) :
    ((u^p).obj E).obj (op X) = (u.obj X → E) :=
  rfl

section

variable (u : C ⥤ Type w)
variable [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/-- The hom-set bijection underlying the adjunction between the presheaf fiber functor of `u` and
the costalk functor `u^p`. -/
private noncomputable def presheafCostalkHomEquiv (F : Cᵒᵖ ⥤ Type w) (E : Type w) :
    (u.presheafFiber.obj F ⟶ E) ≃ (F ⟶ (u^p).obj E) where
  toFun f :=
    { app := fun X s x ↦ f (u.toPresheafFiber X.unop x F s)
      naturality := by
        intro X Y g
        ext s
        funext x
        have h : u.toPresheafFiber Y.unop x F ((F.map g) s) =
            u.toPresheafFiber X.unop (u.map g.unop x) F s := by
          simpa using congr_fun (u.toPresheafFiber_w g.unop x) s
        exact congrArg f h }
  invFun g :=
    u.presheafFiberDesc
      (fun X x s ↦ g.app (op X) s x)
      (fun {Y Z} α y ↦ by
        ext s
        exact congr_fun (congr_fun (g.naturality α.op) s) y)
  left_inv f := by
    apply u.presheafFiber_hom_ext
    intro X x
    change u.toPresheafFiber X x F ≫
        u.presheafFiberDesc (fun X x s ↦ f (u.toPresheafFiber X x F s))
          (fun {Y Z} α y ↦ by
            ext s
            exact congrArg f (congr_fun (u.toPresheafFiber_w α y) s)) =
      u.toPresheafFiber X x F ≫ f
    exact u.toPresheafFiber_presheafFiberDesc _ _ X x
  right_inv g := by
    ext X s
    funext x
    change (u.toPresheafFiber X.unop x F ≫
        u.presheafFiberDesc (fun X x s ↦ g.app (op X) s x)
          (fun {Y Z} α y ↦ by
            ext s
            exact congr_fun (congr_fun (g.naturality α.op) s) y)) s = _
    simpa using congr_fun (u.toPresheafFiber_presheafFiberDesc _ _ X.unop x) s

/-- Evaluating the inverse hom-equivalence on a generator of the presheaf fiber recovers the
corresponding component of the given presheaf map. -/
private lemma toPresheafFiber_presheafCostalkHomEquiv_symm {F : Cᵒᵖ ⥤ Type w} {E : Type w}
    (g : F ⟶ (u^p).obj E) (X : C) (x : u.obj X) :
    u.toPresheafFiber X x F ≫ (presheafCostalkHomEquiv u F E).symm g =
      fun s ↦ g.app (op X) s x := by
  change u.toPresheafFiber X x F ≫
      u.presheafFiberDesc (fun X x s ↦ g.app (op X) s x)
        (fun {Y Z} α y ↦ by
          ext s
          exact congr_fun (congr_fun (g.naturality α.op) s) y) = _
  exact u.toPresheafFiber_presheafFiberDesc _ _ X x

/-- Naturality on the presheaf argument for the inverse of the hom-equivalence defining the
adjunction `presheafFiber u ⊣ u^p`. -/
private lemma presheafCostalkHomEquiv_naturality_left_symm {F G : Cᵒᵖ ⥤ Type w} {E : Type w}
    (f : F ⟶ G) (g : G ⟶ (u^p).obj E) :
    (presheafCostalkHomEquiv u F E).symm (f ≫ g) =
      u.presheafFiber.map f ≫ (presheafCostalkHomEquiv u G E).symm g := by
  apply u.presheafFiber_hom_ext
  intro X x
  rw [← Category.assoc, u.toPresheafFiber_naturality]
  ext s
  have h₁ := congr_fun
    (toPresheafFiber_presheafCostalkHomEquiv_symm u (f ≫ g) X x) s
  have h₂ := congr_fun
    (toPresheafFiber_presheafCostalkHomEquiv_symm u g X x)
    (f.app (op X) s)
  simpa [NatTrans.comp_app] using h₁.trans h₂.symm

/-- Naturality on the target set for the hom-equivalence defining `presheafFiber u ⊣ u^p`. -/
private lemma presheafCostalkHomEquiv_naturality_right {F : Cᵒᵖ ⥤ Type w} {E E' : Type w}
    (f : u.presheafFiber.obj F ⟶ E) (g : E ⟶ E') :
    presheafCostalkHomEquiv u F E' (f ≫ g) =
      presheafCostalkHomEquiv u F E f ≫ (u^p).map g := by
  ext X s
  funext x
  rfl

/-- Lemma 7.32.4: for any functor `u : C ⥤ Type`, the costalk functor `u^p` is right adjoint to
the presheaf fiber functor of `u`. -/
noncomputable def presheafCostalkAdjunction :
    u.presheafFiber ⊣ u^p :=
  Adjunction.mkOfHomEquiv
    { homEquiv := presheafCostalkHomEquiv u
      homEquiv_naturality_left_symm := presheafCostalkHomEquiv_naturality_left_symm u
      homEquiv_naturality_right := presheafCostalkHomEquiv_naturality_right u }

/-- The adjunction `presheafCostalkAdjunction u` induces the expected bijection on Hom-sets. -/
-- Proof sketch: use the generic fact that the Hom-equivalence of any adjunction is bijective.
theorem presheafCostalkAdjunction_homEquiv_bijective (F : Cᵒᵖ ⥤ Type w) (E : Type w) :
    Function.Bijective ((presheafCostalkAdjunction u).homEquiv F E) := by
  -- The adjunction already packages the source proof as an equivalence of Hom-sets.
  exact ((presheafCostalkAdjunction u).homEquiv F E).bijective

/-- Lemma 7.32.4 in `IsRightAdjoint` form: once the presheaf fiber of `u` is available as the
canonical colimit over `u.Elementsᵒᵖ`, the functor `u^p` is a right adjoint. -/
instance presheafCostalk_isRightAdjoint :
    (u^p).IsRightAdjoint :=
  (presheafCostalkAdjunction u).isRightAdjoint

end

end CategoryTheory

/-! ### Lemma_7_32_5 (from Chap07) -/
open CategoryTheory

universe u v w

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.5:
- primary domain: points of Grothendieck sites, their fiber functors, and the associated
  skyscraper sheaf construction;
- sampled owner API:
  `GrothendieckTopology.Point.skyscraperPresheaf`,
  `GrothendieckTopology.Point.isSheaf_skyscraperPresheaf`,
  `GrothendieckTopology.Point.skyscraperSheafAdjunction`,
  `GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`;
- primitive data: only the point `Φ : Point.{w} J`;
- derived API: the sheaf condition for `Φ.skyscraperPresheaf E`, the adjunction
  `Φ.sheafFiber ⊣ Φ.skyscraperSheafFunctor`, and the sheafification/fiber comparison isomorphism.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 7.32.5;
- `core/canonical`: the owner namespace `GrothendieckTopology.Point`;
- `bridge/view`: the set-valued specialization `A := Type w`.

The source statements already coincide with canonical owner-level declarations in mathlib, so this
file should remain a direct recall of those declarations rather than introducing any parallel local
wrapper API.
-/

variable (Φ : Point.{w} J) (E : Type w)

/- Lemma 7.32.5 (1): for a point `p` of the site `(C, J)` and a set `E`, the canonical
skyscraper presheaf `p^p E`, given by `X ↦ (p.fiber.obj X → E)`, is a sheaf. In mathlib this is
the canonical point API `Φ.isSheaf_skyscraperPresheaf E`. -/
#check
  (Φ.isSheaf_skyscraperPresheaf E :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf E))

/- Lemma 7.32.5 (2): the stalk functor on sheaves attached to a point is left adjoint to the
canonical skyscraper-sheaf functor; this is `Φ.skyscraperSheafAdjunction`. -/
#check
  (Φ.skyscraperSheafAdjunction :
    (Φ.sheafFiber : Sheaf J (Type w) ⥤ Type w) ⊣ Φ.skyscraperSheafFunctor)

variable [HasWeakSheafify J (Type w)]

/- Lemma 7.32.5 (3): the point fiber functor on presheaves identifies canonically with the point
fiber functor on associated sheaves; this is `Φ.presheafToSheafCompSheafFiberIso`. -/
#check
  (Φ.presheafToSheafCompSheafFiberIso (Type w) :
    presheafToSheaf J (Type w) ⋙ (Φ.sheafFiber : Sheaf J (Type w) ⥤ Type w) ≅
      Φ.presheafFiber)

end CategoryTheory

/-! ### Definition_7_32_6 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v w u' v'

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Definition 7.32.6:
- primary domain: skyscraper sheaves attached to points of a site;
- sampled owner declarations:
  `Point.skyscraperPresheaf`,
  `Point.skyscraperSheafFunctor`,
  `Point.skyscraperSheaf`,
  `Point.toToposPoint_pointPushforwardIso`;
- source/core/bridge triage:
  `source-facing`: the direct-image functor `p_*` of a site point and its objectwise set-valued
    description;
  `core/canonical`: `Point.skyscraperSheafFunctor`;
  `bridge/view`: the owner-level presheaf view `Φ.skyscraperPresheaf E`, the canonical
    `Type`-level product comparison `Types.productIso`, and later in the chapter the comparison
    `Point.toToposPoint_pointPushforwardIso` to the direct image of the induced topos point.

The primitive data are only the point `Φ` and the target object `E`. The objectwise identification
with maps `Φ.fiber.obj X → E` is derived API of the owner `Φ.skyscraperSheafFunctor`, best exposed
through the canonical view `Φ.skyscraperPresheaf E` rather than a parallel local wrapper or a
low-level underlying-sheaf expression.
-/

/- Definition 7.32.6: for a point `p` of the site `(C, J)`, the direct-image/skyscraper functor
`p_*` is the canonical mathlib functor `Point.skyscraperSheafFunctor`.
For sets, `Φ.skyscraperSheaf E` is the sheaf denoted `u^s E` in the Stacks Project. -/
recall Point.skyscraperSheafFunctor
  {C : Type u} [Category.{v, u} C] {J : GrothendieckTopology C}
  (Φ : J.Point) {A : Type u'} [Category.{v', u'} A] [HasProducts A] :
  A ⥤ Sheaf J A

variable (Φ : Point.{w} J) (E : Type w) (X : C)

/- For sets, the owner-level presheaf view `Φ.skyscraperPresheaf E` evaluates at `X` to the
product of copies of `E` indexed by `Φ.fiber.obj X`, so in `Type` it is canonically equivalent to
the set of maps `Φ.fiber.obj X → E` via `Types.productIso`. -/
#check
  (((Types.productIso (fun _ : Φ.fiber.obj X ↦ E)).toEquiv) :
    (Φ.skyscraperPresheaf E).obj (op X) ≃ (Φ.fiber.obj X → E))

end CategoryTheory

/-! ### Lemma_7_32_7 (from Chap07) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite Functor

universe u v w

noncomputable section

namespace CategoryTheory

open scoped MorphismOfTopoiIn
open scoped GrothendieckTopology.SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- A point of the site `(C, J)` canonically defines a point of the topos `Sh(C)`. -/
noncomputable def toToposPoint
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    MorphismOfTopoiIn J typesGrothendieckTopology.{w} where
  inverseImageFunctor :=
    let _ : PreservesFiniteLimits (p.sheafFiber ⋙ typeEquiv.{w}.functor) := inferInstance
    LeftExactFunctor.of (p.sheafFiber ⋙ typeEquiv.{w}.functor)
  pushforward := typeEquiv.{w}.inverse ⋙ p.skyscraperSheafFunctor
  adjunction := p.skyscraperSheafAdjunction.comp typeEquiv.{w}.toAdjunction

/-- The `Type`-valued inverse-image functor of the point induced by a site point recovers the
usual stalk functor. -/
noncomputable def toToposPoint_pointInverseImageIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typeInverseImage ≅ p.sheafFiber :=
  (Functor.associator p.sheafFiber typeEquiv.{w}.functor typeEquiv.{w}.inverse).symm ≪≫
    (Functor.isoWhiskerLeft p.sheafFiber typeEquiv.{w}.unitIso.symm) ≪≫
      Functor.rightUnitor p.sheafFiber

/-- The `Type`-valued direct-image functor of the point induced by a site point recovers the
usual skyscraper functor. -/
noncomputable def toToposPoint_pointPushforwardIso
    [LocallySmall.{w} C]
    (p : Point.{w} J) :
    p.toToposPoint.typePushforward ≅ p.skyscraperSheafFunctor :=
  (Functor.associator typeEquiv.{w}.functor typeEquiv.{w}.inverse p.skyscraperSheafFunctor).symm ≪≫
    (Functor.isoWhiskerRight typeEquiv.{w}.unitIso.symm p.skyscraperSheafFunctor) ≪≫
      Functor.leftUnitor p.skyscraperSheafFunctor

/-- The canonical point of the jointly surjective site on `Type`. -/
noncomputable def typesPoint : Point.{w} typesGrothendieckTopology.{w} where
  fiber := 𝟭 (Type w)
  jointly_surjective {X} R hR x :=
    ⟨PUnit, fun _ ↦ x, hR x, PUnit.unit, rfl⟩

private noncomputable abbrev typesPointBaseObj : typesPoint.fiber.Elements :=
  typesPoint.fiber.elementsMk PUnit PUnit.unit

private instance (Y : typesPoint.fiber.Elements) : Unique (typesPointBaseObj ⟶ Y) := by
  let g : typesPointBaseObj ⟶ Y := ⟨fun _ ↦ Y.2, rfl⟩
  refine { default := g, uniq := ?_ }
  intro f
  apply CategoryOfElements.ext typesPoint.fiber f g
  funext u
  cases u
  simpa [g] using f.2

private noncomputable def typesPointInitial : IsInitial typesPointBaseObj :=
  IsInitial.ofUnique _

private noncomputable abbrev typesPointTerminalObj : typesPoint.fiber.Elementsᵒᵖ :=
  op typesPointBaseObj

private noncomputable def typesPointTerminal : IsTerminal typesPointTerminalObj :=
  terminalOpOfInitial typesPointInitial

private noncomputable def typesPointPresheafFiberObjIso (P : Type wᵒᵖ ⥤ Type w) :
    typesPoint.presheafFiber.obj P ≅ P.obj (op PUnit) := by
  let Q := (CategoryOfElements.π typesPoint.fiber).op ⋙ P
  change colimit Q ≅ Q.obj typesPointTerminalObj
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal typesPointTerminal Q)

private lemma toPresheafFiber_typesPointPresheafFiberObjIso_hom
    (P : Type wᵒᵖ ⥤ Type w) (X : Type w) (x : X) :
    typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom =
      P.map (show PUnit ⟶ X from fun _ ↦ x).op := by
  simpa [typesPointPresheafFiberObjIso, GrothendieckTopology.Point.presheafFiber,
    typesPointTerminalObj, typesPointTerminal] using
    (colimit.comp_coconePointUniqueUpToIso_hom
      (hc := colimitOfDiagramTerminal typesPointTerminal
        ((CategoryOfElements.π typesPoint.fiber).op ⋙ P))
      (op (typesPoint.fiber.elementsMk X x)))

private noncomputable def typesPointPresheafFiberIso :
    typesPoint.presheafFiber ≅ (evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit) := by
  refine NatIso.ofComponents (fun P ↦ typesPointPresheafFiberObjIso P) ?_
  intro P Q f
  apply typesPoint.presheafFiber_hom_ext
  intro X x
  rw [toPresheafFiber_naturality_assoc]
  calc
    (f.app (op X) ≫ typesPoint.toPresheafFiber X x Q) ≫ (typesPointPresheafFiberObjIso Q).hom =
        f.app (op X) ≫
          (typesPoint.toPresheafFiber X x Q ≫ (typesPointPresheafFiberObjIso Q).hom) := by
            simp [Category.assoc]
    _ = f.app (op X) ≫ Q.map (show PUnit ⟶ X from fun _ ↦ x).op := by
      rw [toPresheafFiber_typesPointPresheafFiberObjIso_hom]
    _ = P.map (show PUnit ⟶ X from fun _ ↦ x).op ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa using
              (NatTrans.naturality f
                (show op X ⟶ op PUnit from (show PUnit ⟶ X from fun _ ↦ x).op)).symm
    _ = typesPoint.toPresheafFiber X x P ≫ (typesPointPresheafFiberObjIso P).hom ≫
          ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦
                  k ≫ ((evaluation (Type wᵒᵖ) (Type w)).obj (op PUnit)).map f)
                (toPresheafFiber_typesPointPresheafFiberObjIso_hom P X x).symm

/-- The sheaf fiber of the canonical point on the jointly surjective site of types is evaluation
at `PUnit`, i.e. `typeEquiv.inverse`. -/
noncomputable def typesPointSheafFiberIso :
    typesPoint.sheafFiber ≅ typeEquiv.{w}.inverse := by
  simpa [GrothendieckTopology.Point.sheafFiber] using
    Functor.isoWhiskerLeft (sheafToPresheaf typesGrothendieckTopology (Type w))
      typesPointPresheafFiberIso

/-- The skyscraper functor of the canonical point on the jointly surjective site of types is the
canonical equivalence `typeEquiv.functor`. -/
noncomputable def typesPointSkyscraperSheafFunctorIso :
    typeEquiv.{w}.functor ≅ typesPoint.skyscraperSheafFunctor :=
  (conjugateIsoEquiv typeEquiv.{w}.symm.toAdjunction typesPoint.skyscraperSheafAdjunction)
    typesPointSheafFiberIso

/-- Comapping the canonical point of the jointly surjective site of types along the fiber functor
of a site point recovers the original point. -/
theorem typesPoint_comap_eq
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    (p : Point.{w} K)
    [RepresentablyFlat p.fiber]
    (hcover : CoverPreserving K typesGrothendieckTopology p.fiber)
    [InitiallySmall (p.fiber ⋙ typesPoint.fiber).Elements] :
    typesPoint.comap p.fiber hcover = p := by
  apply
    (show
      (typesPoint.comap p.fiber hcover = p) =
        ((typesPoint.comap p.fiber hcover).fiber = p.fiber) from
          mk.injEq _ _ _ _ _ _ _ _).mpr
  rfl

end GrothendieckTopology.Point

/- Lemma 7.32.7 (1): a point of the site `(C, J)` canonically defines a point of the topos
`Sh(C)`, and the inverse-image functor of the resulting point of the topos is the stalk functor. -/
#check GrothendieckTopology.Point.toToposPoint_pointInverseImageIso

-- Proof sketch: apply the inverse-image functor of the given topos point to the sheafified
-- representables `h_U^#` to obtain the site fiber functor `U ↦ p^{-1}(h_U^#)`, then prove this
-- functor is a site point and that its sheaf fiber recovers the original inverse-image functor.
namespace MorphismOfTopoiIn

open GrothendieckTopology.Point

/- Domain-style sampling for Lemma 7.32.7 (2):
- primary domain: points of a site and points of the associated topos, organized around the
  sheafified-representable owner layer and inverse image of points along a site morphism;
- sampled owner declarations:
  `GrothendieckTopology.Point.typesPoint`,
  `GrothendieckTopology.sheafifiedRepresentableFunctor`,
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`,
  `GrothendieckTopology.Point.sheafFiber`,
  `GrothendieckTopology.Point.toToposPoint_pointInverseImageIso`;
- source/core/bridge triage:
  `source-facing`: the site point attached to a topos point by the fibers `U ↦ p^{-1}(h[U]^#[J])`;
  `core/canonical`: the chapter owners `J.sheafifiedRepresentableFunctor`, `p.typeInverseImage`,
  and `GrothendieckTopology.Point.comap`;
  `bridge/view`: the composite `J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage`, together
  with the comparison isomorphism identifying the resulting site-point sheaf fiber with the
  original inverse-image functor.

Primitive data are only the topos point `p`; the functor `U ↦ p^{-1}(h[U]^#[J])` is derived API
from the existing owners `J.sheafifiedRepresentableFunctor` and `p.typeInverseImage`, and the
associated site point should be built through the canonical point-comap owner rather than by
restating the primitive `Point` fields. -/

private theorem typePresentationFunctor_coverPreserving
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    CoverPreserving J typesGrothendieckTopology
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) := by
  constructor
  intro U S hS x
  let T : J.Cover U := ⟨S, hS⟩
  let π : ∐ (fun I : T.Arrow ↦ h[I.Y]^#[J]) ⟶ h[U]^#[J] :=
    J.sheafifiedRepresentableCoverMap T
  let _ : p.typeInverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction p.typeAdjunction
  -- The source proof starts from the canonical cover map on sheafified representables.
  have hsurj : Function.Surjective (p.typeInverseImage.map π) := by
    have hπ : Epi π := by
      simpa [π] using GrothendieckTopology.sheafifiedRepresentableCoverMap_epi (J := J) T
    exact (CategoryTheory.epi_iff_surjective _).1 (p.typeInverseImage.map_epi π)
  obtain ⟨z, hz⟩ := hsurj x
  let X : Discrete T.Arrow ⥤ Sheaf J (Type (max u v)) :=
    Discrete.functor (fun I : T.Arrow ↦ h[I.Y]^#[J])
  let _ : PreservesColimitsOfSize p.typeInverseImage := p.typeAdjunction.leftAdjoint_preservesColimits
  let hc : IsColimit (Functor.mapCocone p.typeInverseImage (colimit.cocone X)) :=
    isColimitOfPreserves p.typeInverseImage (colimit.isColimit X)
  -- Decompose the chosen preimage through the preserved coproduct, then read off one cover leg.
  obtain ⟨I, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc z
  have hz' :
      (p⁻¹.map π).hom.app (op PUnit.{(max u v) + 1})
        ((p⁻¹.map (colimit.ι X I)).hom.app (op PUnit.{(max u v) + 1}) y) = x := by
    simpa [MorphismOfTopoiIn.typeInverseImage, X, π] using hz
  refine ⟨I.as.Y, I.as.f, fun _ ↦ y, I.as.hf, ?_⟩
  funext u
  -- The `I`-th coproduct injection into the cover map is exactly the `I.f`-component.
  have hι := congrArg
    (fun α => (p⁻¹.map α).hom.app (op PUnit.{(max u v) + 1}) y)
    (Limits.Sigma.ι_desc (fun I : T.Arrow ↦ J.sheafifiedRepresentableMap I.f) I.as)
  have hι' :
      (p⁻¹.map π).hom.app (op PUnit.{(max u v) + 1})
        ((p⁻¹.map (colimit.ι X I)).hom.app (op PUnit.{(max u v) + 1}) y) =
      (p⁻¹.map (J.sheafifiedRepresentableMap I.as.f)).hom.app (op PUnit.{(max u v) + 1}) y := by
    simpa [GrothendieckTopology.sheafifiedRepresentableCoverMap, π, X, Functor.map_comp] using hι
  simpa [MorphismOfTopoiIn.typeInverseImage] using hz'.symm.trans hι'

/-- Helper for Lemma 7.32.7: covering sieves act jointly surjectively on the fibers
`U ↦ p^{-1}(h_U^#)`. -/
private theorem typePresentationFunctor_jointly_surjective
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    ∀ {U : C} (R : Sieve U) (hR : R ∈ J U)
      (x : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj U),
      ∃ (Y : C) (f : Y ⟶ U) (_ : R f)
        (y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj Y),
        (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map f y = x := by
  intro U R hR x
  let S := R.functorPushforward (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage)
  have hS : S ∈ typesGrothendieckTopology
      ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).obj U) :=
    (typePresentationFunctor_coverPreserving (J := J) p).cover_preserve hR
  -- Read the pushed-forward covering sieve through the canonical point of the type site.
  obtain ⟨T, f, hf, t, ht⟩ := typesPoint.jointly_surjective S hS x
  let hs := Presieve.getFunctorPushforwardStructure
    (F := J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage) hf
  refine ⟨hs.preobj, hs.premap, hs.cover, hs.lift t, ?_⟩
  simpa [hs.fac] using ht

/-- Helper for Lemma 7.32.7: the comparison functor from representable neighborhoods to
arbitrary sheaf neighborhoods. -/
private noncomputable def typePresentationFunctor_elements_toInverseImageElements
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements ⥤
      p.typeInverseImage.Elements where
  obj X := Functor.elementsMk _ (J.sheafifiedRepresentableFunctor.obj X.1) X.2
  map {X Y} f := CategoryOfElements.homMk _ _ (J.sheafifiedRepresentableFunctor.map f.1) (by
    exact f.2)

/-- Helper for Lemma 7.32.7: evaluating a morphism out of `h[U]^#` on the identity section
recovers the section corresponding to that morphism. -/
private theorem sheafifiedRepresentable_component_eq_section
    [HasWeakSheafify J (Type (max u v))]
    {ℱ : Sheaf J (Type (max u v))} {U : C} (α : h[U]^#[J] ⟶ ℱ) :
    α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) =
      J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
  -- Rewrite evaluation on the identity section through naturality in the sheaf variable.
  have hcomp :=
    J.uliftSheafifiedRepresentableHomEquiv_comp
      (𝟙 (h[U]^#[J])) α
  -- The identity of `h[U]^#` corresponds to the canonical identity section.
  simpa using hcomp.symm

/-- Helper for Lemma 7.32.7: the section of `h[U]^#` corresponding to a site morphism `f` is the
sheafification of the Yoneda section `f`. -/
private theorem sheafifiedRepresentable_section_eq_toSheafify_app
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (f : U' ⟶ U) :
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
        (J.sheafifiedRepresentableFunctor.map f) =
      ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
  have hId :
      J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J])) =
        ((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U)) := by
    rfl
  -- Evaluate the morphism `h[U']^# ⟶ h[U]^#` by transporting the identity section along `f`.
  calc
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
        (J.sheafifiedRepresentableFunctor.map f) =
      (h[U]^#[J]).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) := by
          simpa using
            GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality
              (J := J) f (h[U]^#[J]) (𝟙 (h[U]^#[J]))
    _ = (h[U]^#[J]).obj.map f.op
        (((sheafificationAdjunction J (Type (max u v))).unit.app
          (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U) (ULift.up (𝟙 U))) := by
            rw [hId]
    _ = ((sheafificationAdjunction J (Type (max u v))).unit.app
        (CategoryTheory.uliftYoneda.{max u v}.obj U)).app (op U') (ULift.up f) := by
          let η :
              CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
            (sheafificationAdjunction J (Type (max u v))).unit.app
              (CategoryTheory.uliftYoneda.{max u v}.obj U)
          have hnat := congrFun (NatTrans.naturality η f.op) (ULift.up (𝟙 U))
          simpa [η, CategoryTheory.uliftYoneda] using hnat.symm

/-- Helper for Lemma 7.32.7: every morphism into a sheafified representable is locally induced by
an actual site morphism. -/
private theorem sheafifiedRepresentableFunctor_imageSieve_mem
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (c : h[U']^#[J] ⟶ h[U]^#[J]) :
    J.sheafifiedRepresentableFunctor.imageSieve c ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  let x : (h[U]^#[J]).obj.obj (op U') :=
    J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U' c
  have hx :
      J.sheafifiedRepresentableFunctor.imageSieve c = Presheaf.imageSieve η x := by
    -- Compare the source image sieve with the sheafification image sieve sectionwise.
    ext W g
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ULift.up l, ?_⟩
      calc
        η.app (op W) (ULift.up l) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map l) := by
              exact (sheafifiedRepresentable_section_eq_toSheafify_app (J := J) l).symm
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map g ≫ c) := by
              exact congrArg (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W) hl
        _ = (h[U]^#[J]).obj.map g.op x := by
              simpa [x, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c)
    · rintro ⟨l, hl⟩
      refine ⟨ULift.down l, ?_⟩
      apply (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map (ULift.down l)) =
          η.app (op W) l := by
            exact sheafifiedRepresentable_section_eq_toSheafify_app
              (J := J) (ULift.down l)
        _ = (h[U]^#[J]).obj.map g.op x := hl
        _ = J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) W
            (J.sheafifiedRepresentableFunctor.map g ≫ c) := by
              simpa [x, GrothendieckTopology.sheafifiedRepresentableMap,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                GrothendieckTopology.uliftSheafifiedRepresentableFunctor] using
                (J.uliftSheafifiedRepresentableHomEquiv_naturality g (h[U]^#[J]) c).symm
  -- The standard presheaf image-sieve cover becomes exactly the source image sieve.
  simpa [hx] using (Presheaf.imageSieve_mem J η x)

/-- Helper for Lemma 7.32.7: if two source arrows induce the same sheafified-representable map,
their equalizer sieve is covering. -/
private theorem sheafifiedRepresentableFunctor_equalizer_mem
    [HasWeakSheafify J (Type (max u v))]
    {U' U : C} (a b : U' ⟶ U)
    (h : J.sheafifiedRepresentableFunctor.map a = J.sheafifiedRepresentableFunctor.map b) :
    Sieve.equalizer a b ∈ J U' := by
  let η :
      CategoryTheory.uliftYoneda.{max u v}.obj U ⟶ (h[U]^#[J]).obj :=
    (sheafificationAdjunction J (Type (max u v))).unit.app
      (CategoryTheory.uliftYoneda.{max u v}.obj U)
  have hsection :
      η.app (op U') (ULift.up a) = η.app (op U') (ULift.up b) := by
    -- Equality after sheafification gives equality of the corresponding sheafification sections.
    have h' := congrArg
      (fun α : h[U']^#[J] ⟶ h[U]^#[J] ↦
        α.hom.app (op U')
          (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
            (𝟙 (h[U']^#[J])))) h
    have ha :
        (J.sheafifiedRepresentableFunctor.map a).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up a) := by
      calc
        (J.sheafifiedRepresentableFunctor.map a).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            (J.sheafifiedRepresentableFunctor.map a) := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := J.sheafifiedRepresentableFunctor.map a)
        _ = η.app (op U') (ULift.up a) := by
              exact sheafifiedRepresentable_section_eq_toSheafify_app (J := J) a
    have hb :
        (J.sheafifiedRepresentableFunctor.map b).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          η.app (op U') (ULift.up b) := by
      calc
        (J.sheafifiedRepresentableFunctor.map b).hom.app (op U')
            (J.uliftSheafifiedRepresentableHomEquiv (h[U']^#[J]) U'
              (𝟙 (h[U']^#[J]))) =
          J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U'
            (J.sheafifiedRepresentableFunctor.map b) := by
              exact sheafifiedRepresentable_component_eq_section
                (J := J) (α := J.sheafifiedRepresentableFunctor.map b)
        _ = η.app (op U') (ULift.up b) := by
              exact sheafifiedRepresentable_section_eq_toSheafify_app (J := J) b
    exact ha.symm.trans (h'.trans hb)
  let xa : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up a
  let xb : ToType ((CategoryTheory.uliftYoneda.{max u v}.obj U).obj (op U')) := ULift.up b
  have hEqSieve :
      Presheaf.equalizerSieve (F := CategoryTheory.uliftYoneda.{max u v}.obj U) xa xb =
        Sieve.equalizer a b := by
    ext W g
    change (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xa =
        (CategoryTheory.uliftYoneda.{max u v}.obj U).map g.op xb ↔
      g ≫ a = g ≫ b
    simpa [CategoryTheory.uliftYoneda, xa, xb]
  -- The presheaf equalizer sieve for the sheafification unit is exactly the source equalizer sieve.
  simpa [hEqSieve] using
    (Presheaf.equalizerSieve_mem (J := J) (φ := η) (X := op U') xa xb hsection)

/-- Helper for Lemma 7.32.7: every sheaf admits a locally surjective map from a coproduct of
sheafified representables indexed by all of its local sections. -/
private theorem exists_locally_surjective_map_from_sheafified_representables
    [HasWeakSheafify J (Type (max u v))]
    (ℱ : Sheaf J (Type (max u v))) :
    ∃ ι : Type (max u v), ∃ Y : ι → C,
      let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
        Sheaf.instHasColimitsOfShape
      ∃ π : (∐ fun i : ι ↦ h[Y i]^#[J]) ⟶ ℱ,
        Sheaf.IsLocallySurjective π := by
  let ι : Type (max u v) := Σ U : C, (h[U]^#[J] ⟶ ℱ)
  let Y : ι → C := fun i ↦ i.1
  refine ⟨ι, Y, ?_⟩
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let π : (∐ fun i : ι ↦ h[Y i]^#[J]) ⟶ ℱ :=
    Limits.Sigma.desc (fun i : ι ↦ i.2)
  refine ⟨π, ?_⟩
  refine ⟨fun {U} x ↦ ?_⟩
  let α : h[U]^#[J] ⟶ ℱ :=
    (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm x
  let i : ι := ⟨U, α⟩
  let t :
      ((∐ fun j : ι ↦ h[Y j]^#[J]).obj).obj (op U) :=
    (Limits.Sigma.ι (fun j : ι ↦ h[Y j]^#[J]) i).hom.app (op U)
      (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J])))
  -- Evaluate the chosen coproduct inclusion on the identity section of `h[U]^#`.
  have hι : Limits.Sigma.ι (fun j : ι ↦ h[Y j]^#[J]) i ≫ π = α := by
    simpa [π, i, Y] using
      (Limits.Sigma.ι_desc (fun j : ι ↦ j.2) i)
  have ht : π.hom.app (op U) t = x := by
    calc
    π.hom.app (op U)
        t =
      α.hom.app (op U)
        (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U (𝟙 (h[U]^#[J]))) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦
                k.hom.app (op U)
                  (J.uliftSheafifiedRepresentableHomEquiv (h[U]^#[J]) U
                    (𝟙 (h[U]^#[J])))) hι
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
      rw [sheafifiedRepresentable_component_eq_section (J := J) α]
    _ = x := by
      rw [(J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply]
  have htop : Presheaf.imageSieve π.hom x = ⊤ := by
    calc
      Presheaf.imageSieve π.hom x =
          Presheaf.imageSieve π.hom (π.hom.app (op U) t) := by rw [ht]
      _ = ⊤ := Presheaf.imageSieve_app π.hom t
  rw [htop]
  exact J.top_mem U

/-- Helper for Lemma 7.32.7: every sheaf neighborhood of the point is refined by a representable
neighborhood. -/
private theorem typePresentationFunctor_elements_toInverseImageElements_obj_lift
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (Y : p.typeInverseImage.Elements) :
    ∃ X : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      Nonempty
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X ⟶ Y) := by
  obtain ⟨ι, Y₀, π, hπ₀⟩ :=
    exists_locally_surjective_map_from_sheafified_representables (J := J) Y.1
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  let X₀ : Discrete ι ⥤ Sheaf J (Type (max u v)) :=
    Discrete.functor (fun i : ι ↦ h[Y₀ i]^#[J])
  let _ : Sheaf.IsLocallySurjective π := hπ₀
  let _ : Epi π := by infer_instance
  let _ : p.typeInverseImage.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction p.typeAdjunction
  have hsurj : Function.Surjective (p.typeInverseImage.map π) := by
    exact (CategoryTheory.epi_iff_surjective _).1 (p.typeInverseImage.map_epi π)
  obtain ⟨z, hz⟩ := hsurj Y.2
  let _ : PreservesColimitsOfSize p.typeInverseImage := p.typeAdjunction.leftAdjoint_preservesColimits
  let hc : IsColimit (Functor.mapCocone p.typeInverseImage (colimit.cocone X₀)) :=
    isColimitOfPreserves p.typeInverseImage (colimit.isColimit X₀)
  -- Decompose the chosen preimage through the preserved coproduct.
  obtain ⟨I, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc z
  let X :
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ (Y₀ I.as) x
  refine ⟨X, ⟨CategoryOfElements.homMk _ _ ((colimit.ι X₀ I) ≫ π) ?_⟩⟩
  -- The chosen coproduct component maps exactly to the original target element.
  simpa [X, X₀, MorphismOfTopoiIn.typeInverseImage] using hz

/-- Helper for Lemma 7.32.7: a morphism between two representable neighborhoods lifts locally to
an actual morphism in the source element category after refining the domain neighborhood. -/
private theorem typePresentationFunctor_elements_lift_hom
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {X Y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements}
    (φ :
      (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X ⟶
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y) :
    ∃ Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      ∃ t : Z ⟶ X, ∃ u : Z ⟶ Y,
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t ≫ φ =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u := by
  let R : Sieve X.1 := J.sheafifiedRepresentableFunctor.imageSieve φ.1
  have hR : R ∈ J X.1 := sheafifiedRepresentableFunctor_imageSieve_mem (J := J) φ.1
  obtain ⟨W, g, hg, w, hw⟩ :=
    typePresentationFunctor_jointly_surjective (J := J) p R hR X.2
  rcases hg with ⟨l, hl⟩
  let Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ W w
  let t : Z ⟶ X := CategoryOfElements.homMk _ _ g hw
  have hu :
      (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map l w = Y.2 := by
    -- The chosen local lift lands in the target neighborhood because it factors `φ`.
    have hfactor :
        (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map l w =
          (p.typeInverseImage.map φ.1)
            ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map g w) := by
      simpa [Functor.map_comp] using congrArg
        (fun α => (p.typeInverseImage.map α) w) hl
    have hsource :
        (p.typeInverseImage.map φ.1)
            ((J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).map g w) =
          (p.typeInverseImage.map φ.1) X.2 := by
      exact congrArg (p.typeInverseImage.map φ.1) hw
    have htarget : (p.typeInverseImage.map φ.1) X.2 = Y.2 := by
      exact φ.2
    exact hfactor.trans (hsource.trans htarget)
  let u : Z ⟶ Y := CategoryOfElements.homMk _ _ l hu
  refine ⟨Z, t, u, ?_⟩
  -- After refinement, the target morphism is literally induced by the lifted source arrow.
  apply CategoryOfElements.ext p.typeInverseImage
  exact hl.symm

/-- Helper for Lemma 7.32.7: if two source morphisms become equal after comparison, they are equal
after refining the domain neighborhood by a covering sieve. -/
private theorem typePresentationFunctor_elements_equalize_of_map_eq
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {X Y : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements}
    (f g : X ⟶ Y)
    (h :
      (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f =
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g) :
    ∃ Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements,
      ∃ t : Z ⟶ X, t ≫ f = t ≫ g := by
  let R : Sieve X.1 := Sieve.equalizer f.1 g.1
  have hmap :
      J.sheafifiedRepresentableFunctor.map f.1 =
        J.sheafifiedRepresentableFunctor.map g.1 := by
    simpa using congrArg Subtype.val h
  have hR : R ∈ J X.1 := sheafifiedRepresentableFunctor_equalizer_mem (J := J) f.1 g.1 hmap
  obtain ⟨W, t, ht, w, hw⟩ :=
    typePresentationFunctor_jointly_surjective (J := J) p R hR X.2
  let Z : (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements :=
    Functor.elementsMk _ W w
  let k : Z ⟶ X := CategoryOfElements.homMk _ _ t hw
  refine ⟨Z, k, ?_⟩
  apply CategoryOfElements.ext (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage)
  exact ht

/-- Helper for Lemma 7.32.7: the neighborhood category of
`U ↦ p^{-1}(h_U^#)` is cofiltered. -/
private instance typePresentationFunctor_elements_isCofiltered
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    IsCofiltered (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements := by
  let _ : PreservesFiniteLimits (p⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits p
  let _ : PreservesFiniteLimits p.typeInverseImage := by infer_instance
  letI : IsCofiltered p.typeInverseImage.Elements :=
    Functor.isCofiltered_elements p.typeInverseImage
  refine
    { cone_objs := ?_
      cone_maps := ?_
      nonempty := ?_ }
  · intro X Y
    -- Start from the target-side common predecessor and then refine it back to a representable
    -- neighborhood so both comparison arrows come from actual source neighborhoods.
    let Zt : p.typeInverseImage.Elements :=
      IsCofiltered.min
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y)
    let α : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X :=
      IsCofiltered.minToLeft _ _
    let β : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj Y :=
      IsCofiltered.minToRight _ _
    obtain ⟨Z₀, ⟨m⟩⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Zt
    obtain ⟨Z₁, t₁, u₁, hu₁⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p (φ := m ≫ α)
    obtain ⟨Z₂, t₂, u₂, hu₂⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p
        (φ := (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
          m ≫ β)
    exact ⟨Z₂, t₂ ≫ u₁, u₂, trivial⟩
  · intro X Y f g
    -- Equalize the compared arrows in the target element category, then pull that equality back
    -- along the refined representable neighborhood to equalize the original source arrows.
    let Zt : p.typeInverseImage.Elements :=
      IsCofiltered.eq
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g)
    let α : Zt ⟶ (typePresentationFunctor_elements_toInverseImageElements (J := J) p).obj X :=
      IsCofiltered.eqHom
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f)
        ((typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g)
    obtain ⟨Z₀, ⟨m⟩⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Zt
    obtain ⟨Z₁, t₁, u₁, hu₁⟩ :=
      typePresentationFunctor_elements_lift_hom (J := J) p (φ := m ≫ α)
    have hEq :
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ f) =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ g) := by
      calc
        (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ f) =
          (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u₁ ≫
            (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f := by
              simp
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
            m ≫ α ≫
              (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map f := by
                simpa [Category.assoc] using congrArg
                  (fun k =>
                    k ≫ (typePresentationFunctor_elements_toInverseImageElements
                      (J := J) p).map f) hu₁.symm
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map t₁ ≫
            m ≫ α ≫
              (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g := by
                rw [IsCofiltered.eq_condition]
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map u₁ ≫
            (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map g := by
                simpa [Category.assoc] using congrArg
                  (fun k =>
                    k ≫ (typePresentationFunctor_elements_toInverseImageElements
                      (J := J) p).map g) hu₁
        _ = (typePresentationFunctor_elements_toInverseImageElements (J := J) p).map (u₁ ≫ g) := by
              simp
    obtain ⟨Z₂, t₂, ht₂⟩ :=
      typePresentationFunctor_elements_equalize_of_map_eq (J := J) p (u₁ ≫ f) (u₁ ≫ g) hEq
    exact ⟨Z₂, t₂ ≫ u₁, by simpa [Category.assoc] using ht₂⟩
  · obtain ⟨Y⟩ := IsCofiltered.nonempty (C := p.typeInverseImage.Elements)
    obtain ⟨X, -⟩ :=
      typePresentationFunctor_elements_toInverseImageElements_obj_lift (J := J) p Y
    exact ⟨X⟩

/-- Helper for Lemma 7.32.7: the element category of `U ↦ p^{-1}(h_U^#)` is initially small. -/
private instance typePresentationFunctor_elements_initiallySmall
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    InitiallySmall.{max u v} (J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage).Elements := by
  classical
  exact initiallySmall_of_essentiallySmall _

/-- For a point `p` of the topos `Sh(C)`, the functor `U ↦ p^{-1}(h_U^#)` defines the
associated point of the site `(C, J)`. -/
noncomputable def toSitePoint
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    GrothendieckTopology.Point.{max u v} J := by
  -- Route correction: the site point only needs cofilteredness of the category of elements of
  -- `U ↦ p^{-1}(h_U^#)`, not the stronger representably-flat packaging from `typesPoint.comap`.
  refine
    { fiber := J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage
      jointly_surjective := ?_ }
  intro U R hR x
  simpa using typePresentationFunctor_jointly_surjective (J := J) p R hR x

/-- Helper for Lemma 7.32.7: on sheafified representables, the stalk functor of `p.toSitePoint`
agrees with `p.typeInverseImage`. -/
private noncomputable def toSitePoint_comparison_sheafifiedRepresentableIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    :
    J.sheafifiedRepresentableFunctor ⋙ p.toSitePoint.sheafFiber ≅
      J.sheafifiedRepresentableFunctor ⋙ p.typeInverseImage := by
  -- Compare the sheaf fiber on `h_U^#` with the presheaf fiber on `uliftYoneda.obj U`,
  -- then identify that presheaf fiber with the defining fiber functor of `p.toSitePoint`.
  simpa [GrothendieckTopology.sheafifiedRepresentable, GrothendieckTopology.sheafifiedRepresentableFunctor,
    MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
    (Functor.associator CategoryTheory.uliftYoneda.{max u v}
      (presheafToSheaf J (Type (max u v))) p.toSitePoint.sheafFiber) ≪≫
      (Functor.isoWhiskerLeft CategoryTheory.uliftYoneda.{max u v}
        (p.toSitePoint.presheafToSheafCompSheafFiberIso (Type (max u v)))) ≪≫
      ((Functor.isoWhiskerRight CategoryTheory.uliftYonedaIsoShrinkYoneda
        p.toSitePoint.presheafFiber) ≪≫
          p.toSitePoint.shrinkYonedaCompPresheafFiberIso)

/-- Helper for Lemma 7.32.7: on sheafified representables, the stalk functor of `p.toSitePoint`
agrees with `p.typeInverseImage`. -/
private noncomputable def toSitePoint_comparison_app_sheafifiedRepresentable
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (U : C) :
    (p.toSitePoint.sheafFiber.obj (h[U]^#[J])) ≅
      p.typeInverseImage.obj (h[U]^#[J]) :=
  (toSitePoint_comparison_sheafifiedRepresentableIso (J := J) p).app U

/-- Helper for Lemma 7.32.7: sections of `p_* E` over a sheafified representable are functions on
the corresponding fiber of `p.toSitePoint`. -/
private noncomputable def toSitePoint_typePushforward_sectionEquiv
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) (U : C) :
    ((p.typePushforward.obj E).obj.obj (op U)) ≃
      (((toSitePoint (J := J) p).fiber.obj U) → E) := by
  -- Rewrite sections of `p_* E` as morphisms from `h_U^#`, transpose them across the
  -- adjunction `p⁻¹ ⊣ p_*`, and then read the result as the defining fiber of `p.toSitePoint`.
  let e₁ :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm
  let e₂ := (p.typeAdjunction.homEquiv (h[U]^#[J]) E).symm
  simpa [MorphismOfTopoiIn.typeInverseImage, toSitePoint] using e₁.trans e₂

/-- Helper for Lemma 7.32.7: restricting a section of `p_* E` corresponds to precomposing the
associated function with the map on fibers of `p.toSitePoint`. -/
private theorem toSitePoint_typePushforward_sectionEquiv_naturality_left
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) {U V : C} (g : V ⟶ U)
    (s : ((p.typePushforward.obj E).obj.obj (op U))) :
    toSitePoint_typePushforward_sectionEquiv (J := J) p E V
        (((p.typePushforward.obj E).obj.map g.op) s) =
      fun x ↦
        toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
          (((toSitePoint (J := J) p).fiber.map g) x) := by
  let t : ((toSitePoint (J := J) p).fiber.obj V) → E :=
    ((toSitePoint (J := J) p).fiber.map g) ≫
      toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
  let αV :
      h[V]^#[J] ⟶ p.typePushforward.obj E :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V).symm
      (((p.typePushforward.obj E).obj.map g.op) s)
  -- First identify the restricted section with precomposition on the sheafified representable.
  apply (p.typeAdjunction.homEquiv (h[V]^#[J]) E).injective
  have hsection :
      αV =
      (J.sheafifiedRepresentableFunctor.map g) ≫
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    -- This is exactly naturality of `Hom(h_U^#, -) ≃ sections over U`.
    apply (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V
          αV =
        ((p.typePushforward.obj E).obj.map g.op) s := by
            exact Equiv.apply_symm_apply _ _
      _ = ((p.typePushforward.obj E).obj.map g.op)
            (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U
              ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)) := by
            rw [Equiv.apply_symm_apply]
      _ = J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) V
            ((J.sheafifiedRepresentableFunctor.map g) ≫
              (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s) := by
            symm
            exact
              J.uliftSheafifiedRepresentableHomEquiv_naturality g
                (p.typePushforward.obj E)
                ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)
  have happlyU :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
          (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    simpa [toSitePoint_typePushforward_sectionEquiv] using
      (Equiv.apply_symm_apply
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
        ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s))
  have hadj :
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    -- Then move the left action across the adjunction equivalence.
    calc
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
            (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) := by
              simpa [t, GrothendieckTopology.sheafifiedRepresentable,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
                (p.typeAdjunction.homEquiv_naturality_left
                  ((J.uliftSheafifiedRepresentableFunctor).map g)
                  (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s))
      _ =
        (J.sheafifiedRepresentableFunctor.map g) ≫
          (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
              rw [happlyU]
  calc
    (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
        (toSitePoint_typePushforward_sectionEquiv (J := J) p E V
          (((p.typePushforward.obj E).obj.map g.op) s)) =
      (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
        ((p.typeAdjunction.homEquiv (h[V]^#[J]) E).symm αV) := by
          rfl
    _ = αV := by
          exact Equiv.apply_symm_apply _ _
    _ = (p.typeAdjunction.homEquiv (h[V]^#[J]) E) t := by
          rw [hsection, hadj.symm]
    _ = (p.typeAdjunction.homEquiv (h[V]^#[J]) E)
          (fun x ↦
            toSitePoint_typePushforward_sectionEquiv (J := J) p E U s
              (((toSitePoint (J := J) p).fiber.map g) x)) := by
          rfl

/-- Helper for Lemma 7.32.7: the sectionwise description of `p_* E` packages into an isomorphism
of underlying presheaves. -/
private noncomputable def toSitePoint_typePushforward_presheafObjIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (E : Type (max u v)) :
    (p.typePushforward.obj E).obj ≅ (toSitePoint (J := J) p).skyscraperPresheaf E := by
  let q := toSitePoint (J := J) p
  let e :
      ∀ U : Cᵒᵖ,
        ((p.typePushforward.obj E).obj.obj U) ≅ (q.skyscraperPresheaf E).obj U :=
    fun U ↦
      (Equiv.toIso (toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop)) ≪≫
        (Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).symm
  -- Package the pointwise section equivalences into a presheaf isomorphism.
  refine NatIso.ofComponents e ?_
  intro U V f
  funext s
  apply Types.limit_ext
  intro x
  cases x with
  | mk x =>
  -- After rewriting the skyscraper sections as functions, naturality is exactly the left
  -- sectionwise naturality statement proved above.
  calc
    Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x
        ((e V).hom (((p.typePushforward.obj E).obj.map f) s)) =
      toSitePoint_typePushforward_sectionEquiv (J := J) p E V.unop
        (((p.typePushforward.obj E).obj.map f) s) x := by
          change
            ((Types.productIso (fun _ : q.fiber.obj V.unop ↦ E)).inv ≫
              Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x)
              (toSitePoint_typePushforward_sectionEquiv (J := J) p E V.unop
                (((p.typePushforward.obj E).obj.map f) s)) =
              _
          rw [Types.productIso_inv_comp_π]
    _ =
      toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop s
        (q.fiber.map f.unop x) := by
          simpa [q] using
            congrFun
              (toSitePoint_typePushforward_sectionEquiv_naturality_left
                (J := J) p E f.unop s) x
    _ =
      Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x
        ((q.skyscraperPresheaf E).map f ((e U).hom s)) := by
          change
            (p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s
                (q.fiber.map f.unop x) =
              (((Pi.map' (q.fiber.map f.unop) (fun _ ↦ 𝟙 E)) ≫
                  Pi.π (fun _ : q.fiber.obj V.unop ↦ E) x)
                (((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).inv
                  ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s))))
          rw [Pi.map'_comp_π]
          rw [Category.comp_id]
          symm
          simpa using
            congrFun
              (Types.productIso_inv_comp_π
                (fun _ : q.fiber.obj U.unop ↦ E) (q.fiber.map f.unop x))
              ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s)

/-- Helper for Lemma 7.32.7: maps `E ⟶ E'` act on the sectionwise comparison by postcomposition
on the target functions. -/
private theorem toSitePoint_typePushforward_sectionEquiv_naturality_right
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    {E E' : Type (max u v)} (f : E ⟶ E') (U : C)
    (s : ((p.typePushforward.obj E).obj.obj (op U))) :
    toSitePoint_typePushforward_sectionEquiv (J := J) p E' U
        (((p.typePushforward.map f).hom.app (op U)) s) =
      fun x ↦ f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s x) := by
  let t : ((toSitePoint (J := J) p).fiber.obj U) → E' :=
    toSitePoint_typePushforward_sectionEquiv (J := J) p E U s ≫ f
  let αU' :
      h[U]^#[J] ⟶ p.typePushforward.obj E' :=
    (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U).symm
      (((p.typePushforward.map f).hom.app (op U)) s)
  -- First identify the action of `f` on sections with postcomposition in the Hom-set.
  apply (p.typeAdjunction.homEquiv (h[U]^#[J]) E').injective
  have hsection :
      αU' =
      (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
        (p.typePushforward.map f) := by
    -- This is naturality of `Hom(h_U^#, -) ≃ sections over U` in the sheaf variable.
    apply (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U
          αU' =
        ((p.typePushforward.map f).hom.app (op U)) s := by
            exact Equiv.apply_symm_apply _ _
      _ = ((p.typePushforward.map f).hom.app (op U))
            (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U
              ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)) := by
            rw [Equiv.apply_symm_apply]
      _ = J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E') U
            ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
              (p.typePushforward.map f)) := by
            symm
            exact
              J.uliftSheafifiedRepresentableHomEquiv_comp
                ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s)
                (p.typePushforward.map f)
  have happlyU :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
          (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s := by
    simpa [toSitePoint_typePushforward_sectionEquiv] using
      (Equiv.apply_symm_apply
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
        ((J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s))
  have hadj :
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
          (p.typePushforward.map f) := by
    -- Finally move postcomposition across the transported adjunction.
    calc
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t =
        (p.typeAdjunction.homEquiv (h[U]^#[J]) E)
            (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s) ≫
          (p.typePushforward.map f) := by
              simpa [t, GrothendieckTopology.sheafifiedRepresentable,
                GrothendieckTopology.sheafifiedRepresentableFunctor,
                MorphismOfTopoiIn.typeInverseImage, toSitePoint] using
                (p.typeAdjunction.homEquiv_naturality_right
                  (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s)
                  f)
      _ =
        (J.uliftSheafifiedRepresentableHomEquiv (p.typePushforward.obj E) U).symm s ≫
          (p.typePushforward.map f) := by
              rw [happlyU]
  calc
    (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
        (toSitePoint_typePushforward_sectionEquiv (J := J) p E' U
          (((p.typePushforward.map f).hom.app (op U)) s)) =
      (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
        ((p.typeAdjunction.homEquiv (h[U]^#[J]) E').symm αU') := by
          rfl
    _ = αU' := by
          exact Equiv.apply_symm_apply _ _
    _ = (p.typeAdjunction.homEquiv (h[U]^#[J]) E') t := by
          rw [hsection, hadj.symm]
    _ = (p.typeAdjunction.homEquiv (h[U]^#[J]) E')
          (fun x ↦ f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U s x)) := by
          rfl

/-- Helper for Lemma 7.32.7: the direct image of a topos point agrees with the skyscraper sheaf
functor of the associated site point. -/
private noncomputable def toSitePoint_typePushforwardIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    p.typePushforward ≅ (toSitePoint (J := J) p).skyscraperSheafFunctor := by
  let q := toSitePoint (J := J) p
  let ePresheaf :
      p.typePushforward ⋙ sheafToPresheaf J (Type (max u v)) ≅ q.skyscraperPresheafFunctor := by
    refine NatIso.ofComponents (toSitePoint_typePushforward_presheafObjIso (J := J) p) ?_
    intro E E' f
    ext U s
    apply Types.limit_ext
    intro x
    cases x with
    | mk x =>
    -- After rewriting the skyscraper sections as functions, naturality is exactly the right
    -- sectionwise naturality statement proved above.
    calc
      Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
          ((toSitePoint_typePushforward_presheafObjIso (J := J) p E').hom.app U
            (((p.typePushforward.map f).hom.app U) s)) =
        toSitePoint_typePushforward_sectionEquiv (J := J) p E' U.unop
          (((p.typePushforward.map f).hom.app U) s) x := by
            change
              ((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E')).inv ≫
                Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x)
                (toSitePoint_typePushforward_sectionEquiv (J := J) p E' U.unop
                  (((p.typePushforward.map f).hom.app U) s)) =
                _
            rw [Types.productIso_inv_comp_π]
      _ = f (toSitePoint_typePushforward_sectionEquiv (J := J) p E U.unop s x) := by
            simpa using
              congrFun
                (toSitePoint_typePushforward_sectionEquiv_naturality_right
                  (J := J) p f U.unop s) x
      _ =
        Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
          ((q.skyscraperPresheafFunctor.map f).app U
            ((toSitePoint_typePushforward_presheafObjIso (J := J) p E).hom.app U s)) := by
            change
              f ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s x) =
                Pi.π (fun _ : q.fiber.obj U.unop ↦ E') x
                  ((Limits.Pi.map (fun _ : q.fiber.obj U.unop ↦ f))
                    (((Types.productIso (fun _ : q.fiber.obj U.unop ↦ E)).inv
                      ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s))))
            rw [Types.pi_map_π_apply']
            exact congrArg f <|
              (congrFun
                (Types.productIso_inv_comp_π
                  (fun _ : q.fiber.obj U.unop ↦ E) x)
                ((p.toSitePoint_typePushforward_sectionEquiv E (unop U)) s)).symm
  -- Reflect the presheaf comparison back to sheaves through the fully faithful forgetful functor.
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf J (Type (max u v))) ePresheaf

/-- Lemma 7.32.7: for a point `p` of the topos `Sh(C)`, the functor
`U ↦ p^{-1}(h_U^#)` defines a point of the site `(C, J)`, and the stalk functor of that site
point recovers the inverse-image functor of `p`. -/
noncomputable def toSitePoint_sheafFiberIso
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v}) :
    (toSitePoint (J := J) p).sheafFiber ≅ p.typeInverseImage :=
  -- Compare the two right adjoints first, then recover the left-adjoint comparison by the
  -- uniqueness of left adjoints to a fixed right adjoint.
  Adjunction.leftAdjointUniq
    ((toSitePoint (J := J) p).skyscraperSheafAdjunction)
    (p.typeAdjunction.ofNatIsoRight (toSitePoint_typePushforwardIso (J := J) p))

-- Proof sketch: evaluate the canonical natural isomorphism
-- `p.toSitePoint_sheafFiberIso` on a sheaf and use the identity law for isomorphisms.
/-- The component of `toSitePoint_sheafFiberIso` followed by its inverse is the identity. -/
theorem toSitePoint_sheafFiberIso_hom_inv_app
    [HasWeakSheafify J (Type (max u v))]
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{max u v})
    (F : Sheaf J (Type (max u v))) :
    (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p).hom.app F ≫
        (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p).inv.app F =
      𝟙 _ := by
  -- Once the natural isomorphism is fixed, the componentwise identity is formal.
  simpa using Iso.hom_inv_id_app (MorphismOfTopoiIn.toSitePoint_sheafFiberIso (J := J) p) F

end MorphismOfTopoiIn

end CategoryTheory
