import Mathlib
import StacksProject_2024.stacks_project.Chap18.Definition_18_32_1
import StacksProject_2024.stacks_project.Chap18.Lemma_18_36_4
import StacksProject_2024.stacks_project.Chap18.Definition_18_40_9
import StacksProject_2024.stacks_project.Chap18.Lemma_18_40_2
import StacksProject_2024.stacks_project.Chap18.Lemma_18_40_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 18.40.8:
- primary domain: locally ringed morphisms of site-presented topoi, with the induced stalk maps
  viewed through both the source-side cartesian-units condition and the actual target-stalk map
  `\mathcal O_{D,q} \to \mathcal O_{C,p}`;
- sampled owner declarations:
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`,
  `pointStructureRingHom`,
  `IsLocallyRingedSite`,
  `IsLocalHom`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `CategoryTheory.IsMorphismOfLocallyRingedTopoi`;
- best owner abstraction: the source-facing global owner is
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, while the source-facing stalk map is the
  Chapter 18 owner `pointStructureRingHom`; under the Chapter 7 point-pullback hypotheses
  `[RepresentablyFlat F]` and `hF : CoverPreserving JD JC F`, the target point is canonically
  `p.comap F hF`, so the numbered clauses should be stated on that actual stalk map rather than on
  the raw bridge morphism `p.sheafFiber.map fSharp`;
- primitive data: the unbundled inverse-image structure-sheaf morphism `fSharp`, the point-pullback
  data `[RepresentablyFlat F]` and `hF`, and a source point `p : JC.Point`;
- derived API: the objectwise maps `fSharp.hom.app (op U)`, the induced stalk map
  `pointStructureRingHom ... p (p.comap F hF) ((p.sheafFiberComapIso F hF _).symm) fSharp`, the
  associated stalkwise cartesian-units condition, and its ring-theoretic reformulation by
  `IsLocalHom`.

Source/core/bridge triage:
- `source-facing`: the sectionwise-to-stalkwise implications and conservative-family criteria of
  Lemma 18.40.8, stated on the actual target-stalk map
  `pointStructureRingHom ... : \mathcal O_{D,p.comap F hF} \to \mathcal O_{C,p}`;
- `core/canonical`: `IsLocallyRingedSite`,
  `Point.comap`,
  `Point.sheafFiberComapIso`,
  `pointStructureRingHom`,
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, and
  `unitsSquareCartesianForLocallyRingedMorphism`;
- `bridge/view`: the raw inverse-image stalk map `p.sheafFiber.map fSharp` and the predicate
  `IsLocalHom`, which become source-facing only after transport to the actual target stalk.

This file should therefore reuse the existing Chapter 18 owner for the global units-square
condition, state the stalkwise clauses directly on `pointStructureRingHom`, and use `IsLocalHom`
only as the ring-theoretic reformulation of that source-facing stalk map.
-/

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S]

-- Proof sketch: an element of the pullback is a source element whose image is a unit; lifting it
-- to a source unit is exactly the unit-reflection property, namely `IsLocalHom φ`.
/-- The units square for a ring map is cartesian exactly when the map reflects units. -/
theorem unitsSquareCartesian_iff_isLocalHom (φ : R →+* S) :
    unitsSquareCartesianForLocallyRingedMorphism φ ↔ IsLocalHom φ := by
  constructor
  · intro hCartesian
    -- A preimage of any pullback witness records a source unit mapping to the chosen target unit.
    refine IsLocalHom.mk ?_
    intro r hr
    obtain ⟨u, hu⟩ :=
      hCartesian.2 ⟨⟨hr.unit, r⟩, hr.unit_spec⟩
    have hu_eq : (u : R) = r := by
      simpa [unitsSquareComparisonForLocallyRingedMorphism] using
        congrArg (fun x ↦ x.1.2) hu
    simpa [hu_eq] using u.isUnit
  · intro hLocal
    letI : IsLocalHom φ := hLocal
    constructor
    · intro u v huv
      -- Injectivity is read off from the source-ring component of the pullback point.
      apply Units.ext
      simpa [unitsSquareComparisonForLocallyRingedMorphism] using
        congrArg (fun x ↦ x.1.2) huv
    · intro x
      -- Surjectivity amounts to lifting a pullback point whose target component is already a unit.
      have hx_unit : IsUnit (φ x.1.2) := by
        rw [← x.2]
        exact x.1.1.isUnit
      let u : Rˣ := (isUnit_map_iff φ x.1.2).1 hx_unit |>.unit
      refine ⟨u, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Units.ext
        calc
          φ (u : R) = φ x.1.2 := by
            rw [show (u : R) = x.1.2 by exact ((isUnit_map_iff φ x.1.2).1 hx_unit).unit_spec]
          _ = (x.1.1 : S) := x.2.symm
      · exact ((isUnit_map_iff φ x.1.2).1 hx_unit).unit_spec

variable {T : Type u} [CommRing T]

/-- Helper for Lemma 18.40.8: precomposing by an isomorphism of commutative rings does not change
the cartesian-units predicate. -/
theorem unitsSquareCartesian_precompIso_iff
    {A B C : CommRingCat.{u}} (e : A ≅ B) (φ : B ⟶ C) :
    unitsSquareCartesianForLocallyRingedMorphism ((e.hom ≫ φ).hom) ↔
      unitsSquareCartesianForLocallyRingedMorphism φ.hom := by
  -- The cartesian-units condition is equivalent to `IsLocalHom`, and localness is invariant under
  -- composition with an isomorphism on the source.
  rw [unitsSquareCartesian_iff_isLocalHom, unitsSquareCartesian_iff_isLocalHom]
  constructor
  · intro hComp
    let _ : IsLocalHom ((e.hom ≫ φ).hom) := hComp
    refine IsLocalHom.mk ?_
    intro b hb
    have hPrecompUnit : IsUnit (((e.hom ≫ φ).hom) (e.inv.hom b)) := by
      simpa using hb
    have hInvUnit : IsUnit (e.inv.hom b) :=
      (isUnit_map_iff ((e.hom ≫ φ).hom) (e.inv.hom b)).1 hPrecompUnit
    simpa using hInvUnit.map e.hom.hom
  · intro hφ
    let _ : IsLocalHom φ.hom := hφ
    let _ : IsLocalHom e.hom.hom := isLocalHom_of_iso e
    simpa using RingHom.isLocalHom_comp φ.hom e.hom.hom

/-- Helper for Lemma 18.40.8: if the germ of a section at a site point is a unit, then after
restricting along some arrow in the point fiber the section itself becomes a unit. -/
theorem exists_isUnit_restriction_of_pointFiber_isUnit
    {E : Type u} [Category.{u} E] {JE : GrothendieckTopology E}
    (𝒪 : Sheaf JE CommRingCat.{u}) (p : JE.Point)
    (U : E) (x : p.fiber.obj U) (s : 𝒪.1.obj (op U))
    (hs : IsUnit ((p.toPresheafFiber U x 𝒪.1).hom s)) :
    ∃ (V : E) (f : V ⟶ U) (y : p.fiber.obj V),
      p.fiber.map f y = x ∧ IsUnit ((𝒪.1.map f.op).hom s) := by
  let u : Units ↑(p.presheafFiber.obj 𝒪.1) := hs.unit
  obtain ⟨V, xV, t, ht⟩ :=
    p.toPresheafFiber_jointly_surjective (P := 𝒪.1) ((u⁻¹ : Units ↑(p.presheafFiber.obj 𝒪.1)) : _)
  let leftObj : p.fiber.Elements := ⟨U, x⟩
  let rightObj : p.fiber.Elements := ⟨V, xV⟩
  let commonObj : p.fiber.Elements := IsCofiltered.min leftObj rightObj
  let leftMap : commonObj ⟶ leftObj := IsCofiltered.minToLeft leftObj rightObj
  let rightMap : commonObj ⟶ rightObj := IsCofiltered.minToRight leftObj rightObj
  let W : E := commonObj.1
  let xW : p.fiber.obj W := commonObj.2
  let fW : W ⟶ U := leftMap.1
  let gW : W ⟶ V := rightMap.1
  have hfW : p.fiber.map fW xW = x := leftMap.2
  have hgW : p.fiber.map gW xW = xV := rightMap.2
  let sW : 𝒪.1.obj (op W) := (𝒪.1.map fW.op).hom s
  let tW : 𝒪.1.obj (op W) := (𝒪.1.map gW.op).hom t
  have hsW :
      (p.toPresheafFiber W xW 𝒪.1).hom sW =
        (p.toPresheafFiber U x 𝒪.1).hom s := by
    simpa [W, xW, fW, hfW, sW] using
      congrArg (fun k ↦ k.hom s) (p.toPresheafFiber_w fW xW 𝒪.1)
  have htW :
      (p.toPresheafFiber W xW 𝒪.1).hom tW =
        ((u⁻¹ : Units ↑(p.presheafFiber.obj 𝒪.1)) : ↑(p.presheafFiber.obj 𝒪.1)) := by
    calc
      (p.toPresheafFiber W xW 𝒪.1).hom tW =
          (p.toPresheafFiber V xV 𝒪.1).hom t := by
            simpa [W, xW, gW, hgW, tW] using
              congrArg (fun k ↦ k.hom t) (p.toPresheafFiber_w gW xW 𝒪.1)
      _ = ((u⁻¹ : Units ↑(p.presheafFiber.obj 𝒪.1)) : ↑(p.presheafFiber.obj 𝒪.1)) := ht
  have hmul :
      (p.toPresheafFiber W xW 𝒪.1).hom (sW * tW) =
        (p.toPresheafFiber W xW 𝒪.1).hom 1 := by
    calc
      (p.toPresheafFiber W xW 𝒪.1).hom (sW * tW) =
          (p.toPresheafFiber W xW 𝒪.1).hom sW *
            (p.toPresheafFiber W xW 𝒪.1).hom tW := by
              rw [map_mul]
      _ = ((u : Units ↑(p.presheafFiber.obj 𝒪.1)) :
            ↑(p.presheafFiber.obj 𝒪.1)) *
          ((u⁻¹ : Units ↑(p.presheafFiber.obj 𝒪.1)) :
            ↑(p.presheafFiber.obj 𝒪.1)) := by
              rw [hsW, htW, hs.unit_spec]
      _ = 1 := by simp
      _ = (p.toPresheafFiber W xW 𝒪.1).hom 1 := by simp
  rcases (p.toPresheafFiber_eq_iff' (P := 𝒪.1) W xW (sW * tW) 1).1 hmul with
    ⟨Z, hZW, xZ, hxZ, hmulZ⟩
  have hunitZ :
      ((𝒪.1.map (hZW ≫ fW).op).hom s) *
          ((𝒪.1.map (hZW ≫ gW).op).hom t) = 1 := by
    simpa [FunctorToTypes.map_comp_apply, sW, tW, hxZ, map_mul] using hmulZ
  refine ⟨Z, hZW ≫ fW, xZ, ?_, ?_⟩
  · simpa [FunctorToTypes.map_comp_apply, hxZ, hfW]
  · refine ⟨⟨_, _, hunitZ, ?_⟩, rfl⟩
    simpa [mul_comm] using hunitZ

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [(F.sheafPushforwardContinuous CommRingCat.{u} JD JC).IsRightAdjoint]
variable (𝒪C : Sheaf JC CommRingCat.{u}) (𝒪D : Sheaf JD CommRingCat.{u})

variable
    (fSharp :
      inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D ⟶ 𝒪C)

-- Proof sketch: taking the stalk at a point preserves finite limits, so an objectwise cartesian
-- units square on the source site yields a cartesian units square on every actual induced stalk
-- map `\mathcal O_{D,p.comap F hF} \to \mathcal O_{C,p}`.
/-- Lemma 18.40.8 (1): the cartesian units square on the inverse-image structure sheaf implies the
corresponding cartesian units square on every stalk. -/
theorem inverseImageUnitsCartesian_implies_stalkUnitsCartesian
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    (h : inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp)
    (p : JC.Point) [InitiallySmall (F ⋙ p.fiber).Elements] :
    let φ :=
      (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
        ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
    unitsSquareCartesianForLocallyRingedMorphism φ := by
  -- First show that the raw stalk map on the inverse-image sheaf reflects units.
  have hRawLocal : IsLocalHom ((p.sheafFiber.map fSharp).hom) := by
    refine IsLocalHom.mk ?_
    intro x hx
    let x' :
        ToType
          (p.presheafFiber.obj
            (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1) := x
    obtain ⟨U, xU, s, rfl⟩ :=
      p.toPresheafFiber_jointly_surjective
        (P := (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1) x'
    -- Rewrite the unit germ in the target stalk as the germ of the image section.
    have hsImage :
        ((p.sheafFiber.map fSharp).hom)
            ((p.toPresheafFiber U xU
              (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1).hom s) =
          (p.toPresheafFiber U xU 𝒪C.1).hom ((fSharp.hom.app (op U)).hom s) := by
      exact congrArg (fun k ↦ k.hom s) (p.toPresheafFiber_naturality fSharp.hom U xU)
    have hsImageUnit :
        IsUnit ((p.toPresheafFiber U xU 𝒪C.1).hom ((fSharp.hom.app (op U)).hom s)) := by
      rw [← hsImage]
      exact hx
    -- Shrink to a stage where the image section itself is a unit.
    obtain ⟨V, f, y, hy, hsVUnit⟩ :=
      exists_isUnit_restriction_of_pointFiber_isUnit
        (𝒪 := 𝒪C) p U xU ((fSharp.hom.app (op U)).hom s) hsImageUnit
    have hVCartesian := h V
    have hVLocal : IsLocalHom ((fSharp.hom.app (op V)).hom) :=
      (unitsSquareCartesian_iff_isLocalHom _).1 hVCartesian
    -- Naturality converts the target-side restricted unit into the image of the restricted source
    -- section, so localness of the objectwise map yields a source-side unit.
    have hsRestrImage :
        ((fSharp.hom.app (op V)).hom)
            (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s) =
          (𝒪C.1.map f.op).hom ((fSharp.hom.app (op U)).hom s) := by
      simpa [CategoryTheory.types_comp_apply] using
        congrFun (fSharp.hom.naturality f.op) s
    have hsRestrSourceUnit :
        IsUnit
          (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s) := by
      let _ : IsLocalHom ((fSharp.hom.app (op V)).hom) := hVLocal
      have hsRestrImageUnit :
          IsUnit
            (((fSharp.hom.app (op V)).hom)
              (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s)) := by
        rw [hsRestrImage]
        exact hsVUnit
      exact
        (isUnit_map_iff ((fSharp.hom.app (op V)).hom)
          (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s)).1
        hsRestrImageUnit
    -- The restricted source section represents the same germ as the original element.
    have hsRestrGerm :
        (p.toPresheafFiber V y
            (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1).hom
            (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s) =
          (p.toPresheafFiber U xU
            (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1).hom s := by
      simpa [hy] using
        congrArg (fun k ↦ k.hom s)
          (p.toPresheafFiber_w f y
            (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1)
    have hsGermUnit :
        IsUnit
          ((p.toPresheafFiber V y
              (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1).hom
            (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1.map f.op).hom s)) :=
      hsRestrSourceUnit.map
        ((p.toPresheafFiber V y
          (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D).1).hom)
    simpa [hsRestrGerm] using hsGermUnit
  have hRawCartesian : unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) :=
    (unitsSquareCartesian_iff_isLocalHom _).2 hRawLocal
  -- Transport the raw stalk result across the canonical comparison with the actual target stalk.
  simpa [pointStructureRingHom] using
    (unitsSquareCartesian_precompIso_iff
      ((p.sheafFiberComapIso F hF CommRingCat.{u}).app 𝒪D) (p.sheafFiber.map fSharp)).2
      hRawCartesian

variable (P : ObjectProperty JC.Point)

/-- Helper for Lemma 18.40.8: the source-facing cartesian-units condition on the actual induced
stalk map is equivalent to the same condition on the raw inverse-image stalk map used by
`p.sheafFiber.map fSharp`. -/
theorem rawStalkUnitsCartesian_of_actualStalkUnitsCartesian
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    (p : JC.Point) [InitiallySmall (F ⋙ p.fiber).Elements]
    (hActual :
      let φ :=
        (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
          ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
      unitsSquareCartesianForLocallyRingedMorphism φ) :
    unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := by
  -- Rewrite the actual stalk map as the raw inverse-image stalk map precomposed with the
  -- canonical comparison isomorphism on source stalks.
  simpa [pointStructureRingHom] using
    (unitsSquareCartesian_precompIso_iff
      ((p.sheafFiberComapIso F hF CommRingCat.{u}).app 𝒪D) (p.sheafFiber.map fSharp)).1
      hActual

/-- Helper for Lemma 18.40.8: the units subsheaf sits inside the underlying `Type`-valued sheaf
by forgetting that a section is a unit. -/
noncomputable def ringedSiteUnitsSubsheafInclusion
    (𝒪 : Sheaf JC CommRingCat.{u}) :
    SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪 ⟶
      (sheafCompose JC (forget CommRingCat)).obj 𝒪 :=
  -- Proof comment: this is the literal inclusion of the unit-valued subtype into the ambient
  -- section sheaf.
  ⟨{ app := fun U s ↦ s.1
      ,
      naturality := by
        intro U V f
        rfl }⟩

/-- Helper for Lemma 18.40.8: applying `f^\sharp` to a unit section of the inverse-image
structure sheaf yields a unit section of `\mathcal O_\mathcal C`. -/
noncomputable def inverseImageUnitsToTargetUnits :
    SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf
        (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D) ⟶
      SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪C :=
  -- Proof comment: the objectwise map is `f^\sharp` on the underlying section, together with the
  -- transported `IsUnit` proof.
  ⟨{ app := fun U s ↦
        ⟨(fSharp.hom.app U).hom s.1, s.2.map ((fSharp.hom.app U).hom)⟩
      ,
      naturality := by
        intro U V f
        funext s
        apply Subtype.ext
        simpa [CategoryTheory.types_comp_apply] using
          congrFun (fSharp.hom.naturality f) s.1 }⟩

/-- Helper for Lemma 18.40.8: the unit-valued image map and the underlying section map have the
same composite to the ambient sheaf of types. -/
theorem inverseImageUnitsToTargetUnits_comm :
    inverseImageUnitsToTargetUnits (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) ≫
        ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪C =
      ringedSiteUnitsSubsheafInclusion (JC := JC)
          (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D) ≫
        (sheafCompose JC (forget CommRingCat)).map fSharp := by
  -- Proof comment: both composites forget the unit witness and evaluate to the same section
  -- `(f^\sharp)_U(s)`.
  ext U s
  rfl

/-- Helper for Lemma 18.40.8: the global comparison from inverse-image units to the pullback of
the target units inclusion along `f^\sharp`. -/
noncomputable def inverseImageUnitsComparison :
    SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf
        (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D) ⟶
      pullback
        (ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪C)
        ((sheafCompose JC (forget CommRingCat)).map fSharp) :=
  -- Proof comment: the pullback mediator packages the target unit image and the original source
  -- section into the cartesian-units square.
  pullback.lift
    (inverseImageUnitsToTargetUnits (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp))
    (ringedSiteUnitsSubsheafInclusion (JC := JC)
      (inverseImageStructureSheafForLocallyRingedMorphism F 𝒪D))
    (inverseImageUnitsToTargetUnits_comm
      (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp))

/-- Helper for Lemma 18.40.8: the underlying germ of a unit-valued point section is a unit in the
stalk ring. -/
theorem pointUnitsSubsheafImage_isUnit
    (𝒪 : Sheaf JC CommRingCat.{u}) (p : JC.Point)
    (x : p.sheafFiber.obj
      (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪)) :
    IsUnit
      ((p.sheafFiber.map (ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪)) x) := by
  -- Represent the germ by a unit section and map that unit into the stalk ring.
  obtain ⟨U, xU, s, rfl⟩ := p.toPresheafFiber_jointly_surjective
    (P := (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1) x
  simpa [ringedSiteUnitsSubsheafInclusion, CategoryTheory.types_comp_apply] using
    s.2.map ((p.toPresheafFiber U xU 𝒪.1).hom)

/-- Helper for Lemma 18.40.8: the point fiber of the units subsheaf maps canonically to the
subtype of unit germs in the stalk ring. -/
noncomputable def pointUnitsSubsheafToUnitSubtype
    (𝒪 : Sheaf JC CommRingCat.{u}) (p : JC.Point) :
    p.sheafFiber.obj
        (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪) →
      {u : sourcePointRing 𝒪 p // IsUnit u} :=
  fun x ↦
    ⟨(p.sheafFiber.map (ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪)) x,
      pointUnitsSubsheafImage_isUnit (JC := JC) 𝒪 p x⟩

/-- Helper for Lemma 18.40.8: every unit germ in the stalk comes from a unique germ of a
unit-valued section. -/
theorem pointUnitsSubsheafToUnitSubtype_bijective
    (𝒪 : Sheaf JC CommRingCat.{u}) (p : JC.Point) :
    Function.Bijective (pointUnitsSubsheafToUnitSubtype (JC := JC) 𝒪 p) := by
  constructor
  · intro x y hxy
    -- Compare two unit germs on a common stage, then use proof irrelevance on the unit witness.
    obtain ⟨U, xU, s, t, rfl, rfl⟩ := p.toPresheafFiber_jointly_surjective₂
      (P := (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1) x y
    have hVal :
        (p.toPresheafFiber U xU 𝒪.1).hom s.1 =
          (p.toPresheafFiber U xU 𝒪.1).hom t.1 := by
      simpa [pointUnitsSubsheafToUnitSubtype, ringedSiteUnitsSubsheafInclusion,
        CategoryTheory.types_comp_apply] using congrArg Subtype.val hxy
    rcases (p.toPresheafFiber_eq_iff' (P := 𝒪.1) U xU s.1 t.1).1 hVal with
      ⟨V, f, y, hy, hst⟩
    have hSubtype :
        ((SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1.map f.op) s =
          ((SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1.map f.op) t := by
      apply Subtype.ext
      simpa using hst
    exact
      (p.toPresheafFiber_eq_iff'
        (P := (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1)
        U xU s t).2 ⟨V, f, y, hy, hSubtype⟩
  · intro u
    -- Choose a representative of the underlying germ, then shrink until that representative is
    -- already a unit section.
    obtain ⟨U, xU, s, hs⟩ := p.toPresheafFiber_jointly_surjective (P := 𝒪.1) u.1
    obtain ⟨V, f, y, hy, hsVUnit⟩ :=
      exists_isUnit_restriction_of_pointFiber_isUnit (𝒪 := 𝒪) p U xU s u.2
    refine ⟨p.toPresheafFiber V y
      (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1
      ⟨(𝒪.1.map f.op).hom s, hsVUnit⟩, ?_⟩
    apply Subtype.ext
    calc
      (p.sheafFiber.map (ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪))
          (p.toPresheafFiber V y
            (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪).1
            ⟨(𝒪.1.map f.op).hom s, hsVUnit⟩)
          = (p.toPresheafFiber V y 𝒪.1).hom ((𝒪.1.map f.op).hom s) := by
              rfl
      _ = (p.toPresheafFiber U xU 𝒪.1).hom s := by
            simpa [hy] using congrArg (fun k ↦ k.hom s) (p.toPresheafFiber_w f y 𝒪.1)
      _ = u.1 := hs

/-- Helper for Lemma 18.40.8: the point fiber of the units subsheaf identifies with the units of
the stalk ring. -/
noncomputable def pointUnitsSubsheafIso
    (𝒪 : Sheaf JC CommRingCat.{u}) (p : JC.Point) :
    p.sheafFiber.obj
        (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪) ≅
      Units (sourcePointRing 𝒪 p) :=
  ((Equiv.ofBijective
      (pointUnitsSubsheafToUnitSubtype (JC := JC) 𝒪 p)
      (pointUnitsSubsheafToUnitSubtype_bijective (JC := JC) 𝒪 p)).trans
    { toFun := fun u ↦ u.2.unit
      invFun := fun u ↦ ⟨u, u.isUnit⟩
      left_inv := fun u ↦ Subtype.ext rfl
      right_inv := fun u ↦ Units.ext rfl }).toIso

/-- Helper for Lemma 18.40.8: under the pointwise units identification, the image of a germ of a
unit section is its underlying stalk element. -/
theorem pointUnitsSubsheafIso_hom_val
    (𝒪 : Sheaf JC CommRingCat.{u}) (p : JC.Point)
    (x : p.sheafFiber.obj
      (SheafOfModules.RingedSite.UnderlyingTypes.ringedSiteUnitsSubsheaf 𝒪)) :
    ((pointUnitsSubsheafIso (JC := JC) 𝒪 p).hom x : sourcePointRing 𝒪 p) =
      (p.sheafFiber.map (ringedSiteUnitsSubsheafInclusion (JC := JC) 𝒪)) x := by
  rfl

-- Proof sketch: apply conservativity of the chosen family of point functors to the comparison map
-- from `f^{-1}(\mathcal O_\mathcal D^*)` to the pullback sheaf; if all canonical point-stalk
-- squares in the family are cartesian, then the comparison is an isomorphism globally.
/-- Lemma 18.40.8 (4): if a conservative family of points of the source site satisfies the
stalkwise cartesian units square condition, then the global units square for `f^\sharp` is
cartesian. -/
theorem inverseImageUnitsCartesian_of_stalkUnitsCartesian_of_conservativeFamily
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ (p : JC.Point) (_ : P p) [InitiallySmall (F ⋙ p.fiber).Elements],
      let φ :=
        (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
          ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
      unitsSquareCartesianForLocallyRingedMorphism φ) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := by
  -- Route correction: the remaining work is not the conservative-family reflection step itself,
  -- but one bridge identifying the point fiber of the global units-comparison morphism with the
  -- stalk-level `unitsSquareComparisonForLocallyRingedMorphism` after the canonical units-sheaf
  -- and `sheafFiberComapIso` transports.
  have hRaw :
      ∀ (p : JC.Point) (_ : P p) [InitiallySmall (F ⋙ p.fiber).Elements],
        unitsSquareCartesianForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom) := by
    intro p hp
    -- First transport the source-facing stalk hypothesis to the raw inverse-image stalk map that
    -- appears after applying the point fiber functor.
    exact rawStalkUnitsCartesian_of_actualStalkUnitsCartesian
      (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) hF p (h p hp)
  let comparison :=
    inverseImageUnitsComparison (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp)
  -- TODO: the global comparison object is now explicit. The remaining blocker is to identify
  -- `p.sheafFiber.map comparison` with the raw stalk comparison
  -- `unitsSquareComparisonForLocallyRingedMorphism ((p.sheafFiber.map fSharp).hom)` after
  -- normalizing the source with the stalk of the units subsheaf and the target with
  -- `PreservesPullback.iso` plus `Types.pullbackIsoPullback`.
  sorry

-- Proof sketch: with enough points, cartesianness of the units square can be checked stalkwise,
-- since the comparison morphism to the pullback is an isomorphism exactly when it is so on all
-- stalks.
/-- Lemma 18.40.8 (2): if the source site has enough points, the cartesian units square condition
for `f^\sharp` is equivalent to the stalkwise cartesian units square condition. -/
theorem inverseImageUnitsCartesian_iff_stalkUnitsCartesian_of_hasEnoughPoints
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    [GrothendieckTopology.HasEnoughPoints.{u} JC] :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp ↔
      ∀ (p : JC.Point) [InitiallySmall (F ⋙ p.fiber).Elements],
        let φ :=
          (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
            ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
        unitsSquareCartesianForLocallyRingedMorphism φ := by
  constructor
  · intro hCartesian p
    -- The forward clause is exactly the previously established stalk theorem.
    exact inverseImageUnitsCartesian_implies_stalkUnitsCartesian
      (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) hF hCartesian p
  · intro hStalk
    -- Route correction: under enough points, choose one conservative family and invoke the
    -- conservative-family converse instead of repeating the stalk-to-global reflection argument.
    obtain ⟨P, -, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty JC
    exact inverseImageUnitsCartesian_of_stalkUnitsCartesian_of_conservativeFamily
      (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) (P := P) hF hP
      (fun p _ ↦ hStalk p)

-- Proof sketch: for each source point `p`, the displayed cartesian-units condition is exactly the
-- ring-theoretic unit-reflection condition for the actual map on stalks.
/-- Companion bridge: the stalkwise cartesian units square condition at `p` is equivalent to the
ring-theoretic unit-reflection predicate `IsLocalHom` on the actual induced map on stalks. By
itself this does not assert that the stalk rings are local. -/
theorem stalkUnitsCartesian_iff_stalkMapsAreLocalHom
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    (p : JC.Point) [InitiallySmall (F ⋙ p.fiber).Elements] :
    let φ : sourcePointRing 𝒪D (p.comap F hF) →+* sourcePointRing 𝒪C p :=
      (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
        ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
    unitsSquareCartesianForLocallyRingedMorphism φ ↔ IsLocalHom φ := by
  -- This is the algebraic bridge above, specialized to the actual stalk map.
  change unitsSquareCartesianForLocallyRingedMorphism _ ↔ IsLocalHom _
  exact unitsSquareCartesian_iff_isLocalHom _

-- Proof sketch: combine the nontriviality clause built into `IsLocallyRingedSite` with the
-- stalkwise “zero or local” criterion from Lemma `18.40.2`; this rules out the zero case and
-- forces every point stalk ring to be local.
/-- In a locally ringed site, every point stalk ring is a local ring. -/
theorem sourcePointRing_isLocalRing
    {E : Type u} [Category.{u} E] {JE : GrothendieckTopology E}
    (𝒪 : Sheaf JE CommRingCat.{u}) [IsLocallyRingedSite 𝒪]
    (p : JE.Point) :
    IsLocalRing (sourcePointRing 𝒪 p) := by
  -- Nontriviality rules out the zero-ring branch in the stalkwise dichotomy.
  have hNontrivial : Nontrivial (sourcePointRing 𝒪 p) :=
    stalkwise_nontrivial_of_isIso_oneNeverZeroEqualizerMap (𝒪 := 𝒪) inferInstance p
  rcases stalkwise_zero_or_local_of_hasLocalUnitDichotomy (𝒪 := 𝒪) p with hSub | hLocal
  · exact False.elim ((not_subsingleton_iff_nontrivial.2 hNontrivial) hSub)
  · exact hLocal

/-- Lemma 18.40.8 (3): when both structure sheaves define locally ringed sites, the induced map on
stalks is a map between local rings, so `IsLocalHom` is equivalent to the usual maximal-ideal
criterion for local ring homomorphisms. -/
theorem pointStructureRingHom_isLocalHom_iff_comapMaximalIdeal
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (p : JC.Point) [InitiallySmall (F ⋙ p.fiber).Elements] :
    let _ : IsLocalRing (sourcePointRing 𝒪D (p.comap F hF)) :=
      sourcePointRing_isLocalRing 𝒪D (p.comap F hF)
    let _ : IsLocalRing (sourcePointRing 𝒪C p) := sourcePointRing_isLocalRing 𝒪C p
    let φ : sourcePointRing 𝒪D (p.comap F hF) →+* sourcePointRing 𝒪C p :=
      (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
        ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
    IsLocalHom φ ↔
      Ideal.comap φ (IsLocalRing.maximalIdeal (sourcePointRing 𝒪C p)) =
        IsLocalRing.maximalIdeal (sourcePointRing 𝒪D (p.comap F hF)) := by
  -- Between local rings, the canonical TFAE gives exactly the maximal-ideal criterion.
  let _ : IsLocalRing (sourcePointRing 𝒪D (p.comap F hF)) :=
    sourcePointRing_isLocalRing 𝒪D (p.comap F hF)
  let _ : IsLocalRing (sourcePointRing 𝒪C p) :=
    sourcePointRing_isLocalRing 𝒪C p
  change IsLocalHom _ ↔
    Ideal.comap _ (IsLocalRing.maximalIdeal (sourcePointRing 𝒪C p)) =
      IsLocalRing.maximalIdeal (sourcePointRing 𝒪D (p.comap F hF))
  simpa using (IsLocalRing.local_hom_TFAE (f := (_ : _ →+* _))).out 0 4

-- Proof sketch: convert the stalkwise `IsLocalHom` hypothesis into the stalkwise cartesian units
-- square hypothesis using the previous bridge equivalence, then apply the conservative-family
-- criterion.
/-- Companion bridge: if a conservative family of source points yields stalk maps satisfying
`IsLocalHom`, then the global units square for `f^\sharp` is cartesian. This is the ring-theoretic
bridge underlying Lemma 18.40.8 (5). -/
theorem inverseImageUnitsCartesian_of_stalkMapsAreLocalHom_of_conservativeFamily
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ (p : JC.Point) (_ : P p) [InitiallySmall (F ⋙ p.fiber).Elements],
      let φ : sourcePointRing 𝒪D (p.comap F hF) →+* sourcePointRing 𝒪C p :=
        (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
          ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
      IsLocalHom φ) :
    inverseImageUnitsCartesianForLocallyRingedMorphism F 𝒪C 𝒪D fSharp := by
  -- Convert the stalkwise local-hom hypotheses into the cartesian-units hypotheses required above.
  refine inverseImageUnitsCartesian_of_stalkUnitsCartesian_of_conservativeFamily
    (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) (P := P) hF hP ?_
  intro p hp
  dsimp
  exact
    (stalkUnitsCartesian_iff_stalkMapsAreLocalHom
      (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) hF p).2
      (h p hp)

-- Proof sketch: in the locally ringed setting, clause `(3)` identifies the stalkwise
-- cartesian-units condition with the textbook local-ring-homomorphism condition on the induced
-- stalk maps. Combining that source-facing clause with the conservative-family criterion yields
-- the canonical owner condition that `f^\sharp` defines a morphism of locally ringed topoi.
/-- Lemma 18.40.8 (5): if both structure sheaves define locally ringed sites and a conservative
family of source points yields local ring maps on the actual target stalk maps
`\mathcal O_{D,p.comap F hF} \to \mathcal O_{C,p}`, then the global units square for `f^\sharp`
is cartesian, equivalently `f^\sharp` is a morphism of locally ringed topoi. -/
theorem isMorphismOfLocallyRingedTopoi_of_stalkMapsAreLocal_of_conservativeFamily
    [RepresentablyFlat F]
    (hF : CoverPreserving JD JC F)
    [IsLocallyRingedSite 𝒪C] [IsLocallyRingedSite 𝒪D]
    (hP : P.IsConservativeFamilyOfPoints)
    (h : ∀ (p : JC.Point) (_ : P p) [InitiallySmall (F ⋙ p.fiber).Elements],
      let φ : sourcePointRing 𝒪D (p.comap F hF) →+* sourcePointRing 𝒪C p :=
        (pointStructureRingHom F 𝒪C 𝒪D p (p.comap F hF)
          ((p.sheafFiberComapIso F hF CommRingCat.{u}).symm) fSharp).hom
      IsLocalHom φ) :
    IsMorphismOfLocallyRingedTopoi F 𝒪C 𝒪D fSharp := by
  -- Package the global cartesian-units condition as the unique field of the owner class.
  exact ⟨inverseImageUnitsCartesian_of_stalkMapsAreLocalHom_of_conservativeFamily
    (F := F) (𝒪C := 𝒪C) (𝒪D := 𝒪D) (fSharp := fSharp) (P := P) hF hP h⟩

end

end CategoryTheory
