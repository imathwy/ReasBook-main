import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_31_1 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open TopCat
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]
variable (𝒜 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (𝒝 : Under 𝒜)

/- Domain-style sampling for Definition 17.31.1:
- primary domain: naive cotangent complexes of sheaves of `\mathcal A`-algebras on a space `X`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationNaiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`;
- best owner abstraction: the generic site-level owner
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site
  `Opens.grothendieckTopology X`;
- primitive data: the opens-site Grothendieck topology on `X`, the sheaf of rings `𝒜`, and the
  `𝒜`-algebra sheaf `𝒝 : Under 𝒜`;
- derived API: the opens-site specialization itself and its degree `-1/0` identification theorems,
  already owned upstream by Chapter 18.

Source/core/bridge triage:
- `source-facing`: the naive cotangent complex `NL_{\mathcal B/\mathcal A}` on a topological
  space;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: this file is only the opens-site specialization, so it should recall the
  canonical owner rather than maintain a second parallel definition. -/

/- Definition 17.31.1: for sheaves of rings `\mathcal A → \mathcal B` on a topological space
`X`, the naive cotangent complex `NL_{\mathcal B/\mathcal A}` is the canonical Chapter 18 owner
`SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site
`Opens.grothendieckTopology X`. -/
noncomputable abbrev naiveCotangent :
    CochainComplex
      (SheafOfModules (ringSheaf (Opens.grothendieckTopology X) 𝒝.right)) ℤ :=
  SheafOfModules.RingedSite.naiveCotangent
    (J := Opens.grothendieckTopology X) 𝒜 𝒝

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of `NL_{\mathcal B/\mathcal A}` is the conormal source
`\mathcal I/\mathcal I^2` of the canonical presentation `\mathcal A[\mathcal B] \to \mathcal B`.
-/
theorem naiveCotangent_X_negOne :
    (naiveCotangent 𝒜 𝒝).X (-1) =
      SheafOfModules.RingedSite.conormalSource (presentationMap 𝒜 𝒝) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_negOne
      (J := Opens.grothendieckTopology X) 𝒜 𝒝)

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of `NL_{\mathcal B/\mathcal A}` is the tensor term
`\mathcal B \otimes_{\mathcal A[\mathcal B]}
  \Omega_{\mathcal A[\mathcal B]/\mathcal A}` of the canonical presentation. -/
theorem naiveCotangent_X_zero :
    (naiveCotangent 𝒜 𝒝).X 0 =
      SheafOfModules.RingedSite.conormalTensorTerm
        (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_zero
      (J := Opens.grothendieckTopology X) 𝒜 𝒝)

end TopCat.Sheaf

/-! ### Lemma_17_31_2 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open TopCat
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]

local notation "JX" => Opens.grothendieckTopology X

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (CategoryTheory.Sheaf JX CommRingCat.{u}) := by
  simpa [TopCat.Sheaf] using
    (inferInstance : HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X))

variable (𝒜 : X.Sheaf CommRingCat.{u}) (𝒝 : Under 𝒜)

local notation "ModB" => SheafOfModules (ringSheaf JX 𝒝.right)
local notation "DModB" => DerivedCategory ModB

local instance : HasDerivedCategory ModB :=
  HasDerivedCategory.standard ModB

/- Domain-style sampling for Lemma 17.31.2:
- primary domain: presentation-independence of naive cotangent complexes for sheaves of
  `\mathcal A`-algebras on the opens site of a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.presentationVariables`,
  `SheafOfModules.RingedSite.presentationNaiveCotangentOf`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.presentationNaiveCotangent_iso`;
- best owner abstraction: the Chapter 18 site-level comparison theorem
  `presentationNaiveCotangent_iso`, specialized to `JX = Opens.grothendieckTopology X`;
- primitive data: a sheaf of sets `E`, a locally surjective map
  `α : E ⟶ presentationVariables 𝒝`, and the resulting presentation
  `presentationMapOf 𝒜 𝒝 E α : \mathcal A[E] ⟶ \mathcal B`;
- derived API: the derived-category objects
  `Q.obj (presentationNaiveCotangentOf E α)` and
  `Q.obj (SheafOfModules.RingedSite.naiveCotangent 𝒜 𝒝)`.

Source/core/bridge triage:
- `source-facing`: the statement that the naive cotangent complex attached to a chosen
  presentation of `\mathcal B` is isomorphic in `D(\mathcal B)` to the canonical
  `NL_{\mathcal B/\mathcal A}`;
- `core/canonical`: the site-level owners `presentationNaiveCotangentOf`, `naiveCotangent`, and
  `presentationNaiveCotangent_iso`;
- `bridge/view`: this file is only the opens-site specialization, so it should recall the Chapter
  18 owner theorem directly rather than introduce a second named theorem with the same interface. -/

/- Lemma 17.31.2: for a locally surjective presentation
`α : E ⟶ presentationVariables 𝒝` of the `\mathcal A`-algebra sheaf `\mathcal B`, the
presentationwise naive cotangent complex and the canonical naive cotangent complex determine
canonically isomorphic objects of `D(\mathcal B)`. This is exactly the Chapter 18 owner theorem
`presentationNaiveCotangent_iso`, specialized to the opens site of `X`. -/
recall presentationNaiveCotangent_iso

end TopCat.Sheaf

/-! ### Lemma_17_31_3 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}}
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts (X.Sheaf CommRingCat.{u})]
variable [Limits.HasBinaryCoproducts (Y.Sheaf CommRingCat.{u})]

/- Domain-style sampling for Lemma 17.31.3:
- primary domain: inverse-image compatibility for the naive cotangent complex of a morphism of
  sheaves of commutative rings on a topological space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `TopCat.Sheaf.inverseImage_relativeDifferentialsIso`,
  `CategoryTheory.Functor.mapHomologicalComplex`;
- best owner abstraction: the source-facing owner is the whole two-term complex
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site of `X`, not only its
  degree-`0` relative-differentials term;
- primitive data: the morphism `φ : O₁ ⟶ O₂`, the actual inverse-image functor on
  `O₂`-module sheaves, and the pulled-back morphism `(pullback CommRingCat f).map φ`;
- derived API: the named complex isomorphism `inverseImage_naiveCotangentIso` and its thin
  theorem-level `IsIsomorphic` companion between the actual inverse image of the opens-site
  specialization `naiveCotangent (J := Opens.grothendieckTopology X) O₁ (Under.mk φ)` and the
  pulled-back opens-site specialization, transported across `pullbackRingSheafIso f O₂`.

Source/core/bridge triage:
- `source-facing`: the canonical identification
  `f^{-1} NL_{\mathcal O_2 / \mathcal O_1} = NL_{f^{-1}\mathcal O_2 / f^{-1}\mathcal O_1}`;
- `core/canonical`: `SheafOfModules.RingedSite.naiveCotangent`, `pullbackRingSheafIso`, and
  `Functor.mapHomologicalComplex`;
- `bridge/view`: this file should expose the inverse-image comparison by the actual complex
  isomorphism over the raw pulled-back `RingCat`-valued structure sheaf, with `IsIsomorphic`
  retained only as the thin theorem companion. -/

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)] in
/-- The inverse image of the naive cotangent complex is canonically isomorphic, as a cochain
complex, to the naive cotangent complex of the pulled-back morphism. -/
noncomputable def inverseImage_naiveCotangentIso
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    (((SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).mapHomologicalComplex
      (up ℤ)).obj
      (naiveCotangent O₁ (Under.mk φ))) ≅
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent
          ((pullback CommRingCat.{u} f).obj O₁)
          (Under.mk ((pullback CommRingCat.{u} f).map φ)))) := by
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
  [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)] in
/-- The inverse image of the naive cotangent complex is canonically identified with the naive
cotangent complex of the pulled-back morphism. This is the theorem-level `IsIsomorphic` companion
to `inverseImage_naiveCotangentIso`. -/
theorem inverseImage_naiveCotangent_isIsomorphic
    (f : Y ⟶ X) (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent O₁ (Under.mk φ)))
      (((SheafOfModules.restrictScalars
          (pullbackRingSheafIso f O₂).inv).mapHomologicalComplex
        (up ℤ)).obj
        (naiveCotangent
          ((pullback CommRingCat.{u} f).obj O₁)
          (Under.mk ((pullback CommRingCat.{u} f).map φ)))) := by
  exact ⟨inverseImage_naiveCotangentIso f φ⟩

end TopCat.Sheaf

/-! ### Lemma_17_31_4 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace ComplexShape
open PresheafOfModules.DifferentialsConstruction
open TopCat.Presheaf
open scoped NaiveCotangent TensorProduct ZeroObject

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X) := by
  simpa [TopCat.Sheaf] using
    (inferInstance :
      HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}))

private abbrev asCommModulePresheaf
    (O : X.Sheaf CommRingCat.{u}) (ℱ : SheafOfModules (ringSheaf O)) :
    PresheafOfModules (O.obj ⋙ forget₂ CommRingCat RingCat) :=
  ℱ.val

/- Domain-style sampling for Lemma 17.31.4:
- primary domain: naive cotangent complexes of morphisms of sheaves of commutative rings, together
  with their stalkwise realization on local rings;
- sampled owner declarations:
  `TopCat.Sheaf.naiveCotangent`,
  `CommRingCat.Hom.naiveCotangent`,
  `CategoryTheory.point_stalk_ring`,
  `CategoryTheory.point_sheaf_module_stalk_functor`,
  `CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `SheafOfModules.RingedSite.conormalSource`,
  `SheafOfModules.RingedSite.conormalTensorTerm`,
  `SheafOfModules.RingedSite.conormalMap`;
- best owner abstraction: the source-facing owner statement should compare the site-point stalk of
  `TopCat.Sheaf.naiveCotangent` with the commutative-ring morphism owner
  `CommRingCat.Hom.naiveCotangent` for the induced stalk map, i.e. the map-level view of the
  Chapter 10 owner `Algebra.naiveCotangent`; the actual stalked sheaf complex is therefore
  bridge/view data obtained from the canonical site-point module-stalk functor, retargeted to the
  actual topological-space stalk ring, and then `Functor.mapHomologicalComplex`;
- primitive data: a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings and a point `x : X`;
- derived API: the bridge/view complex `stalkedNaiveCotangent O₁ O₂ φ x`, the comparison
  theorem `stalkedNaiveCotangent_isIsomorphic O₁ O₂ φ x` from the explicit stalk complex model to
  the canonical Chapter 10 owner `Algebra.naiveCotangent (stalkRing O₁ x) (stalkRing O₂ x)` of
  the induced stalk morphism,
  the explicit degree `-1/0` identifications and `-1 → 0` differential of the bridge/view
  complex, and the companion
  `relativeDifferentials_stalkIso` for the older degree-`0` differentials statement.

Source/core/bridge triage:
- `source-facing`: the comparison
  `NL_{\mathcal O_2/\mathcal O_1, x}` as the naive cotangent complex of the induced stalk map in
  the canonical Chapter 10 owner category, together with its explicit two-term stalk model;
- `core/canonical`: `TopCat.Sheaf.naiveCotangent`,
  `point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O₂)`,
  `point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (ringSheaf O₂)`,
  `pointGrothendieckTopology_presheafFiber_obj_iso_stalk`,
  `Functor.mapHomologicalComplex`, `CommRingCat.Hom.naiveCotangent`, `Algebra.naiveCotangent`,
  `Algebra.Extension.naiveCotangentChainComplex`,
  `presentationBase`, `presentationMap`, `conormalSource`, `conormalTensorTerm`, `conormalMap`,
  and `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: this file specializes the canonical site-point stalk owner to the opens site of
  `X`, retargets it to the commutative stalk ring, and records the explicit `-1`, `0`, and
  `d(-1,0)` pieces of the resulting bridge complex `stalkedNaiveCotangent`; the induced-stalk
  owner itself is the canonical Chapter 10 object
  `Algebra.naiveCotangent (stalkRing O₁ x) (stalkRing O₂ x)`.

This file should therefore expose the main stalk statement by an actual comparison with the
Chapter 10 stalk-map owner, and treat the direct site-point stalk complex only as the bridge/view
realizing that comparison. -/

private abbrev pointCommPresheafStalk
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    CommRingCat.{u} :=
  (Opens.pointGrothendieckTopology x).presheafFiber.obj O.obj

private abbrev pointStalkRingEquivPointCommPresheafStalk
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ↑(point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O)) ≃+*
      ↑(pointCommPresheafStalk O x) :=
  ((Opens.pointGrothendieckTopology x).presheafFiberCompIso
    (forget₂ CommRingCat RingCat)).app O.obj |>.ringCatIsoToRingEquiv

private abbrev pointStalkRingEquivStalkRing
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    ↑(point_stalk_ring (Opens.pointGrothendieckTopology x) (ringSheaf O)) ≃+*
      ↑((stalkFunctor CommRingCat x).obj O.obj) :=
  (pointStalkRingEquivPointCommPresheafStalk O x).trans
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (CategoryTheory.pointGrothendieckTopology_presheafFiber_obj_iso_stalk x O.obj))

noncomputable abbrev stalkModuleFunctor
    (O : X.Sheaf CommRingCat.{u}) (x : X) :
    SheafOfModules (ringSheaf O) ⥤
      ModuleCat ((stalkFunctor CommRingCat x).obj O.obj) :=
  point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (ringSheaf O) ⋙
    ModuleCat.restrictScalars (pointStalkRingEquivStalkRing O x).symm.toRingHom

private abbrev stalkRing (O : X.Sheaf CommRingCat.{u}) (x : X) : CommRingCat :=
  (stalkFunctor CommRingCat x).obj O.obj

private abbrev stalkRingHom
    {O O' : X.Sheaf CommRingCat.{u}} (φ : O ⟶ O') (x : X) :
    stalkRing O x ⟶ stalkRing O' x :=
  (stalkFunctor CommRingCat x).map φ.hom

private abbrev stalkKaehlerDifferential
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
  ModuleCat (stalkRing O₂ x) :=
  CommRingCat.KaehlerDifferential (stalkRingHom φ x)

private noncomputable def relativeDifferentialsGermHom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    (U : Opens X) (hx : x ∈ U) :
    ((relativeDifferentials' φ.hom).presheaf.obj (Opposite.op U)) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) := by
  let comparison :=
    CommRingCat.KaehlerDifferential.map
      (by
        simpa using stalkFunctor_map_germ U x hx φ.hom)
  exact AddCommGrpCat.ofHom
    { toFun := fun m ↦ comparison m
      map_zero' := by
        exact comparison.hom.map_zero
      map_add' := by
        intro m n
        exact comparison.hom.map_add m n }

private noncomputable def relativeDifferentialsNhdsGermHom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) := by
  exact show (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).obj U) ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) from
    relativeDifferentialsGermHom O₁ O₂ φ x (Opposite.unop U).1 (Opposite.unop U).2

private theorem relativeDifferentialsNhdsGermHom_naturality
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X)
    {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf).map i) ≫
        relativeDifferentialsNhdsGermHom O₁ O₂ φ x V =
      relativeDifferentialsNhdsGermHom O₁ O₂ φ x U := sorry

private def presheafRelativeDifferentialsStalkComparison
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    stalk (relativeDifferentials' φ.hom).presheaf x ⟶
      AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (relativeDifferentials' φ.hom).presheaf) <|
    Cocone.mk _ <|
      { app := fun U ↦ relativeDifferentialsNhdsGermHom O₁ O₂ φ x U
        naturality := by
          intro U V i
          exact relativeDifferentialsNhdsGermHom_naturality O₁ O₂ φ x i }

private instance instStalkModule
    (O : X.Sheaf CommRingCat.{u}) (ℱ : SheafOfModules (ringSheaf O)) (x : X) :
    Module ((stalkFunctor CommRingCat x).obj O.obj)
      ↑(stalk ℱ.val.presheaf x) := by
  simpa [asCommModulePresheaf] using
    (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (asCommModulePresheaf O ℱ) x)

private noncomputable def relativeDifferentialsStalkComparison_hom
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat.of (stalkRing O₂ x)
      ↑(stalk Ω(φ).val.presheaf x) ⟶
      stalkKaehlerDifferential O₁ O₂ φ x := by
  letI : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  letI :
      (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  let η :
      stalk (relativeDifferentials' φ.hom).presheaf x ⟶
      stalk Ω(φ).val.presheaf x :=
    (stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) (relativeDifferentials' φ.hom).presheaf)
  haveI : IsIso η := by
    simpa [relativeDifferentials] using
      (stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
        (relativeDifferentials' φ.hom).presheaf)
  let comparison :
      stalk Ω(φ).val.presheaf x ⟶
        AddCommGrpCat.of ↑(stalkKaehlerDifferential O₁ O₂ φ x) :=
    inv η ≫ presheafRelativeDifferentialsStalkComparison O₁ O₂ φ x
  exact ModuleCat.ofHom
    { toFun := comparison
      map_add' := by
        intro m n
        simpa [comparison] using comparison.hom.map_add m n
      map_smul' := by
        intro r m
        sorry }

private theorem relativeDifferentialsStalkComparison_hom_isIso
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    IsIso (relativeDifferentialsStalkComparison_hom O₁ O₂ φ x) := sorry

/-- The canonical stalk comparison for relative differentials
`(Ω_{O₂/O₁})_x ≅ Ω_{(O₂)_x/(O₁)_x}`. This is the companion degree-`0` differentials bridge used
in Lemma `17.28.7`, not the whole naive cotangent complex comparison of Lemma `17.31.4`. -/
noncomputable def relativeDifferentials_stalkIso
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat.of
      ((stalkFunctor CommRingCat x).obj O₂.obj)
      ↑(stalk Ω(φ).val.presheaf x) ≅
      CommRingCat.KaehlerDifferential ((stalkFunctor CommRingCat x).map φ.hom) := by
  letI := relativeDifferentialsStalkComparison_hom_isIso O₁ O₂ φ x
  exact asIso (relativeDifferentialsStalkComparison_hom O₁ O₂ φ x)

/-- The stalked naive cotangent complex `NL_{\mathcal O_2/\mathcal O_1, x}`, obtained by taking
the stalk of the opens-site owner `NL_{\mathcal O_2/\mathcal O_1}` via the canonical site-point
module-stalk functor, retargeted to the actual topological-space stalk ring
`(\mathcal O_2)_x`, and then `Functor.mapHomologicalComplex`. This is a thin bridge/view
abbreviation, not a second owner. -/
noncomputable abbrev stalkedNaiveCotangent
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    CochainComplex
      (ModuleCat ((stalkFunctor CommRingCat x).obj O₂.obj)) ℤ :=
  (((stalkModuleFunctor O₂ x).mapHomologicalComplex (up ℤ)).obj
    (naiveCotangent O₁ (Under.mk φ)))

/-- Lemma 17.31.4: the stalk of the opens-site naive cotangent complex is canonically
isomorphic, after passing from the explicit stalk cochain model to the derived owner category, to
the Chapter 10 naive cotangent complex of the induced stalk morphism
`(\mathcal O_1)_x \to (\mathcal O_2)_x`, written on the explicit ring-morphism surface as
`CommRingCat.Hom.naiveCotangentObject (stalkRingHom φ x)`. This is the source-facing owner
statement; the direct site-point stalk
complex `stalkedNaiveCotangent` is only its bridge/view realization, while the target remains the
canonical owner `NL_{(stalkRing O₂ x)⁄(stalkRing O₁ x)}` for the stalk algebra structure induced
by `stalkRingHom φ x`. The statement is kept theorem-level so no chosen isomorphism witness
enters the public API. -/
theorem stalkedNaiveCotangent_isIsomorphic
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    IsIsomorphic
      (DerivedCategory.Q.obj (stalkedNaiveCotangent O₁ O₂ φ x))
      (CommRingCat.Hom.naiveCotangentObject (stalkRingHom φ x)) := by
  sorry

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of the stalked naive cotangent complex is the stalk of the conormal
source sheaf of the canonical presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_X_negOne
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).X (-1) =
      (stalkModuleFunctor O₂ x).obj
        (SheafOfModules.RingedSite.conormalSource
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  exact
    congrArg
      ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_negOne O₁ (Under.mk φ))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of the stalked naive cotangent complex is the stalk of the tensor term
`conormalTensorTerm (presentationBase O₁ (Under.mk φ)) (presentationMap O₁ (Under.mk φ))`. -/
theorem stalkedNaiveCotangent_X_zero
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).X 0 =
      (stalkModuleFunctor O₂ x).obj
        (SheafOfModules.RingedSite.conormalTensorTerm
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  exact
    congrArg
      ((stalkModuleFunctor O₂ x).obj)
      (naiveCotangent_X_zero O₁ (Under.mk φ))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The differential in degrees `-1 → 0` of the stalked naive cotangent complex is the map on
stalks induced by the canonical conormal map of the presentation
`\mathcal O_1[\mathcal O_2] \to \mathcal O_2`. -/
theorem stalkedNaiveCotangent_d_negOne_zero
    (O₁ O₂ : X.Sheaf CommRingCat.{u}) (φ : O₁ ⟶ O₂) (x : X) :
    (stalkedNaiveCotangent O₁ O₂ φ x).d (-1) 0 =
      (stalkModuleFunctor O₂ x).map
        (SheafOfModules.RingedSite.conormalMap
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ))) := by
  change
    (stalkModuleFunctor O₂ x).map
      ((naiveCotangent O₁ (Under.mk φ)).d (-1) 0) =
      (stalkModuleFunctor O₂ x).map
        (SheafOfModules.RingedSite.conormalMap
          (SheafOfModules.RingedSite.presentationBase O₁ (Under.mk φ))
          (SheafOfModules.RingedSite.presentationMap O₁ (Under.mk φ)))
  rfl

end TopCat.Sheaf

/-! ### Lemma_17_31_5 (from Chap17) -/
open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

/-- The category of `\mathcal O`-module cochain complexes indexed by `\mathbb Z`. -/
abbrev SheafModuleComplex
    {X : TopCat.{u}} (O : X.Sheaf CommRingCat.{u}) :=
  CochainComplex (SheafOfModules (ringSheaf O)) ℤ

/-- The desuspension `K[-1]` of a cochain complex of sheaves of modules. -/
abbrev cochainDesuspension
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}} (K : SheafModuleComplex O) :
    SheafModuleComplex O :=
  (CochainComplex.shiftFunctor _ (-1)).obj K

/-- The cohomology sheaf `H^n(K)` of a cochain complex of sheaves of modules. -/
abbrev cohomologySheaf
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}} (K : SheafModuleComplex O) (n : ℤ) :=
  HomologicalComplex.homology K n

-- Proof sketch: construct the comparison map
-- `NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C ⟶
--   (mappingCone comparison)[-1]`
-- from the functoriality morphism to `NL_{\mathcal C/\mathcal A}` together with the explicit
-- null-homotopy of Remark `10.134.5`, transported to sheaves. Then identify the induced maps on
-- `H^0` and `H^{-1}` stalkwise via Lemma `17.31.4` and apply the algebraic Jacobi-Zariski result
-- `10.134.4`.
/-- Lemma 17.31.5: if `comparison : NL_{\mathcal C/\mathcal A} ⟶ NL_{\mathcal C/\mathcal B}` is
the canonical morphism of naive cotangent complexes of `\mathcal C`-modules and
`NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C` denotes the corresponding base-change
complex, then there is a canonical map
`NL_{\mathcal B/\mathcal A} \otimes_{\mathcal B} \mathcal C ⟶ Cone(comparison)[-1]`.
Moreover, its induced map on `H^0` is an isomorphism and its induced map on `H^{-1}` is an
epimorphism, which is the input needed for the canonical six-term exact cohomology sequence in the
source statement. -/
theorem naiveCotangent_transitivity_map_exists_with_homology_control
    {X : TopCat.{u}} {O : X.Sheaf CommRingCat.{u}}
    (naiveCotangentTensor : SheafModuleComplex O)
    (naiveCotangentOverA naiveCotangentOverB : SheafModuleComplex O)
    (comparison : naiveCotangentOverA ⟶ naiveCotangentOverB)
    [HomologicalComplex.HasHomotopyCofiber comparison] :
    ∃ c :
      naiveCotangentTensor ⟶
        cochainDesuspension (CochainComplex.mappingCone comparison),
      IsIso (HomologicalComplex.homologyMap c 0) ∧
        Epi (HomologicalComplex.homologyMap c (-1)) := sorry

end TopCat.Sheaf

/-! ### Definition_17_31_6 (from Chap17) -/
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open TopCat.Sheaf
open scoped ZeroObject AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

private instance topCatSheaf_hasBinaryCoproducts :
    HasBinaryCoproducts (TopCat.Sheaf CommRingCat.{u} X) := by
  simpa [TopCat.Sheaf] using
    (inferInstance :
      HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}))

/- Domain-style sampling for Definition 17.31.6:
- primary domain: naive cotangent complexes of morphisms of ringed spaces;
- sampled owner declarations:
  `inverseImageStructureSheafHomComm`,
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `Algebra.naiveCotangent`;
- best owner abstraction: the source-facing ringed-space complex `NL_f`, obtained as the thin
  specialization of the site-level owner `SheafOfModules.RingedSite.naiveCotangent` to the opens
  site of `X`, along the inverse-image structure-sheaf morphism
  `inverseImageStructureSheafHomComm f`;
- primitive data: only the inverse-image structure sheaf `f⁻¹𝒪_Y` and the induced `Under` object
  `f⁻¹𝒪_Y ⟶ 𝒪_X`;
- derived API: the source-facing notation `NL[f]` for textbook `NL_f` and the degree `-1/0`
  identification lemmas obtained from the site-level owner.

Source/core/bridge triage:
- `source-facing`: the notation `NL[f]`, the Lean surface for textbook
  `NL_f = NL_{\mathcal O_X / f^{-1}\mathcal O_Y}`;
- `core/canonical`: the Chapter 18 site-level owner
  `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: the specialization from an arbitrary sheaf of `\mathcal A`-algebras to the
  inverse-image structure-sheaf morphism of a ringed-space map.
-/

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/- Definition 17.31.6: for a morphism of ringed spaces `f : X ⟶ Y`, the naive cotangent complex
`NL_f` is the opens-site specialization of the Chapter 18 site-level owner
`NL_{\mathcal O_X / f^{-1}\mathcal O_Y}` along the canonical inverse-image structure-sheaf
morphism `f^{-1}\mathcal O_Y ⟶ \mathcal O_X`. -/
scoped[AlgebraicGeometry] notation:max "NL[" f "]" =>
  SheafOfModules.RingedSite.naiveCotangent _ <|
    Under.mk (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

end AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

open RingedSpace.Hom

variable {X Y : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) CommRingCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})]

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `-1` term of `NL[f]` is the conormal sheaf `\mathcal I/\mathcal I^2` of the
canonical presentation of `\mathcal O_X` over `f^{-1}\mathcal O_Y`. -/
theorem naiveCotangent_X_negOne (f : X ⟶ Y) :
    (NL[f]).X (-1) =
      conormalSource
        (presentationMap _ (Under.mk (inverseImageStructureSheafHomComm f))) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_negOne
      _ (Under.mk (inverseImageStructureSheafHomComm f)))

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- The degree `0` term of `NL[f]` is the canonical tensor term
`\mathcal O_X \otimes_{f^{-1}\mathcal O_Y[\mathcal O_X]}
  \Omega_{f^{-1}\mathcal O_Y[\mathcal O_X]/f^{-1}\mathcal O_Y}`. -/
theorem naiveCotangent_X_zero (f : X ⟶ Y) :
    (NL[f]).X 0 =
      conormalTensorTerm
        (presentationBase _ (Under.mk (inverseImageStructureSheafHomComm f)))
        (presentationMap _ (Under.mk (inverseImageStructureSheafHomComm f))) := by
  simpa using
    (SheafOfModules.RingedSite.naiveCotangent_X_zero
      _ (Under.mk (inverseImageStructureSheafHomComm f)))

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_17_31_7 (from Chap17) -/
open CategoryTheory
open CategoryTheory.ComposableArrows
open AlgebraicGeometry
open TopCat
open TopCat.Sheaf

noncomputable section

universe u

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of `\mathcal O_X`-module cochain complexes attached to a ringed space `X`. -/
abbrev ringedSpaceModuleComplex (X : RingedSpace.{u}) :=
  CochainComplex (SheafOfModules (ringedSpaceRingCatSheaf X)) ℤ

/-- The linearized six-term cohomology segment attached to a morphism
`c : f^*NL_{Y/Z} ⟶ Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1]`. It is written as
`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z}) ⟶
H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`. -/
noncomputable def ringedSpace_naiveCotangent_six_term_segment
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)] :
    ComposableArrows (SheafOfModules (ringedSpaceRingCatSheaf X)) 5 :=
  mk₅
    (HomologicalComplex.homologyMap (c ≫ CochainComplex.mappingCocone.fst comparison) (-1))
    (HomologicalComplex.homologyMap comparison (-1))
    (CochainComplex.homologyδOfTriangle (CochainComplex.mappingCocone.triangle comparison) (-1) 0 ≫
      @inv _ _ _ _ (HomologicalComplex.homologyMap c 0) hc0)
    (HomologicalComplex.homologyMap (c ≫ CochainComplex.mappingCocone.fst comparison) 0)
    (HomologicalComplex.homologyMap comparison 0)

-- Proof sketch: compare the standard exact five-arrow homology segment of the mapping-cocone
-- triangle for `comparison` with the segment obtained by transporting the cocone term along `c`.
-- The isomorphism on `H^0` transports the boundary map, and the epimorphism on `H^{-1}` preserves
-- the image of the first map.
/-- Lemma 17.31.7 (1): for a chosen transitivity map
`f^*NL_{Y/Z} ⟶ Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1]` whose induced map on `H^0` is an isomorphism and on
`H^{-1}` is an epimorphism, the associated six-term cohomology segment
`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z}) ⟶
H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`
is exact. -/
theorem ringedSpace_naiveCotangent_six_term_segment_exact
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    [Epi (HomologicalComplex.homologyMap c (-1))] :
    (ringedSpace_naiveCotangent_six_term_segment
      pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY comparison c).Exact := sorry

-- Proof sketch: the long exact homology sequence of the mapping-cocone triangle ends with
-- `H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y}) ⟶ H^1(Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1])`. Transport the last term
-- across the `H^0`-isomorphism induced by `c`, and use the vanishing of `H^1(f^*NL_{Y/Z})`.
/-- Lemma 17.31.7 (2): if `H^1(f^*NL_{Y/Z}) = 0`, then the final map
`H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})` in the six-term sequence is an epimorphism, i.e. the displayed
sequence continues with `H^0(NL_{X/Y}) ⟶ 0`. -/
theorem ringedSpace_naiveCotangent_h0_map_epi
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    (hH1 : Limits.IsZero (HomologicalComplex.homology pullbackNaiveCotangent 1)) :
    Epi (HomologicalComplex.homologyMap comparison 0) := sorry
