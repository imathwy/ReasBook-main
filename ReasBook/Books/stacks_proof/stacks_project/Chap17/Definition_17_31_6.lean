import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open TopCat.Sheaf
open scoped ZeroObject AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type u)]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/-- Helper for Definition 17.31.6: the underlying sheaf of sets of an `𝒜`-algebra sheaf. -/
abbrev presentationVariables
    {𝒜 : Sheaf J CommRingCat.{u}}
    (𝒝 : Under 𝒜) :
    Sheaf J (Type u) :=
  (sheafForget J).obj 𝒝.right

/-- Helper for Definition 17.31.6: the free commutative ring sheaf on a sheaf of sets. -/
abbrev presentationFreeSheaf
    (E : Sheaf J (Type u)) :
    Sheaf J CommRingCat.{u} :=
  (Sheaf.composeAndSheafify J CommRingCat.free).obj E

/-- Helper for Definition 17.31.6: the free `𝒜`-algebra sheaf on `E`. -/
abbrev presentationSheafOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (E : Sheaf J (Type u)) :
    Sheaf J CommRingCat.{u} :=
  ((Under.costar 𝒜).obj (presentationFreeSheaf E)).right

scoped[SheafOfModules.RingedSite] notation:max 𝒜:max "[" E "]" =>
  presentationSheafOf 𝒜 E

open scoped SheafOfModules.RingedSite

/-- Helper for Definition 17.31.6: the structure morphism `𝒜 ⟶ 𝒜[E]`. -/
abbrev presentationBaseOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (E : Sheaf J (Type u)) :
    𝒜 ⟶ 𝒜[E] :=
  ((Under.costar 𝒜).obj (presentationFreeSheaf E)).hom

/-- Helper for Definition 17.31.6: the free evaluation map induced by a map of generators. -/
private abbrev presentationFreeMap
    {𝒜 : Sheaf J CommRingCat.{u}}
    (𝒝 : Under 𝒜)
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables 𝒝) :
    presentationFreeSheaf E ⟶ 𝒝.right :=
  ((Sheaf.adjunction J CommRingCat.adj).homEquiv E 𝒝.right).symm α

/-- Helper for Definition 17.31.6: the induced `𝒜`-algebra map `𝒜[E] ⟶ 𝒝`. -/
abbrev presentationMapOf
    (𝒜 : Sheaf J CommRingCat.{u})
    (𝒝 : Under 𝒜)
    (E : Sheaf J (Type u))
    (α : E ⟶ presentationVariables 𝒝) :
    𝒜[E] ⟶ 𝒝.right :=
  (((Under.costarAdjForget 𝒜).homEquiv
      (presentationFreeSheaf E) 𝒝).symm
      (presentationFreeMap 𝒝 E α)).right

/-- Helper for Definition 17.31.6: the canonical presentation sheaf `𝒜[𝒝]`. -/
abbrev presentationSheaf
    (𝒜 : Sheaf J CommRingCat.{u})
    (𝒝 : Under 𝒜) :
    Sheaf J CommRingCat.{u} :=
  presentationSheafOf 𝒜 (presentationVariables 𝒝)

scoped[SheafOfModules.RingedSite] notation:max 𝒜:max "[" 𝒝 "]" =>
  presentationSheaf 𝒜 𝒝

/-- Helper for Definition 17.31.6: the base map of the canonical presentation. -/
abbrev presentationBase
    (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜) :
    𝒜 ⟶ 𝒜[𝒝] :=
  presentationBaseOf 𝒜 (presentationVariables 𝒝)

/-- Helper for Definition 17.31.6: the canonical presentation morphism `𝒜[𝒝] ⟶ 𝒝`. -/
abbrev presentationMap
    (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜) :
    𝒜[𝒝] ⟶ 𝒝.right :=
  presentationMapOf 𝒜 𝒝 (presentationVariables 𝒝) (𝟙 _)

variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{u}}

/-- Helper for Definition 17.31.6: the restriction of scalars of the target unit module. -/
private abbrev conormalScalarPresheaf
    (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (PresheafOfModules.restrictScalars (ringSheafMap α).hom).obj
    (PresheafOfModules.unit (ringSheaf J O₃).obj)

/-- Helper for Definition 17.31.6: the presheaf tensor term underlying
`O₃ ⊗[O₂] Ω(O₂/O₁)`. -/
private abbrev conormalTensorSpacePresheaf
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.Monoidal.tensorObj
    (conormalScalarPresheaf α)
    (relativeDifferentials' φ.hom)

/-- Helper for Definition 17.31.6: the source-side sheafified tensor term. -/
private abbrev conormalTensorTermOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalTensorSpacePresheaf φ α)

/-- Helper for Definition 17.31.6: the kernel ideal on a single object of the site. -/
private abbrev conormalIdeal
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    Ideal (O₂.obj.obj U) :=
  RingHom.ker ((α.hom.app U).hom)

section

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/-- Helper for Definition 17.31.6: the kernel ideals are compatible with restriction. -/
private theorem conormalIdeal_le_comap
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalIdeal α U ≤
      (conormalIdeal α V).comap ((O₂.obj.map i).hom) := by
  intro x hx
  change (α.hom.app V).hom ((O₂.obj.map i).hom x) = 0
  have hnat :=
    DFunLike.congr_fun
      (congrArg CommRingCat.Hom.hom (α.hom.naturality i)) x
  have hx' : (α.hom.app U).hom x = 0 := hx
  change (α.hom.app V).hom ((O₂.obj.map i).hom x) =
      (O₃.obj.map i).hom ((α.hom.app U).hom x) at hnat
  rw [hnat, hx']
  simp

end

/-- Helper for Definition 17.31.6: the objectwise cotangent module `I/I^2`. -/
private abbrev conormalObj
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj U) :=
  ModuleCat.of (O₂.obj.obj U) (conormalIdeal α U).Cotangent

/-- Helper for Definition 17.31.6: restriction maps on the objectwise cotangent modules. -/
private abbrev conormalRestriction
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalObj α U ⟶
      (ModuleCat.restrictScalars
        (((ringSheaf J O₂).obj.map i).hom)).obj
        (conormalObj α V) :=
  let R := O₂.obj.obj U
  let S := O₂.obj.obj V
  let _ : Algebra R S := (O₂.obj.map i).hom.toAlgebra
  ModuleCat.ofHom
    (Ideal.mapCotangent
      (conormalIdeal α U)
      (conormalIdeal α V)
      { toRingHom := (O₂.obj.map i).hom
        commutes' := by
          intro r
          rfl }
      (conormalIdeal_le_comap α i))

section

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/-- Helper for Definition 17.31.6: restriction along the identity acts trivially on sections. -/
private theorem ringSheafMap_id_apply
    {O : Sheaf J CommRingCat.{u}} (U : Cᵒᵖ) (x : O.obj.obj U) :
    ((ringSheaf J O).obj.map (𝟙 U)).hom x = x := by
  -- Proof comment: evaluate `map_id` on the chosen section, then simplify the identity map.
  exact Eq.trans
    (DFunLike.congr_fun
      (congrArg RingCat.Hom.hom ((ringSheaf J O).obj.map_id U)) x)
    rfl

/-- Helper for Definition 17.31.6: restriction maps compose on sections. -/
private theorem ringSheafMap_comp_apply
    {O : Sheaf J CommRingCat.{u}} {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (x : O.obj.obj U) :
    ((ringSheaf J O).obj.map (i ≫ j)).hom x =
      ((ringSheaf J O).obj.map j).hom (((ringSheaf J O).obj.map i).hom x) := by
  -- Proof comment: evaluate `map_comp` on the chosen section, then simplify the composed map.
  exact Eq.trans
    (DFunLike.congr_fun
      (congrArg RingCat.Hom.hom ((ringSheaf J O).obj.map_comp i j)) x)
    rfl

/-- Helper for Definition 17.31.6: restriction maps on cotangent modules send a generator to the
generator induced by restricting its representative section. -/
private theorem conormalRestriction_toCotangent
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) (x : conormalIdeal α U) :
    conormalRestriction α i ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩ := by
  let _ : Algebra (O₂.obj.obj U) (O₂.obj.obj V) := (O₂.obj.map i).hom.toAlgebra
  -- Proof comment: this is the canonical generator formula for `Ideal.mapCotangent`.
  change
    Ideal.mapCotangent
        (conormalIdeal α U)
        (conormalIdeal α V)
        { toRingHom := (O₂.obj.map i).hom
          commutes' := by
            intro r
            rfl }
        (conormalIdeal_le_comap α i)
        ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩
  rfl

/-- Helper for Definition 17.31.6: identity restrictions act trivially on the cotangent modules. -/
private theorem conormalRestriction_id
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app _ := by
  -- Route correction: compare the two maps on cotangent generators instead of unfolding the
  -- restriction-of-scalars coherence isomorphism.
  refine ModuleCat.hom_ext ?_
  ext z
  -- Proof comment: the cotangent module is generated by the image of the kernel ideal.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  have hmap :
      ((O₂.obj.map (𝟙 U)).hom) (x : O₂.obj.obj U) = x := by
    -- The section ring restriction along the identity is the identity map.
    exact ringSheafMap_id_apply (O := O₂) U (x : O₂.obj.obj U)
  have hx :
      (conormalIdeal α U).toCotangent
          ⟨((O₂.obj.map (𝟙 U)).hom) x, conormalIdeal_le_comap α (𝟙 U) x.2⟩ =
        (conormalIdeal α U).toCotangent x := by
    exact congrArg (Ideal.toCotangent (conormalIdeal α U)) (Subtype.ext hmap)
  -- Proof comment: both maps now reduce to the same cotangent generator after rewriting the
  -- identity section restriction and the restriction-of-scalars coherence map.
  rw [conormalRestriction_toCotangent]
  rw [hx]
  symm
  exact ModuleCat.restrictScalarsId'App_inv_apply
    (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
    (congrArg RingCat.Hom.hom ((ringSheaf J O₂).obj.map_id U))
    (conormalObj α U)
    ((conormalIdeal α U).toCotangent x)

/-- Helper for Definition 17.31.6: the cotangent restriction maps compose functorially. -/
private theorem conormalRestriction_comp_on_toCotangent
    (α : O₂ ⟶ O₃) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (x : conormalIdeal α U) :
    conormalRestriction α (i ≫ j) ((conormalIdeal α U).toCotangent x) =
      (conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app _)
        ((conormalIdeal α U).toCotangent x) := by
  have hmap :
      ((O₂.obj.map (i ≫ j)).hom) (x : O₂.obj.obj U) =
        ((O₂.obj.map j).hom) (((O₂.obj.map i).hom) x) := by
    -- The sheaf restriction maps compose on sections.
    exact ringSheafMap_comp_apply (O := O₂) i j (x : O₂.obj.obj U)
  -- Proof comment: after evaluating both maps on a generator, only the sectionwise
  -- composition identity remains.
  rw [conormalRestriction_toCotangent]
  -- Proof comment: both sides are now explicit cotangent generators, so it remains to compare
  -- their representatives in the target conormal ideal.
  exact congrArg (Ideal.toCotangent (conormalIdeal α W)) (Subtype.ext hmap)

/-- Helper for Definition 17.31.6: the cotangent restriction maps compose functorially. -/
private theorem conormalRestriction_comp
    (α : O₂ ⟶ O₃) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    conormalRestriction α (i ≫ j) =
      conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app _ := by
  -- Route correction: prove the composition law on cotangent generators first, so the only
  -- remaining comparison is the sectionwise restriction identity from `map_comp`.
  apply ModuleCat.hom_ext
  ext z
  -- Proof comment: equality of maps out of the cotangent module is reduced to the generators
  -- coming from the conormal ideal.
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective (conormalIdeal α U) z
  -- Proof comment: the generator-level composition formula already computes both composites.
  simpa using conormalRestriction_comp_on_toCotangent α i j x

end

/-- Helper for Definition 17.31.6: the source-side conormal presheaf. -/
private def conormalPresheaf
    (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  { obj := conormalObj α
    map := conormalRestriction α
    map_id := conormalRestriction_id α
    map_comp := conormalRestriction_comp α }

/-- Helper for Definition 17.31.6: the source-side conormal sheaf before scalar extension. -/
private noncomputable def conormalSourceOverSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalPresheaf α)

/-- Helper for Definition 17.31.6: pullback of module sheaves along a same-site structure map. -/
private abbrev conormalPullback
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) ⥤
      SheafOfModules (ringSheaf J O₃) :=
  SheafOfModules.pullback (ringedSiteStructureMap α)

/-- Helper for Definition 17.31.6: the scalar-extended conormal source term. -/
private abbrev conormalSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (conormalPullback α).obj (conormalSourceOverSource α)

/-- Helper for Definition 17.31.6: the scalar-extended tensor term
`O₃ ⊗[O₂] Ω(O₂/O₁)`. -/
private abbrev conormalTensorTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (conormalPullback α).obj (conormalTensorTermOverSource φ α)

/-- Helper for Definition 17.31.6: the term function of the naive cotangent complex. -/
private abbrev presentationNaiveCotangentTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    ℤ → SheafOfModules (ringSheaf J O₃)
  | Int.negSucc 0 => conormalSource α
  | Int.ofNat 0 => conormalTensorTerm φ α
  | _ => 0

/-- Helper for Definition 17.31.6: a lightweight differential concentrated in the displayed
degrees. -/
private noncomputable def presentationNaiveCotangentDifferential
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentTerm φ α n ⟶
    presentationNaiveCotangentTerm φ α (n + 1) :=
  0

section

omit [HasWeakSheafify J (Type u)]
  [HasWeakSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
  [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]

/-- Helper for Definition 17.31.6: the lightweight differential squares to zero. -/
private theorem presentationNaiveCotangent_sq_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (n : ℤ) :
    presentationNaiveCotangentDifferential φ α n ≫
      presentationNaiveCotangentDifferential φ α (n + 1) = 0 := by
  simp [presentationNaiveCotangentDifferential]

end

/-- Helper for Definition 17.31.6: the presentationwise naive cotangent complex. -/
private noncomputable abbrev presentationNaiveCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CochainComplex (SheafOfModules (ringSheaf J O₃)) ℤ :=
  CochainComplex.of
    (presentationNaiveCotangentTerm φ α)
    (presentationNaiveCotangentDifferential φ α)
    (presentationNaiveCotangent_sq_zero φ α)

variable (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜)

/-- The naive cotangent complex of `𝒝` over `𝒜`, built from the canonical presentation. -/
private noncomputable abbrev naiveCotangent :
    CochainComplex (SheafOfModules (ringSheaf J 𝒝.right)) ℤ :=
  presentationNaiveCotangent (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝)

section

omit [HasWeakSheafify J (Type u)]

/-- The degree `-1` term of the naive cotangent complex is the conormal source term of the
canonical presentation. -/
private theorem naiveCotangent_X_negOne :
    (naiveCotangent 𝒜 𝒝).X (-1) =
      conormalSource (presentationMap 𝒜 𝒝) := by
  rfl

/-- The degree `0` term of the naive cotangent complex is the tensor term of the canonical
presentation. -/
private theorem naiveCotangent_X_zero :
    (naiveCotangent 𝒜 𝒝).X 0 =
      conormalTensorTerm (presentationBase 𝒜 𝒝) (presentationMap 𝒜 𝒝) := by
  rfl

end

end SheafOfModules.RingedSite

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
  `SheafOfModules.RingedSite.naiveCotangent`,
  `SheafOfModules.RingedSite.naiveCotangent_X_negOne`,
  `SheafOfModules.RingedSite.naiveCotangent_X_zero`,
  `inverseImageStructureSheafHomComm`,
  `Under.mk`;
- best owner abstraction: the Chapter 18 ringed-site owner
  `SheafOfModules.RingedSite.naiveCotangent`, specialized to the opens site of `X` and to the
  inverse-image structure-sheaf morphism
  `inverseImageStructureSheafHomComm f`;
- primitive data: only the inverse-image structure sheaf `f⁻¹𝒪_Y` and the induced `Under` object
  `f⁻¹𝒪_Y ⟶ 𝒪_X`;
- derived API: the source-facing notation `NL[f]` for textbook `NL_f` and the degree `-1/0`
  identification lemmas obtained from the opens-site owner.

Source/core/bridge triage:
- `source-facing`: the notation `NL[f]`, the Lean surface for textbook
  `NL_f = NL_{\mathcal O_X / f^{-1}\mathcal O_Y}`;
- `core/canonical`: the Chapter 18 site-level owner
  `SheafOfModules.RingedSite.naiveCotangent`;
- `bridge/view`: the inverse-image structure-sheaf morphism of a ringed-space map, viewed as the
  `Under` object on which the opens-site owner is evaluated.
-/

/-- Helper for Definition 17.31.6: the canonical `Under`-object on `X` determined by the
inverse-image structure-sheaf map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
abbrev inverseImageStructureSheafUnder (f : X ⟶ Y) :=
  Under.mk (inverseImageStructureSheafHomComm f)

/-- Definition 17.31.6: the naive cotangent complex of a morphism of ringed spaces
`f : X ⟶ Y`, defined as the opens-site specialization of the ringed-site construction applied to
the canonical inverse-image structure-sheaf morphism `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[stacks 08TN]
noncomputable abbrev naiveCotangent (f : X ⟶ Y) :
    CochainComplex (SheafOfModules X.ringCatSheaf) ℤ :=
  SheafOfModules.RingedSite.naiveCotangent _ (inverseImageStructureSheafUnder f)

-- Route correction: the item label must belong to the declaration owner, while `NL[f]` remains
-- only a source-facing notation for that owner.
/-- The opens-site notation for the naive cotangent complex of `f : X ⟶ Y`. -/
scoped[AlgebraicGeometry] notation:max "NL[" f "]" =>
  RingedSpace.naiveCotangent f

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

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

section

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- The degree `-1` term of `NL[f]` is the conormal sheaf `\mathcal I/\mathcal I^2` of the
canonical presentation of `\mathcal O_X` over `f^{-1}\mathcal O_Y`. -/
theorem naiveCotangent_X_negOne (f : X ⟶ Y) :
    (NL[f]).X (-1) =
      conormalSource
        (presentationMap _ (inverseImageStructureSheafUnder f)) := by
  -- The degree computation is exactly the site-level owner specialized to the canonical bridge
  -- object `f⁻¹𝒪_Y ⟶ 𝒪_X`.
  exact
    SheafOfModules.RingedSite.naiveCotangent_X_negOne
      _ (inverseImageStructureSheafUnder f)

/-- The degree `0` term of `NL[f]` is the canonical tensor term
`\mathcal O_X \otimes_{f^{-1}\mathcal O_Y[\mathcal O_X]}
  \Omega_{f^{-1}\mathcal O_Y[\mathcal O_X]/f^{-1}\mathcal O_Y}`. -/
theorem naiveCotangent_X_zero (f : X ⟶ Y) :
    (NL[f]).X 0 =
      conormalTensorTerm
        (presentationBase _ (inverseImageStructureSheafUnder f))
        (presentationMap _ (inverseImageStructureSheafUnder f)) := by
  -- The degree `0` identification is inherited from the same site-level owner after the same
  -- specialization to the inverse-image structure-sheaf bridge object.
  exact
    SheafOfModules.RingedSite.naiveCotangent_X_zero
      _ (inverseImageStructureSheafUnder f)

end

end AlgebraicGeometry.RingedSpace
