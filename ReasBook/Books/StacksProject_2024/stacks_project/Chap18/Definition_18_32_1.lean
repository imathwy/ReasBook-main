import Mathlib
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Definition_18_32_1.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Domain-style sampling for Definition 18.32.1:
- primary domain: finite locally free modules of fixed rank, invertible modules, and the units
  sheaf on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFree`,
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `tensorRight`,
  `CategoryTheory.Subfunctor`,
  `CommMonCat.units`;
- best owner abstractions:
  the ambient owner category `ringedSiteModuleCategory J 𝒪`, the Chapter 18 over-site cover
  pattern on `((J.over U).over X)`, the source-facing invertibility owner
  `Functor.IsEquivalence (tensorRight ℒ)` on the ambient monoidal tensor-right owner
  `tensorRight`, and the units sheaf `\mathcal O^*` in `CommGrpCat`, with the underlying units
  subfunctor and the additive bridge derived from that owner;
- primitive data:
  local rank-`r` trivializations of `((ℱ.over U).over X)` on an over-site cover of each `U`,
  the tensor-right endofunctor for invertibility, and the objectwise invertible sections of
  `\mathcal O`;
- derived API:
  finite local freeness, the structure-sheaf rank-one and invertibility instances, and the sheaf
  of commutative groups `\mathcal O^*`, together with its underlying subsheaf and additive-group
  bridge.

Source/core/bridge triage:
- `source-facing`: fixed-rank finite local freeness and the units subsheaf
  `\mathcal O^* \subset \mathcal O`;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFree`,
  `tensorRight`,
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `CommMonCat.units`,
  `CategoryTheory.Subfunctor`;
- `bridge/view`: iterated restriction `((ℱ.over U).over X)` and the additive-group-valued units
  sheaf built from the commutative-group-valued units owner.
-/

section Modules

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ CommRingCat RingCat)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

section Rank

/-- Helper for Definition 18.32.1: the singleton family given by the identity of `U` covers the
top object in the slice site `(C / U, J.over U)`. -/
private theorem identity_singleton_coversTop_over (U : C) :
    (J.over U).CoversTop (fun _ : PUnit => Over.mk (𝟙 U)) := by
  -- The slice terminal object is `Over.mk (𝟙 U)`, so a singleton family containing it covers.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have htop :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun _ : PUnit => Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
    ext Z g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.overEquiv_iff]
      exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
  rw [htop]
  exact J.top_mem U

/-- Helper for Definition 18.32.1: on any ringed site, the unit module is the free rank-one
module. -/
private theorem unitModule_iso_free_singleton
    {D : Type u} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
    {ℛ : Sheaf K CommRingCat.{max u v}} :
    Nonempty
      ((unitModule K ℛ : ringedSiteModuleCategory K ℛ) ≅
        (SheafOfModules.free (ULift.{max u v} (Fin 1)) :
          ringedSiteModuleCategory K ℛ)) := by
  let c : Cofan (fun _ : ULift.{max u v} (Fin 1) ↦
      (unitModule K ℛ : ringedSiteModuleCategory K ℛ)) :=
    Cofan.mk
      (P := (unitModule K ℛ : ringedSiteModuleCategory K ℛ))
      (fun _ ↦ 𝟙 _)
  let hc : IsColimit c :=
    mkCofanColimit c
      (fun t ↦ t.inj (default : ULift.{max u v} (Fin 1)))
      (fun t j ↦ by
        simpa [c, Subsingleton.elim j (default : ULift.{max u v} (Fin 1))])
      (fun t m hm ↦ by
        simpa [c] using hm (default : ULift.{max u v} (Fin 1)))
  -- The unit module is the coproduct of one copy of itself, hence the free singleton module.
  exact ⟨IsColimit.coconePointUniqueUpToIso hc
    (SheafOfModules.isColimitFreeCofan
      (R := ringSheaf K ℛ) (ULift.{max u v} (Fin 1)))⟩

/-- Definition 18.32.1 (1): a finite locally free `\mathcal O`-module has rank `r` if on every
object `U` there is a covering on which the restriction is isomorphic to
`\mathcal O^{\oplus r}`. -/
class IsFiniteLocallyFreeOfRank (r : ℕ) (ℱ : Mod) : Prop where
  /-- Every object admits a covering on which `ℱ` is free of rank `r`. -/
  exists_iso_free_over (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I,
        Nonempty
          (((ℱ.over U).over (X i)) ≅
            (SheafOfModules.free (ULift.{max u v} (Fin r)) :
              ringedSiteModuleCategory ((J.over U).over (X i)) ((𝒪.over U).over (X i))))


-- Proof sketch: forget that each local model is specifically `\mathcal O^{\oplus r}`. Since
-- `Fin r` is finite, the same covering data witnesses finite local freeness.
/-- A locally free module of constant rank `r` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (r : ℕ)
    (ℱ : Mod) [IsFiniteLocallyFreeOfRank r ℱ] :
    IsFiniteLocallyFree ℱ := by
  refine ⟨?_⟩
  intro U
  let h : IsFiniteLocallyFreeOfRank r ℱ := inferInstance
  rcases h.exists_iso_free_over U with ⟨I, X, hX, hfree⟩
  refine ⟨I, X, hX, ?_⟩
  intro i
  rcases hfree i with ⟨e⟩
  -- Forget only the rank information: the same local model is finite free because `Fin r` is
  -- finite.
  exact ⟨ULift.{max u v} (Fin r), inferInstance, ⟨e⟩⟩

-- Proof sketch: for every object `U`, the singleton covering by `𝟙 U` trivializes the unit
-- module as the free rank-one module over `\mathcal O_U`.
/-- The structure sheaf on a ringed site is finite locally free of rank `1`. -/
instance :
    IsFiniteLocallyFreeOfRank 1
      (unitModule J 𝒪 : Mod) := by
  refine ⟨?_⟩
  intro U
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
  intro i
  cases i
  -- Restrict to the identity cover and identify the localized unit module with the singleton free
  -- module on the iterated slice site.
  simpa using
    (unitModule_iso_free_singleton
      (K := (J.over U).over (Over.mk (𝟙 U)))
      (ℛ := ((𝒪.over U).over (Over.mk (𝟙 U)))))

end Rank

section Invertible

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/- Definition 18.32.1 (2): an `\mathcal O`-module on a ringed site is invertible precisely when
right tensoring with it is an equivalence, i.e. when `Functor.IsEquivalence (tensorRight ℒ)`.
-/

-- Proof sketch: the tensor unit in `Mod(\mathcal O)` is the sheafification of the presheaf-side
-- unit model, so the canonical counit comparison identifies `unitModule J 𝒪` with `𝟙_ Mod`.
/-- Helper for Definition 18.32.1: after unfolding the ringed-site abbreviations, the structure
sheaf module is the ambient tensor unit. -/
private noncomputable def unitModule_iso_tensorUnit :
    (unitModule J 𝒪 : Mod) ≅ (𝟙_ Mod) := by
  -- Route correction: the owner-level tensor-unit comparison is isolated in the theorem-local
  -- helper file, so the target proof only adapts it through the ringed-site abbreviations.
  simpa [unitModule, ringedSiteModuleCategory, ringSheaf] using
    (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪))

/-- Helper for Definition 18.32.1: tensoring on the right by the structure sheaf is naturally
isomorphic to the identity functor. -/
private noncomputable def tensorRight_unitModule_iso_id :
    tensorRight (unitModule J 𝒪 : Mod) ≅ 𝟭 Mod :=
  (tensoringRight Mod).mapIso (unitModule_iso_tensorUnit (J := J) (𝒪 := 𝒪)) ≪≫
    rightUnitorNatIso Mod

/-- The structure sheaf is an invertible module on a ringed site. -/
instance unit_isInvertible :
    Functor.IsEquivalence
      (tensorRight (unitModule J 𝒪 : Mod)) :=
  by
    -- The endofunctor `tensorRight (unitModule J 𝒪)` is identified with the identity through the
    -- ambient tensor unit, so the categorical right unitor gives the equivalence.
    exact Functor.isEquivalence_of_iso ((tensorRight_unitModule_iso_id (J := J) (𝒪 := 𝒪)).symm)

end Invertible

end Modules

section Units

private noncomputable abbrev unitsPresheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ CommGrpCat :=
  𝒪.1 ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

-- Proof sketch: we glue ordinary sections and glued inverse sections in the underlying ring
-- presheaf, then use separatedness of the ring sheaf to prove the two gluings are inverse.
/-- Helper for Definition 18.32.1: the underlying `Type`-valued presheaf of ring sections of
`\mathcal O`. -/
private abbrev ringSectionsPresheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ Type (max u v) :=
  𝒪.1 ⋙ CategoryTheory.forget CommRingCat.{max u v}

/-- Helper for Definition 18.32.1: forgetting the group law on the units presheaf yields the
objectwise units of the structure sheaf. -/
private abbrev unitsTypePresheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Cᵒᵖ ⥤ Type (max u v) :=
  unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}

-- Proof sketch: forget the ring sheaf to `Type` and then apply the standard equivalence between
-- the categorical and elementwise sheaf conditions for type-valued presheaves.
/-- Helper for Definition 18.32.1: the underlying `Type`-valued presheaf of ring sections of
`\mathcal O` is a sheaf. -/
private theorem ringSectionsPresheaf_isSheaf :
    Presieve.IsSheaf J (ringSectionsPresheaf 𝒪) := by
  refine (isSheaf_iff_isSheaf_of_type J (ringSectionsPresheaf 𝒪)).1 ?_
  exact
    (Presheaf.isSheaf_iff_isSheaf_forget J 𝒪.1
      (CategoryTheory.forget CommRingCat.{max u v})).1 𝒪.property

-- Proof sketch: equality of units is detected on their underlying values, and the underlying ring
-- presheaf is already separated.
/-- Helper for Definition 18.32.1: the objectwise units presheaf is separated because the
underlying ring presheaf is separated. -/
private theorem unitsTypePresheaf_isSeparated :
    Presieve.IsSeparated J (unitsTypePresheaf 𝒪) := by
  intro X S hS x t₁ t₂ ht₁ ht₂
  -- Equality of units is detected after forgetting to the underlying ring sections.
  apply Units.ext
  apply ((ringSectionsPresheaf_isSheaf (J := J) (𝒪 := 𝒪)).isSeparated S hS).ext
  intro Y f hf
  exact (congrArg Units.val (ht₁ f hf)).trans (congrArg Units.val (ht₂ f hf)).symm

/-- Helper for Definition 18.32.1: the underlying `Type`-valued units presheaf is a sheaf once
separatedness is combined with the explicit units gluing lemma. -/
private theorem unitsTypePresheaf_isSheaf :
    Presieve.IsSheaf J (unitsTypePresheaf 𝒪) := by
  intro X S hS
  -- We use the source-faithful route: glue values and inverse values in the ring sheaf, then use
  -- separatedness of ring sections to prove the glued sections are inverse.
  intro x hx
  let hRing := ringSectionsPresheaf_isSheaf (J := J) (𝒪 := 𝒪)
  let hRingFor := hRing S hS
  let hSep := unitsTypePresheaf_isSeparated (J := J) (𝒪 := 𝒪) S hS
  let xVal : Presieve.FamilyOfElements (ringSectionsPresheaf 𝒪) S :=
    fun _ f hf ↦ (x f hf).1
  have hxVal : xVal.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    exact congrArg Units.val (hx g₁ g₂ h₁ h₂ fac)
  let xInv : Presieve.FamilyOfElements (ringSectionsPresheaf 𝒪) S :=
    fun Y f hf ↦
      Units.val
        ((x f hf : Units ((ringSectionsPresheaf 𝒪).obj (op Y)))⁻¹)
  have hxInv : xInv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
    change
      Units.val (((unitsTypePresheaf 𝒪).map g₁.op (x f₁ h₁))⁻¹) =
        Units.val (((unitsTypePresheaf 𝒪).map g₂.op (x f₂ h₂))⁻¹)
    simpa [unitsTypePresheaf, unitsPresheaf, Units.coe_map, Units.coe_map_inv] using
      congrArg Units.val (congrArg Inv.inv (hx g₁ g₂ h₁ h₂ fac))
  let gluedVal := hRingFor.amalgamate xVal hxVal
  let gluedInv := hRingFor.amalgamate xInv hxInv
  have hgluedVal : xVal.IsAmalgamation gluedVal := hRingFor.isAmalgamation hxVal
  have hgluedInv : xInv.IsAmalgamation gluedInv := hRingFor.isAmalgamation hxInv
  have hmul : gluedVal * gluedInv = 1 := by
    -- Restricting the product to the cover gives the local identity `u * u⁻¹ = 1`, so
    -- separatedness of the ring sheaf upgrades this to a global identity.
    apply (hRing.isSeparated S hS).ext
    intro Y f hf
    let φ := (𝒪.1.map f.op).hom
    change φ (gluedVal * gluedInv) = φ 1
    have hφVal : φ gluedVal = (x f hf).1 := by
      simpa [xVal] using hgluedVal f hf
    have hφInv : φ gluedInv = Units.val ((x f hf : Units ((ringSectionsPresheaf 𝒪).obj (op Y)))⁻¹) := by
      simpa [xInv] using hgluedInv f hf
    calc
      φ (gluedVal * gluedInv) = φ gluedVal * φ gluedInv := by
        exact φ.map_mul gluedVal gluedInv
      _ = (x f hf).1 * Units.val ((x f hf : Units ((ringSectionsPresheaf 𝒪).obj (op Y)))⁻¹) := by
        rw [hφVal, hφInv]
      _ = 1 := by
        simpa [xVal, xInv] using (x f hf).val_inv
      _ = φ 1 := by
        symm
        exact φ.map_one
  have hmul' : gluedInv * gluedVal = 1 := by
    -- The same separatedness argument with the opposite order gives the left inverse identity.
    apply (hRing.isSeparated S hS).ext
    intro Y f hf
    let φ := (𝒪.1.map f.op).hom
    change φ (gluedInv * gluedVal) = φ 1
    have hφInv : φ gluedInv = Units.val ((x f hf : Units ((ringSectionsPresheaf 𝒪).obj (op Y)))⁻¹) := by
      simpa [xInv] using hgluedInv f hf
    have hφVal : φ gluedVal = (x f hf).1 := by
      simpa [xVal] using hgluedVal f hf
    calc
      φ (gluedInv * gluedVal) = φ gluedInv * φ gluedVal := by
        exact φ.map_mul gluedInv gluedVal
      _ = Units.val ((x f hf : Units ((ringSectionsPresheaf 𝒪).obj (op Y)))⁻¹) * (x f hf).1 := by
        rw [hφInv, hφVal]
      _ = 1 := by
        simpa [xVal, xInv] using (x f hf).inv_val
      _ = φ 1 := by
        symm
        exact φ.map_one
  let gluedUnit : (unitsTypePresheaf 𝒪).obj (op X) := ⟨gluedVal, gluedInv, hmul, hmul'⟩
  have hgluedUnit : x.IsAmalgamation gluedUnit := by
    -- Equality of units is detected on underlying values, and the glued value section matches the
    -- original compatible family on the cover.
    intro Y f hf
    apply Units.ext
    exact hgluedVal f hf
  exact ⟨gluedUnit, hgluedUnit, fun t ht ↦ hSep x t gluedUnit ht hgluedUnit⟩

-- Proof sketch: the sheaf condition for `\mathcal O` descends to units because units glue
-- uniquely and restriction preserves multiplication and inverses.
private theorem unitsPresheaf_isSheaf :
    Presheaf.IsSheaf J (unitsPresheaf 𝒪) := by
  -- For the concrete category `CommGrpCat`, it is enough to prove the sheaf condition after
  -- forgetting to the underlying `Type`-valued presheaf of units.
  exact
    (Presheaf.isSheaf_iff_isSheaf_forget J (unitsPresheaf 𝒪)
      (CategoryTheory.forget CommGrpCat.{max u v})).2
      ((isSheaf_iff_isSheaf_of_type J (unitsTypePresheaf 𝒪)).2
        (unitsTypePresheaf_isSheaf (J := J) (𝒪 := 𝒪)))

/-- Definition 18.32.1 (3): the units sheaf `\mathcal O^*` of invertible local sections of the
structure sheaf. -/
noncomputable def ringedSiteUnitsSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J CommGrpCat :=
  ⟨unitsPresheaf 𝒪, unitsPresheaf_isSheaf⟩

/- Lean surface notation for the source-facing units sheaf `\mathcal O^*`. -/
scoped[RingedSiteUnits] postfix:max "⁎" =>
  ringedSiteUnitsSheaf

open scoped RingedSiteUnits

section UnderlyingTypes

variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{max u v})]

private noncomputable abbrev underlyingRingedSiteSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{max u v})).obj 𝒪

/-- The canonical units subfunctor `\mathcal O^* \subset \mathcal O` on the underlying
`Type`-valued presheaf of the structure sheaf. -/
noncomputable def ringedSiteUnitsSubfunctor
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Subfunctor (underlyingRingedSiteSheaf 𝒪).1 where
  obj U := by
    let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
      change CommRing (𝒪.1.obj U)
      infer_instance
    exact { x | IsUnit x }
  map {U V} f := by
    let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
      change CommRing (𝒪.1.obj U)
      infer_instance
    let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj V) := by
      change CommRing (𝒪.1.obj V)
      infer_instance
    intro x hx
    change IsUnit ((𝒪.1.map f).hom x)
    exact hx.map ((𝒪.1.map f).hom)

/-- Helper for Definition 18.32.1: forgetting the group law on the units presheaf identifies it
with the canonical underlying units subfunctor of `\mathcal O`. -/
private noncomputable def unitsPresheaf_forgetIso_subfunctor :
    (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}) ≅
      (ringedSiteUnitsSubfunctor 𝒪).toFunctor where
  hom :=
    { app := fun U u ↦ by
        let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
          change CommRing (𝒪.1.obj U)
          infer_instance
        refine ⟨u.1, ?_⟩
        change IsUnit u.1
        exact u.isUnit
      naturality := by
        intro U V f
        rfl }
  inv :=
    { app := fun U s ↦ by
        let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
          change CommRing (𝒪.1.obj U)
          infer_instance
        exact s.2.unit
      naturality := by
        intro U V f
        funext s
        apply Units.ext
        rfl }
  hom_inv_id := by
    ext U u
    apply Units.ext
    rfl
  inv_hom_id := by
    ext U s
    apply Subtype.ext
    rfl

-- Proof sketch: the units subfunctor is isomorphic to the underlying `Type`-valued presheaf of
-- the units sheaf `\mathcal O^*`, so it inherits the sheaf condition.
private theorem unitsSubfunctor_isSheaf :
    Presheaf.IsSheaf J (ringedSiteUnitsSubfunctor 𝒪).toFunctor := by
  have hForget :
      Presheaf.IsSheaf J (unitsPresheaf 𝒪 ⋙ CategoryTheory.forget CommGrpCat.{max u v}) := by
    exact
      (Presheaf.isSheaf_iff_isSheaf_forget J (unitsPresheaf 𝒪)
        (CategoryTheory.forget CommGrpCat.{max u v})).1 unitsPresheaf_isSheaf
  -- Transport the `Type`-valued sheaf condition along the explicit units-subfunctor isomorphism.
  exact (Presheaf.isSheaf_of_iso_iff (unitsPresheaf_forgetIso_subfunctor (𝒪 := 𝒪))).1 hForget

/-- The underlying `Type`-valued sheaf of the units subsheaf `\mathcal O^* \subset \mathcal O`,
derived from the canonical units subfunctor. -/
noncomputable def ringedSiteUnitsSubsheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  ⟨(ringedSiteUnitsSubfunctor 𝒪).toFunctor,
    unitsSubfunctor_isSheaf⟩

/-- The underlying sheaf of types of the units sheaf `\mathcal O^*` is canonically isomorphic to
the derived units subsheaf `\mathcal O^* \subset \mathcal O`. -/
noncomputable def ringedSiteUnitsSheafUnderlyingIso
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (sheafCompose J (CategoryTheory.forget CommGrpCat.{max u v})).obj (𝒪⁎) ≅
      ringedSiteUnitsSubsheaf 𝒪 where
  hom :=
    ⟨{ app := fun U u ↦ by
         let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
           change CommRing (𝒪.1.obj U)
           infer_instance
         refine ⟨u.1, ?_⟩
         change IsUnit u.1
         exact u.isUnit
       naturality := by
         intro U V f
         rfl }⟩
  inv :=
    ⟨{ app := fun U s ↦ by
         let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
           change CommRing (𝒪.1.obj U)
           infer_instance
         exact s.2.unit
       naturality := by
         intro U V f
         funext s
         apply Units.ext
         rfl }⟩
  hom_inv_id := by
    ext U u
    apply Units.ext
    rfl
  inv_hom_id := by
    ext U s
    apply Subtype.ext
    rfl

@[simp] theorem ringedSiteUnitsSheafUnderlyingIso_hom_app
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : Cᵒᵖ)
    (u : (𝒪⁎).1.obj U) :
    (ringedSiteUnitsSheafUnderlyingIso 𝒪).hom.hom.app U u =
      (by
        let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
          change CommRing (𝒪.1.obj U)
          infer_instance
        refine ⟨u.1, ?_⟩
        change IsUnit u.1
        exact u.isUnit) := by
  rfl

@[simp] theorem ringedSiteUnitsSheafUnderlyingIso_inv_app
    (𝒪 : Sheaf J CommRingCat.{max u v}) (U : Cᵒᵖ)
    (s : (ringedSiteUnitsSubsheaf 𝒪).1.obj U) :
    ((ringedSiteUnitsSheafUnderlyingIso 𝒪).inv.hom.app U s).1 = s.1 := by
  let _ : CommRing ((underlyingRingedSiteSheaf 𝒪).1.obj U) := by
    change CommRing (𝒪.1.obj U)
    infer_instance
  change ((s.2.unit : Units ((underlyingRingedSiteSheaf 𝒪).1.obj U)) :
      (underlyingRingedSiteSheaf 𝒪).1.obj U) = s.1
  exact s.2.unit_spec

end UnderlyingTypes

private theorem unitsAddPresheaf_isSheaf :
    Presheaf.IsSheaf J ((ringedSiteUnitsSheaf 𝒪).1 ⋙ CommGrpCat.toAddCommGrp) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J
    ((ringedSiteUnitsSheaf 𝒪).1 ⋙ CommGrpCat.toAddCommGrp)
    (CategoryTheory.forget AddCommGrpCat.{max u v})]
  -- Forgetting from additive commutative groups to types is the same underlying presheaf as
  -- forgetting from commutative groups, so the sheaf condition is inherited from `𝒪⁎`.
  simpa [ringedSiteUnitsSheaf, unitsPresheaf] using
    (Presheaf.isSheaf_iff_isSheaf_forget J (unitsPresheaf 𝒪)
      (CategoryTheory.forget CommGrpCat.{max u v})).1 unitsPresheaf_isSheaf

/-- The additive-group-valued sheaf attached to `\mathcal O^*`; this is the abelian-sheaf bridge
used for cohomology. -/
noncomputable abbrev ringedSiteUnitsAddSheaf
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J AddCommGrpCat :=
  ⟨(ringedSiteUnitsSheaf 𝒪).1 ⋙ CommGrpCat.toAddCommGrp, unitsAddPresheaf_isSheaf⟩

end Units

end SheafOfModules.RingedSite
