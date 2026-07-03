import Mathlib
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
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

/- Domain-style sampling for Definition 18.32.1:
- primary domain: finite locally free modules of fixed rank, invertible modules, and the units
  sheaf on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFiniteLocallyFree`,
  `tensorRight`,
  `CategoryTheory.Subfunctor`,
  `CommMonCat.units`;
- best owner abstractions:
  the ambient owner category `ringedSiteModuleCategory J 𝒪`, the Chapter 18 over-site cover
  pattern on `((J.over U).over X)`, the canonical tensor-right owner `tensorRight` packaged by
  `IsInvertible`, and the units
  sheaf `\mathcal O^*` in `CommGrpCat`, with the underlying units subfunctor and the additive
  bridge derived from that owner;
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
  `CommMonCat.units`,
  `CategoryTheory.Subfunctor`;
- `bridge/view`: iterated restriction `((ℱ.over U).over X)` and the additive-group-valued units
  sheaf built from the commutative-group-valued units owner.
-/

/-- Definition 18.32.1 (1): a finite locally free `\mathcal O`-module has rank `r` if on every
object `U` there is a covering on which the restriction is isomorphic to
`\mathcal O^{\oplus r}`. -/
class IsFiniteLocallyFreeOfRank (r : ℕ) (ℱ : ringedSiteModuleCategory J 𝒪) : Prop where
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
    (ℱ : ringedSiteModuleCategory J 𝒪) [IsFiniteLocallyFreeOfRank r ℱ] :
    IsFiniteLocallyFree ℱ := sorry

-- Proof sketch: for every object `U`, the singleton covering by `𝟙 U` trivializes the unit
-- module as the free rank-one module over `\mathcal O_U`.
/-- The structure sheaf on a ringed site is finite locally free of rank `1`. -/
instance :
    IsFiniteLocallyFreeOfRank 1
      (SheafOfModules.unit (ringSheaf J 𝒪) :
        ringedSiteModuleCategory J 𝒪) := sorry

section Invertible

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

/-- Definition 18.32.1 (2): an `\mathcal O`-module is invertible if tensoring with it defines an
equivalence of the category `Mod(\mathcal O)`. -/
class IsInvertible (ℒ : ringedSiteModuleCategory J 𝒪) : Prop
    extends Functor.IsEquivalence (tensorRight ℒ)

-- Proof sketch: the structure sheaf is the tensor unit, so right tensoring with it is naturally
-- isomorphic to the identity functor on `Mod(\mathcal O)`.
/-- The structure sheaf is an invertible module on a ringed site. -/
instance unit_isInvertible :
    IsInvertible (SheafOfModules.unit (ringSheaf J 𝒪)) := sorry

end Invertible

end SheafOfModules.RingedSite

section Units

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The source-facing subpresheaf of `\mathcal O` cut out by invertible local sections. -/
def ringedSiteUnitsSubfunctor :
    Subfunctor (𝒪.1 ⋙ forget CommRingCat.{max u v}) where
  obj U := { s | IsUnit s }
  map f := by
    intro s hs
    exact IsUnit.map ((𝒪.1.map f).hom) hs

/-- The commutative-group-valued presheaf of invertible local sections of the structure sheaf. -/
noncomputable abbrev ringedSiteUnitsPresheaf :
    Cᵒᵖ ⥤ CommGrpCat :=
  𝒪.1 ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

-- Proof sketch: the sheaf condition for `\mathcal O` descends to units because units glue
-- uniquely and restriction preserves multiplication and inverses.
/-- The presheaf of units of the structure sheaf satisfies the sheaf condition. -/
theorem ringedSiteUnitsPresheaf_isSheaf :
    Presheaf.IsSheaf J (ringedSiteUnitsPresheaf 𝒪) := sorry

/-- Definition 18.32.1 (3): the units sheaf `\mathcal O^*` of invertible local sections of the
structure sheaf. -/
noncomputable def ringedSiteUnitsSheaf :
    Sheaf J CommGrpCat :=
  ⟨ringedSiteUnitsPresheaf 𝒪,
    ringedSiteUnitsPresheaf_isSheaf 𝒪⟩

/- Lean surface notation for the source-facing units sheaf `\mathcal O^*`. -/
syntax:max term:max "⁎" : term

macro_rules
  | `($𝒪⁎) => `(ringedSiteUnitsSheaf $𝒪)

/-- The source-facing units subpresheaf agrees with the underlying `Type`-valued presheaf of the
canonical units presheaf. -/
noncomputable def ringedSiteUnitsSubfunctorIso :
    (ringedSiteUnitsSubfunctor 𝒪).toFunctor ≅
      (𝒪⁎).1 ⋙ forget CommGrpCat where
  hom.app U s := s.2.unit
  inv.app U u := ⟨((show (𝒪.1.obj U)ˣ from u) : 𝒪.1.obj U),
    (show (𝒪.1.obj U)ˣ from u).isUnit⟩
  hom.naturality := by
    intro U V f
    ext s
    apply Units.ext
    rfl
  inv.naturality := by
    intro U V f
    ext u
    rfl
  hom_inv_id := by
    ext U s
    rfl
  inv_hom_id := by
    ext U u
    apply Units.ext
    rfl

/-- The source-facing units subpresheaf of `\mathcal O` satisfies the sheaf condition. -/
theorem ringedSiteUnitsSubfunctor_isSheaf :
    Presheaf.IsSheaf J (ringedSiteUnitsSubfunctor 𝒪).toFunctor := by
  refine (Presheaf.isSheaf_of_iso_iff (ringedSiteUnitsSubfunctorIso 𝒪)).2 ?_
  exact Presheaf.isSheaf_comp_of_isSheaf J (𝒪⁎).1
    (forget CommGrpCat) (ringedSiteUnitsPresheaf_isSheaf 𝒪)

/-- The underlying `Type`-valued subsheaf `\mathcal O^* \subset \mathcal O`. -/
noncomputable def ringedSiteUnitsSubsheaf :
    Sheaf J (Type (max u v)) :=
  ⟨(ringedSiteUnitsSubfunctor 𝒪).toFunctor,
    ringedSiteUnitsSubfunctor_isSheaf 𝒪⟩

/-- The canonical inclusion `\mathcal O^* \hookrightarrow \mathcal O` on the underlying sheaves of
types. -/
noncomputable def ringedSiteUnitsSubsheafι :
    ringedSiteUnitsSubsheaf 𝒪 ⟶ (sheafCompose J (forget CommRingCat)).obj 𝒪 :=
  ⟨(ringedSiteUnitsSubfunctor 𝒪).ι⟩

/-- The additive-group-valued presheaf obtained from `\mathcal O^*` by the canonical equivalence
`CommGrpCat ≌ AddCommGrpCat`. -/
noncomputable abbrev ringedSiteUnitsAddPresheaf :
    Cᵒᵖ ⥤ AddCommGrpCat :=
  (𝒪⁎).1 ⋙ CommGrpCat.toAddCommGrp

/-- The additive-group-valued presheaf attached to `\mathcal O^*` satisfies the sheaf condition. -/
theorem ringedSiteUnitsAddPresheaf_isSheaf :
    Presheaf.IsSheaf J (ringedSiteUnitsAddPresheaf 𝒪) := sorry

/-- The additive-group-valued sheaf attached to `\mathcal O^*`; this is the abelian-sheaf bridge
used for cohomology. -/
noncomputable def ringedSiteUnitsAddSheaf :
    Sheaf J AddCommGrpCat :=
  ⟨ringedSiteUnitsAddPresheaf 𝒪,
    ringedSiteUnitsAddPresheaf_isSheaf 𝒪⟩

-- Proof sketch: this follows by unfolding the definition of `ringedSiteUnitsSheaf`.
/-- The underlying commutative-group-valued presheaf of `\mathcal O^*` is the units presheaf. -/
theorem ringedSiteUnitsSheaf_val :
    (𝒪⁎).1 =
      ringedSiteUnitsPresheaf 𝒪 := rfl

-- Proof sketch: this follows by unfolding the definition of `ringedSiteUnitsAddSheaf`.
/-- The underlying additive-group-valued presheaf of the abelian bridge of `\mathcal O^*` is the
canonical additive image of the units presheaf. -/
theorem ringedSiteUnitsAddSheaf_val :
    (ringedSiteUnitsAddSheaf 𝒪).1 =
      ringedSiteUnitsAddPresheaf 𝒪 := rfl

end Units
