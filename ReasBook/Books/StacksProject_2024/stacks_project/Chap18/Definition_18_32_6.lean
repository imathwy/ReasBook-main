import Mathlib
import StacksProject_2024.Chap04.Lemma_4_43_3
import StacksProject_2024.Chap18.Definition_18_32_1
import StacksProject_2024.Chap18.Lemma_18_32_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C]

/- Domain-style sampling for Definition 18.32.6:
- primary domain: Picard groups of ringed sites as isomorphism classes of invertible
  `\mathcal O`-modules under tensor product;
- sampled owner declarations:
  `CommRing.Pic`,
  `Functor.IsEquivalence (tensorRight ℒ)`,
  `ObjectProperty.FullSubcategory`,
  `Skeleton`,
  `SymmetricCategory`;
- best owner abstraction:
  the canonical owner is the additive type of the units group of the skeleton of the full
  subcategory of invertible `\mathcal O`-modules, in the ambient symmetric monoidal module
  category;
- primitive data:
  the invertible-module object property on `ringedSiteModuleCategory J 𝒪`;
- derived API:
  the Picard-group owner type with its canonical abelian-group structure, the canonical class map,
  scoped textbook notation, and the source-facing tensor/unit/dual class formulas.

Source/core/bridge triage:
- `source-facing`: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site;
- `core/canonical`: `Additive ((Skeleton (((fun ℒ ↦ Functor.IsEquivalence (tensorRight ℒ)) :
    ObjectProperty (ringedSiteModuleCategory J 𝒪)).FullSubcategory))ˣ)`;
- `bridge/view`: the class map sending an invertible module to the corresponding unit in that
  skeleton.
-/

private instance invertiblePropIsMonoidal
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ObjectProperty.IsMonoidal
      ((fun ℒ : ringedSiteModuleCategory J 𝒪 ↦ Functor.IsEquivalence (tensorRight ℒ)) :
        ObjectProperty (ringedSiteModuleCategory J 𝒪)) where
  prop_unit := by
    exact
      (tensorRight_isEquivalence_iff_exists_tensor_inverse
        (𝟙_ (ringedSiteModuleCategory J 𝒪))).2
        ⟨𝟙_ (ringedSiteModuleCategory J 𝒪), ⟨λ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))⟩,
          ⟨ρ_ (𝟙_ (ringedSiteModuleCategory J 𝒪))⟩⟩
  prop_tensor X Y hX hY := by
    letI : Functor.IsEquivalence (tensorRight X) := hX
    letI : Functor.IsEquivalence (tensorRight Y) := hY
    exact inferInstance

private abbrev ringedSitePicardRaw
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  (Skeleton
    (ObjectProperty.FullSubcategory
      ((fun ℒ : ringedSiteModuleCategory J 𝒪 ↦ Functor.IsEquivalence (tensorRight ℒ)) :
        ObjectProperty (ringedSiteModuleCategory J 𝒪))))ˣ

/-- Definition 18.32.6: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site is the
abelian group of isomorphism classes of invertible `\mathcal O`-modules, with addition induced by
tensor product. -/
def ringedSitePicardGroup
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  Additive (ringedSitePicardRaw J 𝒪)

/- Textbook notation for the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site. -/
scoped[RingedSitePicard] notation:max "Pic(" 𝒪 ")" => _root_.ringedSitePicardGroup _ 𝒪

open scoped RingedSitePicard

namespace ringedSitePicardGroup

private abbrev invertibleProperty
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ObjectProperty (ringedSiteModuleCategory J 𝒪) :=
  fun ℒ ↦ Functor.IsEquivalence (tensorRight ℒ)

private noncomputable instance
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)] :
    CommGroup (ringedSitePicardRaw J 𝒪) := by
  dsimp [ringedSitePicardRaw]
  infer_instance

instance
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)] :
    AddCommGroup (_root_.ringedSitePicardGroup J 𝒪) :=
  Additive.addCommGroup

private noncomputable def mkRaw
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ : ringedSiteModuleCategory J 𝒪) [Functor.IsEquivalence (tensorRight ℒ)] :
    ringedSitePicardRaw J 𝒪 := by
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) :=
    fun ℒ ↦ Functor.IsEquivalence (tensorRight ℒ)
  let L : ObjectProperty.FullSubcategory P := ⟨ℒ, inferInstance⟩
  let h := (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).1 inferInstance
  let 𝒩 : ringedSiteModuleCategory J 𝒪 := Classical.choose h
  let h𝒩 := Classical.choose_spec h
  let eLN : ℒ ⊗ 𝒩 ≅ 𝟙_ (ringedSiteModuleCategory J 𝒪) := Classical.choice h𝒩.1
  let eNL : 𝒩 ⊗ ℒ ≅ 𝟙_ (ringedSiteModuleCategory J 𝒪) := Classical.choice h𝒩.2
  letI : (tensorRight 𝒩).IsEquivalence :=
    (tensorRight_isEquivalence_iff_exists_tensor_inverse 𝒩).2 ⟨ℒ, ⟨eNL⟩, ⟨eLN⟩⟩
  let N : ObjectProperty.FullSubcategory P := ⟨𝒩, inferInstance⟩
  have hLN : toSkeleton L * toSkeleton N = 1 := by
    refine (Skeleton.toSkeleton_tensorObj L N).symm.trans ?_
    exact Quotient.sound ⟨P.isoMk eLN⟩
  have hNL : toSkeleton N * toSkeleton L = 1 := by
    refine (Skeleton.toSkeleton_tensorObj N L).symm.trans ?_
    exact Quotient.sound ⟨P.isoMk eNL⟩
  exact Units.mk (toSkeleton L) (toSkeleton N) hLN hNL

/-- The Picard class of an invertible `\mathcal O`-module. -/
protected noncomputable def mk
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ : ringedSiteModuleCategory J 𝒪) [Functor.IsEquivalence (tensorRight ℒ)] :
    _root_.ringedSitePicardGroup J 𝒪 :=
  Additive.ofMul (mkRaw J 𝒪 ℒ)

private noncomputable def reprSubcategory
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (x : Pic(𝒪)) :
    (invertibleProperty J 𝒪).FullSubcategory :=
  (fromSkeleton (invertibleProperty J 𝒪).FullSubcategory).obj (Additive.toMul x).1

/-- The canonical invertible-module representative of a Picard class, obtained from the skeleton
used to define `\mathrm{Pic}(\mathcal O)`. -/
protected noncomputable def repr
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (x : Pic(𝒪)) :
    ringedSiteModuleCategory J 𝒪 :=
  (reprSubcategory J 𝒪 x).1

/-- The canonical representative of a Picard class is invertible. -/
protected noncomputable instance repr_isInvertible
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (x : Pic(𝒪)) :
    Functor.IsEquivalence (tensorRight (ringedSitePicardGroup.repr J 𝒪 x)) := by
  simpa [ringedSitePicardGroup.repr, reprSubcategory] using
    (reprSubcategory J 𝒪 x).2

/-- The canonical representative of the Picard class of an invertible module is isomorphic to the
given module. -/
theorem repr_mk_iso
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Nonempty (ringedSitePicardGroup.repr J 𝒪 (ringedSitePicardGroup.mk J 𝒪 ℒ) ≅ ℒ) := by
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := invertibleProperty J 𝒪
  let L : P.FullSubcategory := ⟨ℒ, inferInstance⟩
  refine ⟨?_⟩
  simpa [ringedSitePicardGroup.repr, reprSubcategory, ringedSitePicardGroup.mk, mkRaw, P, L] using
    P.ι.mapIso (fromSkeletonToSkeletonIso L)

/-- Two Picard classes are equal as soon as their canonical representatives are isomorphic. -/
theorem eq_of_repr_iso
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    {x y : Pic(𝒪)}
    (e : Nonempty (ringedSitePicardGroup.repr J 𝒪 x ≅ ringedSitePicardGroup.repr J 𝒪 y)) :
    x = y := by
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := invertibleProperty J 𝒪
  let X : P.FullSubcategory := reprSubcategory J 𝒪 x
  let Y : P.FullSubcategory := reprSubcategory J 𝒪 y
  rcases e with ⟨e⟩
  change Additive.toMul x = Additive.toMul y
  apply Units.ext
  -- Compare the value components of the two raw units in the skeleton model.
  change (Additive.toMul x).1 = (Additive.toMul y).1
  simpa [X, Y, reprSubcategory] using
    ((toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk e⟩ :
      toSkeleton X = toSkeleton Y)

-- Proof sketch: equality in the skeleton quotient of invertible modules is exactly isomorphism
-- of the underlying modules.
/-- Two invertible `\mathcal O`-modules define the same Picard class exactly when they are
isomorphic. -/
theorem mk_eq_mk_iff
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight 𝒩)] :
    ringedSitePicardGroup.mk J 𝒪 ℒ = ringedSitePicardGroup.mk J 𝒪 𝒩 ↔
      Nonempty (ℒ ≅ 𝒩) := by
  constructor
  · intro h
    -- Compare both modules to the canonical representatives of their common Picard class.
    rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 ℒ with ⟨eℒ⟩
    rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 𝒩 with ⟨e𝒩⟩
    -- Transport the class equality through `repr` to identify the canonical representatives.
    have hrepr :
        ringedSitePicardGroup.repr J 𝒪 (ringedSitePicardGroup.mk J 𝒪 ℒ) =
          ringedSitePicardGroup.repr J 𝒪 (ringedSitePicardGroup.mk J 𝒪 𝒩) := by
      simpa using congrArg (ringedSitePicardGroup.repr J 𝒪) h
    refine ⟨eℒ.symm ≪≫ ?_ ≪≫ e𝒩⟩
    exact eqToIso hrepr
  · rintro ⟨e⟩
    -- An isomorphism of representatives identifies the corresponding Picard classes.
    apply ringedSitePicardGroup.eq_of_repr_iso J 𝒪
    rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 ℒ with ⟨eℒ⟩
    rcases ringedSitePicardGroup.repr_mk_iso J 𝒪 𝒩 with ⟨e𝒩⟩
    exact ⟨eℒ ≪≫ e ≪≫ e𝒩.symm⟩

-- Proof sketch: the underlying unit of `mk J 𝒪 𝒪` is the tensor unit class in the skeleton.
/-- The neutral class in `\mathrm{Pic}(\mathcal O)` is represented by the structure module
`\mathcal O`. -/
theorem mk_unit
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)] :
    ringedSitePicardGroup.mk J 𝒪 (unitModule J 𝒪) = (0 : Pic(𝒪)) := by
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := invertibleProperty J 𝒪
  let L : P.FullSubcategory := ⟨unitModule J 𝒪, inferInstance⟩
  -- Pass to the multiplicative skeleton model where the neutral element is explicit.
  change mkRaw J 𝒪 (unitModule J 𝒪) = 1
  apply Units.ext
  -- Normalize the goal to the value component of the raw unit before rewriting the skeleton unit.
  change (mkRaw J 𝒪 (unitModule J 𝒪)).1 = (1 : Skeleton P.FullSubcategory)
  -- The structure module is isomorphic to the tensor unit, so they define the same skeleton class.
  rw [CategoryTheory.Skeleton.one_eq]
  simpa [mkRaw, P, L] using
    ((toSkeleton_eq_toSkeleton_iff).2
    ⟨P.isoMk (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := 𝒪))⟩
      : toSkeleton L = toSkeleton (𝟙_ P.FullSubcategory))

-- Proof sketch: combine `mk_eq_mk_iff` with `mk_unit`.
/-- An invertible `\mathcal O`-module is trivial in the Picard group exactly when it is
isomorphic to the structure module. -/
theorem mk_eq_zero_iff
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    ringedSitePicardGroup.mk J 𝒪 ℒ = (0 : Pic(𝒪)) ↔
      Nonempty (ℒ ≅ unitModule J 𝒪) := by
  -- Rewrite the zero class as the Picard class of the structure module.
  rw [← ringedSitePicardGroup.mk_unit J 𝒪]
  exact ringedSitePicardGroup.mk_eq_mk_iff J 𝒪 ℒ (unitModule J 𝒪)

-- Proof sketch: multiplication of units in the skeleton is induced by tensor product of
-- representatives.
/-- Addition in `\mathrm{Pic}(\mathcal O)` is induced by tensor product of invertible
`\mathcal O`-modules. -/
theorem mk_tensor
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
    [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)]
    [Functor.IsEquivalence (tensorRight 𝒩)] :
    (ringedSitePicardGroup.mk J 𝒪 (ℒ ⊗ 𝒩) : Pic(𝒪)) =
      ringedSitePicardGroup.mk J 𝒪 ℒ + ringedSitePicardGroup.mk J 𝒪 𝒩 := by
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := invertibleProperty J 𝒪
  let L : P.FullSubcategory := ⟨ℒ, inferInstance⟩
  let N : P.FullSubcategory := ⟨𝒩, inferInstance⟩
  -- In the raw units model, addition is multiplication and is computed by tensoring objects.
  change mkRaw J 𝒪 (ℒ ⊗ 𝒩) = mkRaw J 𝒪 ℒ * mkRaw J 𝒪 𝒩
  apply Units.ext
  -- The value component of `mkRaw` records exactly the skeleton class of the object.
  simpa [mkRaw, P, L, N] using (CategoryTheory.Skeleton.toSkeleton_tensorObj L N)

section Duality

variable (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: the evaluation isomorphism trivializes
-- `\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`,
-- and `mk_tensor` then identifies the dual class with the inverse of `[\mathcal L]`.
/-- Negation in `\mathrm{Pic}(\mathcal O)` is represented by the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
theorem mk_internalHom_unit
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    (ringedSitePicardGroup.mk J 𝒪 ((ihom ℒ).obj (unitModule J 𝒪)) : Pic(𝒪)) =
      -ringedSitePicardGroup.mk J 𝒪 ℒ := by
  let D : ringedSiteModuleCategory J 𝒪 := (ihom ℒ).obj (unitModule J 𝒪)
  letI : Functor.IsEquivalence (tensorRight D) :=
    SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible
      (J := J) (𝒪 := 𝒪) ℒ
  letI : Functor.IsEquivalence (tensorRight (ℒ ⊗ D)) :=
    SheafOfModules.RingedSite.isInvertible_tensor_of_isInvertible (J := J) (𝒪 := 𝒪) ℒ D
  have hEvalIso : Nonempty (ℒ ⊗ D ≅ unitModule J 𝒪) := by
    let e :
        (ℒ ⊗ D) ≅ SheafOfModules.unit (ringSheaf J 𝒪) :=
      @asIso (ringedSiteModuleCategory J 𝒪) _ _ _
        ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪)))
        (SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible
          (J := J) (𝒪 := 𝒪) ℒ)
    -- The imported evaluation isomorphism identifies the tensor product with the structure module.
    refine ⟨?_⟩
    simpa [D, unitModule] using e
  have hzero :
      (ringedSitePicardGroup.mk J 𝒪 (ℒ ⊗ D) : Pic(𝒪)) = 0 := by
    -- The tensor product with the internal-Hom dual is trivial in the Picard group.
    exact (ringedSitePicardGroup.mk_eq_zero_iff J 𝒪 (ℒ ⊗ D)).2 hEvalIso
  have hsum :
      (ringedSitePicardGroup.mk J 𝒪 ℒ : Pic(𝒪)) + ringedSitePicardGroup.mk J 𝒪 D = 0 := by
    -- Rewrite the sum using tensor product and then apply the trivialization above.
    calc
      (ringedSitePicardGroup.mk J 𝒪 ℒ : Pic(𝒪)) + ringedSitePicardGroup.mk J 𝒪 D =
          ringedSitePicardGroup.mk J 𝒪 (ℒ ⊗ D) := by
        symm
        exact ringedSitePicardGroup.mk_tensor J 𝒪 ℒ D
      _ = 0 := hzero
  -- Solve the additive equation for the dual class.
  simpa [D] using eq_neg_of_add_eq_zero_right hsum

end Duality

end ringedSitePicardGroup

end
