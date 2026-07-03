import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_32_1 (from Chap18) -/
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

/-! ### Lemma_18_32_2 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.2:
- primary domain: invertible `\mathcal O`-modules on a ringed site and their standard derived
  consequences;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `CategoryTheory.tensorRight_isEquivalence_iff_exists_tensor_inverse`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `leftDualToRingedSiteModuleDual`,
  `isIso_leftDualToRingedSiteModuleDual`;
- best owner abstractions:
  the chapter owners `IsInvertible`, `IsFlat`,
  `IsFinitePresentation`, `IsLocallyDirectSummandOfFiniteFree`, and the source-facing internal Hom
  to the structure sheaf on `ringedSiteModuleCategory J 𝒪`, together with the Chapter 4 tensor
  inverse owner theorem specialized to `ringedSiteModuleCategory J 𝒪`;
- primitive data:
  an invertible module `ℒ`, the two-sided tensor-inverse witness owned upstream by
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`, its symmetric one-sided reformulation
  `ℒ ⊗ 𝒩 ≅ \mathcal O`, and the source-facing internal-Hom object
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`;
- derived API:
  flatness, finite presentation, the local direct-summand criterion, and the canonical comparison
  with internal Hom.

Source/core/bridge triage:
- `source-facing`: the five clauses of Stacks Lemma 18.32.2;
- `core/canonical`: `IsInvertible`, `IsFlat`, `IsFinitePresentation`,
  `IsLocallyDirectSummandOfFiniteFree`,
  `tensorRight_isEquivalence_iff_exists_tensor_inverse`,
  `(ihom ℒ).obj (SheafOfModules.unit (ringSheaf J 𝒪))`,
  `leftDualToRingedSiteModuleDual`, and `isIso_leftDualToRingedSiteModuleDual`;
- `bridge/view`: the symmetric one-sided tensor-trivialization statement in clause `(1)`.
-/

section TensorInverse

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: the canonical owner theorem in Chapter 4 identifies invertibility with a
-- two-sided tensor inverse. In the symmetric monoidal category of `\mathcal O`-modules, the
-- second trivialization is equivalent to the first via the braiding, so the source-facing
-- one-sided statement is equivalent to the owner theorem.
/-- Lemma 18.32.2 (1): an `\mathcal O`-module on a ringed site is invertible if and only if it
admits a tensor inverse `\mathcal N` with `\mathcal L \otimes_{\mathcal O} \mathcal N \cong
\mathcal O`. -/
theorem isInvertible_iff_exists_tensor_inverse
    (ℒ : ringedSiteModuleCategory J 𝒪) :
    IsInvertible ℒ ↔
      ∃ 𝒩 : ringedSiteModuleCategory J 𝒪,
        Nonempty (ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) := sorry

end TensorInverse

section Flat

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: tensoring with an invertible module is an equivalence, hence an exact functor,
-- and flatness is defined by exactness of tensoring with the given module.
/-- Lemma 18.32.2 (2): an invertible `\mathcal O`-module on a ringed site is flat. -/
theorem isFlat_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsFlat 𝒪 ℒ := sorry

end Flat

-- Proof sketch: invertible modules are locally tensor-trivial, hence locally free of rank one;
-- the Chapter 18 ringed-site owner `IsFinitePresentation` is local on restrictions, and free
-- rank-one modules are finitely presented on every localized site.
section FinitePresentation

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

/-- Lemma 18.32.2 (3): an invertible `\mathcal O`-module on a ringed site is of finite
presentation. -/
theorem isFinitePresentation_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsFinitePresentation ℒ := sorry

end FinitePresentation

section LocalDirectSummand

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, ∀ X : Over U, HasWeakSheafify ((J.over U).over X) AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, ∀ X : Over U, ((J.over U).over X).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]

-- Proof sketch: combine the flatness from clause (2) with clause (3), then apply the canonical
-- local direct-summand criterion of Lemma `18.29.3`.
/-- Lemma 18.32.2 (4): an invertible `\mathcal O`-module on a ringed site is locally a direct
summand of a finite free `\mathcal O`-module. Equivalently, for every object `U`, after passing to
a covering of `U`, the restriction becomes a direct summand of a finite free `\mathcal O_U`-module.
-/
theorem isLocallyDirectSummandOfFiniteFree_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsLocallyDirectSummandOfFiniteFree ℒ := sorry

end LocalDirectSummand

section InternalHom

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: the trivialization `e` supplies left-duality data for `𝒩` against `ℒ`; reuse
-- the owner comparison morphism from Lemma `18.29.2` rather than restating the conclusion as a
-- chosen comparison morphism. The chosen exact pairing remains private proof scaffolding, while
-- the public clause stays source-facing as an existential isomorphism.
private theorem nonempty_exactPairing_of_tensor_inverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    Nonempty (ExactPairing 𝒩 ℒ) := sorry

@[implicit_reducible] private noncomputable def exactPairingOfTensorInverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    ExactPairing 𝒩 ℒ :=
  Classical.choice (nonempty_exactPairing_of_tensor_inverse ℒ 𝒩 e)

/-- Lemma 18.32.2 (5): if `\mathcal L \otimes_{\mathcal O} \mathcal N \cong \mathcal O`, then
`\mathcal N` is isomorphic to the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
theorem nonempty_iso_ringedSiteModuleDual_of_tensor_inverse
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    (e : ℒ ⊗ 𝒩 ≅ SheafOfModules.unit (ringSheaf J 𝒪)) :
    Nonempty (𝒩 ≅ ringedSiteModuleDual ℒ) := by
  letI : ExactPairing 𝒩 ℒ := exactPairingOfTensorInverse ℒ 𝒩 e
  letI : IsIso (leftDualToRingedSiteModuleDual ℒ 𝒩) :=
    isIso_leftDualToRingedSiteModuleDual ℒ 𝒩
  exact ⟨asIso (leftDualToRingedSiteModuleDual ℒ 𝒩)⟩

end InternalHom

end SheafOfModules.RingedSite

/-! ### Lemma_18_32_3 (from Chap18) -/
open CategoryTheory
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {E : Type u} [Category.{u} E] {J : GrothendieckTopology E}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {C : Type u} [SmallCategory C]
variable {D : Type u} [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (F : D ⥤ C)
variable [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪C : Sheaf JC CommRingCat.{u}} {𝒪D : Sheaf JD CommRingCat.{u}}
variable
  (φ :
    ringSheaf JD 𝒪D ⟶
      (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj
        (ringSheaf JC 𝒪C))
variable [(SheafOfModules.pushforward φ).IsRightAdjoint]
variable [MonoidalCategory (ringedSiteModuleCategory JC 𝒪C)]
variable [MonoidalCategory (ringedSiteModuleCategory JD 𝒪D)]

-- Proof sketch: choose a tensor inverse of `ℒ` using Lemma `18.32.2`, pull back the tensor
-- trivialization, use the tensor-pullback comparison from Lemma `18.26.2` together with the
-- canonical identification of pullback of the structure module, and apply Lemma `18.32.2` again
-- on the source ringed site.
/-- Lemma 18.32.3: for a site-presentation of a morphism of ringed topoi, the pullback of an
invertible `\mathcal O_\mathcal D`-module is invertible. -/
theorem pullback_isInvertible
    (ℒ : ringedSiteModuleCategory JD 𝒪D)
    [@IsInvertible _ _ JD 𝒪D _ _ ℒ] :
    @IsInvertible _ _ JC 𝒪C _ _
      (((SheafOfModules.pullback φ).obj ℒ) : ringedSiteModuleCategory JC 𝒪C) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_18_32_4 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.4:
- primary domain: invertible objects and duality in the symmetric monoidal closed category
  `ringedSiteModuleCategory J 𝒪`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `ringedSiteModuleDual`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.nonempty_iso_ringedSiteModuleDual_of_tensor_inverse`;
- best owner abstraction:
  `IsInvertible` on `ringedSiteModuleCategory J 𝒪`, with the tensor product `ℒ ⊗ 𝒩`,
  `ringedSiteModuleDual`, and the closed-structure evaluation at the tensor unit as derived API;
- primitive data:
  invertible modules `ℒ` and `𝒩`;
- derived API:
  invertibility of `ℒ ⊗ 𝒩`, invertibility of `ringedSiteModuleDual ℒ`, and the `IsIso`
  statement for the evaluation map at `SheafOfModules.unit (ringSheaf J 𝒪)`.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 18.32.4;
- `core/canonical`: `IsInvertible`, `ringedSiteModuleDual`, and
  `(ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))`;
- `bridge/view`: the tensor-inverse and dual-comparison theorems from Lemma 18.32.2.
-/

section Tensor

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: right tensoring by `\mathcal L \otimes_{\mathcal O} \mathcal N` is the composite
-- of right tensoring by `\mathcal L` and by `\mathcal N`, so it is an equivalence when each
-- factor is.
/-- Lemma 18.32.4 (1): if `\mathcal L` and `\mathcal N` are invertible `\mathcal O`-modules on a
ringed site, then their tensor product `\mathcal L \otimes_{\mathcal O} \mathcal N` is
invertible. -/
theorem isInvertible_tensor_of_isInvertible
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] [IsInvertible 𝒩] :
    IsInvertible (ℒ ⊗ 𝒩) := sorry

instance instIsInvertibleTensor
    (ℒ 𝒩 : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] [IsInvertible 𝒩] :
    IsInvertible (ℒ ⊗ 𝒩) :=
  isInvertible_tensor_of_isInvertible ℒ 𝒩

end Tensor

section Duality

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: by Lemma `18.32.2 (1)`, choose a tensor inverse `𝒩` for `ℒ`; then Lemma
-- `18.32.2 (5)` identifies `𝒩` with `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L,
-- \mathcal O)`, so the internal Hom inherits invertibility from the tensor inverse.
/-- Lemma 18.32.4 (2): if `\mathcal L` is an invertible `\mathcal O`-module on a ringed site,
then `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` is invertible. -/
theorem isInvertible_internalHom_unit_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsInvertible (ringedSiteModuleDual ℒ) := sorry

instance instIsInvertibleRingedSiteModuleDual
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsInvertible (ringedSiteModuleDual ℒ) :=
  isInvertible_internalHom_unit_of_isInvertible ℒ

-- Proof sketch: identify `\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)` with a
-- tensor inverse of `ℒ` via Lemma `18.32.2 (5)`. Under this identification, the evaluation map
-- becomes the chosen trivialization `\mathcal L \otimes_{\mathcal O} \mathcal L^\vee \cong
-- \mathcal O`, hence it is an isomorphism.
/-- Lemma 18.32.4 (3): for an invertible `\mathcal O`-module `\mathcal L` on a ringed site, the
evaluation map
`\mathcal L \otimes_{\mathcal O} \mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)
\to \mathcal O` is an isomorphism. -/
theorem isIso_internalHom_unit_evaluation_of_isInvertible
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) := sorry

instance instIsIsoInternalHomUnitEvaluation
    (ℒ : ringedSiteModuleCategory J 𝒪)
    [IsInvertible ℒ] :
    IsIso ((ihom.ev ℒ).app (SheafOfModules.unit (ringSheaf J 𝒪))) :=
  isIso_internalHom_unit_evaluation_of_isInvertible ℒ

end Duality

end SheafOfModules.RingedSite

/-! ### Lemma_18_32_5 (from Chap18) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.5:
- primary domain: categorical smallness of invertible `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `ObjectProperty.EssentiallySmall`,
  `ObjectProperty.EssentiallySmall.exists_small`,
  `AlgebraicGeometry.RingedSpace.exists_set_of_invertible_module_representatives`;
- best owner abstraction:
  the object property `(IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))`;
- primitive data:
  only the invertibility predicate on objects of `ringedSiteModuleCategory J 𝒪`;
- derived API:
  essential smallness of that owner property and the source-facing representative set obtained
  from the skeleton of a small full subcategory produced by the canonical `exists_small` API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claim that invertible modules admit a set of
  representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.EssentiallySmall
    ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)))`;
- `bridge/view`: the internal small object property whose iso-closure is the invertible-module
  owner property, and the skeleton-based representative set extracted from it.
-/

/-- Invertible modules on a ringed site are closed under isomorphisms. -/
instance isInvertible_isClosedUnderIsomorphisms
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] →
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)) := by
  sorry

section

variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: invertible modules are produced from set-sized local free rank-one data and
-- gluing data over coverings, so the owner object property `IsInvertible` is essentially small.
/-- Core/canonical companion to Lemma 18.32.5: invertible `\mathcal O`-modules on a ringed site
form an essentially small object property. -/
instance invertibleModuleProperty_essentiallySmall
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ObjectProperty.EssentiallySmall.{max u v}
      ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))) := by
  sorry

-- Proof sketch: apply the canonical `ObjectProperty.EssentiallySmall.exists_small` API to the
-- invertible-module owner property to get a small full subcategory whose iso-closure recovers it,
-- then choose one object from each isomorphism class via the skeleton of that small full
-- subcategory.
omit [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 18.32.5: on a ringed site `(\mathcal C, \mathcal O)`, there is a set of representatives
for the isomorphism classes of invertible `\mathcal O`-modules. Equivalently, every invertible
module is isomorphic to a unique chosen representative. -/
theorem exists_set_of_invertible_module_representatives
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ∃ S : Set (ringedSiteModuleCategory J 𝒪),
      ∀ (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ],
        ∃! 𝒩 : ringedSiteModuleCategory J 𝒪, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℒ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{max u v}
      ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)))
  let F : Skeleton P.FullSubcategory ⥤ ringedSiteModuleCategory J 𝒪 :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set (ringedSiteModuleCategory J 𝒪) := Set.range F.obj
  refine ⟨S, ?_⟩
  intro ℒ hℒ'
  letI : IsInvertible ℒ := hℒ'
  have hℒ : P.isoClosure ℒ := by
    rw [← hP]
    infer_instance
  rw [ObjectProperty.prop_isoClosure_iff] at hℒ
  rcases hℒ with ⟨M, hM, ⟨e⟩⟩
  let Y : P.FullSubcategory := ⟨M, hM⟩
  refine ⟨F.obj (toSkeleton Y), ?_, ?_⟩
  · constructor
    · exact ⟨toSkeleton Y, rfl⟩
    · exact ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)) ≪≫ e.symm⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨⟨q, rfl⟩, ⟨e'⟩⟩
    have hq : q = toSkeleton Y := by
      rw [← toSkeleton_fromSkeleton_obj q]
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk (e' ≪≫ e)⟩
    simpa using congrArg F.obj hq

end

end SheafOfModules.RingedSite

/-! ### Definition_18_32_6 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

section

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Definition 18.32.6:
- primary domain: Picard groups of ringed sites as isomorphism classes of invertible
  `\mathcal O`-modules under tensor product;
- sampled owner declarations:
  `CommRing.Pic`,
  `IsInvertible`,
  `ObjectProperty.FullSubcategory`,
  `Skeleton`;
- best owner abstraction:
  the canonical owner is the units group of the skeleton of the full subcategory of invertible
  `\mathcal O`-modules, exactly mirroring the mathlib `CommRing.Pic` design but at the ambient
  ringed-site module category;
- primitive data:
  the invertible-module object property on `ringedSiteModuleCategory J 𝒪`;
- derived API:
  the Picard-group owner type, its additive-group structure, the canonical class map, scoped
  textbook notation, and the source-facing tensor/unit/dual class formulas.

Source/core/bridge triage:
- `source-facing`: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site;
- `core/canonical`: the skeleton of the full subcategory of invertible `\mathcal O`-modules,
  viewed through its units;
- `bridge/view`: the class map sending an invertible module to the corresponding unit in that
  skeleton.
-/

local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

private abbrev InvertibleModuleCat
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  ObjectProperty.FullSubcategory
    (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))

private theorem tensorUnit_isInvertible :
    IsInvertible (𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  let e :
      tensorRight (𝟙_ (ringedSiteModuleCategory J 𝒪)) ≅
        𝟭 (ringedSiteModuleCategory J 𝒪) :=
    MonoidalCategory.rightUnitorNatIso (ringedSiteModuleCategory J 𝒪)
  exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private instance isInvertibleIsMonoidal :
    ObjectProperty.IsMonoidal
      (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)) where
  prop_unit := tensorUnit_isInvertible (J := J) (𝒪 := 𝒪)
  prop_tensor X Y hX hY := by
    let e :
        tensorRight
            (MonoidalCategoryStruct.tensorObj X Y :
              ringedSiteModuleCategory J 𝒪) ≅
          tensorRight X ⋙ tensorRight Y :=
      tensorRightTensor X Y
    letI : IsInvertible X := hX
    letI : IsInvertible Y := hY
    exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private theorem exists_chosenTensorInverse
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    ∃ D : ringedSiteModuleCategory J 𝒪,
      Nonempty
        ((MonoidalCategoryStruct.tensorObj ℒ D :
            ringedSiteModuleCategory J 𝒪) ≅
          𝟙_ (ringedSiteModuleCategory J 𝒪)) ∧
      Nonempty
        ((MonoidalCategoryStruct.tensorObj D ℒ :
            ringedSiteModuleCategory J 𝒪) ≅
          𝟙_ (ringedSiteModuleCategory J 𝒪)) :=
  (tensorRight_isEquivalence_iff_exists_tensor_inverse ℒ).1
    (show (tensorRight ℒ).IsEquivalence from inferInstance)

private noncomputable def chosenTensorInverseObj
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    ringedSiteModuleCategory J 𝒪 := by
  classical
  exact Classical.choose (exists_chosenTensorInverse J 𝒪 ℒ)

private theorem chosenTensorInverseObj_leftIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((MonoidalCategoryStruct.tensorObj ℒ (chosenTensorInverseObj J 𝒪 ℒ) :
          ringedSiteModuleCategory J 𝒪) ≅
        𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  classical
  exact (Classical.choose_spec (exists_chosenTensorInverse J 𝒪 ℒ)).1

private theorem chosenTensorInverseObj_rightIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((MonoidalCategoryStruct.tensorObj (chosenTensorInverseObj J 𝒪 ℒ) ℒ :
          ringedSiteModuleCategory J 𝒪) ≅
        𝟙_ (ringedSiteModuleCategory J 𝒪)) := by
  classical
  exact (Classical.choose_spec (exists_chosenTensorInverse J 𝒪 ℒ)).2

private noncomputable def chosenTensorInverse
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    InvertibleModuleCat J 𝒪 := by
  classical
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  exact ⟨D, hD⟩

private theorem chosenTensorInverse_tensorIso
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      ((⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ⊗
          chosenTensorInverse J 𝒪 ℒ ≅
        𝟙_ (InvertibleModuleCat J 𝒪)) := by
  classical
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := IsInvertible
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  change
    Nonempty
      ((⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ⊗ ⟨D, hD⟩ ≅
        𝟙_ (InvertibleModuleCat J 𝒪))
  rcases hLD with ⟨e⟩
  exact ⟨P.isoMk e⟩

private theorem chosenTensorInverse_tensorIso_symm
    (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ] :
    Nonempty
      (chosenTensorInverse J 𝒪 ℒ ⊗
          (⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ≅
        𝟙_ (InvertibleModuleCat J 𝒪)) := by
  classical
  let P : ObjectProperty (ringedSiteModuleCategory J 𝒪) := IsInvertible
  let D := chosenTensorInverseObj J 𝒪 ℒ
  have hLD := chosenTensorInverseObj_leftIso J 𝒪 ℒ
  have hDL := chosenTensorInverseObj_rightIso J 𝒪 ℒ
  have hD : IsInvertible D := by
    refine { toIsEquivalence := ?_ }
    exact (tensorRight_isEquivalence_iff_exists_tensor_inverse D).2 ⟨ℒ, hDL, hLD⟩
  change
    Nonempty
      (⟨D, hD⟩ ⊗ (⟨ℒ, inferInstance⟩ : InvertibleModuleCat J 𝒪) ≅
        𝟙_ (InvertibleModuleCat J 𝒪))
  rcases hDL with ⟨e⟩
  exact ⟨P.isoMk e⟩

private abbrev PicardMultiplicative
    (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{u})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] : Type _ :=
  (Skeleton (InvertibleModuleCat J 𝒪))ˣ

/-- Definition 18.32.6: the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site is the
abelian group of isomorphism classes of invertible `\mathcal O`-modules, with addition induced by
tensor product. -/
def ringedSitePicardGroup : Type _ :=
  Additive (PicardMultiplicative J 𝒪)

/- Textbook notation for the Picard group `\mathrm{Pic}(\mathcal O)` of a ringed site. -/
scoped[RingedSitePicard] notation:max "Pic(" 𝒪 ")" => _root_.ringedSitePicardGroup _ 𝒪

open scoped RingedSitePicard

namespace ringedSitePicardGroup

local notation "Picard" => _root_.ringedSitePicardGroup J 𝒪

instance : AddGroup Picard :=
  Additive.addGroup

section Tensor

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (ringedSiteModuleCategory J 𝒪)]

private instance instIsInvertibleTensor
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    IsInvertible (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) := by
  let e :
      tensorRight (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) ≅
        tensorRight ℒ ⋙ tensorRight 𝒩 :=
    tensorRightTensor ℒ 𝒩
  exact { toIsEquivalence := (Functor.isEquivalence_iff_of_iso e).2 inferInstance }

private noncomputable def mkMul
    (ℒ : Mod) [IsInvertible ℒ] :
    PicardMultiplicative J 𝒪 :=
  let L : InvertibleModuleCat J 𝒪 := ⟨ℒ, inferInstance⟩
  let D := chosenTensorInverse J 𝒪 ℒ
  have hLD : toSkeleton L * toSkeleton D = 1 := by
    rw [Skeleton.mul_eq, Skeleton.one_eq]
    rcases chosenTensorInverse_tensorIso J 𝒪 ℒ with ⟨e⟩
    exact (toSkeleton_eq_toSkeleton_iff).2
      ⟨(fromSkeletonToSkeletonIso L ⊗ᵢ fromSkeletonToSkeletonIso D) ≪≫ e⟩
  have hDL : toSkeleton D * toSkeleton L = 1 := by
    rw [Skeleton.mul_eq, Skeleton.one_eq]
    rcases chosenTensorInverse_tensorIso_symm J 𝒪 ℒ with ⟨e⟩
    exact (toSkeleton_eq_toSkeleton_iff).2
      ⟨(fromSkeletonToSkeletonIso D ⊗ᵢ fromSkeletonToSkeletonIso L) ≪≫ e⟩
  Units.mk (toSkeleton L) (toSkeleton D) hLD hDL

/-- The Picard class of an invertible `\mathcal O`-module. -/
protected noncomputable def mk
    (ℒ : Mod) [IsInvertible ℒ] :
    Picard :=
  Additive.ofMul (mkMul J 𝒪 ℒ)

-- Proof sketch: equality in the quotient of invertible modules is exactly isomorphism of the
-- underlying modules.
/-- Two invertible `\mathcal O`-modules define the same Picard class exactly when they are
isomorphic. -/
theorem mk_eq_mk_iff
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    _root_.ringedSitePicardGroup.mk J 𝒪 ℒ = _root_.ringedSitePicardGroup.mk J 𝒪 𝒩 ↔
      Nonempty (ℒ ≅ 𝒩) := by
  let P : ObjectProperty Mod := IsInvertible
  let L : InvertibleModuleCat J 𝒪 := ⟨ℒ, inferInstance⟩
  let N : InvertibleModuleCat J 𝒪 := ⟨𝒩, inferInstance⟩
  change mkMul J 𝒪 ℒ = mkMul J 𝒪 𝒩 ↔ Nonempty (ℒ ≅ 𝒩)
  constructor
  · intro h
    have hs : toSkeleton L = toSkeleton N := by
      simpa [mkMul, L, N] using congrArg Units.val h
    rcases (toSkeleton_eq_toSkeleton_iff).1 hs with ⟨e⟩
    exact ⟨P.ι.mapIso e⟩
  · intro h
    rcases h with ⟨e⟩
    apply Units.ext
    have hs : toSkeleton L = toSkeleton N := by
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk e⟩
    simpa [mkMul, L, N] using hs

/-- The Picard group of a ringed site carries its canonical abelian-group structure. -/
instance : AddCommGroup Picard :=
  Additive.addCommGroup

-- Proof sketch: the neutral class is the quotient class of the structure module itself.
/-- The neutral class in `\mathrm{Pic}(\mathcal O)` is represented by the structure module
`\mathcal O`. -/
theorem mk_unit :
    _root_.ringedSitePicardGroup.mk J 𝒪 (SheafOfModules.unit (ringSheaf J 𝒪) : Mod) =
      (0 : Pic(𝒪)) := by
  sorry

-- Proof sketch: combine `mk_eq_mk_iff` with the fact that `0` is the class of the structure
-- module.
/-- An invertible `\mathcal O`-module is trivial in the Picard group exactly when it is
isomorphic to the structure module. -/
theorem mk_eq_zero_iff
    (ℒ : Mod)
    [IsInvertible ℒ] :
    _root_.ringedSitePicardGroup.mk J 𝒪 ℒ = (0 : Pic(𝒪)) ↔
      Nonempty (ℒ ≅ SheafOfModules.unit (ringSheaf J 𝒪)) := by
  sorry

-- Proof sketch: addition on the quotient is induced by tensor product on representatives.
/-- Addition in `\mathrm{Pic}(\mathcal O)` is induced by tensor product of invertible
`\mathcal O`-modules. -/
theorem mk_tensor
    (ℒ 𝒩 : Mod)
    [IsInvertible ℒ]
    [IsInvertible 𝒩] :
    (_root_.ringedSitePicardGroup.mk J 𝒪
      (MonoidalCategoryStruct.tensorObj ℒ 𝒩 : Mod) : Pic(𝒪)) =
      _root_.ringedSitePicardGroup.mk J 𝒪 ℒ + _root_.ringedSitePicardGroup.mk J 𝒪 𝒩 := by
  sorry

-- Proof sketch: inversion in the quotient is induced by the internal-Hom dual on
-- representatives.
/-- Negation in `\mathrm{Pic}(\mathcal O)` is represented by the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O}(\mathcal L, \mathcal O)`. -/
theorem mk_internalHom_unit
    (ℒ : Mod)
    [IsInvertible ℒ] :
    (_root_.ringedSitePicardGroup.mk J 𝒪 (ringedSiteModuleDual ℒ) : Pic(𝒪)) =
      -_root_.ringedSitePicardGroup.mk J 𝒪 ℒ := by
  sorry

end Tensor

end ringedSitePicardGroup

end
