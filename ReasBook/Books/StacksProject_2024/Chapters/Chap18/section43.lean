import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_43_1 (from Chap18) -/
universe u v w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

/- Domain-style sampling for Definition 18.43.1:
- primary domain: locally constant sheaves on a site and their finite variants.
- sampled owner-level declarations:
  `CategoryTheory.Sheaf.IsConstant`,
  `CategoryTheory.constantSheaf`,
  `GrothendieckTopology.over`,
  `GrothendieckTopology.overPullback`.
- best owner abstraction: `Sheaf.IsLocallyConstant`, built from the canonical restriction
  functors `F.over` and the owner predicate `Sheaf.IsConstant` on slice sites.
- primitive data: for each `U : C`, a covering in `J.over U` on which the restricted sheaf is
  constant.
- derived API: finite locally constant variants, obtained by adjoining finiteness conditions on
  the local constant models.

Source/core/bridge triage:
- `source-facing`: `Sheaf.IsLocallyConstant`, `Sheaf.IsFiniteLocallyConstant`,
  `Sheaf.IsFiniteLocallyConstantGrp`, `Sheaf.IsFiniteLocallyConstantAddCommGrp`,
  `Sheaf.IsFiniteTypeLocallyConstantModule`.
- `core/canonical`: `Sheaf.IsConstant`, `constantSheaf`, and sheaf restriction to slice sites.
- `bridge/view`: the constant-sheaf instances showing that a global constant sheaf is locally
  constant, and that finite constant models yield finite locally constant sheaves. -/

section Constant

variable {D : Type w} [Category.{w'} D] [HasWeakSheafify J D]

/- Constant sheaf recall: for a sheaf of sets, groups, abelian groups, rings, modules, and
similar algebraic objects on a site `(C, J)`, being a constant sheaf is the canonical mathlib
predicate `Sheaf.IsConstant`, meaning that the sheaf lies in the essential image of the constant
sheaf functor. -/
#check IsConstant

end Constant

section LocallyConstant

variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- Definition 18.43.1 (1): a sheaf on a site is locally constant if, after restricting to the
localized site above any object `U`, there is a covering family of `U` on which the further
restrictions become constant sheaves. -/
class IsLocallyConstant (F : Sheaf J D) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is constant. -/
  exists_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I, IsConstant (J.over (X i).left) (F.over (X i).left)

-- Proof sketch: for each object `U`, use the singleton covering of `U` by the identity
-- `𝟙_U : U ⟶ U`; the restriction of a constant sheaf to `U` is again constant by functoriality
-- of `constantSheaf` with respect to localization.
/-- A constant sheaf is locally constant. -/
instance isLocallyConstant_of_isConstant (F : Sheaf J D) [IsConstant J F] :
    IsLocallyConstant F := sorry

end LocallyConstant

section FiniteLocallyConstantTypes

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- Definition 18.43.1 (2): a set-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite value. -/
class IsFiniteLocallyConstant (F : Sheaf J (Type w)) : Prop extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ E : Type w, Finite E ∧
            Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) (Type w)).obj E)

-- Proof sketch: use the identity covering of each object `U`; the restriction of the constant
-- sheaf with value `E` is again the constant sheaf with value `E`, and the given `Finite E`
-- supplies the finiteness condition on the local model.
/-- A constant sheaf of finite sets is finite locally constant. -/
instance isFiniteLocallyConstant_of_constant (E : Type w) [Finite E] :
    IsFiniteLocallyConstant ((constantSheaf J (Type w)).obj E) := sorry

end FiniteLocallyConstantTypes

section FiniteLocallyConstantGroups

variable [HasWeakSheafify J GrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) GrpCat.{w}]

/-- Definition 18.43.1 (3): a group-valued sheaf is finite locally constant if, locally on every
object of the site, it is isomorphic to a constant sheaf with finite group value. -/
class IsFiniteLocallyConstantGrp (F : Sheaf J GrpCat.{w}) : Prop extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite group value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ E : GrpCat.{w}, Finite E ∧
            Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) GrpCat.{w}).obj E)

-- Proof sketch: again use the identity covering of each object. Restricting a constant
-- `GrpCat`-valued sheaf preserves its constant value, and finiteness of the underlying group is
-- unchanged under this restriction.
/-- A constant sheaf of finite groups is finite locally constant. -/
instance isFiniteLocallyConstantGrp_of_constant (E : GrpCat.{w}) [Finite E] :
    IsFiniteLocallyConstantGrp ((constantSheaf J GrpCat.{w}).obj E) := sorry

end FiniteLocallyConstantGroups

section FiniteLocallyConstantAddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

/-- Definition 18.43.1 (variant): an abelian-group-valued sheaf is finite locally constant if,
locally on every object of the site, it is isomorphic to a constant sheaf with finite abelian
group value. -/
class IsFiniteLocallyConstantAddCommGrp (F : Sheaf J AddCommGrpCat.{w}) : Prop
    extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite abelian-group value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ A : AddCommGrpCat.{w}, Finite A ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) AddCommGrpCat.{w}).obj A)

-- Proof sketch: use the identity covering of each object. Restricting a constant abelian-group
-- sheaf preserves its constant value, and the given finiteness instance remains valid on every
-- slice site.
/-- A constant sheaf of finite abelian groups is finite locally constant. -/
instance isFiniteLocallyConstantAddCommGrp_of_constant
    (A : AddCommGrpCat.{w}) [Finite A] :
    IsFiniteLocallyConstantAddCommGrp ((constantSheaf J AddCommGrpCat.{w}).obj A) := sorry

end FiniteLocallyConstantAddCommGroups

section FiniteTypeLocallyConstantModules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- Definition 18.43.1 (variant): a `\Lambda`-module-valued sheaf is locally constant of finite
type if, locally on every object of the site, it is isomorphic to a constant sheaf with finite
type module value. -/
class IsFiniteTypeLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop
    extends IsLocallyConstant F where
  /-- Every object admits a covering on which the restriction of `F` is a constant sheaf with
  finite type `\Lambda`-module value. -/
  exists_finite_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ M : ModuleCat.{w} Λ, Module.Finite Λ M ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M)

-- Proof sketch: use the identity covering of each object. Restricting a constant sheaf with
-- value `M` preserves the same constant model, and the given `Module.Finite Λ M` instance
-- supplies the finite-type condition on each local chart.
/-- A constant sheaf of finite type `\Lambda`-modules is locally constant of finite type. -/
instance isFiniteTypeLocallyConstantModule_of_constant
    (M : ModuleCat.{w} Λ) [Module.Finite Λ M] :
    IsFiniteTypeLocallyConstantModule ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := sorry

end FiniteTypeLocallyConstantModules

end Sheaf

end CategoryTheory

/-! ### Lemma_18_43_2 (from Chap18) -/
open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ w

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.43.2:
- primary domain: inverse image for morphisms of topoi and locally constant sheaves.
- sampled owner/bridge declarations:
  `Sheaf.IsLocallyConstant`,
  the inverse-image notation `f⁻¹`,
  `sheaf_pullback_forget`,
  `MorphismOfTopoiIn.presentationFunctor_inverseImageIso`.
- best owner abstraction: the source-facing theorem should be stated directly for the canonical
  inverse-image functor `f⁻¹` of a morphism of topoi; forget-compatibility for algebraic-valued
  sheaves is derived bridge data.
- primitive data: a morphism of topoi `f`, a sheaf `𝒢`, and local constancy of `𝒢`.
- derived API: the set-valued inverse image `f⁻¹ 𝒢` is locally constant, plus the companion
  bridge theorem for `A`-valued inverse image functors commuting with the forgetful functor. -/

namespace Sheaf

/-- Local constancy is invariant under isomorphism. -/
theorem isLocallyConstant_of_iso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C}
    [HasWeakSheafify J D] [∀ U : C, HasWeakSheafify (J.over U) D]
    {F G : Sheaf J D} (e : F ≅ G) [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant G := sorry

end Sheaf

-- Proof sketch: use the compatibility isomorphism `hforget` to identify the underlying
-- set-valued sheaf of `inverseImageA.obj G` with the inverse image of the underlying set-valued
-- sheaf of `G`, then transport local constancy across this isomorphism.
private theorem inverseImageA_isLocallyConstant_of_forget
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A]
    {FA : A → A → Type u₄} {CA : A → Type u₅}
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [JC.HasSheafCompose (forget A)] [JD.HasSheafCompose (forget A)]
    [HasWeakSheafify JC (Type u₅)] [HasWeakSheafify JD (Type u₅)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type u₅)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type u₅)]
    (f : MorphismOfTopoiIn JD JC)
    (inverseImageA : Sheaf JD A ⥤ Sheaf JC A)
    (hforget :
      inverseImageA ⋙ sheafCompose JC (forget A) ≅
        sheafCompose JD (forget A) ⋙ f⁻¹)
    (𝒢 : Sheaf JD A)
    [Sheaf.IsLocallyConstant ((sheafCompose JD (forget A)).obj 𝒢)] :
    Sheaf.IsLocallyConstant ((sheafCompose JC (forget A)).obj (inverseImageA.obj 𝒢)) := sorry

-- Proof sketch: this is the direct set-valued specialization of the preceding forget-compatibility
-- bridge, using that `forget (Type w)` is definitionally the identity functor and hence
-- `sheafCompose _ (forget (Type w))` is definitionally the identity on set-valued sheaves.
/-- Lemma 18.43.2: if `f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)` is a morphism of
topoi and `\mathcal G` is a locally constant sheaf of sets on `\mathcal D`, then its inverse
image `f^{-1}\mathcal G` is a locally constant sheaf of sets on `\mathcal C`. -/
theorem inverseImage_isLocallyConstant
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]
    (f : MorphismOfTopoiIn JD JC)
    (𝒢 : Sheaf JD (Type w))
    [Sheaf.IsLocallyConstant 𝒢] :
    Sheaf.IsLocallyConstant ((f⁻¹).obj 𝒢) := by
  let _ : Sheaf.IsLocallyConstant ((sheafCompose JD (forget (Type w))).obj 𝒢) := by
    simpa using (inferInstance : Sheaf.IsLocallyConstant 𝒢)
  simpa using
    inverseImageA_isLocallyConstant_of_forget f (f⁻¹) (Iso.refl _) 𝒢

/-- Companion bridge theorem: if forgetting a sheaf `\mathcal G` in a concrete algebraic
category on `\mathcal D` yields a locally constant sheaf of sets, then after pulling back along a
morphism of topoi `f : \mathit{Sh}(\mathcal C) \to \mathit{Sh}(\mathcal D)`, the underlying
set-valued sheaf of the chosen `A`-valued inverse image is again locally constant. -/
theorem inverseImage_isLocallyConstant_of_forget
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A]
    {FA : A → A → Type u₄} {CA : A → Type u₅}
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [JC.HasSheafCompose (forget A)] [JD.HasSheafCompose (forget A)]
    [HasWeakSheafify JC (Type u₅)] [HasWeakSheafify JD (Type u₅)]
    [∀ X : C, HasWeakSheafify (JC.over X) (Type u₅)]
    [∀ Y : D, HasWeakSheafify (JD.over Y) (Type u₅)]
    (f : MorphismOfTopoiIn JD JC)
    (inverseImageA : Sheaf JD A ⥤ Sheaf JC A)
    (hforget :
      inverseImageA ⋙ sheafCompose JC (forget A) ≅
        sheafCompose JD (forget A) ⋙ f.inverseImage)
    (𝒢 : Sheaf JD A)
    [Sheaf.IsLocallyConstant ((sheafCompose JD (forget A)).obj 𝒢)] :
    Sheaf.IsLocallyConstant ((sheafCompose JC (forget A)).obj (inverseImageA.obj 𝒢)) :=
  inverseImageA_isLocallyConstant_of_forget f inverseImageA hforget 𝒢

end CategoryTheory

/-! ### Lemma_18_43_3 (from Chap18) -/
noncomputable section

universe u v w

namespace CategoryTheory

namespace Sheaf

/- Domain-style sampling for Lemma 18.43.3:
- primary domain: locally constant sheaves and morphisms that become maps between constant sheaf
  models after restricting to a cover.
- sampled owner-level declarations:
  `CategoryTheory.CommSq`,
  `CategoryTheory.constantSheaf`,
  `CategoryTheory.Sheaf.IsConstant`,
  `CategoryTheory.Sheaf.IsLocallyConstant`,
  `CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp`.
- best owner abstraction: `CategoryTheory.CommSq` for the comparison between a sheaf morphism and
  a chosen map of constant models; the local constant-data predicates remain source-facing owners
  for the covering statements.
- primitive data: chosen constant models for the source and target together with a morphism
  between their constant values.
- derived API: the commuting square relating the original sheaf morphism to that map of constant
  sheaves, and the existence of coverings on which such squares exist.

Source/core/bridge triage:
- `source-facing`: the three existence theorems below.
- `core/canonical`: `CommSq`, `constantSheaf`, and the locally constant owners from
  `Definition_18_43_1`.
- `bridge/view`: the local witnesses showing that a restricted morphism is induced by a map
  between chosen constant models. -/

section MainStatements

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

-- Proof sketch: trivialize the finite locally constant source and the locally constant target on a
-- common covering family of the terminal object. Because the chosen source value is finite, one
-- can refine further so that the restricted morphism is locally determined by a single function on
-- that finite set, yielding a morphism of constant sheaves on each member of the refined cover.
/-- Lemma 18.43.3 (1): for a morphism of locally constant sheaves of sets whose source is finite
locally constant, there is a covering of the terminal object on which the restriction fits into a
commutative square with a map of constant sheaves associated with a map of sets. -/
theorem exists_coversTop_restriction_isConstantSheafMap_type
    {F G : Sheaf J (Type w)} (φ : F ⟶ G) [IsFiniteLocallyConstant F]
    [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (A B : Type w) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj B),
            CommSq ((J.overPullback (Type w) (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) (Type w)).map f) := sorry

end Types

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

-- Proof sketch: trivialize the finite locally constant source and the locally constant target on a
-- common covering family of the terminal object. The source has finite underlying set locally, so
-- after refining the cover the restricted morphism is determined by one homomorphism on the chosen
-- constant model, and hence is a morphism of constant abelian sheaves on each covering object.
/-- Lemma 18.43.3 (2): for a morphism of locally constant sheaves of abelian groups whose source
is finite locally constant, there is a covering of the terminal object on which the restriction is
part of a commutative square with a map of constant abelian sheaves associated with a homomorphism
of abelian groups. -/
theorem exists_coversTop_restriction_isConstantSheafMap_addCommGrp
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
    [IsFiniteLocallyConstantAddCommGrp F] [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (A B : AddCommGrpCat.{w}) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj B),
            CommSq ((J.overPullback AddCommGrpCat.{w} (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) AddCommGrpCat.{w}).map f) := sorry

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

-- Proof sketch: choose a cover on which the source is constant with finitely generated module
-- value and the target is constant. After refining, finitely many generators of the source have
-- images coming from fixed sections of the constant target model, which defines a single
-- `\Lambda`-linear map inducing the restricted morphism on each member of the cover.
/-- Lemma 18.43.3 (3): for a morphism of locally constant sheaves of `\Lambda`-modules whose
source is locally constant of finite type, there is a covering of the terminal object on which the
restriction fits into a commutative square with a map of constant sheaves of `\Lambda`-modules
associated with a `\Lambda`-linear map. -/
theorem exists_coversTop_restriction_isConstantSheafMap_module
    {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
    [IsFiniteTypeLocallyConstantModule F] [IsLocallyConstant G] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        ∃ (M N : ModuleCat.{w} Λ) (f : M ⟶ N)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj M)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj N),
            CommSq ((J.overPullback (ModuleCat.{w} Λ) (U i)).map φ) eF.hom eG.hom
              ((constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).map f) := sorry

end Modules

end MainStatements

end Sheaf

end CategoryTheory

/-! ### Lemma_18_43_4 (from Chap18) -/
open CategoryTheory Opposite

noncomputable section

universe u v w z

namespace CategoryTheory

namespace Sheaf

section FinitePresentationLocallyConstantModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- A locally constant sheaf of `\Lambda`-modules is of finite presentation if locally it is
isomorphic to a constant sheaf with finitely presented module value. -/
class IsFinitePresentationLocallyConstantModule (F : Sheaf J (ModuleCat.{w} Λ)) : Prop
    extends IsLocallyConstant (J := J) (D := ModuleCat.{w} Λ) F where
  /-- Every object admits a covering on which the restriction of the sheaf is constant with
  finitely presented `\Lambda`-module value. -/
  exists_finitePresentation_constant_cover :
    ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ M : ModuleCat.{w} Λ, Module.FinitePresentation Λ M ∧
            Nonempty (F.over (X i).left ≅
              (constantSheaf (J.over (X i).left) (ModuleCat.{w} Λ)).obj M)

-- Proof sketch: use the identity covering of each object `U`; the restriction of a constant
-- sheaf with value `M` remains constant with the same value, and the given finite-presentation
-- instance on `M` supplies the local finite-presentation condition.
/-- A constant sheaf with finitely presented value is finite-presentation locally constant. -/
instance isFinitePresentationLocallyConstantModule_of_constant
    (M : ModuleCat.{w} Λ) [Module.FinitePresentation Λ M] :
    IsFinitePresentationLocallyConstantModule
      ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := sorry

end FinitePresentationLocallyConstantModules

end Sheaf

section IsoSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]

-- Proof sketch: restriction along the identity functor on `Over X` is the identity, so the map
-- on local isomorphisms is pointwise the identity.
/-- Restriction along the identity morphism acts trivially on local isomorphisms. -/
theorem sheafIsoPresheaf_map_id
    (F G : Sheaf J (ModuleCat.{w} Λ)) (X : Cᵒᵖ)
    (φ : (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
      (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G) :
    (J.overMapPullback (ModuleCat.{w} Λ) (𝟙 X.unop)).mapIso φ = φ := sorry

-- Proof sketch: restriction of local isomorphisms is functorial, so restricting first along `g`
-- and then along `f` agrees with restricting once along `f ≫ g`.
/-- Restriction of local isomorphisms is compatible with composition. -/
theorem sheafIsoPresheaf_map_comp
    (F G : Sheaf J (ModuleCat.{w} Λ)) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
      (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G) :
    (J.overMapPullback (ModuleCat.{w} Λ) ((f ≫ g).unop)).mapIso φ =
      (J.overMapPullback (ModuleCat.{w} Λ) g.unop).mapIso
        ((J.overMapPullback (ModuleCat.{w} Λ) f.unop).mapIso φ) := sorry

/-- The presheaf of local isomorphisms between two sheaves of `\Lambda`-modules on a site. -/
def sheafIsoPresheaf
    (F G : Sheaf J (ModuleCat.{w} Λ)) : Cᵒᵖ ⥤ Type (max u v w) where
  obj X := (J.overPullback (ModuleCat.{w} Λ) X.unop).obj F ≅
    (J.overPullback (ModuleCat.{w} Λ) X.unop).obj G
  map f := fun φ ↦ (J.overMapPullback (ModuleCat.{w} Λ) f.unop).mapIso φ
  map_id := by
    intro X
    funext φ
    exact sheafIsoPresheaf_map_id (Λ := Λ) F G X φ
  map_comp := by
    intro X Y Z f g
    funext φ
    exact sheafIsoPresheaf_map_comp (Λ := Λ) F G f g φ

-- Proof sketch: local isomorphisms glue by applying the sheaf condition to the forward and
-- inverse morphisms in the sheaves `sheafHom F G` and `sheafHom G F`; the glued maps remain
-- inverse by uniqueness of gluing.
/-- The presheaf of local isomorphisms satisfies the sheaf condition. -/
theorem sheafIsoPresheaf_isSheaf (F G : Sheaf J (ModuleCat.{w} Λ)) :
    Presheaf.IsSheaf J (sheafIsoPresheaf (J := J) F G) := sorry

/-- The sheaf of local isomorphisms between two sheaves of `\Lambda`-modules on a site. -/
def sheafIso (F G : Sheaf J (ModuleCat.{w} Λ)) : Sheaf J (Type (max u v w)) :=
  ⟨sheafIsoPresheaf (J := J) F G, sheafIsoPresheaf_isSheaf (J := J) F G⟩

end IsoSheaf

section MainStatements

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section ConstantHom

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]

-- Proof sketch: present `M` by a finite free module, apply the sheaf of local
-- `\Lambda`-linear maps from the corresponding constant sheaves into `\underline N`, and reduce
-- to the finite free case where this sheaf is visibly the constant sheaf with value
-- `\operatorname{Hom}_\Lambda(M, N)`.
/-- Lemma 18.43.4 (1): if `M` is finitely presented, then the sheaf of local
`\Lambda`-linear maps from the constant sheaf `\underline M` to the constant sheaf `\underline N`
is a constant sheaf, namely the constant sheaf with value `\operatorname{Hom}_\Lambda(M, N)`. -/
theorem sheafHom_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{w} Λ) [Module.FinitePresentation Λ M] :
    Sheaf.IsConstant J
      (sheafHom
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{w} Λ)).obj N)) := sorry

end ConstantHom

section ConstantIso

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]

-- Proof sketch: by the previous clause the local Hom sheaf between `\underline M` and
-- `\underline N` is constant; the local isomorphism sheaf is the subsheaf of those sections whose
-- inverses lie in the corresponding constant Hom sheaf in the opposite direction, so it is again
-- constant with value `\operatorname{Isom}_\Lambda(M, N)`.
/-- Lemma 18.43.4 (2): if `M` and `N` are finitely presented, then the sheaf of local
isomorphisms between the constant sheaves `\underline M` and `\underline N` is a constant sheaf,
namely the constant sheaf with value `\operatorname{Isom}_\Lambda(M, N)`. -/
theorem sheafIso_constantSheaf_isConstant_of_finitePresentation
    (M N : ModuleCat.{w} Λ)
    [Module.FinitePresentation Λ M] [Module.FinitePresentation Λ N] :
    Sheaf.IsConstant J
      (sheafIso
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M)
        ((constantSheaf J (ModuleCat.{w} Λ)).obj N)) := sorry

end ConstantIso

section LocallyConstantHom

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]

-- Proof sketch: the assertion is local on the site. On a covering where `F` is identified with a
-- constant sheaf of a finitely presented module and `G` with a constant sheaf, apply clause (1)
-- to identify the restricted sheaf of local `\Lambda`-linear maps with a constant sheaf; these
-- local identifications give local constancy of the whole Hom sheaf.
/-- Lemma 18.43.4 (3): if `\mathcal F` is a locally constant sheaf of `\Lambda`-modules of finite
presentation and `\mathcal G` is locally constant, then the sheaf of local `\Lambda`-linear maps
from `\mathcal F` to `\mathcal G` is locally constant. -/
theorem sheafHom_isLocallyConstant_of_finitePresentationLocallyConstant
    (F G : Sheaf J (ModuleCat.{w} Λ))
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) F]
    [Sheaf.IsLocallyConstant (J := J) (D := ModuleCat.{w} Λ) G] :
    Sheaf.IsLocallyConstant (J := J) (D := Type (max u v w)) (sheafHom F G) := sorry

end LocallyConstantHom

section LocallyConstantIso

variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify J (Type (max u v w))]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type (max u v w))]

-- Proof sketch: apply clause (3) in both directions to obtain local constancy of the Hom sheaves
-- `\mathcal H\!om(\mathcal F, \mathcal G)` and `\mathcal H\!om(\mathcal G, \mathcal F)`. The
-- local isomorphism sheaf is the subsheaf cut out by the equations expressing that a section and
-- its inverse compose to the identity, hence it is locally constant as well.
/-- Lemma 18.43.4 (4): if `\mathcal F` and `\mathcal G` are locally constant sheaves of
`\Lambda`-modules of finite presentation, then the sheaf of local isomorphisms
`\mathit{Isom}_{\underline{\Lambda}}(\mathcal F, \mathcal G)` is locally constant. -/
theorem sheafIso_isLocallyConstant_of_finitePresentationLocallyConstant
    (F G : Sheaf J (ModuleCat.{w} Λ))
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) F]
    [Sheaf.IsFinitePresentationLocallyConstantModule (J := J) G] :
    Sheaf.IsLocallyConstant
      (J := J) (D := Type (max u v w)) (sheafIso F G) := sorry

end LocallyConstantIso

end MainStatements

end CategoryTheory

/-! ### Lemma_18_43_5 (from Chap18) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w u₁

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Sets

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

-- Proof sketch: work locally on the site and use the local triviality criterion from the previous
-- lemma to reduce a finite diagram of finite locally constant sheaves to a diagram of constant
-- finite sets. Finite limits of finite sets are finite, and the associated constant sheaf computes
-- the ambient sheaf limit locally.
/-- Lemma 18.43.5 (1): finite locally constant sheaves of sets are closed under finite limits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under limits of that shape. -/
theorem isFiniteLocallyConstant_isClosedUnderFiniteLimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K := sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderLimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderLimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteLimits K

-- Proof sketch: after local trivialization, a finite diagram becomes a diagram of constant sheaves
-- attached to finite sets. Finite colimits of finite sets are finite, so the ambient sheaf colimit
-- is again locally a constant finite sheaf.
/-- Lemma 18.43.5 (2): finite locally constant sheaves of sets are closed under finite colimits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under colimits of that shape. -/
theorem isFiniteLocallyConstant_isClosedUnderFiniteColimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K := sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderColimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderColimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteColimits K

end Sets

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

-- Proof sketch: apply the weak-LinearRepresentations_Serre_1977 criterion recorded in the imported owner abstraction.
-- Kernels and cokernels are handled locally by trivializing maps, and extensions are checked after
-- refining to a cover where the end terms are constant finite abelian sheaves.
/-- Lemma 18.43.5 (3): finite locally constant abelian sheaves form a weak LinearRepresentations_Serre_1977 subcategory of
`Ab(\mathcal C)`. -/
theorem isFiniteLocallyConstantAddCommGrp_isWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J AddCommGrpCat.{w} ↦ IsFiniteLocallyConstantAddCommGrp F) :=
  sorry

/-- Finite locally constant abelian sheaves carry their canonical weak-LinearRepresentations_Serre_1977 instance. -/
instance isFiniteLocallyConstantAddCommGrp_instWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J AddCommGrpCat.{w} ↦ IsFiniteLocallyConstantAddCommGrp F) :=
  isFiniteLocallyConstantAddCommGrp_isWeakSerreClass

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

-- Proof sketch: again use the weak-LinearRepresentations_Serre_1977 criterion. After local trivialization, kernels and
-- cokernels are kernels and cokernels of maps of finite type `\Lambda`-modules; the Noetherian
-- hypothesis guarantees these remain finite type, and the extension argument follows from the
-- pushout description in the source text.
/-- Lemma 18.43.5 (4): for a Noetherian ring `\Lambda`, locally constant sheaves of finite type
`\Lambda`-modules form a weak LinearRepresentations_Serre_1977 subcategory of `Mod(\mathcal C, \Lambda)`. -/
theorem isFiniteTypeLocallyConstantModule_isWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J (ModuleCat.{w} Λ) ↦ IsFiniteTypeLocallyConstantModule F) :=
  sorry

/-- Finite type locally constant module sheaves carry their canonical weak-LinearRepresentations_Serre_1977 instance. -/
instance isFiniteTypeLocallyConstantModule_instWeakSerreClass :
    IsWeakSerreClass
      (fun F : Sheaf J (ModuleCat.{w} Λ) ↦ IsFiniteTypeLocallyConstantModule F) :=
  isFiniteTypeLocallyConstantModule_isWeakSerreClass

end Modules

end

end Sheaf
end CategoryTheory

/-! ### Lemma_18_43_6 (from Chap18) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory

namespace Sheaf

section Modules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

/- Domain-style sampling for Lemma 18.43.6:
- primary domain: locally constant sheaves on a site and their behavior under the monoidal tensor on
  `Sheaf J (ModuleCat Λ)`;
- sampled owner declarations:
  `Sheaf.IsConstant`,
  `Sheaf.IsLocallyConstant`,
  `Sheaf.isLocallyConstant_of_isConstant`,
  `((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat Λ))).IsMonoidal`,
  `Sheaf.monoidalCategory`;
- best owner abstraction: the source-facing owner for local triviality is the earlier chapter
  declaration `Sheaf.IsLocallyConstant`; the tensor product is the canonical sheaf monoidal owner
  `Sheaf.monoidalCategory J (ModuleCat Λ)` induced from the site-level monoidal condition on
  `J.W`, not an arbitrary ambient monoidal structure on the sheaf category;
- primitive data: two sheaves `F`, `G` together with their `Sheaf.IsLocallyConstant` instances;
- derived API: the closure theorem asserting `Sheaf.IsLocallyConstant (F ⊗ G)`.

Source/core/bridge triage:
- `source-facing`: closure of locally constant sheaves of `Λ`-modules under tensor product;
- `core/canonical`: `Sheaf.IsLocallyConstant` from `Definition_18_43_1`;
- `bridge/view`: the canonical passage from the site-level monoidal hypothesis on `J.W` to the
  sheaf tensor via `Sheaf.monoidalCategory`.
-/

local instance : MonoidalCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.monoidalCategory J (ModuleCat.{w} Λ)

-- Proof sketch: choose a common refinement of local trivializing covers for `F` and `G`. On each
-- member of that refinement the restricted sheaves are constant, and the tensor product of two
-- constant sheaves of `Λ`-modules is again constant with value the tensor product of the constant
-- module values.
/-- Lemma 18.43.6: the tensor product of two locally constant sheaves of `\Lambda`-modules on a
site is locally constant. -/
theorem isLocallyConstant_tensor
    {F G : Sheaf J (ModuleCat.{w} Λ)} [IsLocallyConstant F]
    [IsLocallyConstant G] :
    IsLocallyConstant (F ⊗ G) := sorry

end Modules

end Sheaf

end CategoryTheory
