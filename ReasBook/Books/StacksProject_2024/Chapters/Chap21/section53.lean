import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_53_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [∀ U : C, ∀ V : Over U, HasWeakSheafify ((J.over U).over V) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- A complex of sheaves of `\Lambda`-modules is bounded finite-type locally constant if it is
bounded and each term is a locally constant sheaf of finite type. -/
def CochainComplex.IsBoundedFiniteTypeLocallyConstant
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) : Prop :=
  (∃ a b : ℤ, L.IsStrictlyGE a ∧ L.IsStrictlyLE b) ∧
    ∀ n : ℤ, IsFiniteTypeLocallyConstantModule (L.X n)

/-- A derived object has bounded finite-type locally constant cohomology if it is bounded and
each cohomology sheaf is locally constant of finite type. -/
def DerivedCategory.HasBoundedFiniteTypeLocallyConstantCohomology
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) : Prop :=
  (∃ a b : ℤ, K.IsGE a ∧ K.IsLE b) ∧
    ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K)

-- Proof sketch: argue by induction on the cohomological amplitude of `K`. After refining to a
-- cover of the terminal object, make the top nonzero cohomology sheaf constant of finite type,
-- choose a surjection from a finite free constant sheaf, and form the cone to reduce the
-- amplitude. The weak-LinearRepresentations_Serre_1977 closure of locally constant finite-type sheaves keeps the cone in the
-- same class, so on each member of the cover one obtains a bounded complex of locally constant
-- finite-type sheaves whose cohomology identifies with the restricted cohomology sheaves of `K`.
/-- Lemma 21.53.1: if `K ∈ D^b(\mathcal C, \Lambda)` has cohomology sheaves locally constant of
finite type and `X` is a final object of the site, then there exists a covering of `X` such that
on each slice site `(C/U_i, J.over U_i)` there is a bounded complex of locally constant sheaves of
finite type `\Lambda`-modules whose cohomology sheaves identify with the restrictions of the
cohomology sheaves of `K`. This is the statement-stage encoding of the textbook claim that each
`K|_{U_i}` is represented by such a complex. -/
theorem exists_cover_restriction_represented_by_bounded_finite_type_locally_constant_complex
    (X : C) (_hX : Limits.IsTerminal X)
    (K : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hK : DerivedCategory.HasBoundedFiniteTypeLocallyConstantCohomology K) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      ∃ L : CochainComplex (Sheaf (J.over I.Y) (ModuleCat.{w} Λ)) ℤ,
        CochainComplex.IsBoundedFiniteTypeLocallyConstant L ∧
          ∀ n : ℤ,
            IsIsomorphic
              (L.homology n)
              ((localizedModuleRestriction I.Y).obj
                ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K)) := sorry

end

end CategoryTheory.Sheaf

/-! ### Lemma_21_53_2 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]

local instance : Limits.HasZeroMorphisms (Sheaf J (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

local instance (U : C) : Limits.HasZeroMorphisms (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The constant-sheaf functor on `\Lambda`-modules preserves zero morphisms. -/
instance constantSheaf_preservesZeroMorphisms :
    (constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- The functor sending a cochain complex of `\Lambda`-modules to the corresponding constant
complex of sheaves of `\Lambda`-modules on `(C, J)`. -/
abbrev constantModuleComplex :
    CochainComplex (ModuleCat.{w} Λ) ℤ ⥤
      CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  (constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- Restriction to the slice site over `U` preserves zero morphisms. -/
instance localizedModuleRestriction_preservesZeroMorphisms (U : C) :
    ((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)).PreservesZeroMorphisms := sorry

/-- Restriction to the slice site over `U` is additive. -/
instance localizedModuleRestriction_additive (U : C) :
    ((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)).Additive := sorry

/-- Restriction to the slice site over `U` preserves finite limits. -/
instance localizedModuleRestriction_preservesFiniteLimits (U : C) :
    Limits.PreservesFiniteLimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction to the slice site over `U` preserves finite colimits. -/
instance localizedModuleRestriction_preservesFiniteColimits (U : C) :
    Limits.PreservesFiniteColimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction of cochain complexes of sheaves of `\Lambda`-modules to the localized site over
`U`. -/
abbrev localizedModuleRestrictionComplex (U : C) :
    CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ ⥤
      CochainComplex (Sheaf (J.over U) (ModuleCat.{w} Λ)) ℤ :=
  (((localizedModuleRestriction U) :
      Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ))).mapHomologicalComplex
    (ComplexShape.up ℤ)

-- Proof sketch: after restricting the constant complex associated with `K` and the target complex
-- `L` to a suitable covering of the final object `X`, choose local morphisms of complexes between
-- those restrictions. In the full theorem, these become the local chain-level representatives of a
-- restricted derived morphism.
/-- Lemma 21.53.2: if `X` is a final object of the site, `K^\bullet` is a bounded complex of
finite projective `\Lambda`-modules, and `\mathcal L^\bullet` is a complex of sheaves of
`\Lambda`-modules, then there exists a covering of `X` on whose members there are morphisms of
complexes `\underline{K}^\bullet|_{U_i} \to \mathcal L^\bullet|_{U_i}`. -/
theorem exists_cover_local_chain_map_of_isBoundedFiniteProjective
    (X : C) (_hX : Limits.IsTerminal X)
    (K : CochainComplex (ModuleCat.{w} Λ) ℤ) [K.IsBoundedFiniteProjective]
    (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      Nonempty
        (((localizedModuleRestrictionComplex I.Y).obj (constantModuleComplex.obj K)) ⟶
          ((localizedModuleRestrictionComplex I.Y).obj L)) := sorry

end

end CategoryTheory.Sheaf

/-! ### Lemma_21_53_3 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, CategoryWithHomology (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- The constant-sheaf functor on `\Lambda`-modules is additive. -/
instance constantSheaf_additive :
    @Functor.Additive (ModuleCat.{w} Λ) (Sheaf J (ModuleCat.{w} Λ)) _ _
      ModuleCat.abelian.toPreadditive
      ((inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive)
      (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on `\Lambda`-modules preserves finite limits. -/
instance constantSheaf_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on `\Lambda`-modules preserves finite colimits. -/
instance constantSheaf_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` is additive. -/
instance constantSheaf_over_additive (U : C) :
    @Functor.Additive (ModuleCat.{w} Λ) (Sheaf (J.over U) (ModuleCat.{w} Λ)) _ _
      ModuleCat.abelian.toPreadditive
      ((inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive)
      (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` preserves finite limits. -/
instance constantSheaf_over_preservesFiniteLimits (U : C) :
    Limits.PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The constant-sheaf functor on the slice site over `U` preserves finite colimits. -/
instance constantSheaf_over_preservesFiniteColimits (U : C) :
    Limits.PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction of sheaves of `\Lambda`-modules from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestriction (U : C) :
    Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ) :=
  J.overPullback (ModuleCat.{w} Λ) U

/-- Restriction to the slice site over `U` is additive. -/
instance localizedModuleRestriction_additive (U : C) :
    @Functor.Additive (Sheaf J (ModuleCat.{w} Λ)) (Sheaf (J.over U) (ModuleCat.{w} Λ)) _ _
      ((inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive)
      ((inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive)
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction to the slice site over `U` preserves finite limits. -/
instance localizedModuleRestriction_preservesFiniteLimits (U : C) :
    Limits.PreservesFiniteLimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- Restriction to the slice site over `U` preserves finite colimits. -/
instance localizedModuleRestriction_preservesFiniteColimits (U : C) :
    Limits.PreservesFiniteColimits
      ((localizedModuleRestriction U) :
        Sheaf J (ModuleCat.{w} Λ) ⥤ Sheaf (J.over U) (ModuleCat.{w} Λ)) := sorry

/-- The exact functor on derived categories sending `K ∈ D(\Lambda)` to the constant sheaf
`\underline K ∈ D(\mathcal C, \Lambda)`. -/
abbrev constantModuleDerived :
    DerivedCategory (ModuleCat.{w} Λ) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (constantSheaf J (ModuleCat.{w} Λ))

/-- The exact functor on derived categories sending `K ∈ D(\Lambda)` to the constant derived
object on the slice site `(C/U, J.over U)`. -/
abbrev constantModuleDerivedOver (U : C) :
    DerivedCategory (ModuleCat.{w} Λ) ⥤
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (constantSheaf (J.over U) (ModuleCat.{w} Λ))

/-- The exact restriction functor on derived categories from `(C, J)` to the localized site
`(C/U, J.over U)`. -/
abbrev localizedModuleRestrictionDerived (U : C) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Functor.mapDerivedCategory (localizedModuleRestriction U)

/-- A restricted morphism of constant derived objects is induced by a fixed morphism
`α : K ⟶ L` in `D(\Lambda)` when, after identifying the restricted constant objects with the
constant derived objects on the slice site, it becomes the constant-sheaf image of `α`. -/
def IsLocalizedConstantDerivedMap
    (U : C) (K L : DerivedCategory (ModuleCat.{w} Λ)) (α : K ⟶ L)
    (φ :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K))) ⟶
        ((localizedModuleRestrictionDerived U).obj
          (((constantModuleDerived :
              DerivedCategory (ModuleCat.{w} Λ) ⥤
                DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L)))) : Prop :=
  ∃ eK :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K))) ≅
        ((constantModuleDerivedOver U).obj K),
    ∃ eL :
      ((localizedModuleRestrictionDerived U).obj
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L))) ≅
        ((constantModuleDerivedOver U).obj L),
      φ = eK.hom ≫
        (constantModuleDerivedOver U).map α ≫
          eL.inv

-- Proof sketch: choose a bounded finite-projective complex representing the perfect object `K`.
-- Apply Lemma `21.53.2` to obtain, after restricting to a cover of the terminal object, local
-- chain maps from the restricted constant complex of that representative. Degreewise, the source
-- terms are finite type locally constant, so Lemma `18.43.3` refines the cover until each local
-- chain map is induced by a chain map of constant sheaves. Passing to the derived category yields
-- local morphisms `α_i : K ⟶ L` whose constant-sheaf images agree with the restricted morphism.
/-- Lemma 21.53.3: if `X` is a final object of the site, `K, L ∈ D(\Lambda)`, `K` is perfect, and
`\varphi : \underline K \to \underline L` is a morphism in `D(\mathcal C, \Lambda)`, then after
restricting to some covering of `X` each local morphism is induced by a morphism
`\alpha_i : K \to L` in `D(\Lambda)`. In Lean, because the identification between the restricted
constant objects and the constant objects on the slice site is not definitional, this is expressed
using the explicit comparison proposition `IsLocalizedConstantDerivedMap`. -/
theorem exists_cover_restriction_eq_constant_derived_map_of_perfect
    (X : C) (_hX : Limits.IsTerminal X)
    (K L : DerivedCategory (ModuleCat.{w} Λ))
    (hK : DerivedCategory.IsPerfect K)
    (φ :
      (((constantModuleDerived :
          DerivedCategory (ModuleCat.{w} Λ) ⥤
            DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj K)) ⟶
        (((constantModuleDerived :
            DerivedCategory (ModuleCat.{w} Λ) ⥤
              DerivedCategory (Sheaf J (ModuleCat.{w} Λ))).obj L))) :
    ∃ T : J.Cover X, ∀ I : T.Arrow,
      ∃ α : K ⟶ L,
        IsLocalizedConstantDerivedMap I.Y K L α
          ((localizedModuleRestrictionDerived I.Y).map φ) := sorry

end

end CategoryTheory.Sheaf

/-! ### Lemma_21_53_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat.{w} Λ))]

-- Proof sketch: for each degree `n`, truncate `K` and `L` below `n - 1` so that the relevant
-- cohomology of `K ⊗ L` is unchanged. The bounded truncations satisfy Lemma `21.53.1`, so after a
-- cover they are represented by bounded complexes of locally constant finite-type sheaves. Replace
-- those by bounded above complexes of finite free `\Lambda`-modules and compute the derived tensor
-- product termwise; the resulting cohomology sheaf is again locally constant of finite type.
/-- Lemma 21.53.4: if `K, L ∈ D^-(\mathcal C, \Lambda)` and all cohomology sheaves of `K` and `L`
are locally constant sheaves of finite type `\Lambda`-modules, then every cohomology sheaf of the
derived tensor product `K \otimes_\Lambda^{\mathbf L} L` is locally constant of finite type. -/
theorem derivedTensor_cohomology_isFiniteTypeLocallyConstant
    [MonoidalCategoryStruct (DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))]
    (K L : DerivedCategory (Sheaf J (ModuleCat.{w} Λ)))
    (hKboundedAbove : ∃ a : ℤ, K.IsLE a)
    (hLboundedAbove : ∃ b : ℤ, L.IsLE b)
    (hK : ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj K))
    (hL : ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj L)) :
    ∀ n : ℤ,
      IsFiniteTypeLocallyConstantModule
        ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{w} Λ)) n).obj (K ⊗ L)) := sorry

end

end CategoryTheory.Sheaf

/-! ### Lemma_21_53_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat Λ)]
variable [Abelian (Sheaf J (ModuleCat Λ))]
variable [CategoryWithHomology (Sheaf J (ModuleCat Λ))]

local notation "Mod" => Sheaf J (ModuleCat Λ)
local notation "DMod" => DerivedCategory Mod
local notation "single0" => DerivedCategory.singleFunctor Mod (0 : ℤ)

/-- A sheaf of `\Lambda`-modules is locally constant of finite type over `\Lambda / I^n` when,
after forgetting to `\Lambda`-modules, it is locally constant of finite type and every local
section is annihilated by `I^n`. -/
def IsFiniteTypeLocallyConstantIdealPowerQuotientModule
    (I : Ideal Λ) (n : ℕ) (F : Mod) : Prop :=
  IsFiniteTypeLocallyConstantModule F ∧
    ∀ U : C, (I ^ n) • (⊤ : Submodule Λ (F.1.obj (op U))) ≤ ⊥

-- Proof sketch: the helper predicate was defined by adjoining an `I^n`-annihilation condition to
-- `IsFiniteTypeLocallyConstantModule`, so forgetting that extra condition gives the desired
-- conclusion immediately.
/-- Forgetting the `I^n`-annihilation condition leaves a locally constant finite-type sheaf of
`\Lambda`-modules. -/
theorem isFiniteTypeLocallyConstant_of_isFiniteTypeLocallyConstantIdealPowerQuotientModule
    {I : Ideal Λ} {n : ℕ} {F : Mod}
    (hF : IsFiniteTypeLocallyConstantIdealPowerQuotientModule I n F) :
    IsFiniteTypeLocallyConstantModule F := sorry

-- Proof sketch: apply the distinguished triangles
-- `K ⊗ \underline{I^m/I^(m+1)} → K ⊗ \underline{\Lambda/I^(m+1)} → K ⊗ \underline{\Lambda/I^m}`
-- and use the factorization
-- `K ⊗ \underline{I^m/I^(m+1)} ≅ (K ⊗ \underline{\Lambda/I}) ⊗_{\Lambda/I}^{\mathbf L}
-- \underline{I^m/I^(m+1)}` together with Lemma `21.53.4`. The weak-LinearRepresentations_Serre_1977 stability of locally
-- constant finite-type sheaves propagates the property inductively from `n = 1` to all `n ≥ 1`.
/-- Lemma 21.53.5: if the cohomology sheaves of
`K \otimes_\Lambda^{\mathbf L} \underline{\Lambda / I}` are locally constant sheaves of finite
type `\Lambda / I`-modules, then for every `n \geq 1` the cohomology sheaves of
`K \otimes_\Lambda^{\mathbf L} \underline{\Lambda / I^n}` are locally constant sheaves of finite
type `\Lambda / I^n`-modules. -/
theorem derivedTensor_constantIdealPowerQuotient_cohomology_isFiniteTypeLocallyConstant
    [MonoidalCategoryStruct DMod]
    (I : Ideal Λ)
    (K : DMod)
    (hKboundedAbove : ∃ a : ℤ, K.IsLE a)
    (hmodI :
      ∀ i : ℤ,
        IsFiniteTypeLocallyConstantIdealPowerQuotientModule
          I 1
          ((DerivedCategory.homologyFunctor Mod i).obj
            (K ⊗ (single0).obj
              ((constantSheaf J (ModuleCat Λ)).obj
                (ModuleCat.of Λ (Λ ⧸ I)))))) :
    ∀ n : ℕ, 1 ≤ n →
      ∀ i : ℤ,
        IsFiniteTypeLocallyConstantIdealPowerQuotientModule
          I n
          ((DerivedCategory.homologyFunctor Mod i).obj
            (K ⊗ (single0).obj
              ((constantSheaf J (ModuleCat Λ)).obj
                (ModuleCat.of Λ (Λ ⧸ I ^ n))))) := sorry

end

end CategoryTheory.Sheaf
