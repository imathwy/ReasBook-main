import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_12_1 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

/-- Lemma 21.12.1: an injective sheaf of modules on a ringed site is injective as an object of
`PMod(𝒪)`, i.e. of the category `PresheafOfModules 𝒪.obj` of presheaves of `𝒪`-modules. -/
-- Proof sketch: apply Lemma `12.29.1` to the adjunction
-- `PresheafOfModules.sheafificationAdjunction (𝟙 𝒪.obj)`. The left adjoint is exact because
-- module sheafification preserves finite limits, so the right adjoint `SheafOfModules.forget 𝒪`
-- preserves injective objects.
theorem injective_as_presheaf_of_modules
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    (F : SheafOfModules.{v} 𝒪) (hF : Injective F) :
    Injective ((SheafOfModules.forget 𝒪).obj F) := sorry

end CategoryTheory

/-! ### Lemma_21_12_2 (from Chap21) -/
open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]

/- Domain-style sampling for Lemma 21.12.2:
- primary domain: sheaves of modules on a ringed site, their underlying abelian sheaves and
  presheaves, and right derived functors of the inclusion into presheaves of modules;
- sampled owner declarations:
  `SheafOfModules.forget`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.toSheafCompSheafToPresheafIso`,
  `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`,
  `siteAbelianSheaf_hasEnoughInjectives`;
- best owner abstraction: the core owners are the canonical forgetful functors
  `SheafOfModules.forget` and `SheafOfModules.toSheaf`, together with the abelian-sheaf
  comparison theorem `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`; the
  left-exactness clause is already owned by the canonical instance
  `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`, so this file should not keep a parallel local
  theorem name for it, and the needed injective-resolution machinery for underlying abelian sheaves
  comes canonically from Chapter 19 via `siteAbelianSheaf_hasEnoughInjectives`;
- primitive data: the structure sheaf `𝒪`, a sheaf of `𝒪`-modules `ℱ`, and the cohomological
  degree `p`;
- derived API: the underlying-abelian-presheaf comparison in degree `p`, obtained by forgetting the
  module structure from the right derived object of `SheafOfModules.forget`.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison between the derived inclusion
  `Mod(\mathcal O) ⥤ PMod(\mathcal O)` and the cohomology presheaf of the underlying abelian
  sheaf;
- `core/canonical`: `SheafOfModules.forget`, `SheafOfModules.toSheaf`, the anonymous instance
  `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`, and
  `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`;
- `bridge/view`: the module-to-abelian comparison theorem below.
-/

-- Enough injectives for `Mod(𝒪)` is already inferred from the imported owner-level instance
-- `modulesOnRingedSite_hasFunctorialInjectiveEmbeddings 𝒪` via the Chapter 12 bridge
-- `HasFunctorialInjectiveEmbeddings → EnoughInjectives`, so no extra local wrapper is needed here.

/- Lemma 21.12.2 first clause: the inclusion `Mod(\mathcal O) ⥤ PMod(\mathcal O)` is left exact.
This is already the canonical instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`. -/
section

variable (𝒪 : Sheaf J RingCat.{max u v})

#synth PreservesFiniteLimits (SheafOfModules.forget 𝒪)

end

-- Proof sketch: compute the right derived functors of `SheafOfModules.forget 𝒪` on an injective
-- resolution of `ℱ`. After forgetting further to abelian presheaves, this is the same sections
-- complex used to define the cohomology presheaf of the underlying abelian sheaf
-- `(SheafOfModules.toSheaf 𝒪).obj ℱ`.
/-- Lemma 21.12.2: for a sheaf of `\mathcal O`-modules `\mathcal F` on a ringed site, after
forgetting the `\mathcal O`-module structure the `p`-th right derived object of the inclusion
`Mod(\mathcal O) ⥤ PMod(\mathcal O)` is the cohomology presheaf
`U ↦ H^p(U, \mathcal F)` of the underlying abelian sheaf; the left exactness of the inclusion is
the existing instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`. -/
theorem ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    IsIsomorphic
      ((PresheafOfModules.toPresheaf 𝒪.obj).obj
        (((SheafOfModules.forget 𝒪).rightDerived p).obj ℱ))
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).cohomologyPresheaf p) := by
  let h :
      IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
        (Sheaf.cohomologyPresheafFunctor J p) :=
    abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor p
  let ⟨e⟩ := h
  simpa [Sheaf.cohomologyPresheaf] using
    (show IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱ))
        ((Sheaf.cohomologyPresheafFunctor J p).obj ((SheafOfModules.toSheaf 𝒪).obj ℱ)) from
      ⟨e.app ((SheafOfModules.toSheaf 𝒪).obj ℱ)⟩)

/-! ### Lemma_21_12_3 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

/-- The presheaf on `Over U` of `\mathcal O(U)`-modules obtained from a presheaf of
`\mathcal O`-modules by restricting scalars along the maps `\mathcal O(U) → \mathcal O(V)`. -/
abbrev ringedSiteModuleSectionsOnOverPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C) :
    PresheafOfModules 𝒪.obj ⥤ (Over U)ᵒᵖ ⥤ ModuleCat (𝒪.obj.obj (op U)) :=
  PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (Over.mk (𝟙 U)))
      (show Limits.IsInitial (op (Over.mk (𝟙 U))) from Over.mkIdTerminal.op)

/-- The Čech complex of a presheaf of `\mathcal O`-modules with respect to a covering family
`family : ι → Over U`, computed in `\operatorname{Mod}(\mathcal O(U))`. -/
abbrev ringedSiteModuleCechComplexFunctor
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)]
    {ι : Type w} [HasProducts (ModuleCat (𝒪.obj.obj (op U)))]
    (family : ι → Over U) :
    PresheafOfModules 𝒪.obj ⥤
      CochainComplex (ModuleCat (𝒪.obj.obj (op U))) ℕ :=
  ringedSiteModuleSectionsOnOverPresheaf 𝒪 U ⋙ CategoryTheory.cechComplexFunctor family

/-- The degree-`p` Čech cohomology of a presheaf of `\mathcal O`-modules on a ringed site,
viewed as an `\mathcal O(U)`-module. -/
abbrev ringedSiteModuleCechCohomology
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)]
    {ι : Type w} [HasProducts (ModuleCat (𝒪.obj.obj (op U)))]
    (family : ι → Over U) (M : PresheafOfModules 𝒪.obj) (p : ℕ) :
    ModuleCat (𝒪.obj.obj (op U)) :=
  (HomologicalComplex.homologyFunctor
      (ModuleCat (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p).obj
    ((ringedSiteModuleCechComplexFunctor 𝒪 U family).obj M)

-- Proof sketch: by Lemma `21.9.3` and Lemma `18.9.2`, the Čech complex of an
-- `\mathcal O`-module sheaf identifies with the Hom complex
-- `Mor_{PMod(\mathcal O)}(\mathbf Z_{\mathcal U,\bullet} \otimes \mathcal O, \mathcal I)`.
-- Lemma `21.12.1` makes `ℐ` injective in `PMod(\mathcal O)`, so this computes degree-zero
-- sections over `U`; the final identification is the sheaf/equalizer statement of Lemma `21.8.2`.
/-- Lemma 21.12.3 (1): for an injective `\mathcal O`-module sheaf on a ringed site, the degree-zero
Čech cohomology of a covering family `family : ι → Over U` is canonically isomorphic to the
module of sections `\mathcal I(U)`. -/
theorem injective_module_cechCohomology_zero_isomorphic_evaluation
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)]
    [HasProducts (ModuleCat (𝒪.obj.obj (op U)))]
    {ι : Type w} (family : ι → Over U)
    (ℐ : SheafOfModules 𝒪) (hℐ : Injective ℐ) :
    IsIsomorphic
      (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) 0)
      ((SheafOfModules.evaluation 𝒪 (op U)).obj ℐ) := sorry

-- Proof sketch: as in the source proof, Lemma `21.9.3` and Lemma `18.9.2` identify the Čech
-- complex with a Hom complex out of `\mathbf Z_{\mathcal U,\bullet} \otimes \mathcal O`, and
-- Lemma `21.12.1` shows that `ℐ` is injective in `PMod(\mathcal O)`. Exactness of
-- `Hom_{PMod(\mathcal O)}(-, \mathcal I)` then turns Lemma `21.9.5` into vanishing of the higher
-- homology groups.
/-- Lemma 21.12.3 (2): for an injective `\mathcal O`-module sheaf on a ringed site, the positive
Čech cohomology groups of a covering family `family : ι → Over U` vanish. -/
theorem injective_module_cechCohomology_isZero_of_pos
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat) (U : C)
    [HasFiniteProducts (Over U)]
    [HasProducts (ModuleCat (𝒪.obj.obj (op U)))]
    {ι : Type w} (family : ι → Over U)
    (ℐ : SheafOfModules 𝒪) (hℐ : Injective ℐ) :
    ∀ p : ℕ, 0 < p →
      IsZero
        (ringedSiteModuleCechCohomology 𝒪 U family ((SheafOfModules.forget 𝒪).obj ℐ) p) := sorry

end CategoryTheory

/-! ### Lemma_21_12_4 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasSheafify J AddCommGrpCat]
variable {𝒪 : Sheaf J RingCat.{u}}

-- Proof sketch: compute `H^i(\mathcal C, \mathcal F_{ab})` as the right derived functors of
-- global sections on abelian sheaves, compute module cohomology as the Ext-groups
-- `Ext^i_{\mathrm{Mod}(\mathcal O)}(\mathcal O, \mathcal F)`, and compare the two via the exact
-- forgetful functor `SheafOfModules.toSheaf 𝒪` together with the identification of
-- `Hom_{\mathrm{Mod}(\mathcal O)}(\mathcal O, -)` with global sections.
/-- Lemma 21.12.4 (1): the global cohomology of the underlying abelian sheaf of an
`\mathcal O`-module agrees with the module cohomology computed in `\mathrm{Mod}(\mathcal O)`. -/
theorem underlyingAbelianSheaf_globalCohomology_eq_moduleCohomology
    [HasExt (Sheaf J AddCommGrpCat)] [HasExt (SheafOfModules 𝒪)]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    AddCommGrpCat.of (((SheafOfModules.toSheaf 𝒪).obj ℱ).H i) =
      (Abelian.extFunctorObj (SheafOfModules.unit 𝒪) i).obj ℱ := sorry

-- Proof sketch: first identify `H^i(U, \mathcal F_{ab})` with the global cohomology of the
-- restriction of `\mathcal F` to the localized site `(C/U, J.over U)` by Lemma `21.7.1`.
-- Then apply the global comparison from part `(1)` on the localized ringed site
-- `((C/U, J.over U), \mathcal O_U)`.
/-- Lemma 21.12.4 (2): for any object `U` of the site, the cohomology of the underlying abelian
sheaf over `U` agrees with the module cohomology of the localized module on the localized ringed
site `((C/U, J.over U), \mathcal O_U)`. -/
theorem underlyingAbelianSheaf_cohomologyOver_eq_moduleCohomology
    (U : C) [HasExt (SheafOfModules (𝒪.over U))]
    (ℱ : SheafOfModules 𝒪) (i : ℕ) :
    ((SheafOfModules.toSheaf 𝒪).obj ℱ).H' i U =
      (Abelian.extFunctorObj (SheafOfModules.unit (𝒪.over U)) i).obj
        ((SheafOfModules.pushforward (𝟙 (𝒪.over U))).obj ℱ) := sorry

/-! ### Lemma_21_12_5 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [HasProducts (Sheaf J AddCommGrpCat)]

/-- The functor sending an abelian sheaf to its degree-`p` cohomology over `U`. -/
private noncomputable abbrev sheafCohomologyAtObjectFunctor (U : C) (p : ℕ) :
    Sheaf J AddCommGrpCat ⥤ AddCommGrpCat :=
  (Sheaf.cohomologyPresheafFunctor J p) ⋙
    (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj (op U)

/-- The canonical map from the cohomology of a product sheaf over `U` to the product of the
corresponding cohomology groups. -/
private noncomputable abbrev sheafProductCohomologyMap
    (U : C) (p : ℕ) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    (∏ᶜ F).H' p U ⟶ ∏ᶜ fun i ↦ (F i).H' p U :=
  piComparison (sheafCohomologyAtObjectFunctor U p) F

-- Proof sketch: degree-zero cohomology is evaluation of the sheaf on `U`, and products of
-- sheaves are computed on the underlying presheaves, so the induced product comparison map on
-- sections is an isomorphism.
/-- Lemma 21.12.5 (1): for an object `U` of a site and a family of abelian sheaves
`(\mathcal F_i)`, the canonical map
`H^0(U, \prod_i \mathcal F_i) \to \prod_i H^0(U, \mathcal F_i)` is an isomorphism. -/
theorem sheafProductCohomologyMap_isIso_degree_zero
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    IsIso (sheafProductCohomologyMap U 0 F) := sorry

-- Proof sketch: choose a covering on which a class in `H^1(U, \prod_i \mathcal F_i)` vanishes,
-- represent it by a Čech `1`-cocycle, use injectivity of the Čech-to-cohomology map for each
-- factor, and identify the Čech complex of the product sheaf with the product of the Čech
-- complexes so that vanishing of all components forces vanishing of the original class.
/-- Lemma 21.12.5 (2): for an object `U` of a site and a family of abelian sheaves
`(\mathcal F_i)`, the canonical map
`H^1(U, \prod_i \mathcal F_i) \to \prod_i H^1(U, \mathcal F_i)` is injective. -/
theorem sheafProductCohomologyMap_injective_degree_one
    (U : C) {I : Type w} (F : I → Sheaf J AddCommGrpCat) :
    Function.Injective (sheafProductCohomologyMap U 1 F) := sorry

end CategoryTheory

/-! ### Lemma_21_12_6 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v w

-- Proof sketch: represent sections over `U` and `U'` by the extension-by-zero modules
-- `j_{U!}\mathcal O_U` and `j_{U'!}\mathcal O_{U'}`. The monomorphism `a : U' ⟶ U` induces a
-- canonical monomorphism between these representing objects, and injectivity of `ℐ` makes
-- precomposition with that mono surjective. Yoneda then identifies this with surjectivity of the
-- restriction map `ℐ(U) → ℐ(U')`.
/-- Lemma 21.12.6: for a sheaf of rings `R` on a site, a monomorphism `a : U' ⟶ U`, and an
injective `R`-module sheaf `ℐ`, the restriction map on sections along `a` is surjective. -/
theorem injective_module_restriction_surjective_of_mono
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {U U' : C} (a : U' ⟶ U) [Mono a]
    (ℐ : SheafOfModules R) (hℐ : Injective ℐ) :
    Function.Surjective (ℐ.val.map a.op) := sorry
