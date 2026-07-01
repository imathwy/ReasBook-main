import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
