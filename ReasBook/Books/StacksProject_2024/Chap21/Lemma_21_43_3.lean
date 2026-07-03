import Mathlib
import StacksProject_2024.Chap18.Definition_18_34_1
import StacksProject_2024.Chap21.Definition_21_43_1

open CategoryTheory
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Lemma 21.43.3:
- primary domain: derived quasi-coherence on modules over a category with the chaotic topology,
  together with the ordinary quasi-coherent owner for module sheaves;
- sampled owner declarations:
  `CategoryTheory.ModulesOnCategory.isQuasiCoherent`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `SheafOfModules.isQuasicoherent_iff_tensor_sections_map_isIso`;
- best owner abstraction: the source-facing Section `21.43` owner
  `CategoryTheory.ModulesOnCategory.QC 𝒪 RGamma derivedRestrict comparison`, with the Chapter 18
  owner predicate `SheafOfModules.IsQuasicoherent` as the target notion;
- primitive data: the chaotic-site module category `SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)`,
  the derived sections functors `RGamma`, the derived restriction functors `derivedRestrict`, and
  their comparison morphisms;
- derived API: membership in `QC` via the inherited field `M.property`, homology objects via
  `DerivedCategory.homologyFunctor`, and the target quasi-coherence predicate on the top
  cohomology sheaf.

Source/core/bridge triage:
- `source-facing`: the Section `21.43` full subcategory `QC(\mathcal C, \mathcal O)`;
- `core/canonical`: the chapter owner `QC` from Definition `21.43.1` and the Chapter 18 owner
  `(H^b M).IsQuasicoherent`;
- `bridge/view`: the present lemma, which passes from the derived base-change condition on `M` to
  quasi-coherence of the top cohomology sheaf. -/

variable {C : Type u} [Category.{u} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The category `\mathrm{Mod}(\mathcal O)` of module sheaves on a category with the chaotic
topology. -/
abbrev moduleOnCategory :=
  SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)

-- Proof sketch: for each arrow `U ⟶ V`, the `QC` hypothesis gives an isomorphism
-- `RΓ(V,M) ⊗^L_{\mathcal O(V)} \mathcal O(U) ≅ RΓ(U,M)`. Because the objectwise cohomology of
-- `M` vanishes above `b`, the Tor spectral sequence degenerates on the top row and identifies the
-- degree-`b` homology of this derived tensor product with ordinary scalar extension of
-- `H^b(RΓ(V,M))`. Lemma `18.24.3` is then the chaotic-topology criterion for quasi-coherence.
/-- Lemma 21.43.3: in the section-`21.43` setup for modules on a category, if `M` satisfies the
derived base-change condition defining `QC(\mathcal C, \mathcal O)` and its objectwise derived
sections have no cohomology above degree `b`, then the cohomology module `H^b(M)` is
quasi-coherent on `(\mathcal C, \mathcal O)` in the sense of Modules on Sites,
Definition 18.23.1. -/
theorem top_cohomology_isQuasicoherent
    (RGamma :
      ∀ U : C,
        DerivedCategory (moduleOnCategory 𝒪) ⥤
          DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
    (derivedRestrict :
      ∀ {U V : C}, (U ⟶ V) →
        DerivedCategory (ModuleCat (𝒪.1.obj (op V))) ⥤
          DerivedCategory (ModuleCat (𝒪.1.obj (op U))))
    (comparison :
      ∀ {U V : C} (f : U ⟶ V),
        RGamma V ⋙ derivedRestrict f ⟶ RGamma U)
    (M :
      QC 𝒪.1 RGamma derivedRestrict comparison)
    (b : ℤ)
    (hvanish :
      ∀ U : C, ∀ i : ℤ, b < i →
        Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat (𝒪.1.obj (op U))) i).obj
            ((RGamma U).obj M.obj))) :
    (show SheafOfModules (ringSheaf (⊥ : GrothendieckTopology C) 𝒪) from
      (DerivedCategory.homologyFunctor (moduleOnCategory 𝒪) b).obj M.obj).IsQuasicoherent := sorry

end CategoryTheory.ModulesOnCategory
