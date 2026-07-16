import Mathlib
import StacksProject_2024.stacks_project.Chap17.Lemma_17_3_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_3
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

private theorem moduleStalkHom_comp_eq_zero (S : ShortComplex X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x S.f ≫ RingedSpace.moduleStalkHom x S.g = 0 := by
  calc
    RingedSpace.moduleStalkHom x S.f ≫ RingedSpace.moduleStalkHom x S.g =
        RingedSpace.moduleStalkHom x (S.f ≫ S.g) := by
          simpa using ((RingedSpace.stalkModuleFunctor (X := X) x).map_comp S.f S.g).symm
    _ = RingedSpace.moduleStalkHom x 0 := by rw [S.zero]
    _ = 0 := by
          simpa using
            (Functor.map_zero (RingedSpace.stalkModuleFunctor (X := X) x) S.X₁ S.X₃)

private noncomputable abbrev stalkModuleShortComplex
    (S : ShortComplex X.Modules) (x : X) :
    ShortComplex (ModuleCat (X.presheaf.stalk x)) :=
  ShortComplex.mk
    (RingedSpace.moduleStalkHom x S.f)
    (RingedSpace.moduleStalkHom x S.g)
    (moduleStalkHom_comp_eq_zero S x)

private theorem stalkModuleShortComplex_exact
    (hS : S.ShortExact) (x : X) :
    (stalkModuleShortComplex S x).Exact := by
  have hstalk :
      (RingedSpace.stalkShortComplex S x).Exact :=
    (RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact S).1 hS.exact x
  have hforget :
      ((stalkModuleShortComplex S x).map
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).Exact := by
    simpa [stalkModuleShortComplex, RingedSpace.stalkShortComplex, RingedSpace.moduleStalkMap] using
      hstalk
  exact
    ((stalkModuleShortComplex S x).exact_map_iff_of_faithful
      (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat)).mp hforget

-- Semantic recall: `lean_leansearch` surfaced the stalkwise algebra owner
-- `associatedPrimes.subset_union_of_exact`; the local Chapter 31 analogue packages the sheaf-side
-- statement through `ShortComplex.ShortExact` and `Scheme.Modules.associatedPoints`.

/-- Helper for Lemma 31.2.4: a short exact sequence of `\mathcal O_X`-modules induces an exact
sequence on each stalk module. -/
private theorem stalkModuleExact
    (hS : S.ShortExact) (x : X) :
    Function.Exact (RingedSpace.moduleStalkHom x S.f).hom
      (RingedSpace.moduleStalkHom x S.g).hom := by
  exact
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (stalkModuleShortComplex S x)).1
      (stalkModuleShortComplex_exact hS x)

/-- Helper for Lemma 31.2.4: the left map in a short exact sequence of `\mathcal O_X`-modules
induces an injective map on each stalk module. -/
private theorem stalkModuleInjective
    (hS : S.ShortExact) (x : X) :
    Function.Injective (RingedSpace.moduleStalkHom x S.f).hom := by
  let toAbelianSheaf := SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)
  have hmono :
      Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (toAbelianSheaf.map S.f).hom) := by
    letI : Mono S.f := hS.mono_f
    exact (TopCat.Presheaf.mono_iff_stalk_mono (toAbelianSheaf.map S.f)).1
      (Functor.map_mono toAbelianSheaf S.f) x
  simpa [RingedSpace.moduleStalkMap] using (AddCommGrpCat.mono_iff_injective _).1 hmono

/-- Lemma 31.2.4 (1): for a short exact sequence of `\mathcal O_X`-modules on a scheme `X`,
every associated point of the middle term is associated to the left term or to the right term. -/
theorem associatedPoints_middle_subset_union_of_shortExact
    (hS : S.ShortExact) :
    associatedPoints S.X₂ ⊆ associatedPoints S.X₁ ∪ associatedPoints S.X₃ := by
  intro x hx
  rw [mem_associatedPoints_iff] at hx ⊢
  exact
    associatedPrimesOfModule.subset_union_of_exact
      (stalkModuleInjective hS x) (stalkModuleExact hS x) hx

/-- Pointwise form of `associatedPoints_middle_subset_union_of_shortExact`. -/
theorem mem_associatedPoints_left_or_right_of_mem_middle_of_shortExact
    (hS : S.ShortExact) {x : X} (hx : x ∈ associatedPoints S.X₂) :
    x ∈ associatedPoints S.X₁ ∨ x ∈ associatedPoints S.X₃ :=
  associatedPoints_middle_subset_union_of_shortExact hS hx

/-- Lemma 31.2.4 (2): for a short exact sequence of `\mathcal O_X`-modules on a scheme `X`,
every associated point of the left term is associated to the middle term. -/
theorem associatedPoints_left_subset_of_shortExact
    (hS : S.ShortExact) :
    associatedPoints S.X₁ ⊆ associatedPoints S.X₂ := by
  intro x hx
  rw [mem_associatedPoints_iff] at hx ⊢
  exact associatedPrimesOfModule.subset_of_injective (stalkModuleInjective hS x) hx

/-- Pointwise form of `associatedPoints_left_subset_of_shortExact`. -/
theorem mem_associatedPoints_middle_of_mem_left_of_shortExact
    (hS : S.ShortExact) {x : X} (hx : x ∈ associatedPoints S.X₁) :
    x ∈ associatedPoints S.X₂ :=
  associatedPoints_left_subset_of_shortExact hS hx

end AlgebraicGeometry.Scheme.Modules
