import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import stacks_proof.stacks_project.Chap15.Lemma_15_89_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open LinearMap

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

/- 
Domain-style sampling for Lemma 15.89.5:
- primary domain: object properties on the abelian category `ModuleCat R`, with Serre-class
  structure expressed by the owner interface `ObjectProperty.IsSerreClass`;
- inspected same-domain declarations:
  `Module.IsIdealPowerTorsion`,
  `ObjectProperty`,
  `ObjectProperty.IsSerreClass`,
  `isNoetherianObject_isSerreClass`;
- best owner abstraction: the object property on `ModuleCat R` induced directly from the
  source-facing predicate `Module.IsIdealPowerTorsion`;
- primitive data: only the module-level torsion predicate `Module.IsIdealPowerTorsion I M`;
- derived API: the direct `ObjectProperty` view of that predicate on `ModuleCat R` and its
  Serre-class instance.

Source/core/bridge triage:
- `source-facing`: the textbook class of `I`-power torsion modules;
- `core/canonical`: the predicate `Module.IsIdealPowerTorsion`;
- `bridge/view`: the direct `ObjectProperty` view on `ModuleCat R`.

The owner-level object property should therefore be only a thin bridge over
`Module.IsIdealPowerTorsion`, not a second predicate encoded through `I.primaryComponent M = ⊤`.
-/
-- Proof sketch: submodules and quotients of an `I`-power torsion module are again `I`-power
-- torsion by checking the annihilation condition elementwise, and extensions are handled by the
-- corresponding module-theoretic lemma. These are exactly the data
-- needed for the Serre-class constructor on `ModuleCat R`.
/-- Lemma 15.89.5: the `I`-power torsion modules form a Serre subcategory of the abelian
category `Mod_R`. -/
@[stacks 0A6K]
instance
    (I : Ideal R) :
    ObjectProperty.IsSerreClass (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) where
  exists_zero := by
    refine ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩
    rw [Module.isIdealPowerTorsion_iff]
    intro x
    refine ⟨1, fun a ↦ ?_⟩
    simpa using (zero_smul R x)
  prop_of_mono f _ hY := by
    have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 inferInstance
    rw [Module.isIdealPowerTorsion_iff] at hY ⊢
    intro x
    obtain ⟨n, hn⟩ := hY (f.hom x)
    refine ⟨n, fun a ↦ hf ?_⟩
    simpa using hn a
  prop_of_epi f _ hX := by
    have hf : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective f).1 inferInstance
    rw [Module.isIdealPowerTorsion_iff] at hX ⊢
    intro y
    rcases hf y with ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := hX x
    refine ⟨n, fun a ↦ ?_⟩
    simpa using congrArg f.hom (hn a)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
    have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).1 hS.epi_g
    have hRange : Module.IsIdealPowerTorsion I (range S.f.hom) :=
      (Module.isIdealPowerTorsion_iff_of_linearEquiv I (LinearEquiv.ofInjective S.f.hom hf)).1 h₁
    let g := S.g.hom
    have hQuotKer : Module.IsIdealPowerTorsion I (S.X₂ ⧸ ker g) :=
      (Module.isIdealPowerTorsion_iff_of_linearEquiv I
        (quotKerEquivOfSurjective g hg)).2 h₃
    have hQuot : Module.IsIdealPowerTorsion I (S.X₂ ⧸ range S.f.hom) := by
      exact (ShortComplex.Exact.moduleCat_range_eq_ker hS.exact).symm ▸ hQuotKer
    exact isIdealPowerTorsion_of_submodule_and_quotient
      (range S.f.hom) hRange hQuot

end

end CategoryTheory
