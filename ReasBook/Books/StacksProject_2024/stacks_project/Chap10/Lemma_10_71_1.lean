import Mathlib
import StacksProject_2024.Chap10.Definition_10_71_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ChainComplex

universe u v

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (single₀ (ModuleCat R)) (ModuleCat.of R M)

/-
Domain-style sampling:
* primary domain: free resolutions of modules in `ModuleCat R`;
* sampled owner declarations:
  `ModuleCat.projectiveResolution`,
  `CategoryTheory.ProjectiveResolution`,
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`;
* best owner abstraction:
  source-facing statements remain augmentations `π : F ⟶ moduleSingle[R] M`
  equipped with `IsFreeResolution π` or `IsFiniteFreeResolution π`,
  while the proof-level canonical owner for part (1) is the functorial free
  resolution machinery `ModuleCat.projectiveResolution`;
* layer triage:
  the two lemmas below are `source-facing`,
  `ModuleCat.projectiveResolution` and `ProjectiveResolution` are `core/canonical`,
  and `ChainComplex.IsFreeResolution.toProjectiveResolution` is the relevant
  `bridge/view`;
* primitive data: an augmented chain complex `π : F ⟶ moduleSingle[R] M`;
* derived API: termwise freeness, termwise finiteness, and the induced
  projective resolution.
-/

/-- Lemma 10.71.1 (1): every `R`-module admits a resolution by free `R`-modules. -/
-- Proof sketch: this is a `source-facing` existence statement whose proof should be routed through
-- the `core/canonical` owner `ModuleCat.projectiveResolution`. After forgetting from the full
-- subcategory of projective modules back to `ModuleCat R`, the associated augmented chain complex
-- is built termwise from `free R`, so it yields the required `bridge/view`
-- `IsFreeResolution`.
lemma module_exists_free_resolution :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
      IsFreeResolution π := sorry

/-- Lemma 10.71.1 (2): if `R` is Noetherian and `M` is finite, then `M` admits a resolution by
finite free `R`-modules. -/
-- Proof sketch: this is again `source-facing`, but here the finite-generation argument is the
-- primitive input. Start with a surjection from a finite free module onto `M`; over a Noetherian
-- ring the successive kernels remain finite, so iterating the construction produces an exact
-- complex `⋯ ⟶ F₂ ⟶ F₁ ⟶ F₀ ⟶ M ⟶ 0` whose terms are all finite free, i.e. an augmentation
-- carrying the canonical owner predicate `IsFiniteFreeResolution`.
lemma module_exists_finite_free_resolution [IsNoetherianRing R] [Module.Finite R M] :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle[R] M),
      IsFiniteFreeResolution π := sorry

end
