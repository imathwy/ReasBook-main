import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap10.Example_10_8_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_8_8

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

/-
Lemma 10.8.8 (1): for a directed system of complexes of `R`-modules, the stagewise homology
modules form a system over the directed set. This is formalized by `module_system_homology`.
-/
recall module_system_homology

/- Lemma 10.8.8 (2): the induced sequence on colimits is again a complex. -/
recall colimit_module_system_isComplex

/- Lemma 10.8.8 (3): the canonical comparison from the colimit of the stagewise homology modules
to the homology of the colimit complex is an isomorphism. -/
recall module_system_homology_comparison_isIso

noncomputable section

/-- The zero map `0 → ℤ` used at the source vertex of the counterexample span. -/
private abbrev forkZeroToInt : PUnit →ₗ[ℤ] ℤ :=
  0

/-- The identity map `ℤ → ℤ` used at the target vertices of the counterexample span. -/
private abbrev forkIntId : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.id

/-- The source system `(0, \mathbf{Z}, \mathbf{Z}, 0, 0)` on the fork-shaped preorder used in
Example 10.8.9, written as the canonical walking-span diagram. -/
def forkColimitExactnessSource : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkZeroToInt) (ModuleCat.ofHom forkZeroToInt)

/-- The constant target system `(\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` on the fork-shaped
preorder used in Example 10.8.9. -/
def forkColimitExactnessTarget : WalkingSpan ⥤ ModuleCat ℤ :=
  span (ModuleCat.ofHom forkIntId) (ModuleCat.ofHom forkIntId)

private instance : Subsingleton ↑(forkColimitExactnessSource.obj WalkingSpan.zero) := by
  change Subsingleton PUnit
  infer_instance

/-- The morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` from
Example 10.8.9. -/
def forkColimitExactnessHom : forkColimitExactnessSource ⟶ forkColimitExactnessTarget :=
  spanHomMk 0 (𝟙 _) (𝟙 _)

private theorem forkColimitExactnessHom_app_mono (i : WalkingSpan) :
    Mono (forkColimitExactnessHom.app i) := by
  rcases i with _ | (_ | _)
  · exact (ModuleCat.mono_iff_injective _).2 <| by
      intro x y h
      exact Subsingleton.elim _ _
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)
  · simpa [forkColimitExactnessSource, forkColimitExactnessTarget, forkColimitExactnessHom,
      forkZeroToInt, forkIntId] using
      (show Mono (𝟙 (ModuleCat.of ℤ ℤ)) from inferInstance)

private theorem forkColimitExactnessHom_colimit_not_injective :
    ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := sorry

private theorem forkColimitExactnessHom_colimit_not_mono :
    ¬ Mono (colim.map forkColimitExactnessHom) := by
  intro h
  exact forkColimitExactnessHom_colimit_not_injective ((ModuleCat.mono_iff_injective _).1 h)

private theorem forkColimitExactnessHom_mono : Mono forkColimitExactnessHom := by
  rw [NatTrans.mono_iff_mono_app]
  exact forkColimitExactnessHom_app_mono

/-- Example 10.8.9: on the fork-shaped preorder `a < b`, `a < c`, the morphism of systems
`(0, \mathbf{Z}, \mathbf{Z}, 0, 0) → (\mathbf{Z}, \mathbf{Z}, \mathbf{Z}, 1, 1)` is a
monomorphism, but the induced map on colimits is not. Hence the result of Lemma 10.8.8 is false
for general systems. -/
theorem fork_colimit_counterexample_to_exactness :
    Mono forkColimitExactnessHom ∧ ¬ Mono (colim.map forkColimitExactnessHom) := by
  constructor
  · exact forkColimitExactnessHom_mono
  · exact forkColimitExactnessHom_colimit_not_mono

/-- Textbook injectivity formulation of Example 10.8.9. -/
theorem fork_colimit_counterexample_to_exactness_injective :
    (∀ i : WalkingSpan, Function.Injective (forkColimitExactnessHom.app i).hom) ∧
      ¬ Function.Injective (colim.map forkColimitExactnessHom).hom := by
  refine ⟨?_, forkColimitExactnessHom_colimit_not_injective⟩
  intro i
  exact (ModuleCat.mono_iff_injective _).1 (forkColimitExactnessHom_app_mono i)

end
