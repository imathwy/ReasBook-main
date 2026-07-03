import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap15.Lemma_15_23_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Domain-style sampling:
- primary domain: LinearRepresentations_Serre_1977 conditions of finite modules over Noetherian rings and torsion-freeness of
  linear-map modules;
- sampled owner declarations:
  `Module.SerreConditionS`,
  `moduleDepth_linearMap_ge_one`,
  `moduleDepth_linearMap_ge_two`,
  `LinearMap.instIsTorsionFree`;
- best owner abstraction:
  `Module.SerreConditionS` for the `(S₁)` and `(S₂)` clauses, with Lemma `15.23.10` supplying the
  primitive local-depth input, and `LinearMap.instIsTorsionFree` for the torsion-free clause;
- source/core/bridge triage:
  clauses `(1)` and `(2)` are `bridge/view` packaging from the local owner `moduleDepth`, while
  clause `(3)` is a direct `core/canonical` recall.

Primitive data are the local depth inequalities from Lemma `15.23.10`. The
`Module.SerreConditionS` statements below are derived packaging of that owner-level data, and the
torsion-free statement should reuse the canonical upstream owner instead of keeping a parallel
local wrapper.
-/

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

instance LinearMap.instSerreConditionSOneOfCodomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    sorry

-- Proof sketch: localize at each prime ideal and use that localization commutes with finite-module
-- `Hom`. Then apply the depth estimate from Lemma `15.23.10 (1)` to the localized linear-map
-- module, and package the resulting local inequalities back into the definition of
-- `Module.SerreConditionS ... 1`.
/-- Lemma 15.23.11 (1): if the finite `R`-module `N` satisfies LinearRepresentations_Serre_1977's condition `(S_1)`, then
the module `Hom_R(M, N)` also satisfies LinearRepresentations_Serre_1977's condition `(S_1)`. -/
theorem linearMap_serreConditionS_one_of_codomain
    [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 := inferInstance

instance LinearMap.instSerreConditionSTwoOfCodomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 where
  toFinite := inferInstance
  moduleDepth_localizationAtPrime_ge_min_supportDim := by
    sorry

-- Proof sketch: localize at a prime ideal, identify localization of `Hom_R(M, N)` with the `Hom`
-- module of the localized finite modules, and invoke Lemma `15.23.10 (2)` to get the depth bound
-- required in the definition of `Module.SerreConditionS ... 2`.
/-- Lemma 15.23.11 (2): if the finite `R`-module `N` satisfies LinearRepresentations_Serre_1977's condition `(S_2)`, then
the module `Hom_R(M, N)` also satisfies LinearRepresentations_Serre_1977's condition `(S_2)`. -/
theorem linearMap_serreConditionS_two_of_codomain
    [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 := inferInstance

end

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N] [Module.IsTorsionFree R N]

/- Lemma 15.23.11 (3): the torsion-free conclusion for `Hom_R(M, N)` is already the canonical
owner instance `LinearMap.instIsTorsionFree`, which is stronger than the source hypotheses used in
the textbook packaging of Lemma `15.23.11`. -/
recall LinearMap.instIsTorsionFree

end
