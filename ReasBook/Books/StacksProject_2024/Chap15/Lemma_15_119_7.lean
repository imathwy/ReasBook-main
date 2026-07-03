import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.Remark_15_119_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped DeterminantLine

universe u

section

variable (R : Type u) [CommRing R]

local notation "K₀" => projectiveGrothendieckGroup R

/- Domain-style sampling for Lemma 15.119.7:
- primary domain: additive invariants of `K₀(R)` for finite projective `R`-modules, with values in
  the Picard group via the determinant line;
- sampled owner declarations:
  `ModulePropertyK0.lift`,
  `ModulePropertyK0.lift_of`,
  `projectiveGrothendieckGroup`,
  `CommRing.Pic.mk`,
  `Module.det`;
- best owner abstraction:
  the source-facing declaration is the determinant homomorphism
  `projectiveGrothendieckGroup R →+ Additive (CommRing.Pic R)`, while the canonical owner for its
  construction is the Chapter 10 quotient-descending API `ModulePropertyK0.lift`;
- primitive vs. derived:
  primitive data here is only the value of the invariant on a finite projective module,
  `M ↦ Additive.ofMul (CommRing.Pic.mk R det(M.obj))`;
  the descended `K₀` map and its evaluation formula are derived from that owner abstraction;
- source/core/bridge triage:
  `source-facing`: `projectiveGrothendieckGroup_det`;
  `core/canonical`: `ModulePropertyK0.lift`;
  `bridge/view`: the determinant-line owner `Module.det`, used through the textbook notation
  `det(M)` from Remark `15.119.1`.

This file should therefore expose the determinant map on `K₀(R)` as the main public API and build
it directly from the canonical `ModulePropertyK0.lift` owner abstraction, keeping the primitive
module-level determinant class only as the function fed to that owner.
-/

/-- The determinant Picard class attached to a finite projective `R`-module. This is the
primitive generator-level datum fed into the canonical `K₀` quotient lift. -/
private abbrev detClass (M : FiniteProjectiveModuleCat R) :
    Additive (CommRing.Pic R) :=
  Additive.ofMul (CommRing.Pic.mk R
    ((det((M.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M.obj))))

/-- The determinant invariant on finite projective modules kills the short-exact-sequence
relations defining `K₀(R)`. -/
private theorem detClass_relations_le_ker :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (detClass R)).ker := sorry

/-- Lemma 15.119.7: the determinant construction induces a map from `K₀(R)` to the Picard group of
`R`, sending the class of a finite locally free module to the Picard class of its determinant line
`det(M)`, realized here by the exterior-algebra annihilator model from Remark
`15.119.1`. In Lean, the Picard group is viewed
additively so that this becomes a homomorphism out of the additive Grothendieck group. -/
def projectiveGrothendieckGroup_det :
    K₀ →+ Additive (CommRing.Pic R) :=
  ModulePropertyK0.lift R (detClass R) (detClass_relations_le_ker R)

/-- On the class of a finite projective module, the determinant map returns the Picard class of
its determinant line `det((M.obj : ModuleCat R))`. -/
@[simp]
theorem projectiveGrothendieckGroup_det_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroup_det R
        (projectiveGrothendieckGroupOf R M) =
      Additive.ofMul (CommRing.Pic.mk R
        ((det((M.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M.obj)))) := by
  simpa [detClass] using ModulePropertyK0.lift_of R
    (detClass R)
    (detClass_relations_le_ker R) M

end
