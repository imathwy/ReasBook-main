import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_55_6
import stacks_proof.stacks_project.Chap15.Lemma_15_119_2
import stacks_proof.stacks_project.Chap15.Remark_15_119_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
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

/-- Helper for Lemma 15.119.7: determinant Picard classes are multiplicative along a short exact
sequence of finite projective modules. -/
private theorem det_pic_mk_eq_mul_of_shortExact
    {M₁ M₂ M₃ : FiniteProjectiveModuleCat R}
    (f : M₁.obj →ₗ[R] M₂.obj) (g : M₂.obj →ₗ[R] M₃.obj)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    CommRing.Pic.mk R
        ((det((M₂.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₂.obj))) =
      CommRing.Pic.mk R
          ((det((M₁.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₁.obj))) *
        CommRing.Pic.mk R
          ((det((M₃.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₃.obj))) := by
  -- The short exact determinant comparison identifies the middle determinant line with the tensor
  -- product of the outer determinant lines.
  calc
    CommRing.Pic.mk R
        ((det((M₂.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₂.obj))) =
      CommRing.Pic.mk R
        (TensorProduct R
          ((det((M₁.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₁.obj)))
          ((det((M₃.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₃.obj)))) := by
        rw [CommRing.Pic.mk_eq_mk_iff]
        exact ⟨(determinantTensorIsoOfShortExact
          (R := R) (f := f) (g := g) hf hg hexact).symm⟩
    _ =
        CommRing.Pic.mk R
          ((det((M₁.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₁.obj))) *
        CommRing.Pic.mk R
          ((det((M₃.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₃.obj))) := by
        simpa using
          (CommRing.Pic.mk_tensor (R := R)
            (M := ((det((M₁.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₁.obj))))
            (N := ((det((M₃.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R M₃.obj)))))

/-- Helper for Lemma 15.119.7: on a short exact sequence in the finite-projective category, the
determinant class satisfies the defining `K₀` additivity relation. -/
private theorem detClass_add_of_shortExact
    {S : ShortComplex (FiniteProjectiveModuleCat R)}
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    detClass R S.X₂ = detClass R S.X₁ + detClass R S.X₃ := by
  have hf :
      Function.Injective ((S.map (finiteProjectiveModuleProperty R).ι).f.hom) :=
    (ModuleCat.mono_iff_injective _).1 hS.mono_f
  have hg :
      Function.Surjective ((S.map (finiteProjectiveModuleProperty R).ι).g.hom) :=
    (ModuleCat.epi_iff_surjective _).1 hS.epi_g
  have hexact :
      Function.Exact ((S.map (finiteProjectiveModuleProperty R).ι).f.hom)
        ((S.map (finiteProjectiveModuleProperty R).ι).g.hom) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (finiteProjectiveModuleProperty R).ι)).1 hS.exact
  have hdet :
      CommRing.Pic.mk R
          ((det((S.X₂.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R S.X₂.obj))) =
        CommRing.Pic.mk R
            ((det((S.X₁.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R S.X₁.obj))) *
          CommRing.Pic.mk R
            ((det((S.X₃.obj : ModuleCat R)) : Submodule R (ExteriorAlgebra R S.X₃.obj))) :=
    det_pic_mk_eq_mul_of_shortExact (R := R)
      ((S.map (finiteProjectiveModuleProperty R).ι).f.hom)
      ((S.map (finiteProjectiveModuleProperty R).ι).g.hom) hf hg hexact
  -- Pass from multiplicative Picard classes to the additive wrapper used by `detClass`.
  simpa [detClass] using congrArg Additive.ofMul hdet

/-- The determinant invariant on finite projective modules kills the short-exact-sequence
relations defining `K₀(R)`. -/
private theorem detClass_relations_le_ker :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift (detClass R)).ker := by
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    FreeAbelianGroup.lift (detClass R)
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  -- Evaluate the additive invariant on the generator relation coming from this short exact row.
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  rw [detClass_add_of_shortExact (R := R) hS]
  abel

/-- Lemma 15.119.7: the determinant construction induces a map from `K₀(R)` to the Picard group of
`R`, sending the class of a finite locally free module to the Picard class of its determinant line
`det(M)`, realized here by the exterior-algebra annihilator model from Remark
`15.119.1`. In Lean, the Picard group is viewed
additively so that this becomes a homomorphism out of the additive Grothendieck group. -/
@[stacks 0AFX]
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
