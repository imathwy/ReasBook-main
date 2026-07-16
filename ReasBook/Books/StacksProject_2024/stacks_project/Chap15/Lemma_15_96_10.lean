import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.TorsionFree
import StacksProject_2024.stacks_project.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped nonZeroDivisors TensorProduct

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

/- Domain-style sampling:
- primary domain: flat base change for nonzerodivisors and for the owner predicate
  `BerthelotOgusInt.IsTermwiseFTorsionFree` on cochain complexes of modules;
- sampled owner declarations in this domain:
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`,
  `isSMulRegular_algebraMap_iff`,
  `BerthelotOgusInt.IsTermwiseFTorsionFree`,
  `Functor.mapHomologicalComplex`,
  `ModuleCat.extendScalars`;
- best owner abstraction:
  `source-facing`: flat base change for a nonzerodivisor `f` and for termwise `f`-torsion-free
    complexes `K : ModuleComplex A`;
  `core/canonical`: the regularity owners
    `Module.Flat.isSMulRegular_of_nonZeroDivisors`,
    `isSMulRegular_algebraMap_iff`, and the chapter owner
    `BerthelotOgusInt.IsTermwiseFTorsionFree`;
  `bridge/view`: the mapped complex
    `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K`;
- primitive data vs derived API: the primitive inputs are the algebra `A → B`, the element `f`,
  the complex `K`, and the owner-level termwise `f`-torsion-free hypothesis. The image
  nonzerodivisor statement and the mapped-complex torsion-freeness statement are derived from the
  regularity owners, so this file should keep only those source-facing consequences. -/

-- Proof sketch: use flatness of `B` over `A` to preserve the injectivity of multiplication by
-- `f` after tensoring the exact sequence `0 → A --f→ A`. The resulting map on `B` is
-- multiplication by `algebraMap A B f`, so the image element is again a nonzerodivisor.
/-- Lemma 15.96.10 (1): if `f` is a nonzerodivisor in `A`, then its image in the flat `A`-algebra
`B` is a nonzerodivisor in `B`. -/
theorem algebraMap_mem_nonZeroDivisors_of_flat
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    algebraMap A B f ∈ nonZeroDivisors B := by
  -- Flatness makes multiplication by `f` injective on `B` as an `A`-module.
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  let hRegular : IsSMulRegular B (algebraMap A B f) :=
    (isSMulRegular_algebraMap_iff B).2
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hf)
  exact hRegular <| by simpa [smul_eq_mul] using hx

/-- Helper for Lemma 15.96.10: after restricting scalars, the `B`-module `B` is canonically
itself. -/
private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.96.10: the restricted scalar action on `B` still forms the expected scalar
tower over `A`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Lemma 15.96.10: scalar extension in `ModuleCat` is canonically the tensor-product
module. -/
private noncomputable def extendScalars_tensor_module_iso
    (M : ModuleCat A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≅ ModuleCat.of B (B ⊗[A] M) := by
  -- Normalize the wrapped `extendScalars` owner to the tensor-product model.
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A M)).toModuleIso

/-- Helper for Lemma 15.96.10: flat tensoring preserves `f`-regularity, and this is the same as
regularity by `algebraMap A B f` on the resulting `B`-module. -/
private lemma tensor_isSMulRegular_algebraMap
    (f : A) (M : ModuleCat A) (hM : IsSMulRegular M f) :
    IsSMulRegular (ModuleCat.of B (B ⊗[A] M)) (algebraMap A B f) := by
  -- First preserve regularity on the tensor-product model using flatness of `B`.
  have hTensor : IsSMulRegular (B ⊗[A] M) f := by
    simpa using (IsSMulRegular.lTensor (R := A) (M := B) hM)
  -- Then rewrite the scalar `f` as its image under `algebraMap A B`.
  simpa using
    ((isSMulRegular_algebraMap_iff (R := A) (A := B) (M := B ⊗[A] M)).2 hTensor)

/-- Helper for Lemma 15.96.10: scalar extension along a flat algebra preserves regularity of a
single element on a module. -/
lemma extendScalars_isSMulRegular
    (f : A) (M : ModuleCat A) (hM : IsSMulRegular M f) :
    IsSMulRegular ((ModuleCat.extendScalars (algebraMap A B)).obj M) (algebraMap A B f) := by
  -- Route correction: prove regularity on the tensor-product model and transport it back across
  -- the canonical `extendScalars` comparison, rather than fighting the wrapped owner directly.
  let e :
      (((ModuleCat.extendScalars (algebraMap A B)).obj M) : ModuleCat B) ≃ₗ[B] (B ⊗[A] M) :=
    (extendScalars_tensor_module_iso (A := A) (B := B) M).toLinearEquiv
  -- The tensor-product model is the canonical place where flatness preserves regularity.
  have hTensor : IsSMulRegular (B ⊗[A] M) (algebraMap A B f) :=
    tensor_isSMulRegular_algebraMap (A := A) (B := B) f M hM
  -- Transport the regularity statement back to the wrapped `extendScalars` object.
  exact (LinearEquiv.isSMulRegular_congr e (algebraMap A B f)).2 hTensor

namespace BerthelotOgusInt

-- Proof sketch: in each degree `n`, tensor the injective endomorphism `f • ·` on `M.X n` with the
-- flat `A`-module `B`. The induced endomorphism on the scalar extension is multiplication by the
-- image of `f`, so each term of the base-changed complex is `g`-torsion free.
/-- Lemma 15.96.10 (2): if `K^•` is a cochain complex of `f`-torsion-free `A`-modules, then the
base-changed complex `K^• ⊗_A B` is termwise `g`-torsion free for `g = algebraMap A B f`. This is
the owner-level base-change theorem for `BerthelotOgusInt.IsTermwiseFTorsionFree`. -/
theorem IsTermwiseFTorsionFree.extendScalars
    (f : A) (K : ModuleComplex A)
    (hK : IsTermwiseFTorsionFree f K) :
    IsTermwiseFTorsionFree (algebraMap A B f)
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K) := by
  -- Unpack the owner predicate to a degreewise regularity statement.
  rw [isTermwiseFTorsionFree_iff] at hK ⊢
  intro i
  -- In degree `i`, the mapped complex is just the scalar extension of `K.X i`.
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj']
    using extendScalars_isSMulRegular (A := A) (B := B) f (K.X i) (hK i)

end BerthelotOgusInt

end
