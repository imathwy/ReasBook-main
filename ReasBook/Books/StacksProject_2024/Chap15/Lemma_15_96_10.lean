import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.TorsionFree
import StacksProject_2024.Chap15.Lemma_15_96_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped nonZeroDivisors

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
  sorry

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
  sorry

end BerthelotOgusInt

end
