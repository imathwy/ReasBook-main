import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import stacks_project.Chap12.Definition_12_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] (P : ObjectProperty 𝒜)

/- Domain-style sampling for Lemma 12.10.3:
- primary domain: weak Serre object properties in abelian categories and the induced exact
  full-subcategory formalism;
- sampled owner declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ObjectProperty.isWeakSerreClass_of_closure`,
  `ObjectProperty.IsClosedUnderBinaryProducts`,
  `ObjectProperty.IsClosedUnderFiniteProducts`,
  `ObjectProperty.FullSubcategory`;
- best owner abstraction: an object property `P : ObjectProperty 𝒜` equipped with
  `[P.IsWeakSerreClass]`;
- primitive data: the source-facing weak-Serre four-out-of-five exactness criterion from
  Definition 12.10.1;
- derived API: containing zero, closure under kernels/cokernels/extensions and then closure under
  isomorphisms and finite products, the abelian structure on `P.FullSubcategory`, and exactness
  of the inclusion `P.ι`.

Source/core/bridge triage:
- `source-facing`: the Stacks consequences for a weak Serre subcategory;
- `core/canonical`: the `ObjectProperty` owner `P`, together with `P.FullSubcategory` and `P.ι`;
- `bridge/view`: the exactness statement for the inclusion functor, derived from the canonical
  kernel/cokernel preservation API. -/

/- Companion bridge: `isWeakSerreClass_of_closure` recovers the source-facing owner abstraction
from the later closure-package characterization. -/
#check isWeakSerreClass_of_closure

/- Definition 12.10.1 stores the primitive four-out-of-five exactness criterion directly. -/
#check IsWeakSerreClass.prop_X₂_of_exact₄

/-- A weak Serre subcategory is closed under isomorphisms. -/
instance [IsWeakSerreClass P] :
    P.IsClosedUnderIsomorphisms :=
  isClosedUnderIsomorphisms_of_containsZero_of_closedUnderExtensions P

/-- A weak Serre subcategory is closed under binary products. -/
instance [IsWeakSerreClass P] :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have hXY : P (X ⊞ Y) := P.prop_biprod (hF _) (hF _)
  let hPair :
      IsLimit ((Cone.postcompose (diagramIsoPair F).hom).obj (limit.cone F)) :=
    (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).2 (limit.isLimit F)
  exact P.prop_of_iso (IsLimit.conePointUniqueUpToIso hPair (BinaryBiproduct.isLimit X Y)).symm
    hXY

/-- A weak Serre subcategory is closed under finite products. -/
instance [IsWeakSerreClass P] : P.IsClosedUnderFiniteProducts := by
  exact .mk'

section

variable [IsWeakSerreClass P]

/- Lemma 12.10.3 (1): a weak Serre subcategory contains a zero object. -/
#synth P.ContainsZero

/- Lemma 12.10.3 (2): a weak Serre subcategory is strictly full, i.e. closed under
isomorphisms. -/
#synth P.IsClosedUnderIsomorphisms

/- Lemma 12.10.3 (3): kernels and cokernels in `𝒜` of morphisms between objects of the weak
Serre subcategory again belong to the subcategory. -/
#synth P.IsClosedUnderKernels
#synth P.IsClosedUnderCokernels

/- Lemma 12.10.3 (4): an extension of two objects of a weak Serre subcategory again belongs
to the subcategory. -/
#synth P.IsClosedUnderExtensions

/- Lemma 12.10.3 (Moreover): the full subcategory cut out by a weak Serre subcategory of an
abelian category is itself abelian. This is the canonical mathlib instance on
`P.FullSubcategory`, derived from zero, kernel, cokernel, and finite-product closure. -/
#synth Abelian P.FullSubcategory

/-- Lemma 12.10.3 (Moreover): the inclusion functor of a weak Serre subcategory into the ambient
abelian category is exact. -/
theorem weakSerreSubcategory_inclusion_exact :
    exactFunctor P.FullSubcategory 𝒜 P.ι := by
  rw [exactFunctor_iff]
  constructor
  · letI : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) P.ι :=
      fun {_ _} f ↦ P.preservesKernels_ι f
    exact P.ι.preservesFiniteLimits_of_preservesKernels
  · letI : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) P.ι :=
      fun {_ _} f ↦ P.preservesCokernels_ι f
    exact P.ι.preservesFiniteColimits_of_preservesCokernels

/-- The inclusion functor of a weak Serre subcategory preserves finite limits. -/
theorem weakSerreSubcategory_inclusion_preservesFiniteLimits :
    PreservesFiniteLimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.1

/-- The inclusion functor of a weak Serre subcategory preserves finite colimits. -/
theorem weakSerreSubcategory_inclusion_preservesFiniteColimits :
    PreservesFiniteColimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.2

end

end CategoryTheory.ObjectProperty
