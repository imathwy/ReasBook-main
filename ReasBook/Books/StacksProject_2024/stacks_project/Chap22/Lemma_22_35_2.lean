import StacksProject_2024.stacks_project.Chap22.Lemma_22_27_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory

universe u v w

/- Source/core/bridge triage:
- source-facing: the homotopy-category functor induced by a DG tensor functor from Lemma `22.35.1`;
- core/canonical: `DgFunctor.mapK_exact`;
- bridge/view: the Chapter 22 specialization below, recorded as a check of the canonical exactness
  owner rather than a duplicate theorem wrapper.
-/

section

variable {R : Type u} [CommRing R]
variable {DGModE : Type v} {ComplexdgO : Type w}
variable [DGModE_dg : DifferentialGradedCategory R DGModE]
variable [ComplexdgO_dg : DifferentialGradedCategory R ComplexdgO]

variable [HasShift (K R DGModE) ℤ] [HasShift (K R ComplexdgO) ℤ]
variable [HasZeroObject (K R DGModE)] [HasZeroObject (K R ComplexdgO)]
variable [Preadditive (K R DGModE)] [Preadditive (K R ComplexdgO)]
variable [∀ n : ℤ, (shiftFunctor (K R DGModE) n).Additive]
variable [∀ n : ℤ, (shiftFunctor (K R ComplexdgO) n).Additive]
variable [Pretriangulated (K R DGModE)] [Pretriangulated (K R ComplexdgO)]

variable (F : DgFunctor R DGModE ComplexdgO) [F.mapK.CommShift ℤ]

/- Lemma 22.35.2: if `F` is the DG tensor functor from Lemma `22.35.1`, then the induced functor
`F.mapK : K R DGModE ⥤ K R ComplexdgO` is exact in the triangulated sense. In the current
repository this is exactly the canonical specialization `DgFunctor.mapK_exact F`, so the numbered
item is recorded as the checked source-facing specialization below rather than as a duplicate local
theorem alias. -/
#check (DgFunctor.mapK_exact F : F.mapK.IsTriangulated)

end
