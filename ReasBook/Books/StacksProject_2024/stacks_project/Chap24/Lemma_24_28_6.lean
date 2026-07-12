import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe uM vM uD vD uN

namespace DifferentialGradedModule

-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner choice was
-- checked against the local Chapter 13 derived-functor API and the Chapter 21 fixed-right-factor
-- derived tensor owner.

section

variable {DGModA : Type uM} [Category.{vM} DGModA]
variable {DerivedDGModB : Type uD} [Category.{vD} DerivedDGModB]
variable {DGBimodAB : Type uN}

/-- Lemma 24.28.6: let `(\mathcal C, \mathcal O)` be a ringed site, let `\mathcal A` and
`\mathcal B` be differential graded `\mathcal O`-algebras, and let `\mathcal N` be a
differential graded `(\mathcal A, \mathcal B)`-bimodule. If `\mathcal N` is good as a left
differential graded `\mathcal A`-module, formalized here by the fixed-right-factor tensor functor
with `N` inverting quasi-isomorphisms in the left variable, then the corresponding
localization-valued tensor functor admits pointwise left derived values everywhere. -/
theorem tensorRightHasPointwiseLeftDerivedFunctor_of_isInvertedBy
    (QisA : MorphismProperty DGModA)
    (tensorRightToDerived : DGBimodAB → DGModA ⥤ DerivedDGModB)
    {N : DGBimodAB}
    (hN : QisA.IsInvertedBy (tensorRightToDerived N)) :
    (tensorRightToDerived N).HasPointwiseLeftDerivedFunctor QisA :=
  Functor.hasPointwiseLeftDerivedFunctor_of_inverts (tensorRightToDerived N) hN

/-- Lemma 24.28.6: let `(\mathcal C, \mathcal O)` be a ringed site, let `\mathcal A` and
`\mathcal B` be differential graded `\mathcal O`-algebras, and let `\mathcal N` be a
differential graded `(\mathcal A, \mathcal B)`-bimodule. If `\mathcal N` is good as a left
differential graded `\mathcal A`-module, formalized here by the fixed-right-factor tensor functor
with `N` inverting quasi-isomorphisms in the left variable, then for every differential graded
`\mathcal A`-module `M` that fixed-right-factor tensor functor already computes its left derived
functor at `M`. This is the abstract owner form of the source identity
`M \otimes^{\mathbf L}_{\mathcal A} N = M \otimes_{\mathcal A} N`. -/
theorem tensorRightComputesLeftDerivedAt_of_isInvertedBy
    (QisA : MorphismProperty DGModA)
    [QisA.ContainsIdentities]
    (tensorRightToDerived : DGBimodAB → DGModA ⥤ DerivedDGModB)
    {N : DGBimodAB}
    (hN : QisA.IsInvertedBy (tensorRightToDerived N))
    (M : DGModA) :
    (tensorRightToDerived N).ComputesLeftDerivedAt QisA M := by
  let tensorRightN := tensorRightToDerived N
  letI : tensorRightN.HasPointwiseLeftDerivedFunctor QisA :=
    tensorRightHasPointwiseLeftDerivedFunctor_of_isInvertedBy QisA tensorRightToDerived hN
  have hCounit : IsIso ((tensorRightN.totalLeftDerivedCounit QisA.Q QisA).app M) := by
    letI : IsIso (tensorRightN.totalLeftDerivedCounit QisA.Q QisA) :=
      Functor.isIso_of_isLeftDerivedFunctor_of_inverts
        (tensorRightN.totalLeftDerived QisA.Q QisA)
        (tensorRightN.totalLeftDerivedCounit QisA.Q QisA)
        hN
    infer_instance
  exact (tensorRightN.computesLeftDerivedAt_iff QisA M).2 hCounit

end

end DifferentialGradedModule
