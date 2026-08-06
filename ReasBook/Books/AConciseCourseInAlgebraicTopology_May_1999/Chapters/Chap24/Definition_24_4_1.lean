import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.PowerSeries.Evaluation
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v w

-- This file keeps the split-bundle formula itself as the source-facing owner and packages the
-- coefficient-ring hypotheses needed for Chapter 24 characteristic classes into a reusable local
-- target class.

section

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {E : X → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]
variable {A : Type w}

/-- A first-Chern-class assignment for complex line bundles over `X` with values in `A`. -/
abbrev LineBundleFirstChernClass (X : Type u) [TopologicalSpace X] (A : Type w) :=
  ∀ (L : X → Type v),
    [TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) L)] →
    [(x : X) → TopologicalSpace (L x)] →
    [FiberBundle (Fin 1 → ℂ) L] →
    [(x : X) → AddCommGroup (L x)] →
    [(x : X) → Module ℂ (L x)] →
    [VectorBundle ℂ (Fin 1 → ℂ) L] →
    A

/-- `A` carries chosen first Chern classes for complex line bundles over `X`. -/
class HasLineBundleFirstChernClass (X : Type u) [TopologicalSpace X] (A : Type w) where
  firstChernClass : LineBundleFirstChernClass.{u, v, w} X A

/-- A coefficient ring in which Chapter 24 multiplicative characteristic classes of bundles over
`X` take values, equipped with chosen first Chern classes of complex line bundles over `X`. -/
class CharacteristicClassTarget (X : Type u) [TopologicalSpace X] (A : Type w)
    extends CommRing A, UniformSpace A, IsUniformAddGroup A, CompleteSpace A, T2Space A,
      IsTopologicalSemiring A, IsTopologicalRing A, IsLinearTopology A A, ContinuousSMul A A,
      HasLineBundleFirstChernClass X A

variable {A : Type w} [CharacteristicClassTarget X A]

/-- The chosen first Chern class of a complex line bundle over `X`, valued in `A`. -/
abbrev lineBundleFirstChernClass (L : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) L)]
    [(x : X) → TopologicalSpace (L x)] [FiberBundle (Fin 1 → ℂ) L]
    [(x : X) → AddCommGroup (L x)] [(x : X) → Module ℂ (L x)]
    [VectorBundle ℂ (Fin 1 → ℂ) L] : A :=
  HasLineBundleFirstChernClass.firstChernClass L

/-- Explicit split-bundle data for `E`, presented as a Whitney product of complex line bundles.
The Chern roots are derived canonically as the first Chern classes of the summands. -/
structure SplitBundleDatum (A : Type w) [CharacteristicClassTarget X A] (n : ℕ)
    (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
    [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
    [VectorBundle ℂ (Fin n → ℂ) E] where
  /-- The line-bundle summands whose Whitney product is identified with `E`. -/
  lineBundle : Fin n → X → Type v
  /-- The topology on the total space of each line-bundle summand. -/
  totalSpaceTopologicalSpace :
    ∀ i : Fin n, TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) (lineBundle i))
  /-- The topology on each fiber of the line-bundle summands. -/
  fiberTopologicalSpace : ∀ i : Fin n, (x : X) → TopologicalSpace (lineBundle i x)
  /-- Each summand is a complex line bundle. -/
  fiberBundle : ∀ i : Fin n, FiberBundle (Fin 1 → ℂ) (lineBundle i)
  /-- The additive-group structure on each summand fiber. -/
  addCommGroup : ∀ i : Fin n, (x : X) → AddCommGroup (lineBundle i x)
  /-- The complex-vector-space structure on each summand fiber. -/
  module : ∀ i : Fin n, (x : X) → Module ℂ (lineBundle i x)
  /-- The vector-bundle structure on each line-bundle summand. -/
  vectorBundle : ∀ i : Fin n, VectorBundle ℂ (Fin 1 → ℂ) (lineBundle i)
  /-- The total space of the finite Whitney product of the chosen line bundles carries its chosen
  topology. -/
  whitneyProductTotalSpaceTopologicalSpace :
    TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n lineBundle))
  /-- The bundle `E` is identified over `X` with the Whitney product of the chosen line bundles. -/
  splitTotalSpaceHomeomorph :
    Bundle.TotalSpace (Fin n → ℂ) E ≃ₜ
      Bundle.TotalSpace (Fin n → ℂ) (whitneyProductLineBundle n lineBundle)
  /-- Over each `x : X`, the total-space identification restricts to a complex-linear
  equivalence of fibers. -/
  splitFiberLinear :
    ∀ x : X, E x ≃ₗ[ℂ] ((i : Fin n) → lineBundle i x)
  /-- On each fiber, the total-space identification is given by the specified complex-linear
  equivalence. -/
  splitTotalSpaceHomeomorph_mk :
    ∀ (x : X) (v : E x),
      splitTotalSpaceHomeomorph (Bundle.TotalSpace.mk x v) =
        Bundle.TotalSpace.mk x (splitFiberLinear x v)
  /-- Formal power-series evaluation is defined at the first Chern class of each summand. -/
  summandFirstChernClass_hasEval :
    ∀ i : Fin n,
      letI := totalSpaceTopologicalSpace i
      letI := fiberTopologicalSpace i
      letI := fiberBundle i
      letI := addCommGroup i
      letI := module i
      letI := vectorBundle i
      PowerSeries.HasEval ((lineBundleFirstChernClass (lineBundle i)) : A)

namespace SplitBundleDatum

/-- The ambient first Chern class of the `i`th line-bundle summand in a split datum. -/
def summandFirstChernClass (D : SplitBundleDatum A n E) (i : Fin n) : A :=
  letI := D.totalSpaceTopologicalSpace i
  letI := D.fiberTopologicalSpace i
  letI := D.fiberBundle i
  letI := D.addCommGroup i
  letI := D.module i
  letI := D.vectorBundle i
  lineBundleFirstChernClass (D.lineBundle i)

/-- The `i`th Chern root of a split datum is the first Chern class of the corresponding summand. -/
abbrev cRoot (D : SplitBundleDatum A n E) (i : Fin n) : A :=
  D.summandFirstChernClass i

/-- The `i`th Chern root of a split datum is the first Chern class of the corresponding summand. -/
theorem cRoot_spec
    (D : SplitBundleDatum A n E) (i : Fin n) :
    D.cRoot i = D.summandFirstChernClass i := by
  rfl

/-- Formal power-series evaluation is defined at each Chern root of a split datum. -/
theorem cRoot_hasEval
    (D : SplitBundleDatum A n E) (i : Fin n) :
    PowerSeries.HasEval (D.cRoot i) :=
  D.summandFirstChernClass_hasEval i

end SplitBundleDatum

/-- Definition 24.4.1. For a split bundle `E` presented as the Whitney product of line bundles
`L_i` with Chern roots `x_i`, the multiplicative characteristic class attached to a power
series `f` is the product `∏ i, f(x_i)`. Here the split-bundle datum `D` records the
decomposition of `E`, while each `D.cRoot i` is canonically the first Chern class of the
summand `D.lineBundle i` in the chosen coefficient ring `A`. -/
def multiplicativeCharacteristicClass
    (f : PowerSeries A)
    (D : SplitBundleDatum A n E) : A :=
  ∏ i : Fin n, PowerSeries.aeval (D.cRoot_hasEval i) f

/-- Unfolding `multiplicativeCharacteristicClass` recovers the product of the evaluations of `f`
on the Chern roots of the split datum. -/
theorem multiplicativeCharacteristicClass_eq_prod_aeval
    (f : PowerSeries A)
    (D : SplitBundleDatum A n E) :
    multiplicativeCharacteristicClass f D =
      ∏ i : Fin n, PowerSeries.aeval (D.cRoot_hasEval i) f := rfl

end
end
