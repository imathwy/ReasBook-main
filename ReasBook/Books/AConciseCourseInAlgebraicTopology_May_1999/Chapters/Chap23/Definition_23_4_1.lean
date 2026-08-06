import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_3_3

open AlgebraicTopology CategoryTheory
open scoped Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch` and the Chapter 23 tangent-class precedent:
-- `TangentSpace (𝓡 n)` is the canonical tangent-bundle owner for evaluating the chapter-local
-- `CharacteristicClass` API. No dedicated degree-`n` Kronecker-pairing owner surfaced locally
-- for an arbitrary cohomology target `k`, so the pairing remains an explicit parameter.

section

variable {R : Type} [CommRing R]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat}

/-- Definition 23.4.1. For a smooth closed `R`-oriented `n`-manifold `M` and a degree-`n`
characteristic class `c`, the tangential characteristic number `c[M]` associated to a compatible
`R`-fundamental class `[M]` and a chosen degree-`n` pairing is the scalar `⟨c(τM), [M]⟩`,
formalized by pairing the bridge class `tangentialCharacteristicClass c` with `[M]`. -/
abbrev tangentialCharacteristicNumber (c : CharacteristicClass n n k)
    (fundamentalClass : rSingularHomology R n (TopCat.of M))
    (kroneckerPairing :
      (k n).obj (Opposite.op (TopCat.of M)) →+
        rSingularHomology R n (TopCat.of M) →+ R) : R :=
  kroneckerPairing (tangentialCharacteristicClass c) fundamentalClass

end

section

variable {R : Type} [CommRing R]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable {k : ℕ → TopCatᵒᵖ ⥤ AddCommGrpCat}

/-- Unfolding `tangentialCharacteristicNumber` recovers the evaluation of `c(τM)` on the
compatible fundamental class `[M]` via the chosen degree-`n` pairing. -/
theorem tangentialCharacteristicNumber_def
    (c : CharacteristicClass n n k)
    (fundamentalClass : rSingularHomology R n (TopCat.of M))
    (kroneckerPairing :
      (k n).obj (Opposite.op (TopCat.of M)) →+
        rSingularHomology R n (TopCat.of M) →+ R) :
    tangentialCharacteristicNumber c fundamentalClass kroneckerPairing =
      kroneckerPairing (tangentialCharacteristicClass c) fundamentalClass := rfl

end
