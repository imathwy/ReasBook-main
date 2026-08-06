import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open scoped DirectSum

noncomputable section

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M]
variable (H2 : ModTwoCohomologyTheory)
variable (w : StiefelWhitneyClassFamily H2)
variable [CommRing (modTwoCohomologyStar H2 (TopCat.of M))]

/-- The partition-indexed monomial in the Stiefel-Whitney classes of a chosen normal bundle `νₑ`,
viewed in the canonical total mod-`2` cohomology ring of `M`. -/
def normalStiefelWhitneyMonomial
    (r : ℕ) (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (σ : Nat.Partition n) :
    modTwoCohomologyStar H2 (TopCat.of M) :=
  (σ.parts.map fun i ↦
    (DirectSum.lof ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q (TopCat.of M)) i
      ((w r i).onFamily normalBundle) :
      modTwoCohomologyStar H2 (TopCat.of M))).prod

/-- The degree-`n` normal Stiefel-Whitney monomial class of `M` indexed by the partition `σ`,
obtained by projecting the total normal Stiefel-Whitney monomial of the chosen normal bundle `νₑ`
to cohomological degree `n`. -/
abbrev normalStiefelWhitneyMonomialClass
    (r : ℕ) (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (σ : Nat.Partition n) :
    modTwoCohomologyGroup H2 n (TopCat.of M) :=
  DirectSum.component ℤ ℕ (fun q ↦ modTwoCohomologyGroup H2 q (TopCat.of M)) n
    (normalStiefelWhitneyMonomial H2 w r normalBundle σ)

/-- The normal Stiefel-Whitney number of `M` indexed by the partition `σ`, obtained by evaluating
the degree-`n` normal Stiefel-Whitney monomial class of a chosen normal bundle `νₑ` on a chosen
fundamental class via the chosen degree-`n` pairing. The embedding data enters separately through
`IsNormalBundleOfEuclideanEmbedding`. -/
abbrev normalStiefelWhitneyNumber
    (r : ℕ)
    (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (σ : Nat.Partition n) : ZMod 2 :=
  kroneckerPairing (normalStiefelWhitneyMonomialClass H2 w r normalBundle σ) fundamentalClass

namespace CanonicalModTwoCohomologyAlgebra

/-- Evaluate the `σ`-indexed normal Stiefel-Whitney number using the canonical total mod-`2`
cohomology algebra carried by `A`. This is the explicit bridge from the chosen algebra owner to
the chapter-local normal characteristic-number API. -/
abbrev normalStiefelWhitneyNumber
    {H2' : ModTwoCohomologyTheory}
    (A : CanonicalModTwoCohomologyAlgebra H2' (TopCat.of M))
    (w : StiefelWhitneyClassFamily H2')
    (r : ℕ) (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2' n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (σ : Nat.Partition n) : ZMod 2 :=
  let _ : CommRing (modTwoCohomologyStar H2' (TopCat.of M)) := A.toCommRing
  _root_.normalStiefelWhitneyNumber H2' w r normalBundle fundamentalClass kroneckerPairing σ

end CanonicalModTwoCohomologyAlgebra

end
