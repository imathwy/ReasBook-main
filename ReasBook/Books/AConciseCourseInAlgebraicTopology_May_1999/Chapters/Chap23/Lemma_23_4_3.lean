import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_3.Tangential
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open scoped Manifold Topology

noncomputable section

-- Semantic recall via `lean_leansearch` only surfaced the manifold-boundary API, and local
-- Chapter 23 precedent fixes the characteristic-number owner: manifolds with boundary are carried
-- by `IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ⊤ W`, with boundary subtype
-- `(modelWithCornersEuclideanHalfSpace (n + 1)).boundary W`.
-- Definition 23.4.1 keeps the degree-`n` pairing explicit on the chapter-local
-- characteristic-number owner, while `ModTwoCohomologyTheory.comparison` identifies the ambient
-- theory with Chapter 22 mod-`2` singular cohomology and Chapter 20 supplies the compatibility
-- predicate `IsRFundamentalClass (ZMod 2) n M z`. The source-facing vanishing statement is
-- therefore recorded intrinsically through a source-facing vanishing proposition, while the
-- explicit chosen-data evaluation remains helper infrastructure. The public canonical pairing
-- owner is Chapter 20's `IsCanonicalRSingularKroneckerPairing`, while this file keeps only the
-- private comparison bridge from Chapter 22 mod-`2` singular cohomology to the Chapter 20
-- `rSingularCohomology` owner.

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [CompactSpace M]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
variable
  [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]

/-- `M` bounds a compact smooth manifold when it is diffeomorphic, as a smooth `n`-manifold, to
the boundary of some compact smooth `(n + 1)`-manifold with boundary. Since mathlib carries the
boundary as the subtype `(modelWithCornersEuclideanHalfSpace (n + 1)).boundary W`, this is
recorded directly by the existence of a smooth diffeomorphism onto that boundary manifold,
together with an explicit `n`-manifold charted-space structure on the boundary subtype. -/
def boundsCompactSmoothManifold (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  ∃ (W : Type) (_ : TopologicalSpace W) (_ : T2Space W)
    (_ : ChartedSpace (EuclideanHalfSpace (n + 1)) W)
    (_ : IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ⊤ W)
    (_ : CompactSpace W)
    (_ :
      ChartedSpace (EuclideanSpace ℝ (Fin n))
        ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)),
      Nonempty
        (Diffeomorph (𝓡 n) (𝓡 n) M
          ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) ⊤)

variable (H2 : ModTwoCohomologyTheory)
variable (w : StiefelWhitneyClassFamily H2)

/-- The fixed-setup statement that the `σ`-indexed tangential Stiefel-Whitney number of `M` has
the canonical value `value`, independently of which compatible Chapter 20 singular Kronecker
pairing is used to evaluate it. This keeps the public source-facing API at the theorem/spec level,
while the representative-based transport remains private helper infrastructure. -/
def tangentialStiefelWhitneyNumberHasValueInSetup
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (σ : Nat.Partition n) (value : ZMod 2) : Prop :=
  ∀ (canonicalKroneckerPairing :
      rSingularCohomology (ZMod 2) (TopCat.of M) n →ₗ[ZMod 2]
        rSingularHomology (ZMod 2) n (TopCat.of M) →ₗ[ZMod 2] ZMod 2),
    IsCanonicalRSingularKroneckerPairing
        (ZMod 2) (TopCat.of M) n canonicalKroneckerPairing →
      ∀ kroneckerPairing :
          modTwoCohomologyGroup H2 n (TopCat.of M) →+
            rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2,
        IsModTwoSingularKroneckerTransport H2 canonicalKroneckerPairing
            kroneckerPairing →
          A.tangentialStiefelWhitneyNumber w fundamentalClass kroneckerPairing σ = value

/-- The source-facing Chapter 23 condition that all tangential Stiefel-Whitney numbers of the
smooth closed `n`-manifold `M` vanish. This is recorded intrinsically by requiring that for every
compatible chapter-local mod-`2` cohomology theory, Stiefel-Whitney theory, canonical total
cohomology algebra, and partition `σ : Nat.Partition n`, every compatible explicit evaluation
built from a canonical Chapter 20 singular Kronecker pairing has canonical value `0` after
transport along the comparison bridge. -/
def allTangentialStiefelWhitneyNumbersVanish (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
    [IsManifold (𝓡 n) ⊤ M]
    [TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
    [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
    [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)] :
    Prop :=
  ∀ (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2),
      IsStiefelWhitneyTheory H2 normalizationData w →
        ∀ (σ : Nat.Partition n)
          (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M)),
          IsRFundamentalClass (ZMod 2) n M fundamentalClass →
            tangentialStiefelWhitneyNumberHasValueInSetup H2 w A
              fundamentalClass σ 0

namespace allTangentialStiefelWhitneyNumbersVanish

/-- A proof of `allTangentialStiefelWhitneyNumbersVanish n M` specializes to any fixed compatible
Chapter 23 mod-`2` setup. -/
theorem in_setup
    (h_vanish : allTangentialStiefelWhitneyNumbersVanish n M)
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    (σ : Nat.Partition n)
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (h_fundamental : IsRFundamentalClass (ZMod 2) n M fundamentalClass) :
    tangentialStiefelWhitneyNumberHasValueInSetup H2 w A
      fundamentalClass σ 0 :=
  h_vanish H2 w A normalizationData h_stiefelWhitney
    σ fundamentalClass h_fundamental

/-- Specializing `allTangentialStiefelWhitneyNumbersVanish n M` to a fixed compatible Chapter 23
setup and a fixed partition `σ` yields the vanishing of the corresponding explicit tangential
Stiefel-Whitney-number evaluation. -/
theorem eq_zero
    (h_vanish : allTangentialStiefelWhitneyNumbersVanish n M)
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    {σ : Nat.Partition n}
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (h_fundamental : IsRFundamentalClass (ZMod 2) n M fundamentalClass)
    (canonicalKroneckerPairing :
      rSingularCohomology (ZMod 2) (TopCat.of M) n →ₗ[ZMod 2]
        rSingularHomology (ZMod 2) n (TopCat.of M) →ₗ[ZMod 2] ZMod 2)
    (h_pairing :
      IsCanonicalRSingularKroneckerPairing
        (ZMod 2) (TopCat.of M) n canonicalKroneckerPairing)
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (h_transport :
      IsModTwoSingularKroneckerTransport H2 canonicalKroneckerPairing kroneckerPairing) :
    A.tangentialStiefelWhitneyNumber w
      fundamentalClass kroneckerPairing σ = 0 := by
  exact
    (h_vanish.in_setup H2 w A normalizationData h_stiefelWhitney
      σ fundamentalClass h_fundamental)
      canonicalKroneckerPairing h_pairing kroneckerPairing h_transport

/-- Lemma 23.4.3. If `M` is the boundary of a smooth compact manifold, then all tangential
Stiefel-Whitney numbers of `M` vanish. In this file, the source-facing intrinsic owner for that
conclusion is `allTangentialStiefelWhitneyNumbersVanish n M`, and the fixed-setup vanishing claim
is recovered by `allTangentialStiefelWhitneyNumbersVanish.in_setup`. -/
theorem of_boundsCompactSmoothManifold
    (h_bounds : boundsCompactSmoothManifold n M) :
    allTangentialStiefelWhitneyNumbersVanish n M := sorry

end allTangentialStiefelWhitneyNumbersVanish

end
