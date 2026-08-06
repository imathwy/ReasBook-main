import Mathlib.Data.ZMod.Basic
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_4

open scoped Manifold Topology

noncomputable section

-- The canonical intrinsic vanishing owner for Chapter 23 already lives in
-- `allTangentialStiefelWhitneyNumbersVanish`; this file supplies the source-facing bridge from
-- that intrinsic predicate to the chosen-data normal-bundle wording used in Thom's theorem.

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
variable
  [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]

namespace allTangentialStiefelWhitneyNumbersVanish

/-- A proof of the intrinsic Chapter 23 vanishing condition specializes to the vanishing of all
normal Stiefel-Whitney numbers in any fixed compatible setup with a chosen Euclidean embedding
and a chosen normal bundle `νₑ`. -/
theorem normal_in_setup
    (h_vanish : allTangentialStiefelWhitneyNumbersVanish n M)
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily.{0} H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    {r : ℕ}
    (e : M → EuclideanSpace ℝ (Fin (n + r)))
    (h_smooth :
      ContMDiff (𝓡 n) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ e)
    (h_embedding : Topology.IsClosedEmbedding e)
    (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (h_normal : IsNormalBundleOfEuclideanEmbedding e normalBundle)
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
    normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
      fundamentalClass kroneckerPairing := by
  have h_tangential :
      tangentialStiefelWhitneyNumbersVanishInSetup H2 w A
        fundamentalClass kroneckerPairing := by
    intro σ
    exact
      h_vanish.eq_zero H2 w A normalizationData h_stiefelWhitney
        fundamentalClass h_fundamental canonicalKroneckerPairing h_pairing kroneckerPairing
        h_transport
  exact
    StiefelWhitneyNumberVanishing.normal_of_tangential
      H2 w normalizationData h_stiefelWhitney A e h_smooth h_embedding normalBundle h_normal
      fundamentalClass h_fundamental kroneckerPairing h_tangential

end allTangentialStiefelWhitneyNumbersVanish

/-- The source-facing Chapter 23 condition that all normal Stiefel-Whitney numbers of the smooth
closed `n`-manifold `M` vanish. This quantifies over the same chapter-local cohomology,
fundamental-class, Euclidean-embedding, normal-bundle, and Kronecker-pairing data that appear in
the textbook normal-bundle formulation, and requires the resulting fixed-setup normal
Stiefel-Whitney numbers to vanish for every compatible choice. -/
def allNormalStiefelWhitneyNumbersVanish (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
    [IsManifold (𝓡 n) ⊤ M]
    [TopologicalSpace
      (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _))]
    [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)]
    [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : TopCat.of M → Type _)] :
    Prop :=
  ∀ (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily.{0} H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2),
      IsStiefelWhitneyTheory H2 normalizationData w →
        ∀ {r : ℕ}
          (e : M → EuclideanSpace ℝ (Fin (n + r)))
          (normalBundle : TopCat.of M → Type _)
          [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
          [∀ b, NormedAddCommGroup (normalBundle b)]
          [∀ b, NormedSpace ℝ (normalBundle b)]
          [FiberBundle (Fin r → ℝ) normalBundle]
          [VectorBundle ℝ (Fin r → ℝ) normalBundle]
          (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M)),
          ContMDiff (𝓡 n)
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ e →
            Topology.IsClosedEmbedding e →
              IsNormalBundleOfEuclideanEmbedding e normalBundle →
                IsRFundamentalClass (ZMod 2) n M fundamentalClass →
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
                    normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
                      fundamentalClass kroneckerPairing

namespace allNormalStiefelWhitneyNumbersVanish

/-- A proof of `allNormalStiefelWhitneyNumbersVanish n M` specializes to any fixed compatible
Chapter 23 normal-bundle setup. -/
theorem in_setup
    (h_vanish : allNormalStiefelWhitneyNumbersVanish n M)
    (H2 : ModTwoCohomologyTheory) (w : StiefelWhitneyClassFamily.{0} H2)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    {r : ℕ}
    (e : M → EuclideanSpace ℝ (Fin (n + r)))
    (h_smooth :
      ContMDiff (𝓡 n) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + r)))) ⊤ e)
    (h_embedding : Topology.IsClosedEmbedding e)
    (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (h_normal : IsNormalBundleOfEuclideanEmbedding e normalBundle)
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
    normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
      fundamentalClass kroneckerPairing :=
  h_vanish H2 w A normalizationData h_stiefelWhitney
    e normalBundle fundamentalClass h_smooth h_embedding h_normal h_fundamental
    canonicalKroneckerPairing h_pairing kroneckerPairing h_transport

/-- The source-facing normal-vanishing condition implies the intrinsic Chapter 23 tangential
vanishing owner by Lemma 23.4.4 in every compatible fixed setup. -/
theorem tangential
    (h_vanish : allNormalStiefelWhitneyNumbersVanish n M) :
    allTangentialStiefelWhitneyNumbersVanish n M := by
  sorry

end allNormalStiefelWhitneyNumbersVanish

namespace allTangentialStiefelWhitneyNumbersVanish

/-- The intrinsic tangential Chapter 23 vanishing owner and the source-facing normal-bundle
vanishing owner are equivalent. The tangential formulation is the canonical intrinsic bridge,
while the normal formulation preserves the textbook hypothesis of Theorem 23.4.5. -/
theorem iff_normal :
    allTangentialStiefelWhitneyNumbersVanish n M ↔
      allNormalStiefelWhitneyNumbersVanish n M := by
  constructor
  · intro h_vanish
    intro H2 w A normalizationData h_stiefelWhitney r e normalBundle
      _ _ _ _ _ fundamentalClass h_smooth h_embedding h_normal h_fundamental
      canonicalKroneckerPairing h_pairing kroneckerPairing h_transport
    exact
      h_vanish.normal_in_setup H2 w A normalizationData h_stiefelWhitney e h_smooth
        h_embedding normalBundle h_normal fundamentalClass h_fundamental
        canonicalKroneckerPairing h_pairing kroneckerPairing h_transport
  · exact allNormalStiefelWhitneyNumbersVanish.tangential

end allTangentialStiefelWhitneyNumbersVanish

/-- The intrinsic Chapter 23 companion theorem: if all tangential Stiefel-Whitney numbers of a
smooth closed `n`-manifold `M` vanish, then `M` bounds a compact smooth manifold. The main
source-facing theorem below keeps the equivalent normal-bundle hypothesis from the textbook. -/
theorem boundsCompactSmoothManifold_of_allTangentialStiefelWhitneyNumbersVanish
    (h_vanish : allTangentialStiefelWhitneyNumbersVanish n M) :
    boundsCompactSmoothManifold n M := sorry

/-- Theorem 23.4.5. Thom theorem: if all normal Stiefel-Whitney numbers of a smooth closed
`n`-manifold `M` vanish, then `M` is diffeomorphic to the boundary of a smooth compact
`(n + 1)`-manifold with boundary. In this development, the source hypothesis is represented by
the source-facing global owner `allNormalStiefelWhitneyNumbersVanish n M`. The equivalent
intrinsic Chapter 23 owner is
`allTangentialStiefelWhitneyNumbersVanish n M`, and the bridge between the two formulations is
`allTangentialStiefelWhitneyNumbersVanish.iff_normal`. The boundary
conclusion uses the predicate `boundsCompactSmoothManifold n M`. -/
theorem boundsCompactSmoothManifold_of_allNormalStiefelWhitneyNumbersVanish
    (h_vanish : allNormalStiefelWhitneyNumbersVanish n M) :
    boundsCompactSmoothManifold n M :=
  boundsCompactSmoothManifold_of_allTangentialStiefelWhitneyNumbersVanish
    (allNormalStiefelWhitneyNumbersVanish.tangential h_vanish)

end
