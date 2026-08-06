import Mathlib.Geometry.Manifold.Immersion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_4.Normal
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Lemma_23_4_3.Tangential

open scoped Manifold Topology

noncomputable section

-- The reusable partition-indexed normal Stiefel-Whitney monomial/class/number owners live in the
-- item-owned foundation module `Lemma_23_4_4.Normal`. This file keeps the source-facing fixed-setup
-- equivalence between tangential and normal vanishing.

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

variable (H2 : ModTwoCohomologyTheory)
variable (w : StiefelWhitneyClassFamily H2)

/-- The fixed-setup statement that all tangential Stiefel-Whitney numbers of `M` vanish for the
chosen mod-`2` theory, Stiefel-Whitney classes, canonical total cohomology algebra, fundamental
class, and degree-`n` pairing. -/
def tangentialStiefelWhitneyNumbersVanishInSetup
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2) :
    Prop :=
  ∀ σ : Nat.Partition n,
    A.tangentialStiefelWhitneyNumber w fundamentalClass kroneckerPairing σ = 0

/-- The fixed-setup statement that all normal Stiefel-Whitney numbers of `M` vanish for the chosen
mod-`2` theory, Stiefel-Whitney classes, canonical total cohomology algebra, normal bundle,
fundamental class, and degree-`n` pairing. -/
def normalStiefelWhitneyNumbersVanishInSetup
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
    (r : ℕ) (normalBundle : TopCat.of M → Type _)
    [TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) normalBundle)]
    [∀ b, NormedAddCommGroup (normalBundle b)]
    [∀ b, NormedSpace ℝ (normalBundle b)]
    [FiberBundle (Fin r → ℝ) normalBundle]
    [VectorBundle ℝ (Fin r → ℝ) normalBundle]
    (fundamentalClass : rSingularHomology (ZMod 2) n (TopCat.of M))
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2) :
    Prop :=
  ∀ σ : Nat.Partition n,
    A.normalStiefelWhitneyNumber w r normalBundle fundamentalClass kroneckerPairing σ = 0

namespace StiefelWhitneyNumberVanishing

/-- Lemma 23.4.4. All tangential Stiefel-Whitney numbers vanish if and only if all normal
Stiefel-Whitney numbers vanish, for a chosen canonical total mod-`2` cohomology algebra on `M`, a
chosen Euclidean embedding of `M`, a chosen normal bundle `νₑ`, and the degree-`n` pairing used
to form these characteristic numbers. -/
theorem tangential_iff_normal
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
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
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2) :
    tangentialStiefelWhitneyNumbersVanishInSetup H2 w A fundamentalClass kroneckerPairing ↔
      normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
        fundamentalClass kroneckerPairing := sorry

/-- In the fixed Chapter 23 setup of Lemma 23.4.4, tangential vanishing implies normal vanishing
for the chosen normal bundle `νₑ`. -/
theorem normal_of_tangential
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
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
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (h_vanish :
      tangentialStiefelWhitneyNumbersVanishInSetup H2 w A fundamentalClass kroneckerPairing) :
    normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
      fundamentalClass kroneckerPairing :=
  (tangential_iff_normal H2 w normalizationData h_stiefelWhitney A e h_smooth h_embedding
    normalBundle h_normal fundamentalClass h_fundamental kroneckerPairing).mp h_vanish

/-- In the fixed Chapter 23 setup of Lemma 23.4.4, normal vanishing implies tangential vanishing. -/
theorem tangential_of_normal
    (normalizationData : StiefelWhitneyNormalization H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w)
    (A : CanonicalModTwoCohomologyAlgebra H2 (TopCat.of M))
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
    (kroneckerPairing :
      modTwoCohomologyGroup H2 n (TopCat.of M) →+
        rSingularHomology (ZMod 2) n (TopCat.of M) →+ ZMod 2)
    (h_vanish :
      normalStiefelWhitneyNumbersVanishInSetup H2 w A r normalBundle
        fundamentalClass kroneckerPairing) :
    tangentialStiefelWhitneyNumbersVanishInSetup H2 w A fundamentalClass kroneckerPairing :=
  (tangential_iff_normal H2 w normalizationData h_stiefelWhitney A e h_smooth h_embedding
    normalBundle h_normal fundamentalClass h_fundamental kroneckerPairing).mpr h_vanish

end StiefelWhitneyNumberVanishing

end
