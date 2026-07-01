import Mathlib
import SmoothManifoldsLee.Chap04.Sec04_21.Exercise_4_4
import SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_8
import SmoothManifoldsLee.Chap04.Sec04_23.Theorem_4_12

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was fixed from the local constant-rank API in `Exercise_4_4`, the normal-form statement in
-- `Theorem_4_12`, and the local-diffeomorphism bridge in `Proposition_4_8`.

noncomputable section

open scoped ContDiff Manifold

universe uM uN

section GlobalRankTheorem

variable {m n r : ℕ}
variable {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- Theorem 4.14 (1) (Global Rank Theorem): a surjective smooth map of constant rank is a smooth
submersion. -/
-- Proof sketch: if the constant rank were strictly smaller than the target dimension, Theorem 4.12
-- would put the image locally inside coordinate slices of positive codimension; a countable cover
-- and the Baire category theorem would then rule out surjectivity.
theorem constant_rank_surjective_is_smooth_submersion {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFsurj : Function.Surjective F) :
    Manifold.IsSmoothSubmersion I_m I_n F := sorry

/-- Theorem 4.14 (2) (Global Rank Theorem): an injective smooth map of constant rank is a smooth
immersion. -/
-- Proof sketch: if the constant rank were strictly smaller than the source dimension, Theorem 4.12
-- would identify local coordinates in which `F` forgets at least one source coordinate, producing
-- distinct nearby points with the same image and contradicting injectivity.
theorem constant_rank_injective_is_immersion {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFinj : Function.Injective F) :
    Manifold.IsImmersion I_m I_n ∞ F := sorry

/-- Theorem 4.14 (3) (Global Rank Theorem): a bijective smooth map of constant rank is a
diffeomorphism. -/
-- Proof sketch: combine parts (1) and (2) to obtain that `F` is both a smooth submersion and a
-- smooth immersion, apply Proposition 4.8 to get a smooth local diffeomorphism, and then upgrade
-- the bijective local diffeomorphism to a global diffeomorphism.
theorem constant_rank_bijective_is_diffeomorphism {F : M → N}
    (hFsmooth : ContMDiff I_m I_n ∞ F) (hFrank : Manifold.HasConstantRank I_m I_n F r)
    (hFbij : Function.Bijective F) :
    ∃ Φ : M ≃ₘ⟮I_m, I_n⟯ N, ∀ x : M, Φ x = F x := sorry

end GlobalRankTheorem
