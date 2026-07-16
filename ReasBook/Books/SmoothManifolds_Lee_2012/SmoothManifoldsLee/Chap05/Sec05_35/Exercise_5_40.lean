import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Notation_5_35_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_38

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

section SubmanifoldLevelSetTangent

universe u𝕜 uE uE' uF uH uH' uG uM uN

open Manifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]
variable {K : ModelWithCorners 𝕜 F G} [IsManifold K ∞ N]

omit [TopologicalSpace M] in
/-- Helper for Exercise 5.40: on a global level set `S = Φ ⁻¹' {c}`, membership in `S` is
equivalent to having the same `Φ`-value as any chosen base point of `S`. -/
theorem mem_level_set_iff_eq_basepoint {Φ : M → N} {c : N} {p q : M}
    (hlevel : S = Φ ⁻¹' {c}) (hpS : p ∈ S) :
    q ∈ S ↔ Φ q = Φ p := by
  -- First read off the base-point value of `Φ` from the global level-set equation.
  have hpΦ : Φ p = c := by
    have hpΦmem : Φ p ∈ ({c} : Set N) := by
      change p ∈ Φ ⁻¹' ({c} : Set N)
      simpa [hlevel] using hpS
    exact Set.mem_singleton_iff.mp hpΦmem
  -- Then both conditions are the same singleton-membership statement for `c`.
  simp [hlevel, hpΦ]

/-- Helper for Exercise 5.40: near any point of a constant-rank level set, there should exist a
local defining map to `𝕜^r` whose derivative has the same kernel as the original map at the base
point. This is the local slice statement supplied by the constant-rank normal form. -/
theorem exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank
    {r : ℕ} {Φ : M → N} {c : N} (hΦ : ContMDiff I K ∞ Φ)
    (hRank : HasConstantRank I K Φ r) (hlevel : S = Φ ⁻¹' {c}) (p : S) :
    ∃ Ψ : M → Fin r → 𝕜, ∃ U : Set M, (p : M) ∈ U ∧
      IsLocalDefiningMapOn I 𝓘(𝕜, Fin r → 𝕜) S U Ψ ∧
      (mfderiv I 𝓘(𝕜, Fin r → 𝕜) Ψ (p : M)).ker = (mfderiv I K Φ (p : M)).ker := by
  -- TODO: derive the projected defining map from a generic pointwise constant-rank normal form
  -- compatible with arbitrary `𝕜`, `I`, and `K`, then invoke `mem_level_set_iff_eq_basepoint`
  -- to identify the local fiber and compute the base-point kernel.
  sorry

-- Proof sketch: apply the constant-rank theorem at the ambient point `(p : M)` to obtain a local
-- normal form in which the level set `S = Φ ⁻¹' {c}` is cut out by projection onto the rank
-- coordinates, so `Φ` is a local defining map for `S` near `p`. Then invoke Proposition 5.38 to
-- identify the tangent space of `S` with the kernel of `dΦₚ`.
/-- Exercise 5.40: if `S` is the level set `Φ ⁻¹' {c}` of a smooth map `Φ : M → N` with constant
rank, then for each `p ∈ S` the tangent space of `S` at `p`, viewed inside the ambient tangent
space, is the kernel of `dΦₚ`. -/
theorem tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank
    {r : ℕ} {Φ : M → N} {c : N} (hΦ : ContMDiff I K ∞ Φ)
    (hRank : HasConstantRank I K Φ r)
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M)) (hlevel : S = Φ ⁻¹' {c}) (p : S) :
    T[J; p] = (mfderiv I K Φ (p : M)).ker := by
  -- Route correction: the constant-rank case must first be converted into a local defining map of
  -- rank `r`; Proposition 5.38 then applies exactly as in the regular-value case.
  rcases
      exists_local_defining_map_on_nhds_to_fin_of_level_set_of_has_constant_rank
        (I := I) (K := K) (S := S) hΦ hRank hlevel p with
    ⟨Ψ, U, hpU, hΨ, hker⟩
  -- Proposition 5.38 identifies the tangent space with the kernel of the local defining map.
  rw [tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn hS hΨ p hpU]
  -- The auxiliary defining map was chosen so that its kernel agrees with `ker dΦₚ`.
  exact hker

end SubmanifoldLevelSetTangent
