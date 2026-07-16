import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_51.Exercise_7_31

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tooling is unavailable in this environment; local repository inspection
-- verified the source-facing owner `LieSubgroup`, the canonical smooth homomorphism owner
-- `ContMDiffMonoidMorphism`, and the semidirect-product owners `LieGroupIsomorphism`,
-- `semidirectProductGroup`, and `semidirectProductLieGroup` used below.

open scoped Manifold ContDiff

section

universe u𝕜 uEG uHG uG uEN uHN uN uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I_G : ModelWithCorners 𝕜 EG HG}
variable {I_N : ModelWithCorners 𝕜 EN HN}
variable {I_H : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {N : Type uN} [Group N] [TopologicalSpace N] [ChartedSpace HN N]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I_G ∞ G] [LieGroup I_N ∞ N] [LieGroup I_H ∞ H]

/-- Problem 7-19: a Lie group `G` is Lie-group-isomorphic to a semidirect product `N ⋊ H` if and
only if there are Lie group homomorphisms `φ : G → H` and `ψ : H → G` with `φ ∘ ψ = id`, and the
kernel of `φ` admits a Lie subgroup structure that is Lie-group-isomorphic to `N`. On the
semidirect-product side, `N ⋊ H` is realized on `N × H` via some smooth action
`θ : H →* MulAut N`. -/
theorem lie_group_isomorphic_to_semidirect_product_iff_exists_split_lie_homs
    :
    (∃ θ : H →* MulAut N,
      ∃ hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2),
        let _ : Group (N × H) := semidirectProductGroup θ
        let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
        Nonempty (LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G)) ↔
      ∃ φ : ContMDiffMonoidMorphism I_G I_H ∞ G H,
        ∃ ψ : ContMDiffMonoidMorphism I_H I_G ∞ H G,
          (∀ h : H, φ (ψ h) = h) ∧
            ∃ K : LieSubgroup I_G,
              K.carrier = φ.toMonoidHom.ker ∧
                Nonempty (LieGroupIsomorphism I_N (modelWithCornersSelf 𝕜 K.ModelSpace) N K) :=
  sorry

end
