import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_6
import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Theorem_5_12
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Theorem_5_53
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Definition_7_46_extra_3
import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Proposition_7_11
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold

universe u𝕜 uEG uHG uG uEH uHH uH uS

-- Domain sampling pass:
-- * primary domain: kernels of smooth and continuous group homomorphisms;
-- * source-facing layer: the Lie-subgroup structure on `F.ker` and the proper embedding of the
--   kernel subset of a Lie-group homomorphism;
-- * core/canonical owners: `ContMDiffMonoidMorphism` for smooth homomorphisms,
--   `ContinuousMonoidHom` for the closure/proper-embedding companion, and
--   `Set.IsProperlyEmbedded` for the ambient topological property;
-- * primitive data: a smooth or continuous homomorphism together with its canonical subgroup
--   kernel;
-- * derived API: the existential Lie-subgroup structure in part (1) and the proper-embedding
--   statement in part (2).
-- Semantic recall via `lean_leansearch` did not return a useful manifold-specific kernel theorem;
-- the source-facing owner is fixed by local §7.49 precedent: Proposition 7.11 packages embedded
-- subgroups as `LieSubgroup I`.

section KernelProperEmbedding

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable [T1Space H]

namespace ContinuousMonoidHom

/-- Companion theorem for Proposition 7.16 (2): the kernel of a continuous group homomorphism is
properly embedded. -/
theorem ker_isProperlyEmbedded (F : G →ₜ* H) :
    Set.IsProperlyEmbedded (F.ker : Set G) := by
  have hker : (F.ker : Set G) = F ⁻¹' ({(1 : H)} : Set H) := by
    ext g
    rfl
  simpa [hker] using
    (IsClosed.isProperlyEmbedded <| isClosed_singleton.preimage F.continuous_toFun)

end ContinuousMonoidHom

end KernelProperEmbedding

section LieGroupKernel

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

namespace ContMDiffMonoidMorphism

/-- Helper for Proposition 7.16: an embedded subgroup of a Lie group inherits a Lie-group
structure from the ambient multiplication and inversion maps. -/
theorem subgroupLieGroupOfIsEmbeddedSubmanifold
    {E' : Type uS} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (S : Subgroup G) [ChartedSpace E' S]
    [IsManifold (modelWithCornersSelf 𝕜 E') ∞ S]
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') (S : Set G)) :
    LieGroup (modelWithCornersSelf 𝕜 E') ∞ S := by
  -- This is the `C^∞` Lie-group structure supplied by Proposition 7.11 in the embedded-subgroup
  -- situation; no stronger `ω`-level regularity is part of the source statement here.
  sorry

/-- Helper for Proposition 7.16: the subgroup carrier of `F.ker` is exactly the level set
`F ⁻¹' {1}`. -/
lemma ker_coeSet_eq_preimage_one (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (F.ker : Set G) = F ⁻¹' ({(1 : H)} : Set H) := by
  -- Kernel membership is definitionally the equation `F g = 1`.
  ext g
  rfl

/-- Helper for Proposition 7.16: a smooth Lie-group homomorphism has the same manifold rank at
every point as it has at the identity. -/
theorem rankAt_eq_rankAt_one
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    rankAt I J F g = rankAt I J F (1 : G) := by
  -- TODO: reuse Theorem 7.5 once that upstream file compiles again in this workspace.
  sorry

/-- Helper for Proposition 7.16: every smooth Lie-group homomorphism has constant rank, equal to
its rank at the identity. -/
theorem hasConstantRank
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    HasConstantRank I J F (rankAt I J F (1 : G)) := by
  -- Constant rank is smoothness together with the pointwise identity-rank formula.
  refine ⟨?_, ?_⟩
  · simpa using F.contMDiff_toFun.mdifferentiable (by simp)
  · intro g
    exact rankAt_eq_rankAt_one F g

/-- Helper for Proposition 7.16: the constant-rank level-set theorem gives embedded-submanifold
data on the kernel subset of a smooth Lie-group homomorphism. -/
lemma ker_has_embeddedSubmanifold_data
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.ker : Set G),
        ∃ hs : IsManifold K ∞ (F.ker : Set G),
          let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.ker : Set G) := cs
          let _ : IsManifold K ∞ (F.ker : Set G) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K (F.ker : Set G),
            hEmb.codimension = rankAt I J F (1 : G) := by
  -- Reinterpret the kernel as the fiber over the identity and transport the Chapter 5 structure.
  simpa [ker_coeSet_eq_preimage_one] using
    (constant_rank_level_set_has_embedded_submanifold_structure
      F.contMDiff_toFun F.hasConstantRank (1 : H))

/-- Proposition 7.16: if `F : G → H` is a smooth Lie group homomorphism, then its kernel is a
properly embedded Lie subgroup of `G`, and its codimension is the rank of `F` at the identity.
The main theorem records the source-facing Lie-subgroup conclusion; the companion theorems
`ker_isProperlyEmbedded` and `ker_codimension_eq_rank` expose the proper-embedding and
codimension conclusions separately. -/
theorem ker_has_embedded_lieSubgroup_structure
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    ∃ K : LieSubgroup I, K.carrier = F.ker := sorry

/-- Companion theorem for Proposition 7.16: the kernel submanifold has codimension equal to the
rank of `F` at the identity. -/
theorem ker_codimension_eq_rank
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.ker : Set G),
      ∃ hs : IsManifold K ∞ (F.ker : Set G),
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.ker : Set G) := cs
        let _ : IsManifold K ∞ (F.ker : Set G) := hs
        ∃ hEmb : IsEmbeddedSubmanifold I K (F.ker : Set G),
          hEmb.codimension = rankAt I J F (1 : G) := sorry

end ContMDiffMonoidMorphism

end LieGroupKernel

section SmoothKernelProperEmbedding

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [T1Space H]

namespace ContMDiffMonoidMorphism

/-- Companion theorem: the kernel of a smooth Lie group homomorphism is properly embedded in the
ambient Lie group. -/
theorem ker_isProperlyEmbedded (F : ContMDiffMonoidMorphism I J ∞ G H) :
    Set.IsProperlyEmbedded (F.ker : Set G) := by
  simpa using
    (ContinuousMonoidHom.ker_isProperlyEmbedded (F : G →ₜ* H))

end ContMDiffMonoidMorphism

end SmoothKernelProperEmbedding
