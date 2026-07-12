import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH'

section UniquenessOfSubmanifoldStructures

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J (⊤ : WithTop ℕ∞) S]
variable [IsEmbeddedSubmanifold I J S]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was chosen from the local `IsEmbeddedSubmanifold` / `ImmersedSubmanifold` API in Chapter 5.
-- Proof sketch: use Corollary 5.30 to view the alternative inclusion as a smooth map
-- `S̃ → S`, check from injectivity of the ambient differential that this map is an immersion, and
-- then apply the global rank theorem to obtain a diffeomorphism.
/-- Theorem 5.31: if `S ⊆ M` already carries the canonical embedded-submanifold structure, then any
immersed submanifold structure on the same underlying subset is diffeomorphic to `S` through the
ambient inclusion map. Consequently the subspace topology and the smooth structure from Theorem
5.8 are unique among topology and smooth-structure choices making `S` an immersed submanifold. -/
theorem immersed_submanifold_structure_unique_of_same_carrier
    (T : Manifold.ImmersedSubmanifold I M) (hT : T.carrier = S) :
    ∃ Φ : T ≃ₘ⟮modelWithCornersSelf 𝕜 T.ModelSpace, J⟯ S,
      ∀ x : T, (Φ x : M) = T.inclusion x := sorry

end UniquenessOfSubmanifoldStructures
