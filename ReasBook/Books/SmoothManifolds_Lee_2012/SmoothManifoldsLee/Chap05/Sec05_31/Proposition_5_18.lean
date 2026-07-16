import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uN uE'' uS

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was chosen from the local `Manifold.ImmersedSubmanifold` and
-- `IsImmersion.toImmersedSubmanifold` API in §5.31.
/-- Proposition 5.18 (1): an injective smooth immersion `F : N → M` determines an immersed
submanifold of `M` whose carrier is exactly `Set.range F`, and `F` identifies `N` diffeomorphically
with that immersed-submanifold image. -/
theorem injective_immersion_range_has_immersed_submanifold_structure {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F) :
    ∃ T : Manifold.ImmersedSubmanifold I M,
      T.carrier = Set.range F ∧
        ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 T.ModelSpace⟯ T,
          ∀ x : N, T.inclusion (Φ x) = F x := sorry

/-- Proposition 5.18 (2): if another smooth manifold `S` immerses injectively into `M` with the
same image as `F`, then `S` is diffeomorphic to `N` through the ambient maps. This expresses the
uniqueness of the topology and smooth structure on the image of `F` as an immersed submanifold. -/
theorem injective_immersion_range_immersed_submanifold_structure_unique {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F)
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {S : Type uS} [TopologicalSpace S] [ChartedSpace E'' S]
    [IsManifold (modelWithCornersSelf 𝕜 E'') (⊤ : WithTop ℕ∞) S]
    {ι : S → M}
    (hιinj : Function.Injective ι)
    (hι : IsImmersion (modelWithCornersSelf 𝕜 E'') I (⊤ : WithTop ℕ∞) ι)
    (hRange : Set.range ι = Set.range F) :
    ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 E''⟯ S,
      ∀ x : N, ι (Φ x) = F x := sorry

end
