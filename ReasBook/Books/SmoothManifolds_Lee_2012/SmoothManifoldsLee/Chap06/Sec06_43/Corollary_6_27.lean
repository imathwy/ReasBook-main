import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Definition_2_11_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_43.Theorem_6_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * source-facing data: `Function.IsSmoothOn` for a map defined on a closed subset.
-- * core/canonical owner used here: `exists_homotopicRel_to_smooth_map_of_isClosed`.
-- * derived bridge in this corollary: a continuous extension agreeing with `f` is `ContMDiffOn`
--   along the closed subset by locality of smoothness.

universe uN uM

section

variable {n m : ℕ}
variable {N : Type uN} [TopologicalSpace N] [SmoothManifoldWithBoundary n N]
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold m M]
  [IsManifold (𝓡 m) ∞ M]

/-- Corollary 6.27 (Extension Lemma for Smooth Maps). Suppose `N` is a smooth manifold with or
without boundary, `M` is a smooth manifold, `A ⊆ N` is closed, and `f : A → M` is smooth. Then
`f` admits a smooth extension to `N` if and only if it admits a continuous extension to `N`. -/
theorem exists_smooth_extension_iff_exists_continuous_extension_of_isClosed
    {A : Set N} (hA : IsClosed A) (f : A → M)
    (hf : f.IsSmoothOn (leeBoundaryModelWithCorners n) (𝓡 m)) :
    (∃ F : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯, ∀ x : A, F x = f x) ↔
      ∃ F : C(N, M), ∀ x : A, F x = f x := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨(F : C(N, M)), hF⟩
  · rintro ⟨F, hF⟩
    have hFA : ContMDiffOn (leeBoundaryModelWithCorners n) (𝓡 m) ∞ F A := by
      rw [Function.isSmoothOn_iff_exists_local_extension] at hf
      refine contMDiffOn_of_locally_contMDiffOn ?_
      intro x hx
      rcases hf ⟨x, hx⟩ with ⟨U, hU_open, hxU, Fext, hFext, hFext_eq⟩
      refine ⟨U, hU_open, hxU, ?_⟩
      refine (hFext.mono fun _ hy ↦ hy.2).congr fun y hy ↦ ?_
      rw [hF ⟨y, hy.1⟩]
      symm
      exact hFext_eq ⟨y, hy.1⟩ hy.2
    rcases exists_homotopicRel_to_smooth_map_of_isClosed F hA hFA with ⟨G, hG⟩
    refine ⟨G, fun x ↦ ?_⟩
    calc
      G x = F x := by
        simpa using (ContinuousMap.HomotopicRel.fst_eq_snd hG x.2).symm
      _ = f x := hF x

end
