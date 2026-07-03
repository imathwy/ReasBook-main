import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_4_6 (from Chap04/Sec04_27) -/
open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [Nonempty M]

/-- Problem 4-6: a nonempty compact smooth manifold admits no smooth submersion to `ℝ^k` for any
positive integer `k`. -/
-- Proof sketch: pointwise surjectivity of the manifold derivative gives the local projection form
-- for `F`, hence `F` is an open map. Therefore `Set.range F` is a nonempty open subset of
-- `EuclideanSpace ℝ (Fin k)`. Since `M` is compact and `F` is continuous, this range is also
-- compact. For `k > 0`, a nonempty open subset of `ℝ^k` cannot be compact, giving a
-- contradiction.
theorem not_exists_smooth_submersion_to_euclideanSpace {k : ℕ} (hk : 0 < k) :
    ¬ ∃ F : M → EuclideanSpace ℝ (Fin k),
      Manifold.IsSmoothSubmersion I (𝓡 k) F := by
  rintro ⟨F, hF⟩
  have hopen : IsOpen (Set.range F) := hF.isOpenMap.isOpen_range
  have hcompact : IsCompact (Set.range F) := isCompact_range hF.contMDiff.continuous
  have hnonempty : (Set.range F).Nonempty := by
    rcases ‹Nonempty M› with ⟨x⟩
    exact ⟨F x, ⟨x, rfl⟩⟩
  have hrange : Set.range F = Set.univ :=
    IsClopen.eq_univ ⟨hcompact.isClosed, hopen⟩ hnonempty
  have hcompact_target : IsCompact (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    simpa [hrange] using hcompact
  let i : Fin k := ⟨0, hk⟩
  have hcompact_coord : IsCompact (Set.range fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp i) := by
    simpa [Set.image_univ] using hcompact_target.image (EuclideanSpace.proj i).continuous
  have hcoord_surj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp i) := by
    intro t
    refine ⟨EuclideanSpace.single i t, ?_⟩
    simp
  have hcompact_real : IsCompact (Set.univ : Set ℝ) := by
    simpa [hcoord_surj.range_eq] using hcompact_coord
  exact
    (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ))
      (isCompact_univ_iff.mp hcompact_real)

/-! ### Proposition_4_6 (from Chap04/Sec04_22) -/
noncomputable section

open scoped Manifold

section Composition

universe u𝕜 uE uF uG uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {H'' : Type uH''} [TopologicalSpace H'']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  {K : ModelWithCorners 𝕜 G H''}
  {n : WithTop ℕ∞} {f : M → N} {g : N → P}

-- Proof sketch: choose local partial diffeomorphisms for `f` and `g` at each point and compose
-- them to obtain a local partial diffeomorphism for `g ∘ f`.
/-- Proposition 4.6 (1): part (a), the composition of two local diffeomorphisms is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_comp (hg : IsLocalDiffeomorph J K n g)
    (hf : IsLocalDiffeomorph I J n f) : IsLocalDiffeomorph I K n (g ∘ f) := sorry

end Composition

section FiniteProducts

universe u𝕜 uι uE uF uH uG uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {ι : Type uι} [Fintype ι]
  {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {F : ι → Type uF} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  {H : ι → Type uH} [∀ i, TopologicalSpace (H i)]
  {G : ι → Type uG} [∀ i, TopologicalSpace (G i)]
  {M : ι → Type uM} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  {N : ι → Type uN} [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (G i) (N i)]
  {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {J : ∀ i, ModelWithCorners 𝕜 (F i) (G i)}
  {n : WithTop ℕ∞} {f : ∀ i, M i → N i}

-- Proof sketch: prove the statement pointwise using the local product charts on finite products of
-- manifolds and the coordinatewise product of the local inverses.
/-- Proposition 4.6 (2): part (b), a finite product of local diffeomorphisms is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_pi (hf : ∀ i, IsLocalDiffeomorph (I i) (J i) n (f i)) :
    IsLocalDiffeomorph (ModelWithCorners.pi I) (ModelWithCorners.pi J) n
      (fun x : ∀ i, M i ↦ fun i ↦ f i (x i)) := sorry

end FiniteProducts

/- Proposition 4.6 (3): part (c), every local diffeomorphism is a local homeomorphism. -/
#check IsLocalDiffeomorph.isLocalHomeomorph

/- Proposition 4.6 (4): part (c), every local diffeomorphism is an open map. -/
#check IsLocalDiffeomorph.isOpenMap

/- Proposition 4.6 (5): part (d), the restriction of a local diffeomorphism to an open
submanifold is encoded by the canonical owner-level restriction statement
`IsLocalDiffeomorph.isLocalDiffeomorphOn`. -/
#check IsLocalDiffeomorph.isLocalDiffeomorphOn

/- Proposition 4.6 (6): part (e), every diffeomorphism is a local diffeomorphism. -/
#check Diffeomorph.isLocalDiffeomorph

/- Proposition 4.6 (7): part (f), a bijective local diffeomorphism canonically upgrades to a
diffeomorphism. -/
#check IsLocalDiffeomorph.diffeomorphOfBijective

section Coordinates

universe u𝕜 uE uF uH uG uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type uH} [TopologicalSpace H]
  {G : Type uG} [TopologicalSpace G]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {n : WithTop ℕ∞} {f : M → N}

-- Proof sketch: transport the local diffeomorphism data to the preferred extended charts and use
-- compatibility of local diffeomorphisms with chart changes in both directions.
/-- Proposition 4.6 (3): part (g), a map is a local diffeomorphism exactly when each preferred
coordinate representative is a local diffeomorphism at the corresponding chart point. -/
theorem isLocalDiffeomorph_iff_writtenInExtChartAt :
    IsLocalDiffeomorph I J n f ↔
      ∀ x : M,
        IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, F) n
          (writtenInExtChartAt I J x f) (extChartAt I x x) := sorry

end Coordinates
