import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

/-- Proposition 2.25 (Existence of Smooth Bump Functions): for a closed subset `A` of a smooth
manifold and an open neighborhood `U` of `A`, there exists a smooth real-valued bump function for
`A` supported in `U`. -/
-- Proof sketch: apply the existence of a smooth partition of unity subordinate to the two-set open
-- cover `Fin 2 → Set M` given by `U` and `Aᶜ` on the closed set `A`, then take the `0`-th
-- summand. Subordination gives `tsupport` contained in `U`, the other summand vanishes on `A`,
-- and the partition-of-unity identity on `A` forces the chosen summand to equal `1` there.
theorem exists_smooth_bump_function_for
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {A U : Set M} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ ψ : C^∞⟮I, M; ℝ⟯,
      Set.range ψ ⊆ Set.Icc (0 : ℝ) 1 ∧ Set.EqOn ψ 1 A ∧ tsupport ψ ⊆ U := by
  let V : Bool → Set M
    | false => U
    | true => Aᶜ
  have hV_open : ∀ b, IsOpen (V b) := by
    intro b
    cases b
    · exact hU
    · exact hA.isOpen_compl
  have hV_cover : A ⊆ ⋃ b, V b := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨false, hAU hx⟩
  obtain ⟨ρ, hρV⟩ : ∃ ρ : SmoothPartitionOfUnity Bool I M A, ρ.IsSubordinate V :=
    SmoothPartitionOfUnity.exists_isSubordinate I hA V hV_open hV_cover
  refine ⟨ρ false, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨ρ.nonneg false x, ρ.le_one false x⟩
  · intro x hx
    have hρtrue_zero : ρ true x = 0 := by
      rw [← Function.notMem_support]
      intro hx_support
      have hx_tsupport : x ∈ tsupport (ρ true) :=
        subset_closure hx_support
      exact hρV true hx_tsupport hx
    have hsum : ∑ᶠ i : Bool, ρ i x = 1 := ρ.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype, Fintype.sum_bool] at hsum
    simpa [hρtrue_zero] using hsum
  · simpa [V] using hρV false
