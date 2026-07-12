import SmoothManifolds_Lee_2012.Chap08.Sec08_54.Lemma_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- `lean_leansearch` was unavailable in this session, so this proposition follows the local
-- Chapter 8 convention from `Lemma_8_6.lean`: unbundled vector fields are dependent functions
-- `X : ∀ x : M, TangentSpace I x`, with smoothness expressed by `ContMDiff ... (T% X)`.

universe uE uH uM

noncomputable section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I (∞ : ℕ∞ω) M] [T2Space M] [SigmaCompactSpace M]

/-- Proposition 8.7: given a point `p` of a smooth manifold `M` and a tangent vector
`v ∈ TangentSpace I p`, there exists a smooth global vector field on `M` whose value at `p`
is `v`. -/
theorem exists_contMDiff_vectorField_eq_at_point
    (p : M) (v : TangentSpace I p) :
    ∃ X : ∀ x : M, TangentSpace I x,
      ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X) ∧ X p = v := by
  let s : Set M := (extChartAt I p).source
  let w : E := (mfderiv% (extChartAt I p) p) v
  let W : ∀ z : E, TangentSpace 𝓘(ℝ, E) z := fun _ ↦ w
  let Xloc : ∀ x : M, TangentSpace I x :=
    VectorField.mpullbackWithin I 𝓘(ℝ, E) (extChartAt I p) W s
  have hpSource : p ∈ s := by
    simp [s]
  have hsOpen : IsOpen s := by
    simpa [s] using isOpen_extChartAt_source (I := I) p
  have hsUnique : UniqueMDiffOn I s := hsOpen.uniqueMDiffOn
  have hpSingleton : p ∈ ({p} : Set M) := by
    simp
  let pSingleton : ({p} : Set M) := ⟨p, hpSingleton⟩
  have hSingletonSubset : ({p} : Set M) ⊆ (Set.univ : Set M) := by
    exact Set.subset_univ _
  have hInfinityStep : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
    simp
  -- In chart coordinates, a constant vector field is smooth because it is constant as a map to `E`.
  have hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent (∞ : ℕ∞ω) (T% W) := by
    rw [contMDiff_vectorSpace_iff_contDiff]
    change ContDiff ℝ (∞ : ℕ∞ω) (fun _ : E ↦ w)
    simpa using contDiff_const
  -- Pull the constant chart-side field back to the preferred chart source around `p`.
  have hExtChart : ContMDiffOn I 𝓘(ℝ, E) (∞ : ℕ∞ω) (extChartAt I p) s := by
    simpa [s, extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := (∞ : ℕ∞ω)) (x := p))
  have hExtChartInvertible :
      ∀ x ∈ s ∩ (extChartAt I p) ⁻¹' (Set.univ : Set E),
        (mfderiv[s] (extChartAt I p) x).IsInvertible := by
    intro x hx
    have hxSource : x ∈ s := hx.1
    have hxChart : x ∈ (chartAt H p).source := by
      simpa [s, extChartAt_source] using hxSource
    have hmdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) x :=
      mdifferentiableAt_extChartAt (I := I) (x := p) hxChart
    have hEq :
        mfderiv[s] (extChartAt I p) x = mfderiv% (extChartAt I p) x := by
      exact mfderivWithin_eq_mfderiv (hsUnique x hxSource) hmdiff
    rw [hEq]
    exact isInvertible_mfderiv_extChartAt (I := I) (x := p) hxSource
  have hXloc : ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% Xloc) s := by
    have hWOn :
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent (∞ : ℕ∞ω) (T% W) Set.univ :=
      hW.contMDiffOn
    simpa [Xloc, Set.preimage_univ, Set.inter_univ] using
      (hWOn.mpullbackWithin_vectorField_inter (f := extChartAt I p) (s := s) (t := Set.univ)
        hExtChart hExtChartInvertible
        hsUnique hInfinityStep)
  -- At the base point, the pullback inverts the chart derivative and recovers the chosen vector.
  have hXlocAtPoint : Xloc p = v := by
    have hpChart : p ∈ (chartAt H p).source := by
      simp
    have hmdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
      mdifferentiableAt_extChartAt (I := I) (x := p) hpChart
    have hEq :
        mfderiv[s] (extChartAt I p) p = mfderiv% (extChartAt I p) p := by
      exact mfderivWithin_eq_mfderiv (hsUnique p hpSource) hmdiff
    have hInv : (mfderiv% (extChartAt I p) p).IsInvertible :=
      isInvertible_mfderiv_extChartAt (I := I) (x := p) hpSource
    let φ := extChartAt I p
    have hEqφ : mfderiv[s] φ p = mfderiv% φ p := by
      simpa [φ] using hEq
    have hInvφ : (mfderiv% φ p).IsInvertible := by
      simpa [φ] using hInv
    change (mfderiv[s] φ p).inverse ((mfderiv% φ p) v) = v
    rw [hEqφ]
    exact (hInvφ.inverse_apply_eq).2 rfl
  let Xsource : ∀ x : ({p} : Set M), TangentSpace I (x : M) := fun x ↦ Xloc x
  -- Package the chart pullback as the local extension datum required by Lemma 8.6 on `{p}`.
  have hLocal :
      ∀ x : ({p} : Set M), ContMDiffVectorFieldLocalExtension Xsource x := by
    intro x
    have hxEq : (x : M) = p := by
      exact Set.mem_singleton_iff.mp x.property
    have hxMem : (x : M) ∈ s := by
      simpa [hxEq] using hpSource
    have hEqSource : ∀ y : ({p} : Set M), (y : M) ∈ s → Xloc y = Xsource y := by
      intro y hy
      rfl
    exact
      { V := s
        isOpen_V := hsOpen
        mem_V := hxMem
        Xloc := Xloc
        contMDiffOn := hXloc
        eq_source := hEqSource }
  -- Globalize the singleton data by the extension lemma, taking `U = univ`.
  obtain ⟨X, hX⟩ :=
    exists_supported_contMDiff_vectorField_extension_of_isClosed
      (I := I) (A := ({p} : Set M)) (U := Set.univ)
      isClosed_singleton isOpen_univ hSingletonSubset Xsource hLocal
  have hXeq : X p = Xsource pSingleton := by
    simpa [pSingleton, Xsource] using hX.eq_source pSingleton
  refine ⟨X, hX.contMDiff, ?_⟩
  exact hXeq.trans hXlocAtPoint
