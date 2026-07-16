import DifferentialForms_Cartan_1970.cartan.II.section05.«0036_Corollary_II_1_extra_23».ClosedPathTransportBasics
import DifferentialForms_Cartan_1970.cartan.II.section05.«0036_Corollary_II_1_extra_23».ConnectedOpenContourReductions

open scoped BigOperators unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a closed-path homotopy from `γ` to
a constant loop already kills the contour integral of `γ` for a closed form, even without a
separate curve-integrability witness. -/
theorem curveIntegral_eq_zero_of_closedPathHomotopicIn_const_withoutIntegrability
    {C : Set ℂ} {z0 x : ℂ} {γ : Path z0 z0} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hhom : ClosedPathHomotopicIn C γ (Path.refl x))
    (hγ_piece : γ.IsPiecewiseDifferentiable) (hxC : x ∈ C)
    (hω : IsClosedOn ω C) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  -- Convert the comparison homotopy to a null-homotopy, then apply the existing no-integrability
  -- vanishing theorem for closed forms.
  have hγ_null : IsNullHomotopicClosedPathIn C γ :=
    isNullHomotopicClosedPathIn_of_closedPathHomotopicIn_const hhom hxC
  exact
    curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain_without_integrability
      hγ_null hγ_piece hω

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-open contour sum
is already known to vanish, the full comparison package is the formal empty-stage construction with
constant loops. -/
theorem
    IsOrientedBoundaryOf.existsSingleConnectorErrorStageComparisonInConnectedOpen_of_sumZero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ z0 : ℂ, ∃ γ : Path z0 z0,
      ∃ N : ℕ → ℕ, ∃ z w : ∀ n, Fin (N n) → ℂ,
        ∃ γStage : ∀ n, Path z0 z0,
          γ.IsPiecewiseDifferentiable ∧
          Set.range γ ⊆ C ∧
          CurveIntegrable ω γ ∧
          ((∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ) ∧
          (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) ∧
          (∀ n, (γStage n).IsPiecewiseDifferentiable) ∧
          (∀ n, Set.range (γStage n) ⊆ C) ∧
          (∀ n, CurveIntegrable ω (γStage n)) ∧
          (∀ n,
            ∫ᶜ ζ in γStage n, ω ζ =
              ∑ s : Fin (N n),
                ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) ∧
          (∀ n, IsNullHomotopicClosedPathIn C (γ.trans (γStage n).symm)) := by
  obtain ⟨z0, hz0C⟩ := hC_connected.nonempty
  let γ : Path z0 z0 := Path.refl z0
  let N : ℕ → ℕ := fun _ ↦ 0
  let z : ∀ n : ℕ, Fin (N n) → ℂ := fun _ s ↦ nomatch s
  let w : ∀ n : ℕ, Fin (N n) → ℂ := fun _ s ↦ nomatch s
  let γStage : ∀ n : ℕ, Path z0 z0 := fun _ ↦ Path.refl z0
  refine ⟨z0, γ, N, z, w, γStage, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The comparison loop is constant in the zero-sum formal package.
    simpa [γ] using (Path.isPiecewiseDifferentiable_refl z0)
  · -- A constant loop based at `z0 ∈ C` stays in the ambient domain.
    intro ζ hζ
    rcases hζ with ⟨t, ht⟩
    simpa [γ] using ht ▸ hz0C
  · -- Constant loops are curve-integrable for every form.
    simpa [γ] using (CurveIntegrable.refl ω z0)
  · -- The boundary contour sum is identified with the constant loop integral `0`.
    simpa [γ] using hsumZero
  · -- Empty rectangle stages impose no geometric side conditions.
    intro n s
    nomatch s
  · -- Each stage comparison loop is also constant.
    intro n
    simpa [γStage] using (Path.isPiecewiseDifferentiable_refl z0)
  · -- So every stage loop stays in `C`.
    intro n ζ hζ
    rcases hζ with ⟨t, ht⟩
    simpa [γStage] using ht ▸ hz0C
  · -- And every stage loop is curve-integrable.
    intro n
    simpa [γStage] using (CurveIntegrable.refl ω z0)
  · -- The stage contour identity is vacuous because every stage family is empty.
    intro n
    simp [γStage, N, z, w]
  · intro n
    have hconst : IsNullHomotopicClosedPathIn C (Path.refl z0) :=
      isNullHomotopicClosedPathIn_const (D := C) hz0C
    -- The difference between the two constant loops is again the same constant loop.
    simpa [γ, γStage, Path.refl_trans_refl] using hconst

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the exact rooted loop attached to a
connector family already comes with its basepoint in `C` and with the standard topology package in
that exact spelling. -/
theorem rootedBoundaryLoopData_of_orientedBoundaryConnectorFamily
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C) :
    let z0 : ℂ := (Γ i0).toPath 0
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    z0 ∈ C ∧ γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
  let z0 : ℂ := (Γ i0).toPath 0
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  have hz0C : z0 ∈ C := by
    -- The rooted-loop basepoint is one boundary basepoint, hence already lies in the ambient set.
    simpa [z0] using boundaryPath_basepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  have hγ_top :
      γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
    -- Reuse the existing topology package for the exact rooted loop fixed by this connector
    -- family.
    simpa [z0, γ] using
      rootedBoundaryLoopTopology_of_orientedBoundaryConnectorFamily
        (Γ := Γ) hΓ hKC hρ_piece hρC
  exact ⟨hz0C, hγ_top.1, hγ_top.2⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected open ambient set one
can freeze a single connector family together with the exact rooted boundary loop data used later
in the scalar-vanishing reduction. -/
theorem connectedOpenRootedBoundaryLoopData
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C) :
    ∃ i0 : ι, ∃ ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
      (∀ i, (ρ i).IsPiecewiseDifferentiable) ∧
      (∀ i t, ρ i t ∈ C) ∧
      let z0 : ℂ := (Γ i0).toPath 0
      let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
      z0 ∈ C ∧ γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρC⟩ :=
    hΓ.existsConnectorFamilyInConnectedOpen hKC hC_open hC_connected
  -- Freeze the connector family once so later proofs can keep the exact rooted-loop spelling.
  refine ⟨i0, ρ, hρ_piece, hρC, ?_⟩
  simpa using
    rootedBoundaryLoopData_of_orientedBoundaryConnectorFamily
      (Γ := Γ) hΓ hKC hρ_piece hρC

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the same connected-open rooted loop
also carries a primitive along that exact loop under the closed-form hypothesis. -/
theorem connectedOpenRootedBoundaryLoopPrimitiveData_of_isClosedOn
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C) :
    ∃ i0 : ι, ∃ ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
      (∀ i, (ρ i).IsPiecewiseDifferentiable) ∧
      (∀ i t, ρ i t ∈ C) ∧
      let z0 : ℂ := (Γ i0).toPath 0
      let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
      z0 ∈ C ∧ γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C ∧
        ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C γ f := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρC⟩ :=
    hΓ.existsConnectorFamilyInConnectedOpen hKC hC_open hC_connected
  -- Reuse the exact rooted-loop primitive package for the chosen connector family.
  refine ⟨i0, ρ, hρ_piece, hρC, ?_⟩
  have hrooted :
      let z0 : ℂ := (Γ i0).toPath 0
      let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
      z0 ∈ C ∧ γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
    simpa using
      rootedBoundaryLoopData_of_orientedBoundaryConnectorFamily
        (Γ := Γ) hΓ hKC hρ_piece hρC
  have hprimitive :
      let z0 : ℂ := (Γ i0).toPath 0
      let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
      ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C γ f := by
    simpa using
      rootedBoundaryLoop_existsPrimitiveAlongPath_of_isClosedOn
        (Γ := Γ) hΓ hKC hω hρ_piece hρC
  exact ⟨hrooted.1, hrooted.2.1, hrooted.2.2, hprimitive⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the live comparison theorem
has been reduced to a single stage, the stage side can always be packaged as one rooted loop with
an exact finite rectangle-sum identity. -/
theorem rootedRectangleSingleStageLoopDataInConnectedOpen_of_pathwiseCurveIntegrable
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ} {z0 : ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hz0C : z0 ∈ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ) :
    ∃ N : ℕ, ∃ z : Fin N → ℂ, ∃ w : Fin N → ℂ, ∃ γStage : Path z0 z0,
      (∀ s, Complex.Rectangle (z s) (w s) ⊆ interior K) ∧
      γStage.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γStage ∧
      (∫ᶜ ζ in γStage, ω ζ =
        ∑ s : Fin N, ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z s) (w s), ω ζ) := by
  -- The single-stage normal form admits the empty rectangle stage and the constant rooted loop.
  refine ⟨0, (fun s ↦ Fin.elim0 s), (fun s ↦ Fin.elim0 s), Path.refl z0, ?_, ?_, ?_, ?_⟩
  · intro s
    exact Fin.elim0 s
  · simpa using Path.isPiecewiseDifferentiable_refl z0
  · simpa using (CurveIntegrable.refl ω z0)
  · simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once one connected-open connector
family is frozen, the remaining owner-level input is the scalar vanishing statement for the exact
rooted boundary loop attached to that connector family. -/
theorem frozenRootedBoundaryLoopIntegral_eq_boundarySum_of_pathwiseCurveIntegrable
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C)
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ) :
    let z0 : ℂ := (Γ i0).toPath 0
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  -- Specialize the earlier rooted-loop contour comparison theorem to the frozen connector family.
  simpa using
    explicitRootedBoundaryLoopIntegral_eq_boundarySum_of_pathwiseCurveIntegrable
      (Γ := Γ) hΓ hKC hρ_piece hρC hpath_int

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the frozen rooted loop admits
the exact analytic bridge and is null-homotopic in `C`, the total oriented-boundary contour sum
vanishes immediately. -/
theorem connectedAmbient_sum_curveIntegral_eq_zero_of_frozenRootedBoundaryLoopBridges
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C)
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ)
    (hγ_null :
      let z0 : ℂ := (Γ i0).toPath 0
      let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
      IsNullHomotopicClosedPathIn C γ) :
    let z0 : ℂ := (Γ i0).toPath 0
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  -- Keep the scalar-zero consumer in the exact frozen spelling used by the remaining owner
  -- theorem, so the only live blocker is the bridge package itself.
  simpa using
    connectedAmbient_sum_curveIntegral_eq_zero_of_nullHomotopicRootedBoundaryLoop
      (Γ := Γ) hΓ hKC hω hρ_piece hρC hpath_int hγ_null
