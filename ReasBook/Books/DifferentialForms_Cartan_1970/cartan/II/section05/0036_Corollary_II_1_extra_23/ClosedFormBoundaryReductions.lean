import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.II.section05.«0018_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0019_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».BoundaryComponentGeometry
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».RectangleStageReduction
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».RootedBoundaryLoops

open scoped BigOperators unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: closedness restricts from an ambient
domain `D` to any open subset `C ⊆ D`. -/
theorem IsClosedOn.restrictOpen
    {D C : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D)
    (hC_open : IsOpen C) (hCD : C ⊆ D) :
    IsClosedOn ω C := by
  intro z hzC
  rcases hω z (hCD hzC) with ⟨U, hU_open, hzU, hUD, hU_primitive⟩
  -- Intersect the old primitive neighborhood with the open subset `C`.
  refine ⟨U ∩ C, hU_open.inter hC_open, ⟨hzU, hzC⟩, ?_, ?_⟩
  · -- The intersected neighborhood now lies in `C` by construction.
    intro w hw
    exact hw.2
  · -- The same primitive restricts to the smaller neighborhood.
    exact hU_primitive.mono Set.inter_subset_left

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if one boundary component of an
oriented boundary family is viewed inside an ambient domain `D`, its base point already lies in
`D`. -/
theorem boundaryPath_basepoint_mem_domain_of_orientedBoundary
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (i : ι) :
    (Γ i).toPath 0 ∈ D := by
  -- Specialize the global range inclusion to the initial parameter value of the boundary path.
  exact range_toPath_subset_domain_of_orientedBoundary hΓ hKD i ⟨0, by simp⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once `D` is open, closedness of `ω`
restricts to every connected component of `D`. -/
theorem IsClosedOn.restrictConnectedComponent
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D)
    (hD_open : IsOpen D) {z : ℂ} :
    IsClosedOn ω (connectedComponentIn D z) := by
  -- A connected component is an open subset of `D`, so the generic restriction lemma applies.
  exact hω.restrictOpen (hD_open.connectedComponentIn) (connectedComponentIn_subset D z)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: closedness on the ambient domain
restricts to any boundary component selected by the connected-component key. -/
theorem IsClosedOn.restrictBoundaryComponent
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsClosedOn ω C := by
  -- Unpack the chosen boundary component as one connected component of `D`, then restrict the
  -- ambient closedness statement to that connected component.
  rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
  simpa using hω.restrictConnectedComponent hD_open (z := (Γ i).toPath 0)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-case contour sum
is known to vanish, the constant loop at one boundary basepoint already supplies the required
null-homotopic witness in `C`. -/
theorem exists_nullHomotopicBoundaryLoop_with_same_integral_of_sum_eq_zero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ z : ℂ, ∃ γ : Path z z,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      IsNullHomotopicClosedPathIn C γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  let z0 : ℂ := (Γ i0).toPath 0
  have hz0C : z0 ∈ C := by
    -- Use one boundary component basepoint to anchor the constant loop witness inside `C`.
    simpa [z0] using boundaryPath_basepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  refine ⟨z0, Path.refl z0, Path.isPiecewiseDifferentiable_refl z0,
    CurveIntegrable.refl ω z0, ?_, ?_⟩
  · -- A constant loop at a point of `C` is null-homotopic in `C`.
    exact isNullHomotopicClosedPathIn_const (D := C) hz0C
  · -- After the connected-case contour sum is zero, the constant loop has the same integral.
    simp [hsumZero]

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: on a connected open set, a
continuous form lets one compress the oriented-boundary contour sum to one rooted loop in the same
domain. -/
theorem
    IsOrientedBoundaryOf.existsRootedBoundaryLoopWithSameIntegralConnectedOpen_of_continuousOn
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω_cont : ContinuousOn ω C) :
    ∃ z0 : ℂ, ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C ∧
      CurveIntegrable ω γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρC⟩ :=
    hΓ.existsConnectorFamilyInConnectedOpen hKC hC_open hC_connected
  let z0 : ℂ := (Γ i0).toPath 0
  have hz0C : z0 ∈ C := by
    -- The common rooted-loop basepoint is one boundary-loop basepoint, hence lies in `C`.
    simpa [z0] using boundaryPath_basepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  have hΓ_piece : ∀ i, ((Γ i).toPath).IsPiecewiseDifferentiable := by
    -- Each boundary path already carries the piecewise differentiability stored in `hΓ`.
    intro i
    simpa using hΓ.piecewiseDifferentiable i
  have hΓC : ∀ i, Set.range ((Γ i).toPath) ⊆ C := by
    -- Every boundary component stays in `C` because `K ⊆ C`.
    intro i
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i
  have hρ_int : ∀ i, CurveIntegrable ω (ρ i) := by
    -- Continuity on `C` makes each connector path integrable once we know it stays in `C`.
    intro i
    refine Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn hω_cont (hρ_piece i) ?_
    rintro z ⟨t, rfl⟩
    exact hρC i t
  have hΓ_int : ∀ i, CurveIntegrable ω ((Γ i).toPath) := by
    -- The same continuity-on-domain argument applies to the boundary loops themselves.
    intro i
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hω_cont (hΓ_piece i) (hΓC i)
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  rcases
    rootedBoundaryLoop_spec
      (C := C) (ω := ω) (s := Finset.univ) Γ ρ hz0C
      (fun i _ ↦ hρ_piece i)
      (fun i _ ↦ hΓ_piece i)
      (fun i _ ↦ by
        rintro z ⟨t, rfl⟩
        exact hρC i t)
      (fun i _ ↦ hΓC i)
      (fun i _ ↦ hρ_int i)
      (fun i _ ↦ hΓ_int i) with
    ⟨hγ_piece, hγC, hγ_int, hγ_eq⟩
  exact ⟨z0, γ, hγ_piece, hγC, hγ_int, by simpa [γ] using hγ_eq.symm⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected open set, an
explicit pathwise curve-integrability hypothesis is already enough to compress the whole
oriented-boundary contour sum to one rooted loop in the ambient domain. -/
theorem
    IsOrientedBoundaryOf.existsRootedBoundaryLoopWithSameIntegralConnectedOpen_of_pathwiseCurveIntegrable
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ) :
    ∃ z0 : ℂ, ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C ∧
      CurveIntegrable ω γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρC⟩ :=
    hΓ.existsConnectorFamilyInConnectedOpen hKC hC_open hC_connected
  let z0 : ℂ := (Γ i0).toPath 0
  have hz0C : z0 ∈ C := by
    -- The chosen rooted-loop basepoint is one boundary-loop basepoint, so it already lies in `C`.
    simpa [z0] using boundaryPath_basepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  have hΓ_piece : ∀ i, ((Γ i).toPath).IsPiecewiseDifferentiable := by
    -- Each boundary component inherits the piecewise differentiability recorded in `hΓ`.
    intro i
    simpa using hΓ.piecewiseDifferentiable i
  have hΓC : ∀ i, Set.range ((Γ i).toPath) ⊆ C := by
    -- The oriented-boundary family already stays in `K ⊆ C`.
    intro i
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i
  have hρ_int : ∀ i, CurveIntegrable ω (ρ i) := by
    -- The pathwise hypothesis applies directly to each connector path in the chosen family.
    intro i
    refine hpath_int (hρ_piece i) ?_
    rintro z ⟨t, rfl⟩
    exact hρC i t
  have hΓ_int : ∀ i, CurveIntegrable ω ((Γ i).toPath) := by
    -- The same pathwise hypothesis applies to the boundary paths because they stay in `C`.
    intro i
    exact hpath_int (hΓ_piece i) (hΓC i)
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  rcases
    rootedBoundaryLoop_spec
      (C := C) (ω := ω) (s := Finset.univ) Γ ρ hz0C
      (fun i _ ↦ hρ_piece i)
      (fun i _ ↦ hΓ_piece i)
      (fun i _ ↦ by
        rintro z ⟨t, rfl⟩
        exact hρC i t)
      (fun i _ ↦ hΓC i)
      (fun i _ ↦ hρ_int i)
      (fun i _ ↦ hΓ_int i) with
    ⟨hγ_piece, hγC, hγ_int, hγ_eq⟩
  exact ⟨z0, γ, hγ_piece, hγC, hγ_int, by simpa [γ] using hγ_eq.symm⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: when the boundary index type is
empty but the ambient set `C` is connected, a constant loop in `C` already gives the required
null-homotopic witness. -/
theorem existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_of_isEmpty
    {ι : Type u} [Fintype ι] [IsEmpty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ) (_hKC : K ⊆ C)
    (_hC_open : IsOpen C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} :
    ∃ z : ℂ, ∃ γ : Path z z,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      IsNullHomotopicClosedPathIn C γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  obtain ⟨z, hzC⟩ := hC_connected.nonempty
  refine ⟨z, Path.refl z, Path.isPiecewiseDifferentiable_refl z, CurveIntegrable.refl ω z, ?_, ?_⟩
  · -- A constant loop based at a point of `C` is null-homotopic in `C`.
    exact isNullHomotopicClosedPathIn_const (D := C) hzC
  · -- With no boundary components, both contour integrals are definitionally zero.
    simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in the nonempty case, producing one
null-homotopic witness loop in `C` is equivalent to proving that the oriented-boundary contour sum
already vanishes. -/
theorem
    existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_iff_sumZero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C) :
    (∃ z : ℂ, ∃ γ : Path z z,
        γ.IsPiecewiseDifferentiable ∧
        CurveIntegrable ω γ ∧
        IsNullHomotopicClosedPathIn C γ ∧
        (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ) ↔
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  constructor
  · rintro ⟨z, γ, hγ_piece, hγ_integrable, hγ_null, hsum⟩
    -- Collapse the witness loop integral using the closed-form null-homotopy theorem.
    calc
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := hsum
      _ = 0 := by
        exact
          curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain
            hγ_null hγ_piece hγ_integrable hω
  · intro hsumZero
    -- Once the contour sum is already zero, the constant-loop package supplies the witness.
    exact
      exists_nullHomotopicBoundaryLoop_with_same_integral_of_sum_eq_zero
        (hΓ := hΓ) hKC hsumZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once one connected-open connector
family is fixed, the canonical rooted loop should carry the same contour integral as the original
boundary sum for a closed form on `C`. -/
theorem rootedBoundaryLoopTopology_of_orientedBoundaryConnectorFamily
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C) :
    let z0 : ℂ := (Γ i0).toPath 0
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
  let z0 : ℂ := (Γ i0).toPath 0
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  have hz0C : z0 ∈ C := by
    -- The rooted-loop basepoint is one boundary-loop basepoint, so it lies in `C`.
    simpa [z0] using boundaryPath_basepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  have hΓ_piece : ∀ i ∈ (Finset.univ : Finset ι), ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    -- The oriented-boundary package already records piecewise differentiability of each loop.
    simpa using hΓ.piecewiseDifferentiable i
  have hΓC : ∀ i ∈ (Finset.univ : Finset ι), Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    -- Every boundary component lies in `C` because `K ⊆ C`.
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i
  -- Reuse the topology-only rooted-loop package before adding analytic or homotopy data.
  simpa [z0, γ] using
    rootedBoundaryLoop_topology
      (C := C) (s := Finset.univ) Γ ρ hz0C
      (fun i _ ↦ hρ_piece i)
      hΓ_piece
      (fun i _ ↦ by
        rintro z ⟨t, rfl⟩
        exact hρC i t)
      hΓC

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the remaining analytic blocker is a
pathwise `CurveIntegrable` bridge for the concrete connector family and boundary loops under the
closed-form hypothesis. -/
theorem rootedBoundaryLoopIntegrablePieces_of_pathwiseCurveIntegrable
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C)
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ) :
    (∀ i, CurveIntegrable ω (ρ i)) ∧
      (∀ i, CurveIntegrable ω ((Γ i).toPath)) := by
  constructor
  · -- The abstract pathwise bridge closes the connector family immediately.
    intro i
    refine hpath_int (hρ_piece i) ?_
    rintro z ⟨t, rfl⟩
    exact hρC i t
  · -- The same bridge applies to every boundary path because the boundary stays in `C`.
    intro i
    refine hpath_int ?_ ?_
    · simpa using hΓ.piecewiseDifferentiable i
    · exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: closedness on `C` already provides
primitive witnesses along every connector path and every boundary path in the rooted-loop package.
-/
theorem rootedBoundaryLoopPrimitivePieces_of_isClosedOn
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρC : ∀ i t, ρ i t ∈ C) :
    (∀ i, ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C (ρ i) f) ∧
      (∀ i, ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C ((Γ i).toPath) f) := by
  constructor
  · intro i
    -- Each connector path stays in `C`, so closedness provides a primitive along that path.
    exact
      hω.existsPrimitiveAlongPath_of_path_in_domain (by
        rintro z ⟨t, rfl⟩
        exact hρC i t)
  · intro i
    -- Each boundary path also stays in `C` because the oriented boundary lies in `K ⊆ C`.
    exact
      hω.existsPrimitiveAlongPath_of_path_in_domain
        (range_toPath_subset_domain_of_orientedBoundary hΓ hKC i)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: null-homotopy transports across a
closed-path homotopy inside the same ambient domain. -/
theorem isNullHomotopicClosedPathIn_of_closedPathHomotopicIn
    {C : Set ℂ} {z0 z1 : ℂ} {γ0 : Path z0 z0} {γ1 : Path z1 z1}
    (hhom : ClosedPathHomotopicIn C γ0 γ1)
    (hnull : IsNullHomotopicClosedPathIn C γ1) :
    IsNullHomotopicClosedPathIn C γ0 := by
  rcases hnull with ⟨x, hxC, hconst⟩
  -- Compose the comparison homotopy with the chosen contraction of `γ1`.
  exact ⟨x, hxC, hhom.trans hconst⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected ambient set with at
least one boundary component, the ambient set `C` itself occurs among the connected-component keys
of the boundary family. -/
theorem connectedAmbient_mem_boundaryComponentImage_of_orientedBoundary
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C) (hC_connected : IsConnected C) :
    C ∈ Finset.univ.image (fun i : ι => connectedComponentIn C ((Γ i).toPath 0)) := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  refine Finset.mem_image.mpr ?_
  -- Use any one boundary component: connectedness forces its component key to be exactly `C`.
  exact ⟨i0, Finset.mem_univ i0, boundaryComponentKey_eq_ambient_of_connectedAmbient
    hΓ hKC hC_connected i0⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in the nonempty connected-open
branch, once the boundary contour sum is known to vanish, the earlier `..._iff_sumZero`
equivalence turns that scalar statement into the required null-homotopic witness loop. -/
theorem existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_of_sumZero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ z : ℂ, ∃ γ : Path z z,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      IsNullHomotopicClosedPathIn C γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  -- This helper isolates the purely formal conversion from scalar vanishing to the witness loop.
  exact
    (existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_iff_sumZero
      (C := C) (Γ := Γ) hΓ hKC hω).2 hsumZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in the nonempty connected-open
branch, the witness theorem is now reduced to supplying the scalar vanishing statement. -/
theorem
    existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_nonempty_of_sumZero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ z : ℂ, ∃ γ : Path z z,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      IsNullHomotopicClosedPathIn C γ ∧
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := by
  -- Record the stabilized downstream wrapper so the only remaining pre-main task is the scalar
  -- connected-open vanishing theorem.
  exact
    existsNullHomotopicBoundaryLoopWithSameIntegralConnectedOpen_of_sumZero
      (Γ := Γ) hΓ hKC hω hsumZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once a connected-component block has
been filtered out by the key `C`, reindexing that block by the corresponding subtype does not
change its contour sum. -/
theorem componentBlock_sum_eq_subtype_sum
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ} {C : Set ℂ} :
    ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
        (fun i => ∫ᶜ ζ in (Γ i).toPath, ω ζ)) =
      ∑ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C},
        ∫ᶜ ζ in (Γ i.1).toPath, ω ζ := by
  -- Reindex the filtered block by the subtype cut out by the same connected-component predicate.
  simpa using
    (Finset.sum_toFinset_eq_subtype
      (p := fun i : ι => connectedComponentIn D ((Γ i).toPath 0) = C)
      (f := fun i => ∫ᶜ ζ in (Γ i).toPath, ω ζ))

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected ambient set `C`, the
total contour sum is already the subtype sum over the unique connected-component block keyed by
`C`. -/
theorem connectedAmbient_total_curveIntegral_eq_subtypeBoundaryBlockSum
    {ι : Type u} [Fintype ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
      ∑ i : {j // connectedComponentIn C ((Γ j).toPath 0) = C},
        ∫ᶜ ζ in (Γ i.1).toPath, ω ζ := by
  -- First collapse the connected-ambient component filter to the full family, then reindex that
  -- single block by its subtype of indices.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
        ((Finset.univ.filter fun i => connectedComponentIn C ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ ζ in (Γ i).toPath, ω ζ)) := by
      symm
      exact
        connectedAmbient_componentFilter_sum_eq_total
          (Γ := Γ) hΓ hKC hC_connected
          (fun i => ∫ᶜ ζ in (Γ i).toPath, ω ζ)
    _ =
        ∑ i : {j // connectedComponentIn C ((Γ j).toPath 0) = C},
          ∫ᶜ ζ in (Γ i.1).toPath, ω ζ := by
      exact componentBlock_sum_eq_subtype_sum (Γ := Γ) (D := C) (ω := ω) (C := C)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: restricting the oriented-boundary
family to one connected-component block preserves the connected-open and closed-form data needed
for the later block argument. -/
theorem subtypeBoundaryBlock_restrictionData_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
    let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
    IsOrientedBoundaryOf (K ∩ C) ΓC ∧
      IsOpen C ∧
      IsConnected C ∧
      IsClosedOn ω C := by
  classical
  let ιC : Type u := {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}
  let ΓC : ιC → ClosedPath ℂ := fun i ↦ Γ i.1
  have hΓC : IsOrientedBoundaryOf (K ∩ C) ΓC :=
    subtypeBoundaryPaths_isOrientedBoundaryOf_inter_boundaryComponent hΓ hKD hD_open hC
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  have hC_connected : IsConnected C :=
    (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).2
  have hωC : IsClosedOn ω C :=
    hω.restrictBoundaryComponent (Γ := Γ) hD_open hC
  -- Package the boundary-component restriction data once so the later proof only has to supply
  -- the missing stage/approximation owner theorem.
  exact ⟨hΓC, hC_open, hC_connected, hωC⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected ambient set with at
least one boundary component, the unique subtype block keyed by the ambient set `C` is nonempty.
-/
theorem connectedAmbient_subtypeBoundaryBlock_nonempty
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C) (hC_connected : IsConnected C) :
    Nonempty {j : ι // connectedComponentIn C ((Γ j).toPath 0) = C} := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  -- Connectedness collapses the component key of the chosen basepoint to the whole ambient set.
  exact ⟨⟨i0, boundaryComponentKey_eq_ambient_of_connectedAmbient
    hΓ hKC hC_connected i0⟩⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in the nonempty connected-open
case, vanishing of the unique subtype block already implies vanishing of the full ambient contour
sum. -/
theorem connectedAmbient_sum_curveIntegral_eq_zero_of_subtypeBoundaryBlock
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsubtypeZero :
      (∑ i : {j // connectedComponentIn C ((Γ j).toPath 0) = C},
          ∫ᶜ ζ in (Γ i.1).toPath, ω ζ) = 0) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  -- Rewrite the full contour sum as the unique connected-component block before inserting the
  -- already proved subtype-block vanishing statement.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) =
        ∑ i : {j // connectedComponentIn C ((Γ j).toPath 0) = C},
          ∫ᶜ ζ in (Γ i.1).toPath, ω ζ := by
      exact
        connectedAmbient_total_curveIntegral_eq_subtypeBoundaryBlockSum
          (Γ := Γ) (ω := ω) hΓ hKC hC_connected
    _ = 0 := hsubtypeZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-open contour sum
is known to be the limit of rectangle-boundary stages staying inside `C`, closedness kills each
stage and therefore the target sum itself. -/
theorem sum_curveIntegral_eq_zero_of_asymptoticRectangleStages
    {C : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {target : ℂ} {N : ℕ → ℕ} (z w : ∀ n, Fin (N n) → ℂ)
    (hrect : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C)
    (hrect_integrable : ∀ n s,
      CurveIntegrable ω (axisParallelRectangleBoundaryPath (z n s) (w n s)))
    (hcontour :
      Filter.Tendsto
        (fun n ↦ ∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
        Filter.atTop
        (nhds target)) :
    target = 0 := by
  have hzeroStage :
      ∀ n,
        (∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) = 0 := by
    intro n
    -- Each stage is already a finite rectangle family inside `C`, so the rectangle vanishing
    -- lemma applies termwise.
    exact rectangleStage_sum_curveIntegral_eq_zero_of_isClosedOn hω (z n) (w n) (hrect n)
      (hrect_integrable n)
  have hzeroLimit :
      Filter.Tendsto
        (fun n ↦ ∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
        Filter.atTop
        (nhds 0) := by
    -- After rewriting every stage sum to `0`, the approximating sequence is literally constant.
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun n ↦ (hzeroStage n).symm
  -- The same stage sequence cannot converge both to the target contour sum and to `0` unless the
  -- target is already `0`.
  exact tendsto_nhds_unique hcontour hzeroLimit

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-open contour sum
is known to be the limit of rectangle-boundary stages staying inside `C`, closedness kills each
stage and therefore the target sum itself. -/
theorem connectedAmbient_sum_curveIntegral_eq_zero_of_asymptoticRectangleStages
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ) (_hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {N : ℕ → ℕ} (z w : ∀ n, Fin (N n) → ℂ)
    (hrect : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C)
    (hrect_integrable : ∀ n s,
      CurveIntegrable ω (axisParallelRectangleBoundaryPath (z n s) (w n s)))
    (hcontour :
      Filter.Tendsto
        (fun n ↦ ∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ))) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  -- Route correction: isolate the stage-killing argument at a target-agnostic level so the only
  -- remaining owner-level blocker is the construction of the connected-open stage package.
  exact
    sum_curveIntegral_eq_zero_of_asymptoticRectangleStages
      (C := C) (ω := ω) hω z w hrect hrect_integrable hcontour

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if the closed form on the connected
ambient domain already extends to one continuous global primitive witness on `C`, then each
boundary loop integral vanishes individually and so does the total contour sum. -/
theorem connectedAmbient_sum_curveIntegral_eq_zero_of_hasPrimitiveOn_of_continuousOn
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C) (hC_open : IsOpen C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω_cont : ContinuousOn ω C) (hprimitive : HasPrimitiveOn C ω) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  have hloopZero :
      ∀ {z : ℂ} (γ : Path z z), γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C →
        ∫ᶜ ζ in γ, ω ζ = 0 := by
    -- Proposition 2.1 turns the global primitive on the open ambient domain into vanishing for
    -- every closed piecewise differentiable loop contained in `C`.
    exact
      (hasPrimitiveOn_iff_curveIntegral_eq_zero_loops_of_isOpen hC_open hω_cont).1 hprimitive
  -- Apply the loop-vanishing theorem to each boundary component before summing the resulting
  -- zeros.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∑ i, 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact
        hloopZero ((Γ i).toPath) (hΓ.piecewiseDifferentiable i)
          (range_toPath_subset_domain_of_orientedBoundary hΓ hKC i)
    _ = 0 := by
      simp

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once a boundary contour sum is
identified with the contour integral of a null-homotopic loop in the same closed-form domain, the
sum itself vanishes. -/
theorem sum_curveIntegral_eq_zero_of_nullHomotopicWitness
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ}
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D)
    {z : ℂ} {γ : Path z z}
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hγ_integrable : CurveIntegrable ω γ)
    (hγ_null : IsNullHomotopicClosedPathIn D γ)
    (hsum :
      (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  -- Rewrite the boundary contour sum through the null-homotopic loop witness.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := hsum
    _ = 0 := by
      -- The closed-form null-homotopy theorem kills the witness loop.
      exact
        curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain
          hγ_null hγ_piecewise hγ_integrable hω

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the connected-open contour sum
is known to vanish, the asymptotic rectangle-stage package is only the formal empty-stage wrapper.
-/
theorem connectedAmbient_asymptoticRectangleStages_of_sumZero
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hsumZero : (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0) :
    ∃ N : ℕ → ℕ, ∃ z w : ∀ n, Fin (N n) → ℂ,
      (∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ C) ∧
      Filter.Tendsto
        (fun n ↦ ∑ s : Fin (N n),
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ)
        Filter.atTop
        (nhds (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ)) := by
  -- Once the connected-open scalar sum is available, the exact-package support file turns it into
  -- the required asymptotic rectangle-stage family formally.
  exact
    asymptoticRectangleStages_of_sum_curveIntegral_eq_zero
      (C := C) (Γ := Γ) (ω := ω) hΓ hsumZero

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the remaining owner-level blocker is
the direct connected-open scalar vanishing theorem for closed forms in the nonempty ambient case.
-/
theorem curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain_without_integrability
    {D : Set ℂ} {z : ℂ} {γ : Path z z} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hγ : IsNullHomotopicClosedPathIn D γ)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable)
    (hω : IsClosedOn ω D) :
    ∫ᶜ ζ in γ, ω ζ = 0 := by
  by_cases hγ_integrable : CurveIntegrable ω γ
  · -- In the integrable branch, reuse the earlier null-homotopy theorem verbatim.
    exact
      curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain
        hγ hγ_piecewise hγ_integrable hω
  · -- In this development non-integrable curve integrals are definitionally `0`.
    rw [curveIntegral_def]
    simpa [CurveIntegrable] using
      (intervalIntegral.integral_undef (μ := MeasureTheory.volume)
        (f := curveIntegralFun ω γ) (a := (0 : ℝ)) (b := (1 : ℝ)) hγ_integrable)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the remaining owner-level blocker is
the direct connected-open scalar vanishing theorem for closed forms in the nonempty ambient case.
-/
theorem connectedAmbient_sum_curveIntegral_eq_zero_of_isClosedOn_of_witness
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (_hΓ : IsOrientedBoundaryOf K Γ) (_hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    (hWitness :
      ∃ z : ℂ, ∃ γ : Path z z,
        γ.IsPiecewiseDifferentiable ∧
        IsNullHomotopicClosedPathIn C γ ∧
        (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ) :
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = 0 := by
  rcases hWitness with ⟨z, γ, hγ_piecewise, hγ_null, hsum⟩
  -- Once the connected-open witness loop is available, rewrite the target sum through that loop
  -- and collapse the loop integral by null-homotopy.
  calc
    (∑ i, ∫ᶜ ζ in (Γ i).toPath, ω ζ) = ∫ᶜ ζ in γ, ω ζ := hsum
    _ = 0 :=
      curveIntegral_eq_zero_of_nullHomotopicClosedPathIn_domain_without_integrability
        hγ_null hγ_piecewise hω

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once the canonical rooted loop is
known to stay in `C`, closedness already gives a primitive along that whole loop. -/
theorem rootedBoundaryLoop_existsPrimitiveAlongPath_of_isClosedOn
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C) :
    let z0 : ℂ := (Γ i0).toPath 0
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C γ f := by
  let z0 : ℂ := (Γ i0).toPath 0
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  have hγ_top :
      γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
    -- Reuse the topology-only rooted-loop package before asking for any analytic conclusion.
    simpa [z0, γ] using
      rootedBoundaryLoopTopology_of_orientedBoundaryConnectorFamily
        (Γ := Γ) hΓ hKC hρ_piece hρC
  -- Closedness on `C` now produces a primitive along the entire canonical rooted loop.
  simpa [γ] using hω.existsPrimitiveAlongPath_of_path_in_domain hγ_top.2

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: under the closed-form hypothesis,
the canonical rooted loop attached to one connected-open connector family already comes with its
full topology package together with a primitive along that exact loop. -/
theorem IsOrientedBoundaryOf.existsPrimitiveAlongRootedBoundaryLoop_of_isClosedOn
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] {C K : Set ℂ}
    {Γ : ι → ClosedPath ℂ} (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω C)
    {i0 : ι} {ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0)}
    (hρ_piece : ∀ i, (ρ i).IsPiecewiseDifferentiable)
    (hρC : ∀ i t, ρ i t ∈ C) :
    ∃ z : ℂ, ∃ γ : Path z z,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C ∧
      ∃ f : C(I, ℂ), IsPrimitiveAlongPath ω C γ f := by
  let z0 : ℂ := (Γ i0).toPath 0
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  have hγ_top :
      γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
    -- Reuse the topology-only rooted-loop package before attaching the primitive witness.
    simpa [z0, γ] using
      rootedBoundaryLoopTopology_of_orientedBoundaryConnectorFamily
        (Γ := Γ) hΓ hKC hρ_piece hρC
  obtain ⟨f, hf⟩ :=
    rootedBoundaryLoop_existsPrimitiveAlongPath_of_isClosedOn
      (Γ := Γ) hΓ hKC hω hρ_piece hρC
  -- This packages the exact rooted loop spelling used in the connected-open direct theorem.
  exact ⟨z0, γ, hγ_top.1, hγ_top.2, f, by simpa [z0, γ] using hf⟩
