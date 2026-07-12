import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».BoundaryComponentGeometry
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».ClosedFormBoundaryReductions
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».ConnectedOpenContourReductions

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

/-- Helper for Corollary II.1-extra-23: `boundaryComponentIndex Γ D C` is the subtype of boundary
curves in the family `Γ` whose connected-component key in `D` is `C`. -/
abbrev boundaryComponentIndex
    {ι : Type u} (Γ : ι → ClosedPath ℂ) (D C : Set ℂ) : Type u :=
  {j : ι // connectedComponentIn D ((Γ j).toPath 0) = C}

/-- Helper for Corollary II.1-extra-23: `boundaryComponentFamily Γ D C` is the boundary family
obtained by reindexing `Γ` along the subtype `boundaryComponentIndex Γ D C`. -/
def boundaryComponentFamily
    {ι : Type u} (Γ : ι → ClosedPath ℂ) (D C : Set ℂ) :
    boundaryComponentIndex Γ D C → ClosedPath ℂ := fun i ↦ Γ i.1

/-- Helper for Corollary II.1-extra-23: a form that is closed on `D` already forces `D` to be
open, because every point of `D` comes with an open primitive neighborhood contained in `D`. -/
theorem isOpen_of_isClosedOn
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) :
    IsOpen D := by
  rw [Metric.isOpen_iff]
  intro z hz
  rcases hω z hz with ⟨U, hU_open, hzU, hUD, _⟩
  -- Extract a metric ball from the local primitive neighborhood and keep the inclusion into `D`.
  rcases Metric.isOpen_iff.mp hU_open z hzU with ⟨r, hr, hballU⟩
  exact ⟨r, hr, hballU.trans hUD⟩

/-- Helper for Corollary II.1-extra-23: each connected-component block of the oriented boundary
family inherits the connected-open restriction data in an explicit subtype spelling, so later
helpers do not have to unfold the imported package theorem again. -/
theorem subtypeBoundaryBlock_restrictionData_explicit_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsOrientedBoundaryOf (K ∩ C)
        (boundaryComponentFamily Γ D C) ∧
      IsOpen C ∧
      IsConnected C ∧
      IsClosedOn ω C := by
  -- Reuse the owner theorem in its native boundary-component normal form and only unfold the
  -- local subtype family aliases at the outer boundary.
  have hD_open : IsOpen D := isOpen_of_isClosedOn hω
  simpa [boundaryComponentIndex, boundaryComponentFamily] using
    (subtypeBoundaryBlock_restrictionData_of_isClosedOn
      (Γ := Γ) hΓ hKD hD_open hω hC)

/-- Helper for Corollary II.1-extra-23: a component key coming from the boundary-family image
cuts out a nonempty subtype of indices. -/
theorem subtypeBoundaryBlock_nonempty
    {ι : Type u} [Fintype ι] {D : Set ℂ} {Γ : ι → ClosedPath ℂ} {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    Nonempty (boundaryComponentIndex Γ D C) := by
  -- The component key belongs to the image, so it already has a witness index.
  rcases Finset.mem_image.mp hC with ⟨i, _, hiC⟩
  exact ⟨⟨i, hiC⟩⟩

/-- Helper for Corollary II.1-extra-23: the subtype family attached to one connected-component key
already has zero contour sum once it is presented as an oriented boundary in a connected open
ambient set. -/
theorem boundaryComponentFamily_sum_eq_zero_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K C : Set ℂ} {Γ : ι → ClosedPath ℂ}
    [Nonempty (boundaryComponentIndex Γ D C)]
    (hΓC : IsOrientedBoundaryOf (K ∩ C) (boundaryComponentFamily Γ D C))
    (hKC : K ∩ C ⊆ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hωC : IsClosedOn ω C) :
    (∑ i : boundaryComponentIndex Γ D C,
        ∫ᶜ z in (boundaryComponentFamily Γ D C i).toPath, ω z) = 0 := by
  classical
  -- Apply the connected-open scalar theorem directly to the subtype-reindexed boundary family.
  exact
    connectedOpenBoundarySumZero_of_isClosedOn
      (Γ := boundaryComponentFamily Γ D C) hΓC hKC hC_open hC_connected hωC

/-- Helper for Corollary II.1-extra-23: the subtype family attached to one connected-component key
already has zero contour sum, because it is an oriented boundary inside a connected open ambient
set where the connected-open theorem applies. -/
theorem subtypeBoundaryBlock_sum_eq_zero_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    (∑ i : boundaryComponentIndex Γ D C,
        ∫ᶜ z in (boundaryComponentFamily Γ D C i).toPath, ω z) = 0 := by
  have hData :
      IsOrientedBoundaryOf (K ∩ C) (boundaryComponentFamily Γ D C) ∧
        IsOpen C ∧
        IsConnected C ∧
        IsClosedOn ω C :=
    subtypeBoundaryBlock_restrictionData_explicit_of_isClosedOn
      (Γ := Γ) hΓ hKD hω hC
  rcases hData with ⟨hΓC, hC_open, hC_connected, hωC⟩
  -- Feed the restricted boundary package into the connected-open component theorem.
  letI : Nonempty (boundaryComponentIndex Γ D C) := subtypeBoundaryBlock_nonempty hC
  exact
    boundaryComponentFamily_sum_eq_zero_of_isClosedOn
      (Γ := Γ) (D := D) (K := K) (C := C) hΓC
      (fun z hz ↦ hz.2) hC_open hC_connected hωC

/-- Helper for Corollary II.1-extra-23: each connected-component block of the oriented boundary
family already has vanishing contour sum, because the block reindexes to the subtype family whose
connected-open contour sum is zero. -/
theorem componentBoundaryBlock_sum_eq_zero_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {ω : ℂ → ℂ →L[ℝ] ℂ} (hω : IsClosedOn ω D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
      (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) = 0 := by
  -- Reindex the filtered block by the matching subtype and insert the already proved subtype
  -- vanishing statement.
  calc
    ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
        (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) =
      ∑ i : boundaryComponentIndex Γ D C,
        ∫ᶜ z in (boundaryComponentFamily Γ D C i).toPath, ω z := by
        simpa [boundaryComponentFamily, boundaryComponentIndex] using
          (componentBlock_sum_eq_subtype_sum (Γ := Γ) (D := D) (ω := ω) (C := C))
    _ = 0 :=
      subtypeBoundaryBlock_sum_eq_zero_of_isClosedOn
        (Γ := Γ) hΓ hKD hω hC

/-- Helper for Corollary II.1-extra-23: once every connected-component block sum vanishes, the
global contour sum vanishes by the finite connected-component decomposition. -/
theorem sum_curveIntegral_eq_zero_of_zero_componentBlocks
    {ι : Type u} [Fintype ι] {D : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hblock :
      ∀ C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0)),
        ((Finset.univ.filter fun i => connectedComponentIn D ((Γ i).toPath 0) = C).sum
          (fun i => ∫ᶜ z in (Γ i).toPath, ω z)) = 0) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ω z) = 0 := by
  -- Rewrite the total contour sum as the sum of its connected-component blocks.
  rw [sum_curveIntegral_eq_sum_component_blocks (D := D) (Γ := Γ) (ω := ω)]
  -- Then every block is zero by hypothesis, so the whole finite sum vanishes.
  exact Finset.sum_eq_zero hblock

/-- Corollary II.1-extra-23: if the form `ω` is closed in `D`, then the contour integral `∫_Γ ω`
vanishes whenever `Γ` is the oriented boundary of a compact subset of `D`; in this repository
that source contour is represented by the displayed finite sum over the boundary family `Γ`. -/
theorem orientedBoundary_integral_eq_zero_of_isClosedOn
    {ι : Type u} [Fintype ι] {D K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D) :
    (∑ i, ∫ᶜ z in (Γ i).toPath, ω z) = 0 := by
  -- Split the total contour sum into connected-component blocks of the ambient domain `D`.
  refine sum_curveIntegral_eq_zero_of_zero_componentBlocks (D := D) (Γ := Γ) ?_
  intro C hC
  -- Each block reduces to the connected-open case and therefore has zero contour sum.
  exact componentBoundaryBlock_sum_eq_zero_of_isClosedOn (Γ := Γ) hΓ hKD hω hC
