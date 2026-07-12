import DifferentialForms_Cartan_1970.II.section05.«0007_Theorem_II_1_extra_5»
import DifferentialForms_Cartan_1970.II.section05.«0010_Proposition_4_1»
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».ApproximationPackages
import DifferentialForms_Cartan_1970.II.section05.«0035_Theorem_II_1_extra_22».BoundaryGeometry

open scoped BigOperators

universe u v

namespace OrientedBoundaryApproximation

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: recursively concatenate the
connector-conjugated boundary loops listed in `l` to obtain one rooted loop based at `z0`. -/
noncomputable def rootedBoundaryLoopList
    {ι : Type u} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0)) : Path z0 z0 :=
  match l with
  | [] => Path.refl z0
  | i :: l' =>
      (rootedBoundaryLoopList l' Γ ρ).trans (((ρ i).trans (Γ i).toPath).trans (ρ i).symm)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the explicit rooted loop attached to
a finite family of boundary components is obtained by running the recursive concatenation over the
`Finset` enumeration. -/
noncomputable def rootedBoundaryLoop
    {ι : Type u} [DecidableEq ι] {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0)) : Path z0 z0 :=
  rootedBoundaryLoopList s.toList Γ ρ

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: unpacking a loop through
`toClosedPath.toPath` only inserts the trivial endpoint cast. -/
theorem loop_toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath = γ.cast γ.source γ.source := by
  cases γ
  rfl

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: passing a loop through
`toClosedPath.toPath` does not change its contour integral. -/
theorem curveIntegral_toClosedPath_toPath_eq
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x : ℂ} (ω : ℂ → ℂ →L[ℝ] F) (γ : Path x x) :
    ∫ᶜ z in γ.toClosedPath.toPath, ω z = ∫ᶜ z in γ, ω z := by
  rw [loop_toClosedPath_toPath_eq_cast, curveIntegral_def', curveIntegral_def']
  change
    ∫ t in (0 : ℝ)..1, curveIntegralFun (fun z ↦ ω z) (γ.cast γ.source γ.source) t =
      ∫ t in (0 : ℝ)..1, curveIntegralFun (fun z ↦ ω z) γ t
  simpa using
    congrArg
      (fun f : ℝ → F ↦ ∫ t in (0 : ℝ)..1, f t)
      (curveIntegralFun_cast (fun z ↦ ω z) γ γ.source γ.source)

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the recursive rooted loop is
piecewise differentiable, stays in `C`, is curve-integrable, and its contour integral is the sum
of the boundary integrals of the listed components. -/
theorem rootedBoundaryLoopList_spec
    {ι : Type u} {C : Set ℂ} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : ℂ → ℂ →L[ℝ] F}
    (hz0C : z0 ∈ C)
    (hρ_piece : ∀ i, i ∈ l → (ρ i).IsPiecewiseDifferentiable)
    (hΓ_piece : ∀ i, i ∈ l → ((Γ i).toPath).IsPiecewiseDifferentiable)
    (hρC : ∀ i, i ∈ l → Set.range (ρ i) ⊆ C)
    (hΓC : ∀ i, i ∈ l → Set.range ((Γ i).toPath) ⊆ C)
    (hρ_int : ∀ i, i ∈ l → CurveIntegrable ω (ρ i))
    (hΓ_int : ∀ i, i ∈ l → CurveIntegrable ω ((Γ i).toPath)) :
    (rootedBoundaryLoopList l Γ ρ).IsPiecewiseDifferentiable ∧
      Set.range (rootedBoundaryLoopList l Γ ρ) ⊆ C ∧
      CurveIntegrable ω (rootedBoundaryLoopList l Γ ρ) ∧
      (∫ᶜ z in rootedBoundaryLoopList l Γ ρ, ω z =
        (l.map fun i => ∫ᶜ z in (Γ i).toPath, ω z).sum) := by
  induction l generalizing Γ ρ with
  | nil =>
      -- The empty rooted loop is constant, remains in `C`, and contributes zero contour.
      refine ⟨Path.isPiecewiseDifferentiable_refl z0, ?_, CurveIntegrable.refl ω z0, ?_⟩
      · intro z hz
        rcases hz with ⟨t, ht⟩
        simpa [rootedBoundaryLoopList] using (ht ▸ hz0C)
      · simp [rootedBoundaryLoopList]
  | cons i l ih =>
      have hρl : ∀ j, j ∈ l → (ρ j).IsPiecewiseDifferentiable := by
        intro j hj
        exact hρ_piece j (by simp [hj])
      have hΓl : ∀ j, j ∈ l → ((Γ j).toPath).IsPiecewiseDifferentiable := by
        intro j hj
        exact hΓ_piece j (by simp [hj])
      have hρlC : ∀ j, j ∈ l → Set.range (ρ j) ⊆ C := by
        intro j hj
        exact hρC j (by simp [hj])
      have hΓlC : ∀ j, j ∈ l → Set.range ((Γ j).toPath) ⊆ C := by
        intro j hj
        exact hΓC j (by simp [hj])
      have hρl_int : ∀ j, j ∈ l → CurveIntegrable ω (ρ j) := by
        intro j hj
        exact hρ_int j (by simp [hj])
      have hΓl_int : ∀ j, j ∈ l → CurveIntegrable ω ((Γ j).toPath) := by
        intro j hj
        exact hΓ_int j (by simp [hj])
      rcases ih Γ ρ hρl hΓl hρlC hΓlC hρl_int hΓl_int with
        ⟨hloop_piece, hloopC, hloop_int, hloop_eq⟩
      have hρi_piece : (ρ i).IsPiecewiseDifferentiable := hρ_piece i (by simp)
      have hΓi_piece : ((Γ i).toPath).IsPiecewiseDifferentiable := hΓ_piece i (by simp)
      have hρiC : Set.range (ρ i) ⊆ C := hρC i (by simp)
      have hΓiC : Set.range ((Γ i).toPath) ⊆ C := hΓC i (by simp)
      have hρi_int : CurveIntegrable ω (ρ i) := hρ_int i (by simp)
      have hΓi_int : CurveIntegrable ω ((Γ i).toPath) := hΓ_int i (by simp)
      let tail : Path z0 z0 := ((ρ i).trans (Γ i).toPath).trans (ρ i).symm
      have htail_piece : tail.IsPiecewiseDifferentiable := by
        -- The connector-conjugated loop inherits piecewise differentiability from its three pieces.
        dsimp [tail]
        exact (hρi_piece.trans hΓi_piece).trans hρi_piece.symm
      have htailC : Set.range tail ⊆ C := by
        -- The conjugated loop stays in `C` because both the connector and the original loop stay
        -- in `C`.
        dsimp [tail]
        rw [Path.trans_range]
        refine Set.union_subset ?_ ?_
        · rw [Path.trans_range]
          exact Set.union_subset hρiC hΓiC
        · simpa [Path.symm_range] using hρiC
      have htail_int : CurveIntegrable ω tail := by
        -- Curve integrability is stable under concatenating the connector, the loop, and the
        -- return connector.
        dsimp [tail]
        exact (hρi_int.trans hΓi_int).trans hρi_int.symm
      have htail_eq :
          ∫ᶜ z in tail, ω z = ∫ᶜ z in (Γ i).toPath, ω z := by
        -- The connector contribution cancels after conjugation, so only the original loop
        -- integral remains.
        simpa [tail] using curveIntegral_conjugateLoop_eq hρi_int hΓi_int
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Appending one connector-conjugated boundary loop preserves piecewise differentiability.
        dsimp [rootedBoundaryLoopList]
        exact hloop_piece.trans htail_piece
      · -- The recursive loop remains in `C` because every new connector and boundary piece does.
        rw [rootedBoundaryLoopList, Path.trans_range]
        exact Set.union_subset hloopC htailC
      · -- Curve integrability is stable under the same concatenation.
        simpa [rootedBoundaryLoopList] using hloop_int.trans htail_int
      · -- The rooted-loop contour is the sum of the previous stage and the new boundary term.
        calc
          ∫ᶜ z in rootedBoundaryLoopList (i :: l) Γ ρ, ω z =
              ∫ᶜ z in rootedBoundaryLoopList l Γ ρ, ω z + ∫ᶜ z in tail, ω z := by
            simpa [rootedBoundaryLoopList, tail] using curveIntegral_trans hloop_int htail_int
          _ = (l.map fun j => ∫ᶜ z in (Γ j).toPath, ω z).sum +
                ∫ᶜ z in (Γ i).toPath, ω z := by
            rw [hloop_eq, htail_eq]
          _ = ((i :: l).map fun j => ∫ᶜ z in (Γ j).toPath, ω z).sum := by
            simp [add_comm]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the `Finset`-indexed rooted loop
inherits the same regularity, range, integrability, and contour-sum formula from the recursive
list construction. -/
theorem rootedBoundaryLoop_spec
    {ι : Type u} [DecidableEq ι] {C : Set ℂ} {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ω : ℂ → ℂ →L[ℝ] F}
    (hz0C : z0 ∈ C)
    (hρ_piece : ∀ i ∈ s, (ρ i).IsPiecewiseDifferentiable)
    (hΓ_piece : ∀ i ∈ s, ((Γ i).toPath).IsPiecewiseDifferentiable)
    (hρC : ∀ i ∈ s, Set.range (ρ i) ⊆ C)
    (hΓC : ∀ i ∈ s, Set.range ((Γ i).toPath) ⊆ C)
    (hρ_int : ∀ i ∈ s, CurveIntegrable ω (ρ i))
    (hΓ_int : ∀ i ∈ s, CurveIntegrable ω ((Γ i).toPath)) :
    (rootedBoundaryLoop s Γ ρ).IsPiecewiseDifferentiable ∧
      Set.range (rootedBoundaryLoop s Γ ρ) ⊆ C ∧
      CurveIntegrable ω (rootedBoundaryLoop s Γ ρ) ∧
      (∫ᶜ z in rootedBoundaryLoop s Γ ρ, ω z =
        s.sum fun i => ∫ᶜ z in (Γ i).toPath, ω z) := by
  have hρ_piece_list : ∀ i, i ∈ s.toList → (ρ i).IsPiecewiseDifferentiable := by
    intro i hi
    exact hρ_piece i (Finset.mem_toList.1 hi)
  have hΓ_piece_list : ∀ i, i ∈ s.toList → ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    exact hΓ_piece i (Finset.mem_toList.1 hi)
  have hρC_list : ∀ i, i ∈ s.toList → Set.range (ρ i) ⊆ C := by
    intro i hi
    exact hρC i (Finset.mem_toList.1 hi)
  have hΓC_list : ∀ i, i ∈ s.toList → Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    exact hΓC i (Finset.mem_toList.1 hi)
  have hρ_int_list : ∀ i, i ∈ s.toList → CurveIntegrable ω (ρ i) := by
    intro i hi
    exact hρ_int i (Finset.mem_toList.1 hi)
  have hΓ_int_list : ∀ i, i ∈ s.toList → CurveIntegrable ω ((Γ i).toPath) := by
    intro i hi
    exact hΓ_int i (Finset.mem_toList.1 hi)
  rcases rootedBoundaryLoopList_spec (C := C) s.toList Γ ρ hz0C
      hρ_piece_list hΓ_piece_list hρC_list hΓC_list hρ_int_list hΓ_int_list with
    ⟨hloop_piece, hloopC, hloop_int, hloop_eq⟩
  refine ⟨hloop_piece, hloopC, hloop_int, ?_⟩
  -- Convert the list sum back to the canonical `Finset` sum over `s`.
  calc
    ∫ᶜ z in rootedBoundaryLoop s Γ ρ, ω z =
        (s.toList.map fun i => ∫ᶜ z in (Γ i).toPath, ω z).sum := hloop_eq
    _ = (Multiset.map (fun i => ∫ᶜ z in (Γ i).toPath, ω z) s.val).sum := by
      exact Multiset.sum_map_toList s.val (fun i => ∫ᶜ z in (Γ i).toPath, ω z)
    _ = s.sum (fun i => ∫ᶜ z in (Γ i).toPath, ω z) := by
      rw [Finset.sum]

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a finite rectangle stage inside one
open connected ambient set can be compressed into one rooted loop while preserving the contour
integrals of the two coordinate half-forms. -/
theorem rootedRectangleStageLoop_spec
    {κ : Type*} (s : Finset κ) {C : Set ℂ} {z0 : ℂ}
    (hz0C : z0 ∈ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (z w : κ → ℂ) {P Q : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hrect : ∀ i ∈ s, Complex.Rectangle (z i) (w i) ⊆ C) :
    ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C ∧
      CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) γ ∧
      CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) γ ∧
      (∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
        Finset.sum s (fun i ↦
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z i) (w i), (((0 : ℂ → ℝ) dx + Q dy)) ζ)) ∧
      (∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ =
        Finset.sum s (fun i ↦
          ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z i) (w i), (P dx + (0 : ℂ → ℝ) dy) ζ)) := by
  classical
  let Γ : κ → ClosedPath ℂ := fun i ↦ (axisParallelRectangleBoundaryPath (z i) (w i)).toClosedPath
  have hz_mem : ∀ i ∈ s, z i ∈ C := by
    -- Each rectangle base corner lies in `C` because the whole rectangle does.
    intro i hi
    exact hrect i hi (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hΓ_base_eq : ∀ i, ((Γ i).toPath 0) = z i := by
    -- Unpacking `toClosedPath.toPath` at the initial parameter recovers the original start point.
    intro i
    change (((axisParallelRectangleBoundaryPath (z i) (w i)).toClosedPath).toPath 0) = z i
    rw [loop_toClosedPath_toPath_eq_cast]
    calc
      ((axisParallelRectangleBoundaryPath (z i) (w i)).cast _ _) 0 =
          (axisParallelRectangleBoundaryPath (z i) (w i)) 0 := by
        exact congrFun (Path.cast_coe (axisParallelRectangleBoundaryPath (z i) (w i)) _ _) 0
      _ = z i := by
        simp [axisParallelRectangleBoundaryPath]
  have hΓ_base_mem : ∀ i ∈ s, ((Γ i).toPath 0) ∈ C := by
    intro i hi
    simpa [hΓ_base_eq i] using hz_mem i hi
  have hconnector :
      ∀ i ∈ s,
        ∃ ρ : Path z0 ((Γ i).toPath 0), ρ.IsPiecewiseDifferentiable ∧ Set.range ρ ⊆ C := by
    intro i hi
    obtain ⟨ρ, hρ_piece, hρ_mem⟩ :=
      exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
        hC_open hC_connected hz0C (hΓ_base_mem i hi)
    refine ⟨ρ, hρ_piece, ?_⟩
    intro ζ hζ
    rcases hζ with ⟨t, rfl⟩
    exact hρ_mem t
  let ρ : ∀ i, Path z0 ((Γ i).toPath 0) := fun i ↦
    if hi : i ∈ s then
      Classical.choose (hconnector i hi)
    else
      Path.segment z0 ((Γ i).toPath 0)
  have hρ_piece : ∀ i ∈ s, (ρ i).IsPiecewiseDifferentiable := by
    intro i hi
    dsimp [ρ]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hconnector i hi)).1
  have hρ_mem : ∀ i ∈ s, Set.range (ρ i) ⊆ C := by
    intro i hi
    dsimp [ρ]
    rw [dif_pos hi]
    exact (Classical.choose_spec (hconnector i hi)).2
  have hΓ_piece : ∀ i ∈ s, ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    -- Rectangle boundaries are piecewise differentiable because they are concatenations of
    -- affine segments.
    simpa [Γ, Path.toClosedPath] using
      axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z i) (w i)
  have hΓ_mem : ∀ i ∈ s, Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    -- Each rectangle boundary stays in its rectangle, and the rectangle was assumed to lie in `C`.
    intro ζ hζ
    have hζ' : ζ ∈ Set.range (axisParallelRectangleBoundaryPath (z i) (w i)) := by
      simpa [Γ, Path.toClosedPath] using hζ
    exact hrect i hi (axisParallelRectangleBoundaryPath_range_subset_rectangle (z i) (w i) hζ')
  have hQ_form_cont : ContinuousOn (((0 : ℂ → ℝ) dx + Q dy)) C := by
    -- The `Q dy` half-form inherits continuity from `Q`.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := C) (P := (0 : ℂ → ℝ)) (Q := Q)
        continuousOn_const hQ_cont)
  have hP_form_cont : ContinuousOn (P dx + (0 : ℂ → ℝ) dy) C := by
    -- The `P dx` half-form is handled symmetrically.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := C) (P := P) (Q := (0 : ℂ → ℝ))
        hP_cont continuousOn_const)
  have hρ_intQ : ∀ i ∈ s, CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) (ρ i) := by
    intro i hi
    -- Connector paths are integrable against the `Q dy` half-form because they stay in `C`.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hQ_form_cont (hρ_piece i hi) (hρ_mem i hi)
  have hρ_intP : ∀ i ∈ s, CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (ρ i) := by
    intro i hi
    -- The same continuity-on-`C` argument works for the `P dx` half-form.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hP_form_cont (hρ_piece i hi) (hρ_mem i hi)
  have hΓ_intQ : ∀ i ∈ s, CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) ((Γ i).toPath) := by
    intro i hi
    -- Rectangle boundaries are integrable against the `Q dy` half-form because they stay in `C`.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hQ_form_cont (hΓ_piece i hi) (hΓ_mem i hi)
  have hΓ_intP : ∀ i ∈ s, CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) ((Γ i).toPath) := by
    intro i hi
    -- The same argument closes the `P dx` integrability on each rectangle boundary.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hP_form_cont (hΓ_piece i hi) (hΓ_mem i hi)
  let γ : Path z0 z0 := OrientedBoundaryApproximation.rootedBoundaryLoop s Γ ρ
  rcases rootedBoundaryLoop_spec (C := C) (ω := (((0 : ℂ → ℝ) dx + Q dy))) s Γ ρ hz0C
      hρ_piece hΓ_piece hρ_mem hΓ_mem hρ_intQ hΓ_intQ with
    ⟨hγ_piece, hγ_mem, hγ_intQ, hγ_eqQ⟩
  rcases rootedBoundaryLoop_spec (C := C) (ω := (P dx + (0 : ℂ → ℝ) dy)) s Γ ρ hz0C
      hρ_piece hΓ_piece hρ_mem hΓ_mem hρ_intP hΓ_intP with
    ⟨-, -, hγ_intP, hγ_eqP⟩
  refine ⟨γ, hγ_piece, hγ_mem, hγ_intQ, hγ_intP, ?_, ?_⟩
  · -- Replace the auxiliary `ClosedPath` wrapper on each rectangle boundary by the original path.
    calc
      ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
          Finset.sum s (fun i ↦ ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) := hγ_eqQ
      _ =
          Finset.sum s (fun i ↦
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z i) (w i),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [Γ] using
          curveIntegral_toClosedPath_toPath_eq
            ((((0 : ℂ → ℝ) dx + Q dy))) (axisParallelRectangleBoundaryPath (z i) (w i))
  · -- The same wrapper removal gives the exact `P dx` stage formula.
    calc
      ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ =
          Finset.sum s (fun i ↦ ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) := hγ_eqP
      _ =
          Finset.sum s (fun i ↦
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z i) (w i),
              (P dx + (0 : ℂ → ℝ) dy) ζ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [Γ] using
          curveIntegral_toClosedPath_toPath_eq
            ((P dx + (0 : ℂ → ℝ) dy)) (axisParallelRectangleBoundaryPath (z i) (w i))

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: fixing one basepoint `z0 ∈ C`,
every rectangle stage inside `interior K` can be turned into a rooted loop in the same connected
ambient set `C`, while preserving the stagewise contour sums of the two coordinate half-forms. -/
theorem existsRootedRectangleStageLoopFamilyInConnectedOpen
    {C K : Set ℂ} {z0 : ℂ}
    (hz0C : z0 ∈ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {P Q : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C)
    (hKC : K ⊆ C)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∃ γStage : ∀ n, Path z0 z0,
      (∀ n, (γStage n).IsPiecewiseDifferentiable) ∧
      (∀ n, Set.range (γStage n) ⊆ C) ∧
      (∀ n, CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) (γStage n)) ∧
      (∀ n, CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (γStage n)) ∧
      (∀ n,
        ∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (((0 : ℂ → ℝ) dx + Q dy)) ζ) ∧
      (∀ n,
        ∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
              (P dx + (0 : ℂ → ℝ) dy) ζ) := by
  classical
  let γStage : ∀ n, Path z0 z0 := fun n ↦
    Classical.choose
      (rootedRectangleStageLoop_spec
        (s := (Finset.univ : Finset (Fin (N n))))
        (C := C) hz0C hC_open hC_connected (z n) (w n) hP_cont hQ_cont
        (fun s hs => by
          -- Push the rectangle containment through `interior K ⊆ K ⊆ C`.
          exact Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)))
  have hγStageSpec :
      ∀ n,
        (γStage n).IsPiecewiseDifferentiable ∧
          Set.range (γStage n) ⊆ C ∧
          CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) (γStage n) ∧
          CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (γStage n) ∧
          (∫ᶜ ζ in γStage n, (((0 : ℂ → ℝ) dx + Q dy)) ζ =
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (((0 : ℂ → ℝ) dx + Q dy)) ζ) ∧
          (∫ᶜ ζ in γStage n, (P dx + (0 : ℂ → ℝ) dy) ζ =
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s),
                (P dx + (0 : ℂ → ℝ) dy) ζ) := by
    intro n
    exact
      Classical.choose_spec
        (rootedRectangleStageLoop_spec
          (s := (Finset.univ : Finset (Fin (N n))))
          (C := C) hz0C hC_open hC_connected (z n) (w n) hP_cont hQ_cont
          (fun s hs => by
            -- The same rectangle-to-domain containment is needed for the chosen stage loop.
            exact Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)))
  refine ⟨γStage, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hγStageSpec n).1
  · intro n
    exact (hγStageSpec n).2.1
  · intro n
    exact (hγStageSpec n).2.2.1
  · intro n
    exact (hγStageSpec n).2.2.2.1
  · intro n
    exact (hγStageSpec n).2.2.2.2.1
  · intro n
    exact (hγStageSpec n).2.2.2.2.2

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: the rooted-loop construction has a
stable topology-only output even before any contour-integrability input is supplied. -/
theorem rootedBoundaryLoop_topology
    {ι : Type u} [DecidableEq ι] {C : Set ℂ} {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρ_piece : ∀ i ∈ s, (ρ i).IsPiecewiseDifferentiable)
    (hΓ_piece : ∀ i ∈ s, ((Γ i).toPath).IsPiecewiseDifferentiable)
    (hρC : ∀ i ∈ s, Set.range (ρ i) ⊆ C)
    (hΓC : ∀ i ∈ s, Set.range ((Γ i).toPath) ⊆ C) :
    (rootedBoundaryLoop s Γ ρ).IsPiecewiseDifferentiable ∧
      Set.range (rootedBoundaryLoop s Γ ρ) ⊆ C := by
  have hρ_zero : ∀ i ∈ s, CurveIntegrable (0 : ℂ → ℂ →L[ℝ] ℂ) (ρ i) := by
    intro i hi
    simpa using (CurveIntegrable.zero : CurveIntegrable (0 : ℂ → ℂ →L[ℝ] ℂ) (ρ i))
  have hΓ_zero : ∀ i ∈ s, CurveIntegrable (0 : ℂ → ℂ →L[ℝ] ℂ) ((Γ i).toPath) := by
    intro i hi
    simpa using (CurveIntegrable.zero : CurveIntegrable (0 : ℂ → ℂ →L[ℝ] ℂ) ((Γ i).toPath))
  rcases rootedBoundaryLoop_spec (C := C) (ω := (0 : ℂ → ℂ →L[ℝ] ℂ)) s Γ ρ hz0C
      hρ_piece hΓ_piece hρC hΓC hρ_zero hΓ_zero with
    ⟨hloop_piece, hloopC, -, -⟩
  exact ⟨hloop_piece, hloopC⟩

end OrientedBoundaryApproximation

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: a connected open ambient set provides
one common boundary-loop basepoint together with connector paths from that root to every boundary
basepoint, all remaining inside the ambient set. -/
private theorem connectedOpenConnectorFamily
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C) :
    ∃ i0 : ι, ∃ ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
      (∀ i, (ρ i).IsPiecewiseDifferentiable) ∧
      (∀ i, Set.range (ρ i) ⊆ C) := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hi0C : (Γ i0).toPath 0 ∈ C := by
    exact rangeToPathSubsetDomainOfOrientedBoundary hΓ hKC i0 ⟨0, by simp⟩
  have hconnector :
      ∀ i : ι,
        ∃ ρ : Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
          ρ.IsPiecewiseDifferentiable ∧
          Set.range ρ ⊆ C := by
    intro i
    have hiC : (Γ i).toPath 0 ∈ C := by
      exact rangeToPathSubsetDomainOfOrientedBoundary hΓ hKC i ⟨0, by simp⟩
    -- Connectedness of the ambient set gives a connector between the common root and the current
    -- boundary basepoint.
    obtain ⟨ρ, hρ_piece, hρ_mem⟩ :=
      exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
        hC_open hC_connected hi0C hiC
    refine ⟨ρ, hρ_piece, ?_⟩
    intro z hz
    rcases hz with ⟨t, rfl⟩
    exact hρ_mem t
  choose ρ hρ_piece hρ_mem using hconnector
  exact ⟨i0, ρ, hρ_piece, hρ_mem⟩

/-- Helper for Cartan section05 0035_Theorem_II_1_extra_22: in a connected open ambient set, the
full oriented-boundary family can be compressed to one rooted loop that preserves the contour
integrals of the two coordinate half-forms. -/
theorem IsOrientedBoundaryOf.existsRootedBoundaryLoopWithSameCoordinateHalfIntegralsConnectedOpen
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    {P Q : ℂ → ℝ}
    (hP_cont : ContinuousOn P C) (hQ_cont : ContinuousOn Q C) :
    ∃ z0 : ℂ, ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C ∧
      CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) γ ∧
      CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) γ ∧
      ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (((0 : ℂ → ℝ) dx + Q dy)) ζ) =
        ∫ᶜ ζ in γ, (((0 : ℂ → ℝ) dx + Q dy)) ζ) ∧
      ((∑ i, ∫ᶜ ζ in (Γ i).toPath, (P dx + (0 : ℂ → ℝ) dy) ζ) =
        ∫ᶜ ζ in γ, (P dx + (0 : ℂ → ℝ) dy) ζ) := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρ_mem⟩ :=
    connectedOpenConnectorFamily hΓ hKC hC_open hC_connected
  let z0 : ℂ := (Γ i0).toPath 0
  have hz0C : z0 ∈ C := by
    -- The chosen rooted-loop basepoint is already one boundary basepoint.
    simpa [z0] using rangeToPathSubsetDomainOfOrientedBoundary hΓ hKC i0 ⟨0, by simp⟩
  have hΓ_piece :
      ∀ i ∈ (Finset.univ : Finset ι), ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    -- The oriented-boundary structure already stores the piecewise differentiability of each loop.
    simpa using hΓ.piecewiseDifferentiable i
  have hΓ_mem :
      ∀ i ∈ (Finset.univ : Finset ι), Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    -- Every boundary loop stays in the connected ambient set because `K ⊆ C`.
    exact rangeToPathSubsetDomainOfOrientedBoundary hΓ hKC i
  have hQ_form_cont : ContinuousOn (((0 : ℂ → ℝ) dx + Q dy)) C := by
    -- The `Q dy` half-form inherits continuity from `Q`.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := C) (P := (0 : ℂ → ℝ)) (Q := Q)
        continuousOn_const hQ_cont)
  have hP_form_cont : ContinuousOn (P dx + (0 : ℂ → ℝ) dy) C := by
    -- The `P dx` half-form is handled symmetrically.
    simpa using
      (Complex.planarDifferentialForm_continuousOn (D := C) (P := P) (Q := (0 : ℂ → ℝ))
        hP_cont continuousOn_const)
  have hρ_piece_univ :
      ∀ i ∈ (Finset.univ : Finset ι), (ρ i).IsPiecewiseDifferentiable := by
    intro i hi
    exact hρ_piece i
  have hρ_mem_univ :
      ∀ i ∈ (Finset.univ : Finset ι), Set.range (ρ i) ⊆ C := by
    intro i hi
    exact hρ_mem i
  have hρ_intQ :
      ∀ i ∈ (Finset.univ : Finset ι), CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) (ρ i) := by
    intro i hi
    -- Continuity on `C` makes every connector path integrable against the `Q dy` half-form.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hQ_form_cont (hρ_piece_univ i hi) (hρ_mem_univ i hi)
  have hρ_intP :
      ∀ i ∈ (Finset.univ : Finset ι), CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) (ρ i) := by
    intro i hi
    -- The same continuity argument gives integrability for the `P dx` half-form.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hP_form_cont (hρ_piece_univ i hi) (hρ_mem_univ i hi)
  have hΓ_intQ :
      ∀ i ∈ (Finset.univ : Finset ι), CurveIntegrable (((0 : ℂ → ℝ) dx + Q dy)) ((Γ i).toPath) := by
    intro i hi
    -- Boundary loops are integrable against the `Q dy` half-form because they already lie in `C`.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hQ_form_cont (hΓ_piece i hi) (hΓ_mem i hi)
  have hΓ_intP :
      ∀ i ∈ (Finset.univ : Finset ι), CurveIntegrable (P dx + (0 : ℂ → ℝ) dy) ((Γ i).toPath) := by
    intro i hi
    -- The same continuity-on-domain argument applies to the `P dx` half-form.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        hP_form_cont (hΓ_piece i hi) (hΓ_mem i hi)
  let γ : Path z0 z0 := OrientedBoundaryApproximation.rootedBoundaryLoop Finset.univ Γ ρ
  rcases
      OrientedBoundaryApproximation.rootedBoundaryLoop_spec
        (C := C) (ω := (((0 : ℂ → ℝ) dx + Q dy))) (s := Finset.univ) Γ ρ hz0C
        hρ_piece_univ hΓ_piece hρ_mem_univ hΓ_mem hρ_intQ hΓ_intQ with
    ⟨hγ_piece, hγ_mem, hγ_intQ, hγ_eqQ⟩
  rcases
      OrientedBoundaryApproximation.rootedBoundaryLoop_spec
        (C := C) (ω := (P dx + (0 : ℂ → ℝ) dy)) (s := Finset.univ) Γ ρ hz0C
        hρ_piece_univ hΓ_piece hρ_mem_univ hΓ_mem hρ_intP hΓ_intP with
    ⟨-, -, hγ_intP, hγ_eqP⟩
  refine ⟨z0, γ, hγ_piece, hγ_mem, hγ_intQ, hγ_intP, ?_, ?_⟩
  · -- The rooted-loop package rewrites the total `Q dy` contour sum to the single loop integral.
    simpa [γ] using hγ_eqQ.symm
  · -- The same rooted loop also preserves the total `P dx` contour sum.
    simpa [γ] using hγ_eqP.symm
