import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».BoundaryComponentGeometry
import DifferentialForms_Cartan_1970.II.section05.«0036_Corollary_II_1_extra_23».ClosedPathTransportBasics

open scoped BigOperators unitInterval

universe u

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: one boundary-loop basepoint of an
oriented boundary family already lies in every ambient domain containing the compact set. -/
private theorem boundaryPathBasepoint_mem_domain_of_orientedBoundary
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (i : ι) :
    (Γ i).toPath 0 ∈ D := by
  -- Specialize the global range inclusion to the initial parameter value of the chosen loop.
  exact range_toPath_subset_domain_of_orientedBoundary hΓ hKD i ⟨0, by simp⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a connected open ambient set
provides one common boundary basepoint together with piecewise differentiable connector paths from
that basepoint to every boundary-loop basepoint. -/
private theorem connectedOpenConnectorFamily
    {ι : Type u} [Nonempty ι] {C : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (hΓC : ∀ i, Set.range (Γ i).toPath ⊆ C) :
    ∃ i0 : ι, ∃ ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
      (∀ i, (ρ i).IsPiecewiseDifferentiable) ∧
      (∀ i t, ρ i t ∈ C) := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hi0C : (Γ i0).toPath 0 ∈ C := by
    exact hΓC i0 ⟨0, by simp⟩
  have hconnector :
      ∀ i : ι,
        ∃ ρ : Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
          ρ.IsPiecewiseDifferentiable ∧ ∀ t, ρ t ∈ C := by
    intro i
    have hiC : (Γ i).toPath 0 ∈ C := by
      exact hΓC i ⟨0, by simp⟩
    -- Connectedness is used only to join the common root to the current boundary-loop basepoint.
    simpa using
      exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
        hC_open hC_connected hi0C hiC
  choose ρ hρ_piece hρC using hconnector
  exact ⟨i0, ρ, hρ_piece, hρC⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: conjugating a loop by a connector
preserves piecewise differentiability. -/
theorem connectorConjugatedLoop_isPiecewiseDifferentiable
    {z0 z1 : ℂ} {ρ : Path z0 z1} {γ : Path z1 z1}
    (hρ_piece : ρ.IsPiecewiseDifferentiable)
    (hγ_piece : γ.IsPiecewiseDifferentiable) :
    ((ρ.trans γ).trans ρ.symm).IsPiecewiseDifferentiable := by
  -- First concatenate the connector with the loop, then append the reverse connector.
  exact (hρ_piece.trans hγ_piece).trans hρ_piece.symm

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if a connector and a loop both stay
inside `C`, then the connector-conjugated loop also stays inside `C`. -/
theorem connectorConjugatedLoop_range_subset
    {C : Set ℂ} {z0 z1 : ℂ} {ρ : Path z0 z1} {γ : Path z1 z1}
    (hρC : Set.range ρ ⊆ C) (hγC : Set.range γ ⊆ C) :
    Set.range ((ρ.trans γ).trans ρ.symm) ⊆ C := by
  intro z hz
  rw [Path.trans_range] at hz
  rcases hz with hz | hz
  · rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · exact hρC hz
    · exact hγC hz
  · have hzρ : z ∈ Set.range ρ := by
      simpa [Path.symm_range] using hz
    exact hρC hzρ

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: connector conjugation preserves
curve-integrability once both the connector and the loop are curve-integrable. -/
theorem connectorConjugatedLoop_curveIntegrable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {z0 z1 : ℂ} {ω : ℂ → ℂ →L[ℝ] F} {ρ : Path z0 z1} {γ : Path z1 z1}
    (hρ_int : CurveIntegrable ω ρ) (hγ_int : CurveIntegrable ω γ) :
    CurveIntegrable ω ((ρ.trans γ).trans ρ.symm) := by
  -- Concatenating the forward connector, the loop, and the reverse connector preserves
  -- integrability.
  exact (hρ_int.trans hγ_int).trans hρ_int.symm

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: from a finite family of
connector-conjugated boundary loops, one can build a single rooted loop with the same contour sum
as soon as all pieces are piecewise differentiable and curve-integrable. -/
theorem exists_rootedBoundaryLoop_with_same_integral
    {ι : Type u} (s : Finset ι) {z0 : ℂ}
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hρ_piece : ∀ i ∈ s, (ρ i).IsPiecewiseDifferentiable)
    (hΓ_piece : ∀ i ∈ s, ((Γ i).toPath).IsPiecewiseDifferentiable)
    (hρ_int : ∀ i ∈ s, CurveIntegrable ω (ρ i))
    (hΓ_int : ∀ i ∈ s, CurveIntegrable ω ((Γ i).toPath)) :
    ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      CurveIntegrable ω γ ∧
      (∫ᶜ z in γ, ω z = s.sum fun i => ∫ᶜ z in (Γ i).toPath, ω z) := by
  classical
  revert hρ_piece hΓ_piece hρ_int hΓ_int
  refine Finset.induction_on s ?_ ?_
  · intro _ _ _ _
    -- The empty family contributes the constant rooted loop and the empty contour sum.
    refine ⟨Path.refl z0, Path.isPiecewiseDifferentiable_refl z0, CurveIntegrable.refl ω z0, ?_⟩
    simp
  · intro i s hi ih hρ_piece hΓ_piece hρ_int hΓ_int
    have hρs : ∀ j ∈ s, (ρ j).IsPiecewiseDifferentiable := by
      intro j hj
      exact hρ_piece j (by simp [hj])
    have hΓs : ∀ j ∈ s, ((Γ j).toPath).IsPiecewiseDifferentiable := by
      intro j hj
      exact hΓ_piece j (by simp [hj])
    have hρs_int : ∀ j ∈ s, CurveIntegrable ω (ρ j) := by
      intro j hj
      exact hρ_int j (by simp [hj])
    have hΓs_int : ∀ j ∈ s, CurveIntegrable ω ((Γ j).toPath) := by
      intro j hj
      exact hΓ_int j (by simp [hj])
    rcases ih hρs hΓs hρs_int hΓs_int with ⟨γs, hγs_piece, hγs_int, hγs_eq⟩
    have hρi_piece : (ρ i).IsPiecewiseDifferentiable := hρ_piece i (by simp)
    have hΓi_piece : ((Γ i).toPath).IsPiecewiseDifferentiable := hΓ_piece i (by simp)
    have hρi_int : CurveIntegrable ω (ρ i) := hρ_int i (by simp)
    have hΓi_int : CurveIntegrable ω ((Γ i).toPath) := hΓ_int i (by simp)
    let γ : Path z0 z0 := γs.trans ((ρ i).trans ((Γ i).toPath.trans (ρ i).symm))
    have hγ_piece : γ.IsPiecewiseDifferentiable := by
      -- Append one connector-conjugated boundary loop to the already constructed rooted loop.
      dsimp [γ]
      exact hγs_piece.trans (hρi_piece.trans (hΓi_piece.trans hρi_piece.symm))
    have hγ_int : CurveIntegrable ω γ := by
      -- The same concatenation preserves curve-integrability.
      dsimp [γ]
      exact hγs_int.trans (hρi_int.trans (hΓi_int.trans hρi_int.symm))
    have hconj :
        ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
          ∫ᶜ z in (Γ i).toPath, ω z := by
      -- Expand the connector-conjugated loop and cancel the reverse connector term.
      calc
        ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
            ∫ᶜ z in ρ i, ω z + ∫ᶜ z in ((Γ i).toPath.trans (ρ i).symm), ω z := by
          simpa using curveIntegral_trans hρi_int (hΓi_int.trans hρi_int.symm)
        _ = ∫ᶜ z in ρ i, ω z +
              (∫ᶜ z in (Γ i).toPath, ω z + ∫ᶜ z in (ρ i).symm, ω z) := by
          exact congrArg (fun t => ∫ᶜ z in ρ i, ω z + t) (curveIntegral_trans hΓi_int hρi_int.symm)
        _ = ∫ᶜ z in (Γ i).toPath, ω z := by
          rw [curveIntegral_symm]
          ring
    refine ⟨γ, hγ_piece, hγ_int, ?_⟩
    -- Compare the new rooted loop integral with the previous rooted loop and then with the new
    -- boundary term.
    calc
      ∫ᶜ z in γ, ω z =
          ∫ᶜ z in γs, ω z + ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z := by
        simpa [γ] using
          curveIntegral_trans hγs_int (hρi_int.trans (hΓi_int.trans hρi_int.symm))
      _ = s.sum (fun j => ∫ᶜ z in (Γ j).toPath, ω z) + ∫ᶜ z in (Γ i).toPath, ω z := by
        rw [hγs_eq, hconj]
      _ = (insert i s).sum (fun j => ∫ᶜ z in (Γ j).toPath, ω z) := by
        simp [Finset.sum_insert, hi, add_comm]

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: recursively concatenate the
connector-conjugated boundary loops listed in `l` to obtain one rooted loop based at `z0`. -/
noncomputable def rootedBoundaryLoopList
    {ι : Type u} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0)) : Path z0 z0 :=
  match l with
  | [] => Path.refl z0
  | i :: l' =>
      (rootedBoundaryLoopList l' Γ ρ).trans ((ρ i).trans ((Γ i).toPath.trans (ρ i).symm))

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the explicit rooted loop attached to
a finite family of boundary components is obtained by running the recursive concatenation over the
`Finset` enumeration. -/
noncomputable def rootedBoundaryLoop
    {ι : Type u} [DecidableEq ι] {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0)) : Path z0 z0 :=
  rootedBoundaryLoopList s.toList Γ ρ

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the recursive rooted loop is
piecewise differentiable, stays in `C`, is curve-integrable, and its contour integral is the sum
of the boundary integrals of the listed components. -/
theorem rootedBoundaryLoopList_spec
    {ι : Type u} {C : Set ℂ} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {ω : ℂ → ℂ →L[ℝ] ℂ}
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
      have hconjC :
          Set.range ((ρ i).trans ((Γ i).toPath.trans (ρ i).symm)) ⊆ C := by
        intro z hz
        rw [Path.trans_range] at hz
        rcases hz with hz | hz
        · exact hρiC hz
        · have hz' : z ∈ Set.range ((Γ i).toPath.trans (ρ i).symm) := hz
          rw [Path.trans_range] at hz'
          rcases hz' with hz | hz
          · exact hΓiC hz
          · have hzρ : z ∈ Set.range (ρ i) := by
              let hrange : Set.range (ρ i).symm = Set.range (ρ i) := Path.symm_range (ρ i)
              exact hrange ▸ hz
            exact hρiC hzρ
      have hconjEq :
          ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
            ∫ᶜ z in (Γ i).toPath, ω z := by
        -- Expand the connector-conjugated loop and cancel the reverse connector contribution.
        calc
          ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z =
              ∫ᶜ z in ρ i, ω z + ∫ᶜ z in ((Γ i).toPath.trans (ρ i).symm), ω z := by
            simpa using curveIntegral_trans hρi_int (hΓi_int.trans hρi_int.symm)
          _ = ∫ᶜ z in ρ i, ω z +
                (∫ᶜ z in (Γ i).toPath, ω z + ∫ᶜ z in (ρ i).symm, ω z) := by
            exact congrArg (fun t => ∫ᶜ z in ρ i, ω z + t)
              (curveIntegral_trans hΓi_int hρi_int.symm)
          _ = ∫ᶜ z in (Γ i).toPath, ω z := by
            rw [curveIntegral_symm]
            ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Appending one connector-conjugated boundary loop preserves piecewise differentiability.
        dsimp [rootedBoundaryLoopList]
        exact hloop_piece.trans (hρi_piece.trans (hΓi_piece.trans hρi_piece.symm))
      · -- The recursive loop remains in `C` because every new connector and boundary piece does.
        rw [rootedBoundaryLoopList, Path.trans_range]
        exact Set.union_subset hloopC hconjC
      · -- Curve integrability is stable under the same concatenation.
        simpa [rootedBoundaryLoopList] using
          hloop_int.trans (hρi_int.trans (hΓi_int.trans hρi_int.symm))
      · -- The rooted-loop contour is the sum of the previous stage and the new boundary term.
        calc
          ∫ᶜ z in rootedBoundaryLoopList (i :: l) Γ ρ, ω z =
              ∫ᶜ z in rootedBoundaryLoopList l Γ ρ, ω z +
                ∫ᶜ z in (ρ i).trans ((Γ i).toPath.trans (ρ i).symm), ω z := by
            simpa [rootedBoundaryLoopList] using
              curveIntegral_trans hloop_int (hρi_int.trans (hΓi_int.trans hρi_int.symm))
          _ = (l.map fun j => ∫ᶜ z in (Γ j).toPath, ω z).sum +
                ∫ᶜ z in (Γ i).toPath, ω z := by
            rw [hloop_eq, hconjEq]
          _ = ((i :: l).map fun j => ∫ᶜ z in (Γ j).toPath, ω z).sum := by
            simp [add_comm]

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the `Finset`-indexed rooted loop
inherits the same regularity, range, integrability, and contour-sum formula from the recursive
list construction. -/
theorem rootedBoundaryLoop_spec
    {ι : Type u} [DecidableEq ι] {C : Set ℂ} {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    {ω : ℂ → ℂ →L[ℝ] ℂ}
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
    exact hρ_piece i ((Finset.mem_toList.1 hi))
  have hΓ_piece_list : ∀ i, i ∈ s.toList → ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    exact hΓ_piece i ((Finset.mem_toList.1 hi))
  have hρC_list : ∀ i, i ∈ s.toList → Set.range (ρ i) ⊆ C := by
    intro i hi
    exact hρC i ((Finset.mem_toList.1 hi))
  have hΓC_list : ∀ i, i ∈ s.toList → Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    exact hΓC i ((Finset.mem_toList.1 hi))
  have hρ_int_list : ∀ i, i ∈ s.toList → CurveIntegrable ω (ρ i) := by
    intro i hi
    exact hρ_int i ((Finset.mem_toList.1 hi))
  have hΓ_int_list : ∀ i, i ∈ s.toList → CurveIntegrable ω ((Γ i).toPath) := by
    intro i hi
    exact hΓ_int i ((Finset.mem_toList.1 hi))
  rcases rootedBoundaryLoopList_spec (C := C) s.toList Γ ρ hz0C
      hρ_piece_list hΓ_piece_list hρC_list hΓC_list hρ_int_list hΓ_int_list with
    ⟨hloop_piece, hloopC, hloop_int, hloop_eq⟩
  refine ⟨hloop_piece, hloopC, hloop_int, ?_⟩
  -- Convert the list sum back to the canonical `Finset` sum over `s`.
  calc
    ∫ᶜ z in rootedBoundaryLoop s Γ ρ, ω z =
        (s.toList.map fun i => ∫ᶜ z in (Γ i).toPath, ω z).sum := hloop_eq
    _ = (Multiset.map (fun i => ∫ᶜ z in (Γ i).toPath, ω z) s.val).sum := by
      exact
        (Multiset.sum_map_toList s.val (fun i => ∫ᶜ z in (Γ i).toPath, ω z))
    _ = s.sum (fun i => ∫ᶜ z in (Γ i).toPath, ω z) := by
      rw [Finset.sum]

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once curve integrability is
available for every piecewise differentiable path in `C`, each finite rectangle stage inside
`interior K` compresses to one rooted loop in the same ambient domain while preserving the exact
stage contour sum for `ω`. -/
theorem existsRootedRectangleStageLoopFamilyInConnectedOpen_of_pathwiseCurveIntegrable
    {C K : Set ℂ} {z0 : ℂ}
    (hz0C : z0 ∈ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (hKC : K ⊆ C)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hpath_int :
      ∀ {x y : ℂ} {γ : Path x y},
        γ.IsPiecewiseDifferentiable → Set.range γ ⊆ C → CurveIntegrable ω γ)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∃ γStage : ∀ n, Path z0 z0,
      (∀ n, (γStage n).IsPiecewiseDifferentiable) ∧
      (∀ n, Set.range (γStage n) ⊆ C) ∧
      (∀ n, CurveIntegrable ω (γStage n)) ∧
      (∀ n,
        ∫ᶜ ζ in γStage n, ω ζ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) := by
  classical
  have hstage :
      ∀ n,
        ∃ γ : Path z0 z0,
          γ.IsPiecewiseDifferentiable ∧
          Set.range γ ⊆ C ∧
          CurveIntegrable ω γ ∧
          (∫ᶜ ζ in γ, ω ζ =
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) := by
    intro n
    let Γ : Fin (N n) → ClosedPath ℂ :=
      fun s ↦ (axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath
    have hz_mem : ∀ s : Fin (N n), z n s ∈ C := by
      intro s
      have hz_rect : z n s ∈ Complex.Rectangle (z n s) (w n s) := by
        simp [Complex.Rectangle, Complex.mem_reProdIm]
      exact
        (Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)) hz_rect
    have hΓ_base_eq : ∀ s : Fin (N n), ((Γ s).toPath 0) = z n s := by
      intro s
      change (((axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath).toPath 0) =
        z n s
      rw [loopToClosedPath_toPath_eq_cast]
      calc
        ((axisParallelRectangleBoundaryPath (z n s) (w n s)).cast _ _) 0 =
            (axisParallelRectangleBoundaryPath (z n s) (w n s)) 0 := by
          exact congrFun (Path.cast_coe (axisParallelRectangleBoundaryPath (z n s) (w n s)) _ _) 0
        _ = z n s := by
          simp [axisParallelRectangleBoundaryPath]
    have hΓ_base_mem : ∀ s : Fin (N n), ((Γ s).toPath 0) ∈ C := by
      intro s
      simpa [hΓ_base_eq s] using hz_mem s
    have hconnector :
        ∀ s : Fin (N n),
          ∃ ρ : Path z0 ((Γ s).toPath 0),
            ρ.IsPiecewiseDifferentiable ∧ Set.range ρ ⊆ C := by
      intro s
      obtain ⟨ρ, hρ_piece, hρ_mem⟩ :=
        exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
          hC_open hC_connected hz0C (hΓ_base_mem s)
      refine ⟨ρ, hρ_piece, ?_⟩
      rintro ζ ⟨t, rfl⟩
      exact hρ_mem t
    let ρ : ∀ s : Fin (N n), Path z0 ((Γ s).toPath 0) := fun s ↦ Classical.choose (hconnector s)
    have hρ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), (ρ s).IsPiecewiseDifferentiable := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).1
    have hρ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range (ρ s) ⊆ C := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).2
    have hΓ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), ((Γ s).toPath).IsPiecewiseDifferentiable := by
      intro s hs
      simpa [Γ, Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z n s) (w n s)
    have hΓ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range ((Γ s).toPath) ⊆ C := by
      intro s hs
      intro ζ hζ
      have hζ_rect : ζ ∈ Complex.Rectangle (z n s) (w n s) := by
        have hζ' : ζ ∈ Set.range (axisParallelRectangleBoundaryPath (z n s) (w n s)) := by
          simpa [Γ, Path.toClosedPath] using hζ
        exact axisParallelRectangleBoundaryPath_range_subset_rectangle (z n s) (w n s) hζ'
      exact
        Set.Subset.trans
          (hRectSubset n s)
          (Set.Subset.trans interior_subset hKC)
          hζ_rect
    have hρ_int :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), CurveIntegrable ω (ρ s) := by
      intro s hs
      exact hpath_int (hρ_piece s hs) (hρ_mem s hs)
    have hΓ_int :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), CurveIntegrable ω ((Γ s).toPath) := by
      intro s hs
      exact hpath_int (hΓ_piece s hs) (hΓ_mem s hs)
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    rcases
      rootedBoundaryLoop_spec
        (C := C) (ω := ω) (s := Finset.univ) Γ ρ hz0C
        hρ_piece hΓ_piece hρ_mem hΓ_mem hρ_int hΓ_int with
      ⟨hγ_piece, hγ_mem, hγ_int, hγ_eq⟩
    refine ⟨γ, hγ_piece, hγ_mem, hγ_int, ?_⟩
    -- Replace the auxiliary `ClosedPath` wrappers by the original rectangle boundary paths.
    calc
      ∫ᶜ ζ in γ, ω ζ =
          ∑ s : Fin (N n), ∫ᶜ ζ in (Γ s).toPath, ω ζ := hγ_eq
      _ =
          ∑ s : Fin (N n),
            ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        simpa [Γ] using
          curveIntegral_toClosedPath_toPath_eq
            ω (axisParallelRectangleBoundaryPath (z n s) (w n s))
  let γStage : ∀ n, Path z0 z0 := fun n ↦ Classical.choose (hstage n)
  have hγStageSpec :
      ∀ n,
        (γStage n).IsPiecewiseDifferentiable ∧
          Set.range (γStage n) ⊆ C ∧
          CurveIntegrable ω (γStage n) ∧
          (∫ᶜ ζ in γStage n, ω ζ =
            ∑ s : Fin (N n),
              ∫ᶜ ζ in axisParallelRectangleBoundaryPath (z n s) (w n s), ω ζ) := by
    intro n
    exact Classical.choose_spec (hstage n)
  refine ⟨γStage, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hγStageSpec n).1
  · intro n
    exact (hγStageSpec n).2.1
  · intro n
    exact (hγStageSpec n).2.2.1
  · intro n
    exact (hγStageSpec n).2.2.2

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the rooted-loop construction has a
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

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected open ambient set,
one can root every finite rectangle stage at a prescribed basepoint and keep the whole rooted loop
inside `C` without using any contour-integrability input. -/
theorem existsRootedRectangleStageLoopFamilyInConnectedOpen_topology
    {C K : Set ℂ} {z0 : ℂ}
    (hz0C : z0 ∈ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (hKC : K ⊆ C)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∃ γStage : ∀ n : ℕ, Path z0 z0,
      (∀ n : ℕ, (γStage n).IsPiecewiseDifferentiable) ∧
      (∀ n : ℕ, Set.range (γStage n) ⊆ C) := by
  classical
  have hstage :
      ∀ n : ℕ, ∃ γ : Path z0 z0, γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
    intro n
    let Γ : Fin (N n) → ClosedPath ℂ :=
      fun s ↦ (axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath
    have hz_mem : ∀ s : Fin (N n), z n s ∈ C := by
      intro s
      have hz_rect : z n s ∈ Complex.Rectangle (z n s) (w n s) := by
        simp [Complex.Rectangle, Complex.mem_reProdIm]
      exact
        (Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)) hz_rect
    have hΓ_base_eq : ∀ s : Fin (N n), ((Γ s).toPath 0) = z n s := by
      intro s
      change (((axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath).toPath 0) =
        z n s
      rw [loopToClosedPath_toPath_eq_cast]
      calc
        ((axisParallelRectangleBoundaryPath (z n s) (w n s)).cast _ _) 0 =
            (axisParallelRectangleBoundaryPath (z n s) (w n s)) 0 := by
          exact congrFun (Path.cast_coe (axisParallelRectangleBoundaryPath (z n s) (w n s)) _ _) 0
        _ = z n s := by
          simp [axisParallelRectangleBoundaryPath]
    have hΓ_base_mem : ∀ s : Fin (N n), ((Γ s).toPath 0) ∈ C := by
      intro s
      simpa [hΓ_base_eq s] using hz_mem s
    have hconnector :
        ∀ s : Fin (N n),
          ∃ ρ : Path z0 ((Γ s).toPath 0),
            ρ.IsPiecewiseDifferentiable ∧ Set.range ρ ⊆ C := by
      intro s
      obtain ⟨ρ, hρ_piece, hρ_mem⟩ :=
        exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
          hC_open hC_connected hz0C (hΓ_base_mem s)
      refine ⟨ρ, hρ_piece, ?_⟩
      rintro ζ ⟨t, rfl⟩
      exact hρ_mem t
    let ρ : ∀ s : Fin (N n), Path z0 ((Γ s).toPath 0) := fun s ↦ Classical.choose (hconnector s)
    have hρ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), (ρ s).IsPiecewiseDifferentiable := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).1
    have hρ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range (ρ s) ⊆ C := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).2
    have hΓ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), ((Γ s).toPath).IsPiecewiseDifferentiable := by
      intro s hs
      simpa [Γ, Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z n s) (w n s)
    have hΓ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range ((Γ s).toPath) ⊆ C := by
      intro s hs
      intro ζ hζ
      have hζ_rect : ζ ∈ Complex.Rectangle (z n s) (w n s) := by
        have hζ' : ζ ∈ Set.range (axisParallelRectangleBoundaryPath (z n s) (w n s)) := by
          simpa [Γ, Path.toClosedPath] using hζ
        exact axisParallelRectangleBoundaryPath_range_subset_rectangle (z n s) (w n s) hζ'
      exact
        Set.Subset.trans
          (hRectSubset n s)
          (Set.Subset.trans interior_subset hKC)
          hζ_rect
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    have hγ_top :
        γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
      -- The rooted-loop topology package is exactly the ambient-range data needed later.
      exact
        rootedBoundaryLoop_topology
          (C := C) (s := Finset.univ) Γ ρ hz0C hρ_piece hΓ_piece hρ_mem hΓ_mem
    exact ⟨γ, hγ_top.1, hγ_top.2⟩
  let γStage : ∀ n, Path z0 z0 := fun n ↦ Classical.choose (hstage n)
  have hγStageSpec :
      ∀ n, (γStage n).IsPiecewiseDifferentiable ∧ Set.range (γStage n) ⊆ C := by
    intro n
    exact Classical.choose_spec (hstage n)
  refine ⟨γStage, ?_, ?_⟩
  · -- Each rooted stage loop is piecewise differentiable by construction.
    intro n
    exact (hγStageSpec n).1
  · -- And each rooted stage loop stays in the connected open ambient set `C`.
    intro n
    exact (hγStageSpec n).2

/-- Helper for Corollary II.1-extra-23: horizontal composition of path homotopies stays inside
`C` when both constituent homotopies already stay inside `C`. -/
theorem Path.Homotopy.hcomp_mem
    {C : Set ℂ} {x0 x1 x2 : ℂ}
    {p0 q0 : Path x0 x1} {p1 q1 : Path x1 x2}
    {F : p0.Homotopy q0} {G : p1.Homotopy q1}
    (hF : ∀ p : I × I, F p ∈ C) (hG : ∀ p : I × I, G p ∈ C) :
    ∀ p : I × I, F.hcomp G p ∈ C := by
  intro p
  -- Unfold the horizontal composition once: it evaluates either the left homotopy or the right
  -- homotopy at a rescaled parameter value.
  rw [Path.Homotopy.hcomp_apply]
  split_ifs
  · exact hF _
  · exact hG _

/-- Helper for Corollary II.1-extra-23: concatenating two path homotopies that stay inside `C`
still gives a path homotopy that stays inside `C`. -/
theorem Path.Homotopy.trans_mem
    {C : Set ℂ} {x0 x1 : ℂ} {p0 p1 p2 : Path x0 x1}
    {F : p0.Homotopy p1} {G : p1.Homotopy p2}
    (hF : ∀ p : I × I, F p ∈ C) (hG : ∀ p : I × I, G p ∈ C) :
    ∀ p : I × I, F.trans G p ∈ C := by
  intro p
  -- Unfold the vertical concatenation once and reuse the ambient-membership witnesses on the
  -- corresponding half of the square.
  rw [Path.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

/-- Helper for Corollary II.1-extra-23: the constant path homotopy stays inside the range of the
underlying path. -/
theorem Path.Homotopy.refl_mem_range
    {z0 z1 : ℂ} (ρ : Path z0 z1) :
    ∀ p : I × I, Path.Homotopy.refl ρ p ∈ Set.range ρ := by
  intro p
  -- The constant homotopy only evaluates the original path at the second coordinate.
  exact ⟨p.2, rfl⟩

/-- Helper for Corollary II.1-extra-23: reversing a path homotopy preserves ambient-membership
control. -/
theorem Path.Homotopy.symm_mem
    {C : Set ℂ} {x0 x1 : ℂ} {p0 p1 : Path x0 x1} {F : p0.Homotopy p1}
    (hF : ∀ p : I × I, F p ∈ C) :
    ∀ p : I × I, F.symm p ∈ C := by
  intro p
  -- Reversing the homotopy only flips the homotopy-time parameter.
  simpa using hF (σ p.1, p.2)

/-- Helper for Corollary II.1-extra-23: the standard contraction from `Path.refl z0` to
`ρ.trans ρ.symm` never leaves the image of `ρ`. -/
theorem Path.Homotopy.reflTransSymm_mem_range
    {z0 z : ℂ} (ρ : Path z0 z) :
    ∀ p : I × I, Path.Homotopy.reflTransSymm ρ p ∈ Set.range ρ := by
  intro p
  -- The explicit contraction is a reparameterization of the same connector path `ρ`.
  refine ⟨⟨Path.Homotopy.reflTransSymmAux p, Path.Homotopy.reflTransSymmAux_mem_I p⟩, ?_⟩
  rfl

/-- Helper for Corollary II.1-extra-23: if a connector path stays in `C`, then the standard
contraction from `ρ.trans ρ.symm` back to the constant loop at its source also stays in `C`. -/
theorem Path.Homotopy.transSymm_mem
    {C : Set ℂ} {z0 z : ℂ} {ρ : Path z0 z}
    (hρC : Set.range ρ ⊆ C) :
    ∀ p : I × I, (Path.Homotopy.reflTransSymm ρ).symm p ∈ C := by
  -- Reverse the standard `Path.refl ⟶ ρ.trans ρ.symm` contraction after recording that the whole
  -- homotopy already stays inside the range of `ρ`.
  exact
    Path.Homotopy.symm_mem
      (fun p ↦ hρC (Path.Homotopy.reflTransSymm_mem_range ρ p))

/-- Helper for Corollary II.1-extra-23: the standard simplification homotopy from
`ρ.trans Path.refl` to `ρ` never leaves the image of `ρ`. -/
theorem Path.Homotopy.transRefl_mem_range
    {z0 z1 : ℂ} (ρ : Path z0 z1) :
    ∀ p : I × I, Path.Homotopy.transRefl ρ p ∈ Set.range ρ := by
  intro p
  have hmem :
      (↑p.1 * ↑p.2 + (1 - ↑p.1) * Path.Homotopy.transReflReparamAux p.2 : ℝ) ∈ I := by
    constructor
    · have hp10 : (0 : ℝ) ≤ p.1 := p.1.2.1
      have hp11 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hσ10 : (0 : ℝ) ≤ 1 - p.1 := by
        linarith
      have hp21 : (0 : ℝ) ≤ p.2 := p.2.2.1
      have haux0 : (0 : ℝ) ≤ Path.Homotopy.transReflReparamAux p.2 :=
        (Path.Homotopy.transReflReparamAux_mem_I p.2).1
      -- The reparametrized point is a convex combination of two points of `I`.
      nlinarith
    · have hp11 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hp10 : (0 : ℝ) ≤ p.1 := p.1.2.1
      have hσ10 : (0 : ℝ) ≤ 1 - p.1 := by
        linarith
      have hp20 : (p.2 : ℝ) ≤ 1 := p.2.2.2
      have hp21 : (0 : ℝ) ≤ p.2 := p.2.2.1
      have haux1 : (Path.Homotopy.transReflReparamAux p.2 : ℝ) ≤ 1 :=
        (Path.Homotopy.transReflReparamAux_mem_I p.2).2
      have haux0 : (0 : ℝ) ≤ Path.Homotopy.transReflReparamAux p.2 :=
        (Path.Homotopy.transReflReparamAux_mem_I p.2).1
      -- The same convex-combination bounds show the parameter never exceeds `1`.
      nlinarith
  refine ⟨⟨σ (σ p.1) * p.2 + σ p.1 * Path.Homotopy.transReflReparamAux p.2, by
    simpa using hmem⟩, ?_⟩
  -- Unfold the reparametrized homotopy once and simplify the two appearances of `σ`.
  simp [Path.Homotopy.transRefl]
  change
    ρ ⟨↑p.1 * ↑p.2 + (1 - ↑p.1) * Path.Homotopy.transReflReparamAux p.2, hmem⟩ =
      ρ ⟨(1 - ↑(σ p.1)) * ↑p.2 + ↑(σ p.1) * Path.Homotopy.transReflReparamAux p.2, by
        simpa using hmem⟩
  congr 1
  simp

/-- Helper for Corollary II.1-extra-23: if a path stays in `C`, then the standard simplification
homotopy from `ρ.trans Path.refl` to `ρ` stays in `C`. -/
theorem Path.Homotopy.transRefl_mem
    {C : Set ℂ} {z0 z1 : ℂ} {ρ : Path z0 z1}
    (hρC : Set.range ρ ⊆ C) :
    ∀ p : I × I, Path.Homotopy.transRefl ρ p ∈ C := by
  intro p
  -- The simplification homotopy is a reparameterization of the same path `ρ`.
  exact hρC (Path.Homotopy.transRefl_mem_range ρ p)

/-- Helper for Corollary II.1-extra-23: the standard simplification homotopy from
`Path.refl.trans ρ` to `ρ` never leaves the image of `ρ`. -/
theorem Path.Homotopy.reflTrans_mem_range
    {z0 z1 : ℂ} (ρ : Path z0 z1) :
    ∀ p : I × I, Path.Homotopy.reflTrans ρ p ∈ Set.range ρ := by
  intro p
  -- `reflTrans` is `transRefl` on the reversed connector, with the path parameter flipped.
  simpa [Path.Homotopy.reflTrans, Path.symm_range] using
    (Path.Homotopy.transRefl_mem_range ρ.symm (p.1, σ p.2))

/-- Helper for Corollary II.1-extra-23: if a path stays in `C`, then the standard simplification
homotopy from `Path.refl.trans ρ` to `ρ` stays in `C`. -/
theorem Path.Homotopy.reflTrans_mem
    {C : Set ℂ} {z0 z1 : ℂ} {ρ : Path z0 z1}
    (hρC : Set.range ρ ⊆ C) :
    ∀ p : I × I, Path.Homotopy.reflTrans ρ p ∈ C := by
  intro p
  -- This is the same range-subset argument as above, now consumed at the ambient-set level.
  exact hρC (Path.Homotopy.reflTrans_mem_range ρ p)

/-- Helper for Corollary II.1-extra-23: if every listed loop contracts to its own basepoint inside
`C`, then the rooted concatenation contracts to the common root inside `C`. -/
private theorem rootedBoundaryLoopList_pathHomotopyConst_of_memberPathHomotopyConst
    {ι : Type u} {C : Set ℂ} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρC : ∀ i, i ∈ l → Set.range (ρ i) ⊆ C)
    (hΓhom :
      ∀ i, i ∈ l →
        ∃ F : ((Γ i).toPath).Homotopy (Path.refl ((Γ i).toPath 0)),
          ∀ p : I × I, F p ∈ C) :
    ∃ F : (rootedBoundaryLoopList l Γ ρ).Homotopy (Path.refl z0),
      ∀ p : I × I, F p ∈ C := by
  induction l generalizing Γ ρ with
  | nil =>
      refine ⟨Path.Homotopy.refl (Path.refl z0), ?_⟩
      intro p
      -- The empty rooted concatenation is the constant loop at the common root.
      simpa [rootedBoundaryLoopList] using hz0C
  | cons i l ih =>
      have hρlC : ∀ j, j ∈ l → Set.range (ρ j) ⊆ C := by
        intro j hj
        exact hρC j (by simp [hj])
      have hΓhom_l :
          ∀ j, j ∈ l →
            ∃ F : ((Γ j).toPath).Homotopy (Path.refl ((Γ j).toPath 0)),
              ∀ p : I × I, F p ∈ C := by
        intro j hj
        exact hΓhom j (by simp [hj])
      rcases ih Γ ρ hρlC hΓhom_l with ⟨Floop, hFloopC⟩
      have hρiC : Set.range (ρ i) ⊆ C := hρC i (by simp)
      have hρiSymmC : Set.range ((ρ i).symm) ⊆ C := by
        intro z hz
        have hzρ : z ∈ Set.range (ρ i) := by
          let hrange : Set.range (ρ i).symm = Set.range (ρ i) := Path.symm_range (ρ i)
          exact hrange ▸ hz
        exact hρiC hzρ
      rcases hΓhom i (by simp) with ⟨FΓ, hFΓC⟩
      have hreflρC : ∀ p : I × I, Path.Homotopy.refl (ρ i) p ∈ C := by
        intro p
        exact hρiC (Path.Homotopy.refl_mem_range (ρ i) p)
      have hreflρsymmC : ∀ p : I × I, Path.Homotopy.refl ((ρ i).symm) p ∈ C := by
        intro p
        exact hρiSymmC (Path.Homotopy.refl_mem_range ((ρ i).symm) p)
      have hreflTransSymmC :
          ∀ p : I × I, (Path.Homotopy.reflTransSymm (ρ i)).symm p ∈ C := by
        -- Use the new owner-level ambient-membership lemma for the connector contraction.
        exact Path.Homotopy.transSymm_mem hρiC
      have htransReflSymmC :
          ∀ p : I × I, Path.Homotopy.reflTrans ((ρ i).symm) p ∈ C := by
        -- The reflected connector simplification is the same ambient-membership pattern.
        exact Path.Homotopy.reflTrans_mem hρiSymmC
      have hconjStepC :
          ∀ p : I × I,
            ((Path.Homotopy.refl (ρ i)).hcomp
                (FΓ.hcomp (Path.Homotopy.refl ((ρ i).symm)))) p ∈ C := by
        -- First contract the boundary loop inside the connector conjugation.
        exact
          Path.Homotopy.hcomp_mem hreflρC
            (Path.Homotopy.hcomp_mem hFΓC hreflρsymmC)
      have hsimplifyConnectorC :
          ∀ p : I × I,
            ((Path.Homotopy.refl (ρ i)).hcomp
                (Path.Homotopy.reflTrans ((ρ i).symm))) p ∈ C := by
        -- Then simplify `Path.refl.trans ρ.symm` back to `ρ.symm`.
        exact Path.Homotopy.hcomp_mem hreflρC htransReflSymmC
      let Ftail :
          ((ρ i).trans (((Γ i).toPath).trans (ρ i).symm)).Homotopy (Path.refl z0) :=
        ((Path.Homotopy.refl (ρ i)).hcomp
            (FΓ.hcomp (Path.Homotopy.refl ((ρ i).symm)))).trans
          (((Path.Homotopy.refl (ρ i)).hcomp
                (Path.Homotopy.reflTrans ((ρ i).symm))).trans
            ((Path.Homotopy.reflTransSymm (ρ i)).symm))
      have hFtailC : ∀ p : I × I, Ftail p ∈ C := by
        -- Compose the boundary-loop contraction with the two connector simplifications.
        exact
          Path.Homotopy.trans_mem
            hconjStepC
            (Path.Homotopy.trans_mem hsimplifyConnectorC hreflTransSymmC)
      have hreflRootC : Set.range (Path.refl z0) ⊆ C := by
        intro z hz
        rcases hz with ⟨t, rfl⟩
        simpa using hz0C
      have htransReflRootC :
          ∀ p : I × I, Path.Homotopy.transRefl (Path.refl z0) p ∈ C := by
        -- Simplify the doubled root constant loop through the same ambient-membership API.
        exact Path.Homotopy.transRefl_mem hreflRootC
      refine ⟨(Floop.hcomp Ftail).trans (Path.Homotopy.transRefl (Path.refl z0)), ?_⟩
      -- Contract the head and tail separately, then simplify the doubled root constant loop.
      exact
        Path.Homotopy.trans_mem
          (Path.Homotopy.hcomp_mem hFloopC hFtailC)
          htransReflRootC

/-- Helper for Corollary II.1-extra-23: a rooted concatenation is null-homotopic in `C` once each
listed loop contracts to its own basepoint inside `C`. -/
private theorem rootedBoundaryLoopList_nullHomotopicIn_of_memberPathHomotopyConst
    {ι : Type u} {C : Set ℂ} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρC : ∀ i, i ∈ l → Set.range (ρ i) ⊆ C)
    (hΓhom :
      ∀ i, i ∈ l →
        ∃ F : ((Γ i).toPath).Homotopy (Path.refl ((Γ i).toPath 0)),
          ∀ p : I × I, F p ∈ C) :
    IsNullHomotopicClosedPathIn C (rootedBoundaryLoopList l Γ ρ) := by
  rcases
      rootedBoundaryLoopList_pathHomotopyConst_of_memberPathHomotopyConst
        l Γ ρ hz0C hρC hΓhom with
    ⟨F, hFC⟩
  -- Repackage the rooted-loop contraction as a null-homotopy to the constant root loop.
  exact
    isNullHomotopicClosedPathIn_of_closedPathHomotopicIn_const
      (closedPathHomotopicIn_of_pathHomotopyIn F hFC) hz0C

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a `Finset`-indexed rooted loop is
null-homotopic in `C` once each boundary loop in the family contracts to its own basepoint inside
`C`. -/
theorem rootedBoundaryLoop_nullHomotopicIn_of_memberPathHomotopyConst
    {ι : Type u} [DecidableEq ι] {C : Set ℂ} {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρC : ∀ i ∈ s, Set.range (ρ i) ⊆ C)
    (hΓhom :
      ∀ i ∈ s,
        ∃ F : ((Γ i).toPath).Homotopy (Path.refl ((Γ i).toPath 0)),
          ∀ p : I × I, F p ∈ C) :
    IsNullHomotopicClosedPathIn C (rootedBoundaryLoop s Γ ρ) := by
  have hρC_list : ∀ i, i ∈ s.toList → Set.range (ρ i) ⊆ C := by
    intro i hi
    exact hρC i (Finset.mem_toList.1 hi)
  have hΓhom_list :
      ∀ i, i ∈ s.toList →
        ∃ F : ((Γ i).toPath).Homotopy (Path.refl ((Γ i).toPath 0)),
          ∀ p : I × I, F p ∈ C := by
    intro i hi
    exact hΓhom i (Finset.mem_toList.1 hi)
  -- Reindex the recursive rooted-loop contraction to the canonical `Finset` spelling.
  simpa [rootedBoundaryLoop] using
    rootedBoundaryLoopList_nullHomotopicIn_of_memberPathHomotopyConst
      s.toList Γ ρ hz0C hρC_list hΓhom_list

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected open ambient set,
every rooted rectangle stage loop can be chosen null-homotopic in `C`, because each rectangle
boundary already contracts inside its own rectangle. -/
theorem existsRootedRectangleStageLoopFamilyInConnectedOpen_nullHomotopic
    {C K : Set ℂ} {z0 : ℂ}
    (hz0C : z0 ∈ C) (hC_open : IsOpen C) (hC_connected : IsConnected C)
    (hKC : K ⊆ C)
    {N : ℕ → ℕ} {z w : ∀ n, Fin (N n) → ℂ}
    (hRectSubset : ∀ n s, Complex.Rectangle (z n s) (w n s) ⊆ interior K) :
    ∃ γStage : ∀ n : ℕ, Path z0 z0,
      (∀ n : ℕ, (γStage n).IsPiecewiseDifferentiable) ∧
      (∀ n : ℕ, Set.range (γStage n) ⊆ C) ∧
      (∀ n : ℕ, IsNullHomotopicClosedPathIn C (γStage n)) := by
  classical
  have hstage :
      ∀ n : ℕ,
        ∃ γ : Path z0 z0,
          γ.IsPiecewiseDifferentiable ∧
            Set.range γ ⊆ C ∧
            IsNullHomotopicClosedPathIn C γ := by
    intro n
    let Γ : Fin (N n) → ClosedPath ℂ :=
      fun s ↦ (axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath
    have hz_mem : ∀ s : Fin (N n), z n s ∈ C := by
      intro s
      have hz_rect : z n s ∈ Complex.Rectangle (z n s) (w n s) := by
        simp [Complex.Rectangle, Complex.mem_reProdIm]
      exact
        (Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)) hz_rect
    have hΓ_base_eq : ∀ s : Fin (N n), ((Γ s).toPath 0) = z n s := by
      intro s
      change (((axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath).toPath 0) =
        z n s
      rw [loopToClosedPath_toPath_eq_cast]
      calc
        ((axisParallelRectangleBoundaryPath (z n s) (w n s)).cast _ _) 0 =
            (axisParallelRectangleBoundaryPath (z n s) (w n s)) 0 := by
          exact congrFun (Path.cast_coe (axisParallelRectangleBoundaryPath (z n s) (w n s)) _ _) 0
        _ = z n s := by
          simp [axisParallelRectangleBoundaryPath]
    have hΓ_base_mem : ∀ s : Fin (N n), ((Γ s).toPath 0) ∈ C := by
      intro s
      simpa [hΓ_base_eq s] using hz_mem s
    have hconnector :
        ∀ s : Fin (N n),
          ∃ ρ : Path z0 ((Γ s).toPath 0),
            ρ.IsPiecewiseDifferentiable ∧ Set.range ρ ⊆ C := by
      intro s
      obtain ⟨ρ, hρ_piece, hρ_mem⟩ :=
        exists_piecewiseDifferentiable_path_in_of_isOpen_isConnected
          hC_open hC_connected hz0C (hΓ_base_mem s)
      refine ⟨ρ, hρ_piece, ?_⟩
      rintro ζ ⟨t, rfl⟩
      exact hρ_mem t
    let ρ : ∀ s : Fin (N n), Path z0 ((Γ s).toPath 0) := fun s ↦ Classical.choose (hconnector s)
    have hρ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), (ρ s).IsPiecewiseDifferentiable := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).1
    have hρ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range (ρ s) ⊆ C := by
      intro s hs
      exact (Classical.choose_spec (hconnector s)).2
    have hΓ_piece :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), ((Γ s).toPath).IsPiecewiseDifferentiable := by
      intro s hs
      simpa [Γ, Path.toClosedPath] using
        axisParallelRectangleBoundaryPath_isPiecewiseDifferentiable (z n s) (w n s)
    have hΓ_mem :
        ∀ s ∈ (Finset.univ : Finset (Fin (N n))), Set.range ((Γ s).toPath) ⊆ C := by
      intro s hs
      intro ζ hζ
      have hζ_rect : ζ ∈ Complex.Rectangle (z n s) (w n s) := by
        have hζ' : ζ ∈ Set.range (axisParallelRectangleBoundaryPath (z n s) (w n s)) := by
          simpa [Γ, Path.toClosedPath] using hζ
        exact axisParallelRectangleBoundaryPath_range_subset_rectangle (z n s) (w n s) hζ'
      exact
        Set.Subset.trans
          (hRectSubset n s)
          (Set.Subset.trans interior_subset hKC)
          hζ_rect
    let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
    have hγ_top :
        γ.IsPiecewiseDifferentiable ∧ Set.range γ ⊆ C := by
      -- Keep the stage loop in the same rooted spelling as the topology theorem.
      exact
        rootedBoundaryLoop_topology
          (C := C) (s := Finset.univ) Γ ρ hz0C hρ_piece hΓ_piece hρ_mem hΓ_mem
    have hγ_null : IsNullHomotopicClosedPathIn C γ := by
      -- Each rectangle boundary contracts in `C`, so the generic rooted-loop contraction theorem
      -- turns the whole finite rooted stage into a null-homotopic loop.
      refine
        rootedBoundaryLoop_nullHomotopicIn_of_memberPathHomotopyConst
          (s := Finset.univ) Γ ρ hz0C hρ_mem ?_
      intro s hs
      have hrectC : Complex.Rectangle (z n s) (w n s) ⊆ C := by
        exact Set.Subset.trans (hRectSubset n s) (Set.Subset.trans interior_subset hKC)
      rcases
          axisParallelRectangleBoundaryPath_pathHomotopyConstIn_domain
            (z := z n s) (w := w n s) hrectC with
        ⟨F, hFmaps⟩
      have hpath_eq :
          (axisParallelRectangleBoundaryPath (z n s) (w n s)).cast
              (hΓ_base_eq s) (hΓ_base_eq s) =
            (Γ s).toPath := by
        change
          ((axisParallelRectangleBoundaryPath (z n s) (w n s)).toClosedPath).toPath =
            (Γ s).toPath
        rw [loopToClosedPath_toPath_eq_cast]
      have hrefl_eq :
          (Path.refl (z n s)).cast (hΓ_base_eq s) (hΓ_base_eq s) =
            Path.refl ((Γ s).toPath 0) := by
        ext t
        exact (hΓ_base_eq s).symm
      let hFcast₀ :
          ((axisParallelRectangleBoundaryPath (z n s) (w n s)).cast
              (hΓ_base_eq s) (hΓ_base_eq s)).Homotopy
            ((Path.refl (z n s)).cast (hΓ_base_eq s) (hΓ_base_eq s)) :=
        F.pathCast (hΓ_base_eq s) (hΓ_base_eq s)
      let hFcast :
          ((Γ s).toPath).Homotopy (Path.refl ((Γ s).toPath 0)) :=
        -- Change endpoints once at the homotopy level instead of rewriting the path equality
        -- directly in dependent type.
        hFcast₀.cast hpath_eq hrefl_eq
      refine ⟨hFcast, ?_⟩
      · intro p
        have hp_eq : hFcast p = F p := by
          -- Route correction: normalize the dependent homotopy casts by reducing only the two
          -- endpoint/path equalities, instead of asking `simp` to unfold the whole casted object.
          change hFcast₀ p = F p
          rfl
        rw [hp_eq]
        exact hFmaps p
    exact ⟨γ, hγ_top.1, hγ_top.2, hγ_null⟩
  let γStage : ∀ n, Path z0 z0 := fun n ↦ Classical.choose (hstage n)
  have hγStageSpec :
      ∀ n,
        (γStage n).IsPiecewiseDifferentiable ∧
          Set.range (γStage n) ⊆ C ∧
          IsNullHomotopicClosedPathIn C (γStage n) := by
    intro n
    exact Classical.choose_spec (hstage n)
  refine ⟨γStage, ?_, ?_, ?_⟩
  · -- Each rooted stage loop remains piecewise differentiable by the same concrete construction.
    intro n
    exact (hγStageSpec n).1
  · -- The rooted stage loops stay in `C` throughout the connected-open family.
    intro n
    exact (hγStageSpec n).2.1
  · -- The new geometric content is that every stage loop already contracts inside `C`.
    intro n
    exact (hγStageSpec n).2.2

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: in a connected open ambient set,
an oriented boundary family admits one explicit rooted loop in `C` built from connector paths to a
common basepoint. -/
theorem IsOrientedBoundaryOf.existsRootedBoundaryLoopInConnectedOpen
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C) :
    ∃ z0 : ℂ, ∃ γ : Path z0 z0,
      γ.IsPiecewiseDifferentiable ∧
      Set.range γ ⊆ C := by
  classical
  obtain ⟨i0, ρ, hρ_piece, hρC⟩ :=
    connectedOpenConnectorFamily
      (Γ := Γ) hC_open hC_connected
      (fun i ↦ range_toPath_subset_domain_of_orientedBoundary hΓ hKC i)
  let z0 : ℂ := (Γ i0).toPath 0
  have hz0C : z0 ∈ C := by
    -- The chosen root is one boundary-loop basepoint, hence lies in `C`.
    simpa [z0] using boundaryPathBasepoint_mem_domain_of_orientedBoundary hΓ hKC i0
  have hΓ_piece : ∀ i ∈ (Finset.univ : Finset ι), ((Γ i).toPath).IsPiecewiseDifferentiable := by
    intro i hi
    simpa using hΓ.piecewiseDifferentiable i
  have hΓC : ∀ i ∈ (Finset.univ : Finset ι), Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    exact range_toPath_subset_domain_of_orientedBoundary hΓ hKC i
  let γ : Path z0 z0 := rootedBoundaryLoop Finset.univ Γ ρ
  rcases
    rootedBoundaryLoop_topology
      (C := C) (s := Finset.univ) Γ ρ hz0C
      (fun i hi ↦ hρ_piece i)
      hΓ_piece
      (fun i hi ↦ by
        rintro z ⟨t, rfl⟩
        exact hρC i t)
      hΓC with ⟨hγ_piece, hγC⟩
  -- The support API records only the topology of the canonical rooted loop; later proofs can add
  -- contour comparison or null-homotopy data on top of this concrete object.
  exact ⟨z0, γ, hγ_piece, hγC⟩

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: a connected open ambient set
provides explicit connector paths from one chosen boundary basepoint to every other boundary
basepoint. -/
theorem IsOrientedBoundaryOf.existsConnectorFamilyInConnectedOpen
    {ι : Type u} [Fintype ι] [Nonempty ι] {C K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKC : K ⊆ C)
    (hC_open : IsOpen C) (hC_connected : IsConnected C) :
    ∃ i0 : ι, ∃ ρ : ∀ i, Path ((Γ i0).toPath 0) ((Γ i).toPath 0),
      (∀ i, (ρ i).IsPiecewiseDifferentiable) ∧
      (∀ i t, ρ i t ∈ C) := by
  -- Reuse the theorem-local connector package already built from connectedness of `C`.
  exact
    connectedOpenConnectorFamily
      (Γ := Γ) hC_open hC_connected
      (fun i ↦ range_toPath_subset_domain_of_orientedBoundary hΓ hKC i)

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: if every connector path and boundary
loop in a rooted concatenation stays in `C`, then the whole rooted loop stays in `C`. -/
theorem rootedBoundaryLoopList_range_subset
    {ι : Type u} {C : Set ℂ} {z0 : ℂ} (l : List ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρC : ∀ i, i ∈ l → Set.range (ρ i) ⊆ C)
    (hΓC : ∀ i, i ∈ l → Set.range ((Γ i).toPath) ⊆ C) :
    Set.range (rootedBoundaryLoopList l Γ ρ) ⊆ C := by
  induction l generalizing Γ ρ with
  | nil =>
      intro z hz
      rcases hz with ⟨t, ht⟩
      simpa [rootedBoundaryLoopList] using (ht ▸ hz0C)
  | cons i l ih =>
      have hρlC : ∀ j, j ∈ l → Set.range (ρ j) ⊆ C := by
        intro j hj
        exact hρC j (by simp [hj])
      have hΓlC : ∀ j, j ∈ l → Set.range ((Γ j).toPath) ⊆ C := by
        intro j hj
        exact hΓC j (by simp [hj])
      have hloopC : Set.range (rootedBoundaryLoopList l Γ ρ) ⊆ C := ih Γ ρ hρlC hΓlC
      have hρiC : Set.range (ρ i) ⊆ C := hρC i (by simp)
      have hΓiC : Set.range ((Γ i).toPath) ⊆ C := hΓC i (by simp)
      have hconjC : Set.range (((Γ i).toPath).trans (ρ i).symm) ⊆ C := by
        rw [Path.trans_range]
        refine Set.union_subset hΓiC ?_
        simpa [Path.symm_range] using hρiC
      intro z hz
      rw [rootedBoundaryLoopList, Path.trans_range] at hz
      rcases hz with hz | hz
      · exact hloopC hz
      · rw [Path.trans_range] at hz
        rcases hz with hz | hz
        · exact hρiC hz
        · exact hconjC hz

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: the `Finset`-indexed rooted loop
stays in `C` once each connector path and each boundary loop stays in `C`. -/
theorem rootedBoundaryLoop_range_subset
    {ι : Type u} [DecidableEq ι] {C : Set ℂ} {z0 : ℂ} (s : Finset ι)
    (Γ : ι → ClosedPath ℂ) (ρ : ∀ i, Path z0 ((Γ i).toPath 0))
    (hz0C : z0 ∈ C)
    (hρC : ∀ i ∈ s, Set.range (ρ i) ⊆ C)
    (hΓC : ∀ i ∈ s, Set.range ((Γ i).toPath) ⊆ C) :
    Set.range (rootedBoundaryLoop s Γ ρ) ⊆ C := by
  have hρC_list : ∀ i, i ∈ s.toList → Set.range (ρ i) ⊆ C := by
    intro i hi
    exact hρC i (Finset.mem_toList.1 hi)
  have hΓC_list : ∀ i, i ∈ s.toList → Set.range ((Γ i).toPath) ⊆ C := by
    intro i hi
    exact hΓC i (Finset.mem_toList.1 hi)
  simpa [rootedBoundaryLoop] using
    rootedBoundaryLoopList_range_subset s.toList Γ ρ hz0C hρC_list hΓC_list

/-- Helper for Cartan section05 0036_Corollary_II_1_extra_23: once a connected-component block has
been reindexed by the subtype of boundary curves with key `C`, its total contour already vanishes
for a closed form. -/
theorem subtypeBoundaryPaths_isOrientedBoundaryOf_inter_boundaryComponent
    {ι : Type u} [Fintype ι] {D K : Set ℂ} {Γ : ι → ClosedPath ℂ}
    (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD_open : IsOpen D) {C : Set ℂ}
    (hC : C ∈ Finset.univ.image (fun i : ι => connectedComponentIn D ((Γ i).toPath 0))) :
    IsOrientedBoundaryOf (K ∩ C)
      (fun i : {j // connectedComponentIn D ((Γ j).toPath 0) = C} ↦ Γ i.1) := by
  let ΓC : {j // connectedComponentIn D ((Γ j).toPath 0) = C} → ClosedPath ℂ := fun i ↦ Γ i.1
  have hC_open : IsOpen C := (boundaryComponent_isOpen_isConnected hΓ hKD hD_open hC).1
  refine
    { isCompact := compact_inter_boundaryComponent hΓ hKD hD_open hC
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- Restricting the index type does not change the underlying loop regularity.
    intro i
    simpa [ΓC] using hΓ.piecewiseDifferentiable i.1
  · -- The simple-loop property is inherited verbatim from the original boundary family.
    intro i s t hst
    simpa [ΓC] using hΓ.simple_loops i.1 hst
  · -- Distinct subtype indices correspond to distinct original boundary components.
    intro i j hij
    exact hΓ.pairwiseDisjoint_ranges fun hij_eq ↦ hij (Subtype.ext hij_eq)
  · -- The component-restricted boundary family cuts the frontier down to `frontier (K ∩ C)`.
    calc
      (⋃ i : {j // connectedComponentIn D ((Γ j).toPath 0) = C}, Set.range (ΓC i).toPath) =
          frontier K ∩ C := by
        simpa [ΓC] using
          iUnion_subtypeBoundaryPaths_eq_frontier_inter_boundaryComponent hΓ hKD hC
      _ = frontier (K ∩ C) := by
        symm
        exact frontier_inter_boundaryComponent_eq hΓ hKD hD_open hC
  · -- Transfer the original boundary chart to the ambient connected component containing this
    -- boundary loop.
    intro i t₀ ht₀ hdiff hderiv
    obtain ⟨δ, hδi⟩ := hΓ.exists_boundary_chart_at_regular_point i.1 ht₀ hdiff hderiv
    have hpointC : Complex.equivRealProdCLM.symm ((Γ i.1).realCurve t₀) ∈ C :=
      realCurve_mem_component_of_boundaryKey hΓ hKD i.2 ht₀
    obtain ⟨δ', hδ'⟩ :=
      IsBoundaryStraighteningAt.inter_boundaryComponent hδi hC_open hpointC
    exact ⟨δ', hδ'⟩
