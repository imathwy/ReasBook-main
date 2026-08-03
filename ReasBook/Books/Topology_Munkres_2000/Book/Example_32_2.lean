module

public import Topology_Munkres_2000.Book.Example_32_2.DiagonalSeparation

public section

universe u

/-- Example 32.2: The product of the open and closed first-uncountable ordinals
fails the closed-set separation property. -/
theorem OpenOmegaOne.prodClosedOmegaOne_notNormal :
    ¬ NormalSpace (OpenOmegaOne.{u} × ClosedOmegaOne.{u}) := by
  intro hNormal
  letI : NormalSpace (OpenOmegaOne.{u} × ClosedOmegaOne.{u}) := hNormal
  classical
  -- Separate the closed graph diagonal from the closed top slice.
  obtain ⟨U, V, hUOpen, hVOpen, hDiagonalU, hTopV, hUV⟩ := normal_separation
    OpenOmegaOne.isClosed_prodDiagonal
    (isClosed_eq continuous_snd continuous_const)
    OpenOmegaOne.prodDiagonal_disjoint_topSlice
  have hEscape : ∀ x : OpenOmegaOne.{u},
      ∃ y : OpenOmegaOne.{u}, x < y ∧ (x, OpenOmegaOne.toClosed y) ∉ U := by
    intro x
    exact OpenOmegaOne.exists_gt_pair_not_mem_of_disjoint U V x hVOpen
      (hTopV rfl) hUV
  choose β hβGreater hβOutside using hEscape
  -- Iterate the escaping choice to obtain the increasing sequence from the source proof.
  let x : ℕ → OpenOmegaOne.{u} := fun n ↦ β^[n] CountableOrdinal.zero
  have hxSucc (n : ℕ) : x (n + 1) = β (x n) := by
    simp only [x, Function.iterate_succ', Function.comp_apply]
  have hxStrict : StrictMono x := strictMono_nat_of_lt_succ fun n ↦ by
    rw [hxSucc n]
    exact hβGreater (x n)
  obtain ⟨b, hb⟩ := OpenOmegaOne.monotoneSequence_tendsto x hxStrict.monotone
  -- Both the sequence and its shifted image converge to the same diagonal point.
  have hbShift : Filter.Tendsto (fun n ↦ x (n + 1)) Filter.atTop (nhds b) :=
    hb.comp (Filter.tendsto_add_atTop_nat 1)
  have hbClosed :
      Filter.Tendsto (fun n ↦ OpenOmegaOne.toClosed (x (n + 1))) Filter.atTop
        (nhds (OpenOmegaOne.toClosed b)) :=
    OpenOmegaOne.isEmbedding_toClosed.continuous.continuousAt.tendsto.comp hbShift
  have hPairs :
      Filter.Tendsto (fun n ↦ (x n, OpenOmegaOne.toClosed (x (n + 1)))) Filter.atTop
        (nhds (b, OpenOmegaOne.toClosed b)) :=
    hb.prodMk_nhds hbClosed
  have hLimitU : (b, OpenOmegaOne.toClosed b) ∈ U := hDiagonalU rfl
  have hEventuallyU :
      ∀ᶠ n in Filter.atTop, (x n, OpenOmegaOne.toClosed (x (n + 1))) ∈ U :=
    hPairs.eventually (hUOpen.mem_nhds hLimitU)
  obtain ⟨n, hnU⟩ := hEventuallyU.exists
  rw [hxSucc n] at hnU
  exact hβOutside (x n) hnU

/-- The product of the open and closed first-uncountable ordinals is not normal
in Munkres' `T4Space` convention. -/
theorem OpenOmegaOne.prodClosedOmegaOne_notT4 :
    ¬ T4Space (OpenOmegaOne.{u} × ClosedOmegaOne.{u}) := by
  intro h
  exact OpenOmegaOne.prodClosedOmegaOne_notNormal h.toNormalSpace
