module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Separation.Regular

public section

universe u

open scoped Ordinal

/-- Helper for Example 32.2: the countable ordinals converge to `Ω` under the
canonical inclusion into the closed first-uncountable ordinal. -/
lemma OpenOmegaOne.tendsto_toClosed_atTop_omega :
    Filter.Tendsto (OpenOmegaOne.toClosed : OpenOmegaOne.{u} → ClosedOmegaOne.{u})
      Filter.atTop (nhds ClosedOmegaOne.omega) := by
  -- Compute the limit in `Ordinal`, then lift it through the subtype topology.
  rw [tendsto_subtype_rng]
  have hMonotone : Monotone (fun x : OpenOmegaOne.{u} ↦ (x : Ordinal)) := by
    intro x y hxy
    exact hxy
  have hBounded : BddAbove (Set.range fun x : OpenOmegaOne.{u} ↦ (x : Ordinal)) := by
    refine ⟨ω₁, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact x.property.le
  simpa only [OpenOmegaOne.coe_toClosed, ClosedOmegaOne.coe_omega,
    (Cardinal.isSuccLimit_omega 1).iSup_Iio] using
    tendsto_atTop_ciSup hMonotone hBounded

/-- Helper for Example 32.2: the graph diagonal of the canonical inclusion is closed. -/
lemma OpenOmegaOne.isClosed_prodDiagonal :
    IsClosed {p : OpenOmegaOne.{u} × ClosedOmegaOne.{u} |
      OpenOmegaOne.toClosed p.1 = p.2} := by
  -- Express the graph as the equality locus of two continuous maps.
  exact isClosed_eq (OpenOmegaOne.isEmbedding_toClosed.continuous.comp continuous_fst)
    continuous_snd

/-- Helper for Example 32.2: the graph diagonal misses the top horizontal slice. -/
lemma OpenOmegaOne.prodDiagonal_disjoint_topSlice :
    Disjoint
      {p : OpenOmegaOne.{u} × ClosedOmegaOne.{u} |
        OpenOmegaOne.toClosed p.1 = p.2}
      {p : OpenOmegaOne.{u} × ClosedOmegaOne.{u} |
        p.2 = ClosedOmegaOne.omega} := by
  -- Equality with the top point would contradict countability of the first coordinate.
  rw [Set.disjoint_left]
  intro p hpDiagonal hpTop
  have hOrdinal := congrArg Subtype.val (hpDiagonal.trans hpTop)
  simp only [OpenOmegaOne.coe_toClosed, ClosedOmegaOne.coe_omega] at hOrdinal
  exact p.1.property.ne hOrdinal

/-- Helper for Example 32.2: disjointness from a neighborhood of the top slice forces
a point above any prescribed countable ordinal to escape the other set. -/
lemma OpenOmegaOne.exists_gt_pair_not_mem_of_disjoint
    (U V : Set (OpenOmegaOne.{u} × ClosedOmegaOne.{u})) (x : OpenOmegaOne.{u})
    (hVOpen : IsOpen V) (hxV : (x, ClosedOmegaOne.omega) ∈ V) (hUV : Disjoint U V) :
    ∃ y : OpenOmegaOne.{u}, x < y ∧ (x, OpenOmegaOne.toClosed y) ∉ U := by
  -- The vertical copy of `toClosed` converges to the point of the top slice.
  have hPairTendsto :
      Filter.Tendsto (fun y : OpenOmegaOne.{u} ↦ (x, OpenOmegaOne.toClosed y))
        Filter.atTop (nhds (x, ClosedOmegaOne.omega)) :=
    tendsto_const_nhds.prodMk_nhds OpenOmegaOne.tendsto_toClosed_atTop_omega
  have hEventuallyV :
      ∀ᶠ y : OpenOmegaOne.{u} in Filter.atTop, (x, OpenOmegaOne.toClosed y) ∈ V :=
    hPairTendsto.eventually (hVOpen.mem_nhds hxV)
  -- Start the eventual tail at the ordinal successor, which is still below `ω₁`.
  have hxSuccOmega : (x : Ordinal) + 1 < (ω₁ : Ordinal) :=
    (Cardinal.isSuccLimit_omega 1).succ_lt x.property
  let xSucc : OpenOmegaOne.{u} := ⟨(x : Ordinal) + 1, hxSuccOmega⟩
  have hxxSucc : x < xSucc := lt_add_one (x : Ordinal)
  obtain ⟨y, hyV, hySucc⟩ :=
    (hEventuallyV.and (Filter.eventually_ge_atTop xSucc)).exists
  exact ⟨y, hxxSucc.trans_le hySucc, hUV.notMem_of_mem_right hyV⟩

/-- Helper for Example 32.2: every monotone sequence of countable ordinals converges
to a countable ordinal. -/
lemma OpenOmegaOne.monotoneSequence_tendsto (x : ℕ → OpenOmegaOne.{u}) (hx : Monotone x) :
    ∃ b : OpenOmegaOne.{u}, Filter.Tendsto x Filter.atTop (nhds b) := by
  -- The countable supremum remains strictly below `ω₁`.
  have hSupOmega : (⨆ n, (x n : Ordinal)) < (ω₁ : Ordinal) := by
    apply Ordinal.iSup_lt_omega_one
    intro n
    exact (x n).property
  let b : OpenOmegaOne.{u} := ⟨⨆ n, (x n : Ordinal), hSupOmega⟩
  refine ⟨b, tendsto_subtype_rng.mpr ?_⟩
  -- Monotone convergence in `Ordinal` identifies the subtype limit with that supremum.
  have hMonotone : Monotone (fun n ↦ (x n : Ordinal)) := by
    intro m n hmn
    exact hx hmn
  have hBounded : BddAbove (Set.range fun n ↦ (x n : Ordinal)) := by
    refine ⟨ω₁, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (x n).property.le
  exact tendsto_atTop_ciSup hMonotone hBounded
