module

public import Mathlib.Topology.Compactness.Paracompact
import Topology_Munkres_2000.Book.Example_31_2.Instances
import Topology_Munkres_2000.Book.Example_31_3.Separation
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homeomorph.Lemmas

public section

universe u v

namespace ParacompactSpace

/-- Helper for Proposition 41.1: every canonical lower-limit basis interval in the
Sorgenfrey line is clopen. -/
private lemma isClopenOfMemLowerLimitBasis {U : Set SorgenfreyLine}
    (hU : U ∈ RealTopology.lowerLimitBasis) : IsClopen U := by
  rcases hU with ⟨a, b, hab, rfl⟩
  constructor
  · -- The complement is open because every exterior point has a basis interval
    -- that remains on the same side of `[a, b)`.
    apply isOpen_compl_iff.mp
    refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
    intro x hx
    change ¬ (a ≤ SorgenfreyLine.toReal x ∧ SorgenfreyLine.toReal x < b) at hx
    by_cases hxa : SorgenfreyLine.toReal x < a
    · refine ⟨Set.Ico (SorgenfreyLine.toReal x) a,
        ⟨SorgenfreyLine.toReal x, a, hxa, rfl⟩, Set.left_mem_Ico.mpr hxa, ?_⟩
      intro y hy hayb
      exact (not_lt_of_ge hayb.1) hy.2
    · have hbx : b ≤ SorgenfreyLine.toReal x := by
        apply le_of_not_gt
        intro hxb
        exact hx ⟨le_of_not_gt hxa, hxb⟩
      refine ⟨Set.Ico (SorgenfreyLine.toReal x) (SorgenfreyLine.toReal x + 1),
        ⟨SorgenfreyLine.toReal x, SorgenfreyLine.toReal x + 1,
          lt_add_one (SorgenfreyLine.toReal x), rfl⟩,
        Set.left_mem_Ico.mpr (lt_add_one (SorgenfreyLine.toReal x)), ?_⟩
      intro y hy hayb
      exact (not_lt_of_ge (hbx.trans hy.1)) hayb.2
  · -- The interval itself is one of the declared lower-limit basis opens.
    apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
    exact ⟨a, b, hab, rfl⟩

/-- Helper for Proposition 41.1: a natural-number-indexed clopen cover has an open,
locally finite refinement subordinate to the same indices. -/
private lemma isClopenNatCoverHasLocallyFiniteOpenRefinement
    {X : Type u} [TopologicalSpace X] (B : ℕ → Set X)
    (hB : ∀ n, IsClopen (B n)) (hcover : ⋃ n, B n = Set.univ) :
    ∃ T : ℕ → Set X, (∀ n, IsOpen (T n)) ∧ (⋃ n, T n = Set.univ) ∧
      LocallyFinite T ∧ ∀ n, T n ⊆ B n := by
  classical
  let T : ℕ → Set X := fun n ↦ B n \ ⋃ i : Fin n, B i
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · -- Removing the finite union of earlier clopen layers preserves openness.
    intro n
    exact ((hB n).diff (isClopen_iUnion_of_finite fun i : Fin n ↦ hB i)).isOpen
  · -- Assign each point to the first cover member that contains it.
    apply Set.eq_univ_of_forall
    intro x
    have hexists : ∃ n, x ∈ B n := Set.iUnion_eq_univ_iff.mp hcover x
    refine Set.mem_iUnion.mpr ⟨Nat.find hexists, ?_⟩
    refine ⟨Nat.find_spec hexists, ?_⟩
    intro hxEarlier
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxEarlier
    exact (Nat.not_lt_of_ge (Nat.find_min' hexists hxi)) i.isLt
  · -- A cover member containing `x` misses every trimmed layer with a later index.
    intro x
    obtain ⟨N, hxN⟩ := Set.iUnion_eq_univ_iff.mp hcover x
    refine ⟨B N, (hB N).isOpen.mem_nhds hxN, (Set.finite_Iic N).subset ?_⟩
    intro n hn
    by_contra hnN
    have hNn : N < n := Nat.lt_of_not_ge hnN
    obtain ⟨y, hyT, hyN⟩ := hn
    exact hyT.2 (Set.mem_iUnion.mpr ⟨⟨N, hNn⟩, hyN⟩)
  · -- Trimming only removes points, so every layer remains subordinate to `B n`.
    intro n
    exact Set.sdiff_subset

/-- Helper for Proposition 41.1: a nonempty Lindelöf space with a clopen basis is
paracompact. -/
private lemma paracompactSpaceOfLindelofClopenBasis
    {X : Type u} [TopologicalSpace X] [Nonempty X] [LindelofSpace X]
    (B : Set (Set X)) (hBasis : TopologicalSpace.IsTopologicalBasis B)
    (hClopen : ∀ U ∈ B, IsClopen U) : ParacompactSpace X := by
  classical
  constructor
  intro α S hSOpen hSCover
  -- Refine the original cover pointwise to clopen basis members.
  have hchoice : ∀ x : X, ∃ a U, U ∈ B ∧ x ∈ U ∧ U ⊆ S a := by
    intro x
    obtain ⟨a, hxa⟩ := Set.iUnion_eq_univ_iff.mp hSCover x
    obtain ⟨U, hUB, hxU, hUS⟩ :=
      hBasis.exists_subset_of_mem_open hxa (hSOpen a)
    exact ⟨a, U, hUB, hxU, hUS⟩
  choose coverIndex basisSet hBasisSet hxBasisSet hBasisSubset using hchoice
  -- Lindelöfness reduces this basis cover to a sequence.
  have hBasisCover : (Set.univ : Set X) ⊆ ⋃ x, basisSet x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxBasisSet x⟩
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover
    basisSet (fun x ↦ (hClopen _ (hBasisSet x)).isOpen) hBasisCover
  have hSequenceCover : ⋃ n, basisSet (f n) = (Set.univ : Set X) := by
    exact Set.Subset.antisymm (Set.subset_univ _) hf
  obtain ⟨T, hTOpen, hTCover, hTFinite, hTSubset⟩ :=
    isClopenNatCoverHasLocallyFiniteOpenRefinement (fun n ↦ basisSet (f n))
      (fun n ↦ hClopen _ (hBasisSet (f n))) hSequenceCover
  -- Lift the sequence index into the universe required by `ParacompactSpace`, then
  -- compose subordination through the selected basis members.
  refine ⟨ULift.{u} ℕ, fun n ↦ T n.down, fun n ↦ hTOpen n.down, ?_,
    hTFinite.comp_injective ULift.down_injective, ?_⟩
  · rw [ULift.down_surjective.iUnion_comp, hTCover]
  intro n
  exact ⟨coverIndex (f n.down), (hTSubset n.down).trans (hBasisSubset (f n.down))⟩

/-- Helper for Proposition 41.1: the Sorgenfrey line is paracompact, using its
earlier Lindelöf instance and clopen lower-limit basis. -/
private lemma sorgenfreyLineParacompact : ParacompactSpace SorgenfreyLine := by
  -- Apply the abstract clopen-basis criterion to the canonical intervals.
  exact paracompactSpaceOfLindelofClopenBasis RealTopology.lowerLimitBasis
    SorgenfreyLine.isTopologicalBasis_lowerLimitBasis
    (fun _ hU ↦ isClopenOfMemLowerLimitBasis hU)

/-- Helper for Proposition 41.1: the Sorgenfrey plane is not paracompact. -/
private lemma sorgenfreyPlaneNotParacompact :
    ¬ ParacompactSpace (SorgenfreyLine × SorgenfreyLine) := by
  intro hParacompact
  letI : ParacompactSpace (SorgenfreyLine × SorgenfreyLine) := hParacompact
  -- Hausdorff paracompactness would make the plane `T4`, contradicting the earlier example.
  exact SorgenfreyPlane.notT4 T4Space.of_paracompactSpace_t2Space

/- Proposition 41.1 (1). A subspace of a paracompact space need not be paracompact. -/
/-- Paracompactness is not inherited by arbitrary subspaces. -/
theorem not_hereditary :
    ¬ ∀ (X : Type u) [TopologicalSpace X] [ParacompactSpace X] (s : Set X),
      ParacompactSpace s := by
  intro hHereditary
  -- First lift the plane into the quantified universe, then embed it as the canonical
  -- open subspace of its compact one-point extension.
  apply sorgenfreyPlaneNotParacompact
  let liftedPlane := ULift.{u} (SorgenfreyLine × SorgenfreyLine)
  let liftedPlaneEquiv : liftedPlane ≃ₜ (SorgenfreyLine × SorgenfreyLine) :=
    Homeomorph.ulift
  let rangeEquiv : liftedPlane ≃ₜ
      Set.range ((↑) : liftedPlane → OnePoint liftedPlane) :=
    (OnePoint.isOpenEmbedding_coe (X := liftedPlane)).isEmbedding.toHomeomorph
  have hRange : ParacompactSpace
      (Set.range ((↑) : liftedPlane → OnePoint liftedPlane)) :=
    hHereditary (OnePoint liftedPlane)
      (Set.range ((↑) : liftedPlane → OnePoint liftedPlane))
  have hLiftedPlane : ParacompactSpace liftedPlane :=
    rangeEquiv.paracompactSpace_iff.mpr hRange
  exact liftedPlaneEquiv.paracompactSpace_iff.mp hLiftedPlane

end ParacompactSpace

/- Proposition 41.1 (2). Every closed subspace of a paracompact space is paracompact. -/
#check fun {X : Type u} [TopologicalSpace X] [ParacompactSpace X]
    (s : Set X) (hs : IsClosed s) ↦ hs.isClosedEmbedding_subtypeVal.paracompactSpace

/- Proposition 41.1 (3). A paracompact Hausdorff space is normal; in the book's
convention this is the `T4Space` property. -/
#check T4Space.of_paracompactSpace_t2Space

namespace ParacompactSpace

/- Proposition 41.1 (4). The product of two paracompact spaces need not be paracompact. -/
/-- Paracompactness is not preserved by binary products. -/
theorem not_closed_under_prod :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
      [ParacompactSpace X] [ParacompactSpace Y], ParacompactSpace (X × Y) := by
  intro hProduct
  letI : ParacompactSpace (ULift.{u} SorgenfreyLine) :=
    Homeomorph.ulift.paracompactSpace_iff.mpr sorgenfreyLineParacompact
  letI : ParacompactSpace (ULift.{v} SorgenfreyLine) :=
    Homeomorph.ulift.paracompactSpace_iff.mpr sorgenfreyLineParacompact
  let liftedProductEquiv :
      (ULift.{u} SorgenfreyLine × ULift.{v} SorgenfreyLine) ≃ₜ
        (SorgenfreyLine × SorgenfreyLine) :=
    Homeomorph.ulift.prodCongr Homeomorph.ulift
  -- Specializing product closure to universe-lifted Sorgenfrey lines and transporting
  -- back to the plane contradicts the plane lemma.
  exact sorgenfreyPlaneNotParacompact
    (liftedProductEquiv.paracompactSpace_iff.mp
      (hProduct (ULift.{u} SorgenfreyLine) (ULift.{v} SorgenfreyLine)))

/-- Helper for Proposition 41.1: the binary-product counterexample expressed as a
product over `Fin 2`. -/
theorem not_closed_under_finTwo_pi :
    ¬ ∀ (X : Fin 2 → Type u) [∀ i, TopologicalSpace (X i)]
      [∀ i, ParacompactSpace (X i)], ParacompactSpace (∀ i, X i) := by
  intro h
  apply not_closed_under_prod
  intro X Y topologyX topologyY paracompactX paracompactY
  let Z : Fin 2 → Type u := Fin.cases X (fun _ ↦ Y)
  -- Local instance justification (proof-local temporary data): installs the topology on `Z`.
  letI (i : Fin 2) : TopologicalSpace (Z i) :=
    Fin.cases topologyX (fun _ ↦ topologyY) i
  -- Local instance justification (proof-local temporary data): installs paracompactness on `Z`.
  letI (i : Fin 2) : ParacompactSpace (Z i) :=
    Fin.cases paracompactX (fun _ ↦ paracompactY) i
  exact (Homeomorph.piFinTwo Z).paracompactSpace_iff.mp (h Z)

end ParacompactSpace
