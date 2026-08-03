module

public import Topology_Munkres_2000.Book.Definition_6_0_2.SigmaLocallyFinite
public import Topology_Munkres_2000.Book.Lemma_39_1
public import Mathlib.Topology.Separation.GDelta

public section

universe u

namespace HasSigmaLocallyFiniteBasis

/-- Helper for Lemma 40.1: every open set is the union of an open sequence and also
the union of the closures of that sequence. -/
lemma existsOpenSequenceWithClosureUnion {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) {W : Set X} (hW : IsOpen W) :
    ∃ U : ℕ → Set X,
      (∀ n, IsOpen (U n)) ∧ (⋃ n, U n = W) ∧ (⋃ n, closure (U n) = W) := by
  obtain ⟨𝓑, pieces, hbasis, hcover, hfinite⟩ :=
    (hasSigmaLocallyFiniteBasis_iff X).mp hX
  let selected : ℕ → Set (Set X) :=
    fun n ↦ {B | B ∈ pieces n ∧ closure B ⊆ W}
  let U : ℕ → Set X := fun n ↦ ⋃₀ selected n
  -- Each selected family stays locally finite and consists of basis elements.
  have hpiecesSubset (n : ℕ) : pieces n ⊆ 𝓑 := by
    intro B hB
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨n, hB⟩
  have hselectedFinite (n : ℕ) : (selected n).LocallyFinite := by
    apply (hfinite n).mono
    intro B hB
    exact hB.1
  have hselectedBasis (n : ℕ) : selected n ⊆ 𝓑 := by
    intro B hB
    exact hpiecesSubset n hB.1
  have hUOpen (n : ℕ) : IsOpen (U n) := by
    apply isOpen_sUnion
    intro B hB
    exact hbasis.isOpen (hselectedBasis n hB)
  -- Local finiteness identifies the closure of each selected union pointwise.
  have hUClosure (n : ℕ) :
      closure (U n) = ⋃₀ (closure '' selected n) := by
    simpa only [U] using (hselectedFinite n).closure_sUnion
  have hUClosureSubset (n : ℕ) : closure (U n) ⊆ W := by
    rw [hUClosure n]
    intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
    obtain ⟨B, hB, rfl⟩ := hC
    exact hB.2 hxC
  -- Regularity shrinks a basis neighborhood around each point into `W`.
  have hUUnion : ⋃ n, U n = W := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨B, hB, hxB⟩ := Set.mem_sUnion.mp hxn
      exact hB.2 (subset_closure hxB)
    · intro x hxW
      obtain ⟨B, hBbasis, hxB, hBW⟩ :=
        hbasis.exists_closure_subset (hW.mem_nhds hxW)
      rw [hcover] at hBbasis
      obtain ⟨n, hBpiece⟩ := Set.mem_iUnion.mp hBbasis
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      exact Set.mem_sUnion.mpr ⟨B, ⟨hBpiece, hBW⟩, hxB⟩
  -- The ordinary union supplies the reverse inclusion for the closure union.
  have hUClosureUnion : ⋃ n, closure (U n) = W := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      exact hUClosureSubset n hxn
    · intro x hxW
      have hxUnion : x ∈ ⋃ n, U n := by
        rw [hUUnion]
        exact hxW
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxUnion
      exact Set.mem_iUnion.mpr ⟨n, subset_closure hxn⟩
  exact ⟨U, hUOpen, hUUnion, hUClosureUnion⟩

/-- Helper for Lemma 40.1: a closed set disjoint from a set admits a countable
open cover of the latter whose member closures remain disjoint from it. -/
lemma hasSeparatingCover {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) {s t : Set X} (ht : IsClosed t)
    (hst : Disjoint s t) : HasSeparatingCover s t := by
  obtain ⟨U, hUOpen, hUUnion, hUClosureUnion⟩ :=
    hX.existsOpenSequenceWithClosureUnion ht.isOpen_compl
  refine ⟨U, ?_, ?_⟩
  · -- The exhaustion of `tᶜ` covers `s` by disjointness.
    intro x hxs
    rw [hUUnion]
    intro hxt
    exact Set.disjoint_left.mp hst hxs hxt
  · intro n
    refine ⟨hUOpen n, ?_⟩
    -- Each closure lies in `tᶜ`, so it is disjoint from `t`.
    rw [Set.disjoint_left]
    intro x hxU hxt
    have hxUnion : x ∈ ⋃ n, closure (U n) :=
      Set.mem_iUnion.mpr ⟨n, hxU⟩
    rw [hUClosureUnion] at hxUnion
    exact hxUnion hxt

/-- Helper for Lemma 40.1: a regular space with a countably locally finite basis
is normal. -/
lemma normalSpace {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) : NormalSpace X := by
  -- Opposing separating covers feed the standard countable shrinking argument.
  refine ⟨?_⟩
  intro s t hs ht hst
  exact hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hX.hasSeparatingCover ht hst, hX.hasSeparatingCover hs hst.symm⟩

/-- Helper for Lemma 40.1: every closed set in a regular space with a countably
locally finite basis is a `Gδ` set. -/
lemma closedSetIsGδ {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) {C : Set X} (hC : IsClosed C) : IsGδ C := by
  obtain ⟨U, _hUOpen, _hUUnion, hUClosureUnion⟩ :=
    hX.existsOpenSequenceWithClosureUnion hC.isOpen_compl
  -- Complementing the closure exhaustion presents `C` as an open intersection.
  refine isGδ_iff_eq_iInter_nat.mpr ⟨fun n ↦ (closure (U n))ᶜ, ?_, ?_⟩
  · intro n
    exact isClosed_closure.isOpen_compl
  · have hComplement := congrArg (fun S : Set X ↦ Sᶜ) hUClosureUnion
    simpa only [Set.compl_iUnion, compl_compl] using hComplement.symm

end HasSigmaLocallyFiniteBasis

/-- Lemma 40.1: A regular space with a countably locally finite basis is perfectly normal. -/
theorem HasSigmaLocallyFiniteBasis.t6Space {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) : T6Space X := by
  -- Package the normality and closed-`Gδ` consequences with the inherited `T₀` axiom.
  refine { toT0Space := inferInstance, toPerfectlyNormalSpace := ?_ }
  refine { toNormalSpace := hX.normalSpace, closed_gdelta := ?_ }
  intro C hC
  exact hX.closedSetIsGδ hC

/-- Lemma 40.1 (1): A regular space with a countably locally finite basis is normal. -/
theorem HasSigmaLocallyFiniteBasis.t4Space {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) : T4Space X := by
  let h6 := hX.t6Space
  exact
    { toT1Space := inferInstance
      toNormalSpace := h6.toPerfectlyNormalSpace.toNormalSpace }

/-- Lemma 40.1 (2): Every closed subset of a regular space with a countably locally
finite basis is a `Gδ` set. -/
theorem HasSigmaLocallyFiniteBasis.isGδ {X : Type u} [TopologicalSpace X] [T3Space X]
    (hX : HasSigmaLocallyFiniteBasis X) {C : Set X} (hC : IsClosed C) : IsGδ C :=
  hX.t6Space.closed_gdelta hC

end
