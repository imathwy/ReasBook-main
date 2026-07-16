import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0015_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.II.section06.«0018_Exercise_3»
import DifferentialForms_Cartan_1970.cartan.III.section10.frozen_0011_Theorem_III_4_extra_9.LoopHomotopy
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.cartan.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.cartan.III.section11.«frozen_0011_Proposition_5_1»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0007_Remark_III_5_extra_6»
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».NormalFormSupport
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».WeightedLogResidues
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».WeightedLogPeriodicity
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».PeriodParallelogramBoundary
import DifferentialForms_Cartan_1970.cartan.III.section11.«0013_Proposition_5_2».PeriodParallelogramCoordinates

open Filter
open scoped BigOperators Topology unitInterval
open MeromorphicOn

noncomputable section

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: the divisor-weighted compact-owner support sum on the translated
period parallelogram matches the weighted zero sum minus the weighted pole sum on the fixed
quotient section `P`. -/
lemma supportWeightedDivisorSum_eq_rootPoleSums_mod_periodLattice
    {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hperiods : HasPeriodLattice L g)
    (hπ : Set.BijOn ((↑) : ℂ → ℂ ⧸ L.lattice.toAddSubgroup) P Set.univ)
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet g P roots)
    (hpoles : IsPoleRepresentativeSet g P poles)
    (s : Finset ℂ)
    (hs : ∀ z, z ∈ s ↔ z ∈ (MeromorphicOn.divisor g (L.periodParallelogram z₁)).support)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    (((s.sum fun z ↦ ((MeromorphicOn.divisor g (L.periodParallelogram z₁) z : ℂ) * z)) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) =
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) -
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
  classical
  let Q : Set ℂ := L.periodParallelogram z₁
  let D := MeromorphicOn.divisor g Q
  let repP : ℂ → ℂ := fun z ↦
    Classical.choose (exists_section_representative_sub_mem_lattice (L := L) (P := P) hπ z)
  let sPos : Finset ℂ := s.filter (fun z ↦ 0 < D z)
  let sNeg : Finset ℂ := s.filter (fun z ↦ D z < 0)
  let qPosQ : ℂ → ℂ ⧸ L.lattice.toAddSubgroup := fun z ↦
    ((((D z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)
  let qNegQ : ℂ → ℂ ⧸ L.lattice.toAddSubgroup := fun z ↦
    ((((-D z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)
  let qPosP : ℂ → ℂ ⧸ L.lattice.toAddSubgroup := fun z ↦
    ((((divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)
  let qNegP : ℂ → ℂ ⧸ L.lattice.toAddSubgroup := fun z ↦
    ((((-divisor g P z) • z : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)
  have hrepP_mem : ∀ z : ℂ, repP z ∈ P := by
    intro z
    exact
      (Classical.choose_spec
        (exists_section_representative_sub_mem_lattice (L := L) (P := P) hπ z)).1
  have hrepP_sub : ∀ z : ℂ, repP z - z ∈ L.lattice := by
    intro z
    exact
      (Classical.choose_spec
        (exists_section_representative_sub_mem_lattice (L := L) (P := P) hπ z)).2
  have hQ_compact : IsCompact Q := by
    -- The translated period cell is compact, so its divisor support is finite.
    simpa [Q] using isCompact_periodParallelogram (L := L) z₁
  have hboundary_divisor_zero :
      ∀ z ∈ frontier Q, MeromorphicOn.divisor g Q z = 0 := by
    intro z hz
    -- Boundary order zero rewrites directly to divisor zero on the compact owner `Q`.
    simpa [Q] using
      divisor_eq_zero_on_frontier_of_boundary_order_zero
        (L := L) (g := g) z₁ hg hboundary hz
  have hsupport_interior_support :
      ∀ z, z ∈ D.support → z ∈ interior Q := by
    -- Every divisor support point of the compact owner already lies in the interior of `Q`.
    simpa [Q, D] using
      divisor_support_subset_interior_of_frontier_zero
        (K := Q) (g := g) hQ_compact hboundary_divisor_zero
  have hs_support : ∀ z, z ∈ s ↔ z ∈ D.support := by
    intro z
    simpa [Q, D] using hs z
  have hsupport_interior :
      (↑s : Set ℂ) ⊆ interior Q := by
    intro z hz
    exact hsupport_interior_support z ((hs_support z).1 hz)
  have hs_nonzero : ∀ z ∈ s, D z ≠ 0 := by
    intro z hz
    have hzSupport : z ∈ D.support := (hs_support z).1 hz
    simpa [Function.mem_support] using hzSupport
  have hs_mem_Q : ∀ z ∈ s, z ∈ Q := by
    intro z hz
    exact D.supportWithinDomain ((hs_support z).1 hz)
  have hrepP_injPos : Set.InjOn repP (↑sPos : Set ℂ) := by
    intro z hz w hw hEq
    have hzInterior : z ∈ interior Q := hsupport_interior (by exact (Finset.mem_filter.mp hz).1)
    have hwInterior : w ∈ interior Q := hsupport_interior (by exact (Finset.mem_filter.mp hw).1)
    have hzSub : z - repP z ∈ L.lattice := by
      simpa [sub_eq_add_neg] using neg_mem (hrepP_sub z)
    have hwSub : repP w - w ∈ L.lattice := hrepP_sub w
    have hsub : z - w ∈ L.lattice := by
      have hadd : z - repP z + (repP w - w) ∈ L.lattice := L.lattice.add_mem hzSub hwSub
      simpa [hEq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
    exact
      eq_of_mem_interior_periodParallelogram_and_sub_mem_lattice
        (L := L) hzInterior hwInterior hsub
  have hrepP_injNeg : Set.InjOn repP (↑sNeg : Set ℂ) := by
    intro z hz w hw hEq
    have hzInterior : z ∈ interior Q := hsupport_interior (by exact (Finset.mem_filter.mp hz).1)
    have hwInterior : w ∈ interior Q := hsupport_interior (by exact (Finset.mem_filter.mp hw).1)
    have hzSub : z - repP z ∈ L.lattice := by
      simpa [sub_eq_add_neg] using neg_mem (hrepP_sub z)
    have hwSub : repP w - w ∈ L.lattice := hrepP_sub w
    have hsub : z - w ∈ L.lattice := by
      have hadd : z - repP z + (repP w - w) ∈ L.lattice := L.lattice.add_mem hzSub hwSub
      simpa [hEq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
    exact
      eq_of_mem_interior_periodParallelogram_and_sub_mem_lattice
        (L := L) hzInterior hwInterior hsub
  have hpositiveSupportImage :
      sPos.image repP = roots := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨w, hwPos, hwRep⟩
      have hwS : w ∈ s := (Finset.mem_filter.mp hwPos).1
      have hwDiv : 0 < D w := (Finset.mem_filter.mp hwPos).2
      have hzP : z ∈ P := by simpa [hwRep] using hrepP_mem w
      have hwQ : w ∈ Q := hs_mem_Q w hwS
      have hwSub : w - z ∈ L.lattice := by
        have : z - w ∈ L.lattice := by simpa [hwRep] using hrepP_sub w
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using neg_mem this
      have hdiv :
          divisor g Q w = divisor g P z :=
        divisor_eq_of_sub_mem_period_lattice
          (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hzP hwQ hwSub
      -- A positive support point of `Q` maps to a chosen zero representative in `P`.
      exact (hroots.mem_iff z).2 ⟨hzP, by simpa [D, hdiv] using hwDiv⟩
    · intro hz
      obtain ⟨hzP, hzDiv⟩ := (hroots.mem_iff z).1 hz
      obtain ⟨w, hwQ, hwSub⟩ := exists_mem_periodParallelogram_sub_lattice (L := L) z z₁
      have hdiv :
          divisor g Q w = divisor g P z :=
        divisor_eq_of_sub_mem_period_lattice
          (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hzP hwQ hwSub
      have hwS : w ∈ s := by
        apply (hs_support w).2
        rw [Function.mem_support]
        simpa [D, hdiv] using ne_of_gt hzDiv
      have hclassRep :
          (((repP w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrepP_sub w
      have hclassW :
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hwSub
      have hrepEq : repP w = z := hπ.injOn (hrepP_mem w) hzP (hclassRep.trans hclassW)
      -- Surjectivity onto `roots` comes from choosing the period-cell point in the same lattice class.
      exact
        Finset.mem_image.mpr
          ⟨w, by
            refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
            simpa [D, hdiv] using hzDiv, hrepEq⟩
  have hnegativeSupportImage :
      sNeg.image repP = poles := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨w, hwNeg, hwRep⟩
      have hwS : w ∈ s := (Finset.mem_filter.mp hwNeg).1
      have hwDiv : D w < 0 := (Finset.mem_filter.mp hwNeg).2
      have hzP : z ∈ P := by simpa [hwRep] using hrepP_mem w
      have hwQ : w ∈ Q := hs_mem_Q w hwS
      have hwSub : w - z ∈ L.lattice := by
        have : z - w ∈ L.lattice := by simpa [hwRep] using hrepP_sub w
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using neg_mem this
      have hdiv :
          divisor g Q w = divisor g P z :=
        divisor_eq_of_sub_mem_period_lattice
          (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hzP hwQ hwSub
      -- A negative support point of `Q` maps to a chosen pole representative in `P`.
      exact (hpoles.mem_iff z).2 ⟨hzP, by simpa [D, hdiv] using hwDiv⟩
    · intro hz
      obtain ⟨hzP, hzDiv⟩ := (hpoles.mem_iff z).1 hz
      obtain ⟨w, hwQ, hwSub⟩ := exists_mem_periodParallelogram_sub_lattice (L := L) z z₁
      have hdiv :
          divisor g Q w = divisor g P z :=
        divisor_eq_of_sub_mem_period_lattice
          (L := L) (P := P) (Q := Q) (g := g)
          hg hperiods hzP hwQ hwSub
      have hwS : w ∈ s := by
        apply (hs_support w).2
        rw [Function.mem_support]
        simpa [D, hdiv] using ne_of_lt hzDiv
      have hclassRep :
          (((repP w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hrepP_sub w
      have hclassW :
          (((w : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) =
            (((z : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup)) := by
        rw [QuotientAddGroup.eq_iff_sub_mem]
        simpa using hwSub
      have hrepEq : repP w = z := hπ.injOn (hrepP_mem w) hzP (hclassRep.trans hclassW)
      -- The same lattice-class argument recovers every chosen pole representative.
      exact
        Finset.mem_image.mpr
          ⟨w, by
            refine Finset.mem_filter.mpr ⟨hwS, ?_⟩
            simpa [D, hdiv] using hzDiv, hrepEq⟩
  have htermPos :
      ∀ z ∈ sPos, qPosP (repP z) = qPosQ z := by
    intro z hz
    have hzS : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzQ : z ∈ Q := hs_mem_Q z hzS
    have hzSub : z - repP z ∈ L.lattice := by
      simpa [sub_eq_add_neg] using neg_mem (hrepP_sub z)
    -- The divisor-weighted class depends only on the lattice class of the support point.
    exact
      (divisor_weighted_eq_mod_period_lattice_of_sub_mem
        (L := L) (P := P) (Q := Q) (g := g)
        hg hperiods (hrepP_mem z) hzQ hzSub).symm
  have htermNeg :
      ∀ z ∈ sNeg, qNegP (repP z) = qNegQ z := by
    intro z hz
    have hzS : z ∈ s := (Finset.mem_filter.mp hz).1
    have hzQ : z ∈ Q := hs_mem_Q z hzS
    have hzSub : z - repP z ∈ L.lattice := by
      simpa [sub_eq_add_neg] using neg_mem (hrepP_sub z)
    -- The same transport works for the negated pole multiplicities.
    exact
      (neg_divisor_weighted_eq_mod_period_lattice_of_sub_mem
        (L := L) (P := P) (Q := Q) (g := g)
        hg hperiods (hrepP_mem z) hzQ hzSub).symm
  have hroots_sum :
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        sPos.sum qPosQ := by
    have hImage :
        roots.sum qPosP = sPos.sum (fun z ↦ qPosP (repP z)) := by
      rw [← hpositiveSupportImage]
      simpa [qPosP, sPos] using
        (Finset.sum_image
          (s := sPos) (g := repP) (f := qPosP) hrepP_injPos)
    -- Replace the representative sum over `roots` by the transported positive support sum of `Q`.
    calc
      (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) = roots.sum qPosP := by
            simp [qPosP]
      _ = sPos.sum (fun z ↦ qPosP (repP z)) := hImage
      _ = sPos.sum qPosQ := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            exact htermPos z hz
  have hpoles_sum :
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) =
        sNeg.sum qNegQ := by
    have hImage :
        poles.sum qNegP = sNeg.sum (fun z ↦ qNegP (repP z)) := by
      rw [← hnegativeSupportImage]
      simpa [qNegP, sNeg] using
        (Finset.sum_image
          (s := sNeg) (g := repP) (f := qNegP) hrepP_injNeg)
    -- The pole representatives give the negative support contribution after the same transport.
    calc
      (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) = poles.sum qNegP := by
            simp [qNegP]
      _ = sNeg.sum (fun z ↦ qNegP (repP z)) := hImage
      _ = sNeg.sum qNegQ := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            exact htermNeg z hz
  have hfilter_not_pos_eq_neg :
      s.filter (fun z ↦ ¬ 0 < D z) = sNeg := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzS, hzNotPos⟩
      have hzNe : D z ≠ 0 := hs_nonzero z hzS
      rcases lt_or_gt_of_ne hzNe with hzNeg | hzPos
      · exact Finset.mem_filter.mpr ⟨hzS, hzNeg⟩
      · exact (hzNotPos hzPos).elim
    · intro hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, by
        exact not_lt_of_gt ((Finset.mem_filter.mp hz).2)⟩
  have hnegSum :
      sNeg.sum qPosQ = -sNeg.sum qNegQ := by
    -- On the negative part of the support, `D z • z = -((-D z) • z)` pointwise.
    calc
      sNeg.sum qPosQ = sNeg.sum (fun z ↦ -qNegQ z) := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        simp [qPosQ, qNegQ, smul_eq_mul]
      _ = -sNeg.sum qNegQ := by
        simp [qNegQ]
  have hs_split :
      s.sum qPosQ = sPos.sum qPosQ - sNeg.sum qNegQ := by
    -- Split the support into positive and nonpositive parts, then rewrite the nonpositive part
    -- as the negative support using support nonvanishing.
    calc
      s.sum qPosQ =
          sPos.sum qPosQ + (s.filter (fun z ↦ ¬ 0 < D z)).sum qPosQ := by
            symm
            simpa [sPos] using
              (Finset.sum_filter_add_sum_filter_not
                (s := s) (p := fun z ↦ 0 < D z) (f := qPosQ))
      _ = sPos.sum qPosQ + sNeg.sum qPosQ := by rw [hfilter_not_pos_eq_neg]
      _ = sPos.sum qPosQ + (-sNeg.sum qNegQ) := by rw [hnegSum]
      _ = sPos.sum qPosQ - sNeg.sum qNegQ := by abel
  -- Assemble the compact-owner support split with the two transport identities for `roots` and
  -- `poles`.
  calc
    (((s.sum fun z ↦ ((MeromorphicOn.divisor g (L.periodParallelogram z₁) z : ℂ) * z)) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) = s.sum qPosQ := by
          simp [Q, D, qPosQ, smul_eq_mul]
    _ = sPos.sum qPosQ - sNeg.sum qNegQ := hs_split
    _ =
        (((roots.sum fun z ↦ divisor g P z • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) -
        (((poles.sum fun z ↦ (-divisor g P z) • z) : ℂ) :
          ℂ ⧸ L.lattice.toAddSubgroup) := by
          rw [← hroots_sum, ← hpoles_sum]

/-- Helper for Proposition 5.2: on a boundary-generic translated period parallelogram, the source
weighted residue computation rewrites the normalized boundary integral as the weighted divisor
support sum on that compact owner. -/
lemma weightedBoundaryIntegralDivTwoPiI_eq_supportWeightedDivisorSum
    {g : ℂ → ℂ} {z₁ : ℂ}
    (hg : Meromorphic g)
    (hboundary : ∀ z ∈ frontier (L.periodParallelogram z₁),
      meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    let Q : Set ℂ := L.periodParallelogram z₁
    let Γ : Unit → ClosedPath ℂ := fun _ ↦ (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath
    let s : Finset ℂ :=
      (divisor_support_finite_of_isCompact (K := Q) (g := g)
        (isCompact_periodParallelogram (L := L) z₁)).toFinset
    (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
        (2 * Real.pi * Complex.I : ℂ) =
      Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z) := by
  classical
  let Q : Set ℂ := L.periodParallelogram z₁
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (periodParallelogramBoundaryPath (L := L) z₁).toClosedPath
  let s : Finset ℂ :=
    (divisor_support_finite_of_isCompact (K := Q) (g := g)
      (isCompact_periodParallelogram (L := L) z₁)).toFinset
  let gU : Set ℂ := Set.univ
  have hΓ : IsOrientedBoundaryOf Q Γ := by
    -- The explicit translated four-edge loop is already the oriented boundary of `Q`.
    simpa [Q, Γ] using periodParallelogramBoundary_isOrientedBoundaryOf (L := L) z₁
  have hQ_compact : IsCompact Q := by
    -- The translated period cell is compact.
    simpa [Q] using isCompact_periodParallelogram (L := L) z₁
  have hboundary_divisor_zero :
      ∀ z ∈ frontier Q, MeromorphicOn.divisor g Q z = 0 := by
    intro z hz
    -- Boundary order zero translates directly to divisor zero on the compact owner.
    simpa [Q] using
      divisor_eq_zero_on_frontier_of_boundary_order_zero
        (L := L) (g := g) z₁ hg hboundary hz
  have hsupport_iff :
      ∀ z, z ∈ s ↔ z ∈ (MeromorphicOn.divisor g Q).support := by
    intro z
    -- The chosen finset `s` is just the finite support of the divisor on `Q`.
    simpa [s, Q] using
      (Set.Finite.mem_toFinset
        (divisor_support_finite_of_isCompact (K := Q) (g := g) hQ_compact))
  have hsK : (↑s : Set ℂ) ⊆ interior Q := by
    -- The divisor support stays away from the frontier once the frontier divisor vanishes.
    simpa [s] using
      divisor_support_subset_interior_of_frontier_zero
        (K := Q) (g := g) hQ_compact hboundary_divisor_zero
  have hU_exists :=
      exists_open_owner_with_divisor_zero_off_support
        (D := Set.univ) (K := Q) (g := g) hg.meromorphicOn
        isOpen_univ hQ_compact (by intro z hz; simp [gU])
  dsimp only at hU_exists
  rcases hU_exists with ⟨U, hU_open, hQU, hUgU, hdiv_zero_raw⟩
  have hdiv_zero_off_support :
      ∀ z, z ∈ U → z ∉ (↑s : Set ℂ) → MeromorphicOn.divisor g U z = 0 := by
    intro z hzU hzS
    exact hdiv_zero_raw z hzU (by simpa [s] using hzS)
  let gNF : ℂ → ℂ := toMeromorphicNFOn g U
  have hgU : MeromorphicOn g U := hg.meromorphicOn.mono_set hUgU
  have hgNF : MeromorphicNFOn gNF U := by
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g U
  have hhol_nf :
      DifferentiableOn ℂ (fun w ↦ w * logDeriv gNF w) (U \ (↑s : Set ℂ)) := by
    -- Off the support finset, the open-owner divisor vanishes, so the weighted logarithmic
    -- derivative of the normal form is holomorphic there.
    refine
      differentiableOn_weightedLogDeriv_toMeromorphicNFOn_of_divisor_zero
        (g := g) (U := U) (V := U \ (↑s : Set ℂ)) hgU (by intro z hz; exact hz.1) ?_
    intro z hz
    exact hdiv_zero_off_support z hz.1 hz.2
  have hboundary_disjoint :
      ∀ i, Disjoint (Set.range ((Γ i).toPath)) (↑s : Set ℂ) := by
    -- The boundary never meets the interior divisor support finset.
    simpa [Q, Γ, s] using
      (boundary_path_disjoint_of_divisor_frontier_zero
        (K := Q) (Γ := Γ) (g := g) hΓ hboundary_divisor_zero)
  have hboundary_transfer :
      ∀ i,
        ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z =
          ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv gNF w) dz) z := by
    intro i
    have hRangeU : Set.range ((Γ i).toPath) ⊆ U := by
      intro z hz
      exact hQU (hQ_compact.isClosed.frontier_subset (hΓ.range_toPath_subset_frontier i hz))
    -- Replace the boundary integrand by the normal-form owner on the open collar `U`.
    simpa [gNF] using
      (curveIntegral_eq_of_codiscrete_boundary_component
        (K := Q) (U := U) (Γ := Γ) hΓ i
        (φ := fun z ↦ z * logDeriv g z)
        (ψ := fun z ↦ z * logDeriv gNF z)
        (weightedLogDeriv_toMeromorphicNFOn_eq_codiscrete (g := g) hgU)
        hRangeU)
  have hboundary_sum_transfer :
      (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) =
        ∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv gNF w) dz) z := by
    -- Sum the componentwise owner-change equalities over the singleton boundary family.
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hboundary_transfer i
  have hlocal_residue :
      ∀ z ∈ s,
        IsolatedLocalResidueCircle Q U s (fun w ↦ w * logDeriv gNF w)
          z ((MeromorphicOn.divisor g Q z : ℂ) * z) := by
    -- The weighted local residue computation is local; applying the residue theorem also requires
    -- shrinking the chosen circles so they isolate the finite support points.
    intro z hzS
    have hzInterior : z ∈ interior Q := hsK (by simpa using hzS)
    have hzQ : z ∈ Q := interior_subset hzInterior
    have hzU : z ∈ U := hQU hzQ
    have hzSupport : z ∈ (MeromorphicOn.divisor g Q).support := (hsupport_iff z).1 hzS
    have hdiv_ne : MeromorphicOn.divisor g Q z ≠ 0 := by
      simpa [Function.mem_support] using hzSupport
    have horder :
        meromorphicOrderAt gNF z = (MeromorphicOn.divisor g Q z : WithTop ℤ) := by
      -- Read the normal-form order directly from the compact-owner divisor value at `z`.
      simpa [gNF] using
        meromorphicOrderAt_toMeromorphicNFOn_eq_of_divisor_ne_zero
          (D := U) (K := Q) (U := U) (g := g) hgU hQU subset_rfl hzQ hzU hdiv_ne
    let isolatedOwner : Set ℂ := U \ ((↑s : Set ℂ) \ ({z} : Set ℂ))
    have hisolatedOwner_open : IsOpen isolatedOwner := by
      -- Remove the other finitely many support points from the open collar around `Q`.
      refine hU_open.sdiff ?_
      exact (s.finite_toSet.subset (by intro w hw; exact hw.1)).isClosed
    have hzIsolatedOwner : z ∈ isolatedOwner := by
      refine ⟨hzU, ?_⟩
      intro hzBad
      exact hzBad.2 rfl
    have hlocal :
        LocalResidueCircle Q isolatedOwner (fun w ↦ w * logDeriv gNF w)
          z ((MeromorphicOn.divisor g Q z : ℂ) * z) := by
      -- The weighted logarithmic derivative has the expected residue once the order is fixed.
      exact
        localResidueCircle_weighted_logDeriv_of_order
          hzInterior hzIsolatedOwner hisolatedOwner_open (hgNF hzU).meromorphicAt horder
    rcases hlocal with ⟨radius, hradius, hballQ, hballIsolatedOwner, hcircle⟩
    refine ⟨radius, hradius, hballQ, ?_, ?_, ?_, hcircle⟩
    · -- The isolated owner still sits inside the open collar `U`.
      intro w hw
      exact (hballIsolatedOwner hw).1
    · -- The deleted finite set makes every other support point miss the closed ball.
      intro w hwS hwz hwBall
      exact
        (hballIsolatedOwner hwBall).2
          ⟨by simpa using hwS, by simpa [Set.mem_singleton_iff] using hwz⟩
    · -- On the punctured ball, the weighted logarithmic derivative is holomorphic because the
      -- isolated owner deleted the entire finite support set except for the center.
      refine hhol_nf.mono ?_
      intro w hw
      have hwClosed : w ∈ Metric.closedBall z radius := Metric.ball_subset_closedBall hw.1
      have hwOwner : w ∈ isolatedOwner := hballIsolatedOwner hwClosed
      refine ⟨hwOwner.1, ?_⟩
      intro hwS
      have hwne : w ≠ z := by
        simpa [Set.mem_singleton_iff] using hw.2
      exact
        hwOwner.2
          ⟨by simpa using hwS, by simpa [Set.mem_singleton_iff] using hwne⟩
  have hboundary_nf :
      (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv gNF w) dz) z) =
        (2 * Real.pi * Complex.I : ℂ) *
          Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z) := by
    -- Apply the oriented-boundary residue theorem to the weighted logarithmic derivative of the
    -- normal-form owner on the open collar.
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (s := s)
        (residue := fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z)
        hΓ hQU hU_open hboundary_disjoint hhol_nf hlocal_residue
  -- Divide the weighted residue identity by `2π i` after replacing the boundary integrand by the
  -- normal-form owner.
  calc
    (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv g w) dz) z) /
        (2 * Real.pi * Complex.I : ℂ) =
      (∑ i : Unit, ∫ᶜ z in (Γ i).toPath, ((fun w ↦ w * logDeriv gNF w) dz) z) /
        (2 * Real.pi * Complex.I : ℂ) := by
          rw [hboundary_sum_transfer]
    _ =
        ((2 * Real.pi * Complex.I : ℂ) *
            Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z)) /
          (2 * Real.pi * Complex.I : ℂ) := by
            rw [hboundary_nf]
    _ = Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z) := by
      simpa [mul_comm] using
        (mul_div_cancel_left₀
          (Finset.sum s (fun z ↦ (MeromorphicOn.divisor g Q z : ℂ) * z))
          Complex.two_pi_I_ne_zero)

/-- Helper for Proposition 5.2: codiscrete equality on an open owner transfers to equality of the
integrals over a nondegenerate affine segment whose image stays inside that owner. -/
lemma curveIntegral_segment_eq_of_codiscreteWithin
    {φ ψ : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} (hne : a ≠ b)
    (hEq : φ =ᶠ[Filter.codiscreteWithin U] ψ)
    (hRange : Set.range (Path.segment a b) ⊆ U) :
    ∫ᶜ z in Path.segment a b, ((φ dz) z) =
      ∫ᶜ z in Path.segment a b, ((ψ dz) z) := by
  let γ : Path a b := Path.segment a b
  let A : Set ℂ := {z | φ z = ψ z}
  have hA_U : A ∈ Filter.codiscreteWithin U := by
    simpa [A, Filter.EventuallyEq] using hEq
  have hA_range : A ∈ Filter.codiscreteWithin (Set.range γ) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA_U ⊢
    intro z hzRange
    have hzU : z ∈ U := hRange (by simpa [γ] using hzRange)
    -- Restrict the ambient codiscrete equality to the compact segment image.
    refine Filter.mem_of_superset (hA_U z hzU) ?_
    intro w hw
    rcases hw with hwA | hwUc
    · exact Or.inl hwA
    · exact Or.inr fun hwRange ↦ hwUc (hRange (by simpa [γ] using hwRange))
  have hBadImage : (Set.range γ \ A).Finite := by
    -- Compactness of the segment image makes the bad image set finite.
    exact (isCompact_range γ.continuous).finite_diff_of_mem_codiscreteWithin hA_range
  let B : Set ℝ := (γ.extend ⁻¹' (Set.range γ \ A)) ∩ Set.uIoc (0 : ℝ) 1
  have hline_injective :
      Function.Injective (fun t : Set.uIoc (0 : ℝ) 1 ↦ γ.extend t) := by
    intro s t hst
    apply Subtype.ext
    have hsIoc : (s : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using s.2
    have htIoc : (t : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using t.2
    have hsIcc : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hsIoc.1, hsIoc.2⟩
    have htIcc : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
    have hPath : γ ⟨(s : ℝ), hsIcc⟩ = γ ⟨(t : ℝ), htIcc⟩ := by
      simpa [γ, Path.extend_apply (γ := γ) hsIcc, Path.extend_apply (γ := γ) htIcc,
        Path.segment_apply] using hst
    rcases
        (AffineMap.lineMap_eq_lineMap_iff
          (p₀ := a) (p₁ := b) (c₁ := (s : ℝ)) (c₂ := (t : ℝ))).mp hPath with
      hab | hst'
    · exact (hne hab).elim
    · exact hst'
  have hBadParamSubtype :
      {t : Set.uIoc (0 : ℝ) 1 | γ.extend t ∈ Set.range γ \ A}.Finite := by
    -- Injectivity of the affine segment parameterization keeps the bad parameter set finite.
    exact hBadImage.preimage hline_injective.injOn
  have hBadParam : B.Finite := by
    have hImage :
        (Subtype.val '' {t : Set.uIoc (0 : ℝ) 1 | γ.extend t ∈ Set.range γ \ A}).Finite := by
      exact hBadParamSubtype.image Subtype.val
    convert hImage using 1
    ext t
    constructor
    · intro ht
      refine ⟨⟨t, ht.2⟩, ?_, rfl⟩
      simpa [B] using ht.1
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simpa [B] using ht, t.2⟩
  have hParamEq :
      (fun t : ℝ ↦ (((φ dz) (γ.extend t)) (deriv γ.extend t)))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ (((ψ dz) (γ.extend t)) (deriv γ.extend t))) := by
    change
      {t : ℝ |
          (((φ dz) (γ.extend t)) (deriv γ.extend t)) =
            (((ψ dz) (γ.extend t)) (deriv γ.extend t))} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    have hBadParam_cod :
        ({t : ℝ | t ∉ B} : Set ℝ) ∈
          Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1) :=
      compl_finite_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) 1) hBadParam
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hBadParam_cod
    intro t ht
    -- Away from the finite bad parameter set, the two scalar coefficients agree on the segment.
    refine Filter.mem_of_superset (hBadParam_cod t ht) ?_
    intro u hu
    rcases hu with huNotB | huOutside
    · by_cases huI : u ∈ Set.uIoc (0 : ℝ) 1
      · have huNotPre : u ∉ γ.extend ⁻¹' (Set.range γ \ A) := by
          intro huPre
          exact huNotB ⟨huPre, huI⟩
        have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa using huI
        have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt huIoc.1, huIoc.2⟩
        have huRange : γ.extend u ∈ Set.range γ := by
          refine ⟨⟨u, huIcc⟩, ?_⟩
          simpa [γ, Path.extend_apply (γ := γ) huIcc]
        have huA : γ.extend u ∈ A := by
          by_contra huA
          exact huNotPre ⟨huRange, huA⟩
        have huEq : φ (γ.extend u) = ψ (γ.extend u) := by
          simpa [A] using huA
        exact Or.inl (by simp [huEq])
      · exact Or.inr huI
    · exact Or.inr huOutside
  -- Once the parameter integrands agree codiscretely on `Set.uIoc (0,1]`, the segment integrals
  -- coincide.
  simpa [γ] using curveIntegral_eq_of_codiscrete_param_integrand γ hParamEq

/-- Helper for Proposition 5.2: on an open owner, the normal-form representative agrees with the
original meromorphic function on a punctured neighborhood of each owner point. -/
lemma toMeromorphicNFOn_eq_eventuallyEq_punctured
    {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U) (hg : MeromorphicOn g U)
    {z : ℂ} (hz : z ∈ U) :
    (fun w ↦ toMeromorphicNFOn g U w) =ᶠ[nhdsWithin z ({z}ᶜ)] g := by
  let h : ℂ → ℂ := toMeromorphicNFOn g U
  let A : Set ℂ := {w | h w = g w}
  have hA : A ∈ Filter.codiscreteWithin U := by
    simpa [A, h, Filter.EventuallyEq] using
      (toMeromorphicNFOn_eqOn_codiscrete (U := U) hg).symm
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA
  have hA' : A ∪ Uᶜ ∈ nhdsWithin z ({z}ᶜ) := hA z hz
  have hU' : U ∈ nhdsWithin z ({z}ᶜ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨U, hU.mem_nhds hz, ?_⟩
    intro w hw
    exact hw.1
  have hEqSet : A ∈ nhdsWithin z ({z}ᶜ) := by
    -- Intersect the codiscrete equality set with the open owner to remove the ambient complement.
    filter_upwards [hA', hU'] with w hwA hwU
    exact hwA.elim id (fun hwUc => False.elim (hwUc hwU))
  simpa [A, h, Filter.EventuallyEq] using hEqSet

/-- Helper for Proposition 5.2: if the original meromorphic function has order zero at an owner
point, then the chosen normal-form representative is nonzero at that point. -/
lemma toMeromorphicNFOn_nonzero_of_meromorphicOrderAt_eq_zero
    {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U) (hg : MeromorphicOn g U)
    {z : ℂ} (hz : z ∈ U) (horder : meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    toMeromorphicNFOn g U z ≠ 0 := by
  let h : ℂ → ℂ := toMeromorphicNFOn g U
  have hhNF : MeromorphicNFAt h z := (meromorphicNFOn_toMeromorphicNFOn g U) hz
  rcases
      (meromorphicOrderAt_eq_int_iff (f := g) (x := z) (n := 0) (hg z hz)).1
        (by simpa using horder) with
    ⟨g₀, hg₀, hg₀_ne, hEq_g_raw⟩
  have hEq_hg₀ : h =ᶠ[nhdsWithin z ({z}ᶜ)] g₀ := by
    exact
      (toMeromorphicNFOn_eq_eventuallyEq_punctured (g := g) hU hg hz).trans
        (by simpa using hEq_g_raw)
  have hEq_nhds : h =ᶠ[nhds z] g₀ :=
    (hhNF.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg₀.meromorphicNFAt).1 hEq_hg₀
  have hz_eq : h z = g₀ z := hEq_nhds.self_of_nhds
  -- The local analytic representative from the order-zero normal form keeps the center nonzero.
  simpa [h, hz_eq] using hg₀_ne

/-- Helper for Proposition 5.2: if the original meromorphic function has a period `ω` and order
zero at `z`, then the chosen normal-form owner takes the same value at `z` and `z + ω`. -/
lemma toMeromorphicNFOn_period_eq_of_meromorphicOrderAt_eq_zero
    {U : Set ℂ} {g : ℂ → ℂ} (hU : IsOpen U) (hg : MeromorphicOn g U)
    {z ω : ℂ} (hz : z ∈ U) (hzω : z + ω ∈ U)
    (hperiodic : Function.Periodic g ω)
    (horder : meromorphicOrderAt g z = (0 : WithTop ℤ)) :
    toMeromorphicNFOn g U (z + ω) = toMeromorphicNFOn g U z := by
  let h : ℂ → ℂ := toMeromorphicNFOn g U
  have hhNFz : MeromorphicNFAt h z := (meromorphicNFOn_toMeromorphicNFOn g U) hz
  have hhNFzω : MeromorphicNFAt h (z + ω) := (meromorphicNFOn_toMeromorphicNFOn g U) hzω
  rcases
      (meromorphicOrderAt_eq_int_iff (f := g) (x := z) (n := 0) (hg z hz)).1
        (by simpa using horder) with
    ⟨g₀, hg₀, _, hEq_g_raw⟩
  have hEq_g : g =ᶠ[nhdsWithin z ({z}ᶜ)] g₀ := by
    simpa using hEq_g_raw
  have hEq_hz : h =ᶠ[nhds z] g₀ := by
    have hEq_hg₀ : h =ᶠ[nhdsWithin z ({z}ᶜ)] g₀ := by
      exact
        (toMeromorphicNFOn_eq_eventuallyEq_punctured (g := g) hU hg hz).trans
          hEq_g
    exact
      (hhNFz.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg₀.meromorphicNFAt).1 hEq_hg₀
  have hz_eq : h z = g₀ z := hEq_hz.self_of_nhds
  let g₁ : ℂ → ℂ := fun w ↦ g₀ (w - ω)
  have hg₁ : AnalyticAt ℂ g₁ (z + ω) := by
    have hsub : AnalyticAt ℂ (fun w : ℂ ↦ w - ω) (z + ω) := by
      fun_prop
    -- Translate the local order-zero normal form from `z` to `z + ω`.
    have hg₀' : AnalyticAt ℂ g₀ ((fun w : ℂ ↦ w - ω) (z + ω)) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg₀
    have hcomp :
        AnalyticAt ℂ (g₀ ∘ fun w : ℂ ↦ w - ω) (z + ω) :=
      hg₀'.comp (f := fun w : ℂ ↦ w - ω) hsub
    simpa [Function.comp, g₁] using hcomp
  have hsub_tendsto :
      Filter.Tendsto (fun w : ℂ ↦ w - ω)
        (nhdsWithin (z + ω) ({z + ω}ᶜ)) (nhdsWithin z ({z}ᶜ)) := by
    have hmapsto :
        Set.MapsTo (fun w : ℂ ↦ w - ω) ({z + ω}ᶜ) ({z}ᶜ) := by
      intro w hw
      change w - ω ∉ ({z} : Set ℂ)
      intro hwz
      have hwz' : w - ω = z := by
        simpa [Set.mem_singleton_iff] using hwz
      have hne : w ≠ z + ω := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hw
      apply hne
      calc
        w = (w - ω) + ω := by
          abel
        _ = z + ω := by rw [hwz']
    have hcont : ContinuousWithinAt (fun w : ℂ ↦ w - ω) ({z + ω}ᶜ) (z + ω) := by
      fun_prop
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hcont.tendsto_nhdsWithin hmapsto
  have hEq_g₁ : g =ᶠ[nhdsWithin (z + ω) ({z + ω}ᶜ)] g₁ := by
    have hperiod :
        g =ᶠ[nhdsWithin (z + ω) ({z + ω}ᶜ)] fun w ↦ g (w - ω) := by
      filter_upwards [Filter.Eventually.of_forall (fun w : ℂ ↦ hperiodic (w - ω))] with w hw
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hw
    have hcomp :
        (fun w ↦ g (w - ω)) =ᶠ[nhdsWithin (z + ω) ({z + ω}ᶜ)] fun w ↦ g₀ (w - ω) := by
      simpa [g₁] using hEq_g.comp_tendsto hsub_tendsto
    exact hperiod.trans hcomp
  have hEq_hzω : h =ᶠ[nhds (z + ω)] g₁ := by
    have hEq_hg₁ : h =ᶠ[nhdsWithin (z + ω) ({z + ω}ᶜ)] g₁ := by
      exact
        (toMeromorphicNFOn_eq_eventuallyEq_punctured (g := g) hU hg hzω).trans
          hEq_g₁
    exact
      (hhNFzω.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg₁.meromorphicNFAt).1 hEq_hg₁
  have hzω_eq : h (z + ω) = g₁ (z + ω) := hEq_hzω.self_of_nhds
  calc
    h (z + ω) = g₁ (z + ω) := hzω_eq
    _ = g₀ z := by simp [g₁]
    _ = h z := hz_eq.symm

/-- Helper for Proposition 5.2: if the image of an affine segment under a holomorphic
nonvanishing owner closes up, then the normalized logarithmic-derivative integral on that segment
is an integer. -/
lemma segmentLogDerivIntegral_divTwoPiI_eq_int_of_endpoint_eq
    {h : ℂ → ℂ} {a b : ℂ} {U : Set ℂ}
    (hU_open : IsOpen U)
    (hRange : Set.range (Path.segment a b) ⊆ U)
    (hh_diff : DifferentiableOn ℂ h U)
    (hendpoint : h b = h a)
    (hnonzero : ∀ t : I, h (Path.segment a b t) ≠ 0) :
    ∃ n : ℤ,
      (∫ᶜ z in Path.segment a b, ((logDeriv h dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  let η : Path (h a) (h b) := (Path.segment a b).map' ((hh_diff.continuousOn).mono hRange)
  let γ : Path (h a) (h a) := η.cast rfl hendpoint.symm
  have hcont_inv : ContinuousOn (fun w : ℂ ↦ w⁻¹) (h '' Set.range (Path.segment a b)) := by
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    rcases hz with ⟨t, rfl⟩
    exact hnonzero t
  have hchange :=
    Path.curveIntegral_map'_eq_curveIntegral_mul_deriv
      (γ := Path.segment a b)
      (Path.segment_isPiecewiseDifferentiable a b)
      hU_open hRange hh_diff hcont_inv
  have hγ_nonzero : ∀ t : I, γ t ≠ 0 := by
    intro t
    simpa [γ, η] using hnonzero t
  have hchange' :
      ∫ᶜ z in Path.segment a b, ((logDeriv h dz) z) =
        ∫ᶜ w in η, indexForm 0 w := by
    calc
      ∫ᶜ z in Path.segment a b, ((logDeriv h dz) z) =
          ∫ᶜ z in Path.segment a b,
            (1 : ℂ →L[ℂ] ℂ).smulRight ((fun w : ℂ ↦ w⁻¹) (h z) * deriv h z) := by
              simp [Complex.scalarOneForm, logDeriv, div_eq_mul_inv, mul_comm]
      _ = ∫ᶜ w in η, (1 : ℂ →L[ℂ] ℂ).smulRight ((fun w : ℂ ↦ w⁻¹) w) := by
            rw [← hchange]
      _ = ∫ᶜ w in η, indexForm 0 w := by
            simp [indexForm]
  have hη_piecewise : η.IsPiecewiseDifferentiable := by
    -- Mapping the affine segment through the holomorphic owner keeps the path piecewise smooth.
    exact
      (Path.segment_isPiecewiseDifferentiable a b).map'_of_differentiableOn
        (hD := hU_open) hRange hh_diff
  have hγ_piecewise : γ.IsPiecewiseDifferentiable := by
    -- The endpoint cast does not change the underlying parametrized path.
    simpa [γ] using hη_piecewise
  have hγ_range :
      Set.range γ ⊆ ({0} : Set ℂ)ᶜ := by
    rintro _ ⟨t, rfl⟩
    simpa [γ, η, Set.mem_compl_iff, Set.mem_singleton_iff] using hnonzero t
  have hγ_integrable_real :
      CurveIntegrable (fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ) γ := by
    -- The logarithmic index form is continuous on any loop avoiding `0`.
    exact
      Path.curveIntegrable_of_piecewiseDifferentiable_of_continuousOn
        (ω := fun z : ℂ ↦ (indexForm 0 z).restrictScalars ℝ)
        (indexForm_zero_continuousOn hγ_range) hγ_piecewise (by
          intro z hz
          exact hz)
  have hγ_integrable : CurveIntegrable (indexForm 0) γ := by
    simpa using hγ_integrable_real
  rcases Path.curveIntegral_inv_div_two_pi_I_eq_int
      (γ := γ) hγ_nonzero hγ_piecewise hγ_integrable with ⟨n, hn⟩
  -- Rewrite the segment integral through the mapped closed image path and invoke the winding
  -- number theorem.
  refine ⟨n, ?_⟩
  calc
    (∫ᶜ z in Path.segment a b, ((logDeriv h dz) z)) /
        (2 * Real.pi * Complex.I : ℂ) =
      (∫ᶜ w in η, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) := by
        rw [hchange']
    _ = (∫ᶜ w in γ, indexForm 0 w) / (2 * Real.pi * Complex.I : ℂ) := by
        simp [γ, curveIntegral_cast]
    _ = (n : ℂ) := hn

/-- Helper for Proposition 5.2: once a normalized segment logarithmic integral is an integer,
multiplying it by a lattice period gives the zero class in the period quotient. -/
lemma periodSegmentCorrection_eq_zero_mod_periodLattice
    {ω J : ℂ} (hω : ω ∈ L.lattice)
    (hJ : ∃ n : ℤ, J / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) :
    (((ω * J / (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) :
      ℂ ⧸ L.lattice.toAddSubgroup) = 0 := by
  rcases hJ with ⟨n, hn⟩
  -- Rewrite the correction term as an integer multiple of the lattice vector `ω`.
  calc
    (((ω * J / (2 * Real.pi * Complex.I : ℂ) : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) =
      (((ω * (J / (2 * Real.pi * Complex.I : ℂ)) : ℂ) : ℂ) :
        ℂ ⧸ L.lattice.toAddSubgroup) := by
          simp [div_eq_mul_inv, mul_assoc]
    _ = (((ω * (n : ℂ) : ℂ) : ℂ) : ℂ ⧸ L.lattice.toAddSubgroup) := by rw [hn]
    _ = 0 := by
      rw [QuotientAddGroup.eq_zero_iff]
      simpa [smul_eq_mul, mul_comm] using L.lattice.smul_mem n hω
