import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«0011_Proposition_5_1».PeriodParallelogramBoundary

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open MeromorphicOn

noncomputable section

-- Semantic recall note: the source-facing owner for a period parallelogram is
-- `PeriodPair.periodParallelogram`, the core period-data owner is `HasPeriodLattice`, and the
-- zero/pole counts are read from mathlib's canonical divisor owner `MeromorphicOn.divisor`.

/-- `roots` lists the points of `P` where the divisor of `f` is positive. -/
def IsZeroRepresentativeSet (f : ℂ → ℂ) (P : Set ℂ) (roots : Finset ℂ) : Prop :=
  ∀ z : ℂ, z ∈ roots ↔ z ∈ P ∧ 0 < divisor f P z

@[simp]
theorem IsZeroRepresentativeSet.mem_iff
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) (z : ℂ) :
    z ∈ roots ↔ z ∈ P ∧ 0 < divisor f P z :=
  hroots z

/-- `poles` lists the points of `P` where the divisor of `f` is negative. -/
def IsPoleRepresentativeSet (f : ℂ → ℂ) (P : Set ℂ) (poles : Finset ℂ) : Prop :=
  ∀ z : ℂ, z ∈ poles ↔ z ∈ P ∧ divisor f P z < 0

@[simp]
theorem IsPoleRepresentativeSet.mem_iff
    {f : ℂ → ℂ} {P : Set ℂ} {poles : Finset ℂ}
    (hpoles : IsPoleRepresentativeSet f P poles) (z : ℂ) :
    z ∈ poles ↔ z ∈ P ∧ divisor f P z < 0 :=
  hpoles z

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: summing the divisor over a zero
representative set recovers the total positive divisor mass. -/
theorem IsZeroRepresentativeSet.sum_divisor_eq_finsum_posPart
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) :
    roots.sum (fun z ↦ divisor f P z) = ∑ᶠ z, (divisor f P)⁺ z := by
  have hsupp :
      Function.support (fun z ↦ (divisor f P z)⁺) ⊆ (↑roots : Set ℂ) := by
    intro z hz
    have hzsupport : z ∈ (divisor f P)⁺.support := by
      simpa [Function.support, Function.locallyFinsuppWithin.posPart_apply] using hz
    have hzP : z ∈ P := ((divisor f P)⁺).supportWithinDomain hzsupport
    have hzpos : 0 < divisor f P z := by
      have hzneq : (divisor f P z)⁺ ≠ 0 := by
        simpa [Function.locallyFinsuppWithin.posPart_apply] using hzsupport
      have hznot : ¬ divisor f P z ≤ 0 := by
        intro hzle
        exact hzneq (posPart_eq_zero.2 hzle)
      exact lt_of_not_ge hznot
    exact (hroots.mem_iff z).2 ⟨hzP, hzpos⟩
  calc
    roots.sum (fun z ↦ divisor f P z) = roots.sum (fun z ↦ (divisor f P z)⁺) := by
      -- Each chosen root already contributes a positive divisor value.
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzpos : 0 < divisor f P z := (hroots.mem_iff z).1 hz |>.2
      exact (posPart_of_nonneg (le_of_lt hzpos)).symm
    _ = ∑ᶠ z, (divisor f P)⁺ z := by
      -- Replace the finite representative sum by the ambient positive-part `finsum`.
      symm
      exact finsum_eq_sum_of_support_subset _ hsupp

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: summing pole multiplicities over a
pole representative set recovers the total negative divisor mass. -/
theorem IsPoleRepresentativeSet.sum_neg_divisor_eq_finsum_negPart
    {f : ℂ → ℂ} {P : Set ℂ} {poles : Finset ℂ}
    (hpoles : IsPoleRepresentativeSet f P poles) :
    poles.sum (fun z ↦ -divisor f P z) = ∑ᶠ z, (divisor f P)⁻ z := by
  have hsupp :
      Function.support (fun z ↦ (divisor f P z)⁻) ⊆ (↑poles : Set ℂ) := by
    intro z hz
    have hzsupport : z ∈ (divisor f P)⁻.support := by
      simpa [Function.support, Function.locallyFinsuppWithin.negPart_apply] using hz
    have hzP : z ∈ P := ((divisor f P)⁻).supportWithinDomain hzsupport
    have hzneg : divisor f P z < 0 := by
      have hzneq : (divisor f P z)⁻ ≠ 0 := by
        simpa [Function.locallyFinsuppWithin.negPart_apply] using hzsupport
      have hznot : ¬ 0 ≤ divisor f P z := by
        intro hzge
        exact hzneq (negPart_eq_zero.2 hzge)
      exact lt_of_not_ge hznot
    exact (hpoles.mem_iff z).2 ⟨hzP, hzneg⟩
  calc
    poles.sum (fun z ↦ -divisor f P z) = poles.sum (fun z ↦ (divisor f P z)⁻) := by
      -- Each chosen pole already contributes exactly the negative part of the divisor.
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzneg : divisor f P z < 0 := (hpoles.mem_iff z).1 hz |>.2
      exact (negPart_of_nonpos (le_of_lt hzneg)).symm
    _ = ∑ᶠ z, (divisor f P)⁻ z := by
      -- Replace the finite representative sum by the ambient negative-part `finsum`.
      symm
      exact finsum_eq_sum_of_support_subset _ hsupp

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: a period parallelogram is compact
because it is the affine image of the closed unit square. -/
private theorem periodParallelogram_isCompact (L : PeriodPair) (z₀ : ℂ) :
    IsCompact (L.periodParallelogram z₀) := by
  let e : ℝ × ℝ → ℂ := fun t ↦ z₀ + t.1 • L.ω₁ + t.2 • L.ω₂
  have he : Continuous e := by
    -- The affine-coordinate parametrization of the period cell is continuous.
    continuity
  have himage : e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = L.periodParallelogram z₀ := by
    ext z
    constructor
    · rintro ⟨⟨t₁, t₂⟩, ht, rfl⟩
      rcases ht with ⟨ht₁, ht₂⟩
      exact ⟨t₁, t₂, ht₁.1, ht₁.2, ht₂.1, ht₂.2, rfl⟩
    · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
      exact ⟨⟨t₁, t₂⟩, ⟨⟨ht₁0, ht₁1⟩, ⟨ht₂0, ht₂1⟩⟩, rfl⟩
  -- Compactness comes from the closed unit square under the affine parametrization.
  rw [← himage]
  exact (isCompact_Icc.prod isCompact_Icc).image he

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: boundary order zero forces the
divisor to vanish on the frontier of the period parallelogram. -/
private theorem divisor_eq_zero_on_frontier_of_boundary_order_zero
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    {z : ℂ} (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    divisor f (L.periodParallelogram z₀) z = 0 := by
  have hzK : z ∈ L.periodParallelogram z₀ := by
    -- Compactness of the period cell turns frontier membership into ordinary membership.
    exact (periodParallelogram_isCompact L z₀).isClosed.frontier_subset hz
  -- Rewrite the divisor through the meromorphic order and apply the boundary regularity
  -- hypothesis.
  simpa [hboundary z hz] using (hf.meromorphicOn.divisor_apply hzK)

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: the total divisor sum of a
meromorphic periodic function on a boundary-regular period parallelogram vanishes. -/
private theorem total_divisor_finsum_eq_zero_in_periodParallelogram
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ)) :
    ∑ᶠ z, divisor f (L.periodParallelogram z₀) z = 0 := by
  have hΓ :
      IsOrientedBoundaryOf (L.periodParallelogram z₀)
        (fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) := by
    -- Route correction: the frozen file now reuses the extracted shared boundary geometry
    -- instead of reproving the contour package locally.
    exact L.periodParallelogramBoundary_isOrientedBoundaryOf z₀
  have hboundary_divisor_zero :
      ∀ z ∈ frontier (L.periodParallelogram z₀), divisor f (L.periodParallelogram z₀) z = 0 := by
    -- The boundary order-zero hypothesis already forces vanishing of the divisor on the frontier.
    intro z hz
    exact divisor_eq_zero_on_frontier_of_boundary_order_zero L z₀ hf hboundary hz
  have harg :
      (∑ i : Unit,
          ∫ᶜ z in
            ((fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) i).toPath,
            ((logDeriv (fun z ↦ f z - 0) dz) z)) /
          (2 * Real.pi * Complex.I : ℂ) =
        ∑ᶠ z, (divisor (fun z ↦ f z - 0) (L.periodParallelogram z₀) z : ℂ) := by
    -- Proposition 4.1 turns the geometric boundary data into the divisor sum formula.
    simpa using
      argument_principle_on_oriented_boundary
        (Γ := fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath)
        (D := Set.univ) (K := L.periodParallelogram z₀) (f := f) (a := 0)
        hf.meromorphicOn isOpen_univ (by intro z hz; simp) hΓ
        (by
          intro z hz
          simpa using hboundary_divisor_zero z hz)
  have hintegral :
      ∑ i : Unit,
          ∫ᶜ z in
            ((fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) i).toPath,
            ((logDeriv (fun z ↦ f z - 0) dz) z) = 0 := by
    -- The singleton sum collapses to the explicit boundary-loop integral, which cancels on
    -- opposite translated edges.
    simpa using
      L.logDeriv_periodParallelogramBoundaryIntegral_eq_zero
        (f := f) z₀ hf hperiods hboundary
  -- Substitute the vanishing boundary integral back into the argument-principle identity.
  have harg_zero :
      (0 : ℂ) = ∑ᶠ z, (divisor (fun z ↦ f z - 0) (L.periodParallelogram z₀) z : ℂ) := by
    calc
      (0 : ℂ) =
          (∑ i : Unit,
              ∫ᶜ z in
                ((fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) i).toPath,
                ((logDeriv (fun z ↦ f z - 0) dz) z)) /
              (2 * Real.pi * Complex.I : ℂ) := by
            rw [hintegral]
            simp
      _ = ∑ᶠ z, (divisor (fun z ↦ f z - 0) (L.periodParallelogram z₀) z : ℂ) := harg
  -- Remove the harmless constant shift `a = 0` and coerce the complex-valued divisor sum back to
  -- the original integer-valued statement.
  have harg_zero' :
      (∑ᶠ z, (divisor (fun z ↦ f z - 0) (L.periodParallelogram z₀) z : ℂ)) = 0 := by
    simpa using harg_zero.symm
  have hmap :
      ((∑ᶠ z, divisor f (L.periodParallelogram z₀) z : ℤ) : ℂ) =
        ∑ᶠ z, (divisor f (L.periodParallelogram z₀) z : ℂ) := by
    -- Push the canonical complex cast through the finitely supported divisor sum.
    simpa using
      map_finsum (Int.castRingHom ℂ)
        (divisor_support_finite_of_isCompact
          (K := L.periodParallelogram z₀) (g := f)
          (periodParallelogram_isCompact L z₀))
  have hcast :
      ((∑ᶠ z, divisor f (L.periodParallelogram z₀) z : ℤ) : ℂ) = 0 := by
    calc
      ((∑ᶠ z, divisor f (L.periodParallelogram z₀) z : ℤ) : ℂ) =
          ∑ᶠ z, (divisor f (L.periodParallelogram z₀) z : ℂ) := hmap
      _ = 0 := by simpa using harg_zero'
  exact_mod_cast hcast

/-- Helper for Cartan section11 frozen_0011_Proposition_5_1: once the total divisor sum vanishes,
the positive and negative divisor masses in the period parallelogram agree. -/
private theorem positiveDivisorFinsum_eq_negativeDivisorFinsum_in_periodParallelogram
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ)) :
    ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁺ z =
      ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁻ z := by
  let P : Set ℂ := L.periodParallelogram z₀
  let D := divisor f P
  have hcompact : IsCompact P := by
    -- The period cell is compact via its affine-coordinate model.
    simpa [P] using periodParallelogram_isCompact L z₀
  let hsupport := divisor_support_finite_of_isCompact (K := P) (g := f) hcompact
  let s : Finset ℂ := hsupport.toFinset
  have hsuppD : Function.support (fun z ↦ D z) ⊆ (↑s : Set ℂ) := by
    intro z hz
    have hz' : z ∈ D.support := by
      simpa [D, Function.support] using hz
    simpa [s, hsupport] using (Set.Finite.mem_toFinset hsupport).2 hz'
  have hsuppPos : Function.support (fun z ↦ D⁺ z) ⊆ (↑s : Set ℂ) := by
    intro z hz
    have hzD : z ∈ Function.support (fun z ↦ D z) := by
      rw [Function.mem_support] at hz ⊢
      intro hDz
      exact hz (by simp [Function.locallyFinsuppWithin.posPart_apply, hDz])
    exact hsuppD hzD
  have hsuppNeg : Function.support (fun z ↦ D⁻ z) ⊆ (↑s : Set ℂ) := by
    intro z hz
    have hzD : z ∈ Function.support (fun z ↦ D z) := by
      rw [Function.mem_support] at hz ⊢
      intro hDz
      exact hz (by simp [Function.locallyFinsuppWithin.negPart_apply, hDz])
    exact hsuppD hzD
  have hsumD : Finset.sum s (fun z ↦ D z) = 0 := by
    -- The compact-support `finsum` is the contour-theoretic total divisor sum, which vanishes.
    calc
      Finset.sum s (fun z ↦ D z) = ∑ᶠ z, D z := by
        symm
        exact finsum_eq_sum_of_support_subset _ hsuppD
      _ = 0 := by
        simpa [D, P] using
          total_divisor_finsum_eq_zero_in_periodParallelogram L z₀ hf hperiods hboundary
  have hsumParts :
      Finset.sum s (fun z ↦ D⁺ z) - Finset.sum s (fun z ↦ D⁻ z) = 0 := by
    -- Sum the pointwise identity `D⁺ - D⁻ = D` over a common finite support finset.
    calc
      Finset.sum s (fun z ↦ D⁺ z) - Finset.sum s (fun z ↦ D⁻ z) =
          Finset.sum s (fun z ↦ D⁺ z - D⁻ z) := by
        symm
        exact Finset.sum_sub_distrib (fun z ↦ D⁺ z) (fun z ↦ D⁻ z)
      _ = Finset.sum s (fun z ↦ D z) := by
        refine Finset.sum_congr rfl ?_
        intro z hz
        simpa only [Function.locallyFinsuppWithin.posPart_apply,
          Function.locallyFinsuppWithin.negPart_apply] using
          congrArg (fun m : Function.locallyFinsuppWithin P ℤ ↦ m z) (posPart_sub_negPart D)
      _ = 0 := hsumD
  have hsumEq :
      Finset.sum s (fun z ↦ D⁺ z) = Finset.sum s (fun z ↦ D⁻ z) := sub_eq_zero.mp hsumParts
  calc
    ∑ᶠ z, D⁺ z = Finset.sum s (fun z ↦ D⁺ z) := by
      exact finsum_eq_sum_of_support_subset _ hsuppPos
    _ = Finset.sum s (fun z ↦ D⁻ z) := hsumEq
    _ = ∑ᶠ z, D⁻ z := by
      symm
      exact finsum_eq_sum_of_support_subset _ hsuppNeg

/-- Cartan section11 frozen_0011_Proposition_5_1 (Proposition 5.1): if `f` is meromorphic on the
whole complex plane and is periodic with respect to every element of the lattice generated by `L`,
then the positive and negative divisor contributions in a period parallelogram have the same total
multiplicity, provided no zero or pole lies on the boundary of the parallelogram. -/
theorem zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet f (L.periodParallelogram z₀) roots)
    (hpoles : IsPoleRepresentativeSet f (L.periodParallelogram z₀) poles) :
    roots.sum (fun z ↦ divisor f (L.periodParallelogram z₀) z) =
      poles.sum (fun z ↦ -divisor f (L.periodParallelogram z₀) z) := by
  -- Rewrite the source-facing finite sums as the canonical positive and negative divisor masses.
  rw [hroots.sum_divisor_eq_finsum_posPart, hpoles.sum_neg_divisor_eq_finsum_negPart]
  -- The remaining equality is the divisor decomposition together with vanishing total divisor sum.
  exact
    positiveDivisorFinsum_eq_negativeDivisorFinsum_in_periodParallelogram
      L z₀ hf hperiods hboundary

/-- Derived exact-period reformulation of Proposition 5.1. -/
theorem zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram_of_periods_eq_lattice
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods_eq : ∀ ω : ℂ, Function.Periodic f ω ↔ ω ∈ L.lattice.toAddSubgroup)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet f (L.periodParallelogram z₀) roots)
    (hpoles : IsPoleRepresentativeSet f (L.periodParallelogram z₀) poles) :
    roots.sum (fun z ↦ divisor f (L.periodParallelogram z₀) z) =
      poles.sum (fun z ↦ -divisor f (L.periodParallelogram z₀) z) :=
  zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram L z₀ hf
    (fun ω hω ↦ (hperiods_eq ω).2 hω) hboundary roots poles hroots hpoles
