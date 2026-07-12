import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0003_Lemma_II_1_extra_3»
import DifferentialForms_Cartan_1970.II.section05.«0005_Proposition_2_1»
import DifferentialForms_Cartan_1970.II.section05.«0034_Example_II_1_extra_21»
import DifferentialForms_Cartan_1970.III.section11.«0008_Proposition_4_1»
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators unitInterval
open MeromorphicOn

noncomputable section

-- Semantic recall note: the source-facing owner for a period parallelogram is
-- `PeriodPair.periodParallelogram`, the core period-data owner is `HasPeriodLattice`, and the
-- zero/pole counts are read from mathlib's canonical divisor owner `MeromorphicOn.divisor`.

/-- `roots` lists the support of the positive part of the divisor of `f` on `P`. -/
def IsZeroRepresentativeSet (f : ℂ → ℂ) (P : Set ℂ) (roots : Finset ℂ) : Prop :=
  (↑roots : Set ℂ) = (divisor f P)⁺.support

@[simp]
theorem IsZeroRepresentativeSet.mem_support_iff
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) (z : ℂ) :
    z ∈ roots ↔ z ∈ (divisor f P)⁺.support :=
  by simpa [IsZeroRepresentativeSet] using congrArg (fun s : Set ℂ ↦ z ∈ s) hroots

/-- Source-facing characterization of zero representatives. -/
@[simp]
theorem IsZeroRepresentativeSet.mem_iff
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) (z : ℂ) :
    z ∈ roots ↔ z ∈ P ∧ 0 < divisor f P z := by
  constructor
  · intro hz
    -- Read root membership through the support of the positive divisor part.
    have hzsupport : z ∈ (divisor f P)⁺.support := (hroots.mem_support_iff z).1 hz
    have hzP : z ∈ P := ((divisor f P)⁺).supportWithinDomain hzsupport
    have hzpos : 0 < divisor f P z := by
      have hzneq : (divisor f P z)⁺ ≠ 0 := by
        simpa [Function.locallyFinsuppWithin.posPart_apply] using hzsupport
      have hznot : ¬ divisor f P z ≤ 0 := by
        intro hzle
        exact hzneq (posPart_eq_zero.2 hzle)
      exact lt_of_not_ge hznot
    exact ⟨hzP, hzpos⟩
  · rintro ⟨hzP, hzpos⟩
    -- Positive divisor mass puts the point back into the positive-part support.
    have hzsupport : z ∈ (divisor f P)⁺.support := by
      change (divisor f P z)⁺ ≠ 0
      exact ne_of_gt (by
        simpa [Function.locallyFinsuppWithin.posPart_apply] using posPart_pos hzpos)
    exact (hroots.mem_support_iff z).2 hzsupport

/-- `poles` lists the support of the negative part of the divisor of `f` on `P`. -/
def IsPoleRepresentativeSet (f : ℂ → ℂ) (P : Set ℂ) (poles : Finset ℂ) : Prop :=
  (↑poles : Set ℂ) = (divisor f P)⁻.support

@[simp]
theorem IsPoleRepresentativeSet.mem_support_iff
    {f : ℂ → ℂ} {P : Set ℂ} {poles : Finset ℂ}
    (hpoles : IsPoleRepresentativeSet f P poles) (z : ℂ) :
    z ∈ poles ↔ z ∈ (divisor f P)⁻.support :=
  by simpa [IsPoleRepresentativeSet] using congrArg (fun s : Set ℂ ↦ z ∈ s) hpoles

/-- Source-facing characterization of pole representatives. -/
@[simp]
theorem IsPoleRepresentativeSet.mem_iff
    {f : ℂ → ℂ} {P : Set ℂ} {poles : Finset ℂ}
    (hpoles : IsPoleRepresentativeSet f P poles) (z : ℂ) :
    z ∈ poles ↔ z ∈ P ∧ divisor f P z < 0 := by
  constructor
  · intro hz
    -- Read pole membership through the support of the negative divisor part.
    have hzsupport : z ∈ (divisor f P)⁻.support := (hpoles.mem_support_iff z).1 hz
    have hzP : z ∈ P := ((divisor f P)⁻).supportWithinDomain hzsupport
    have hzneg : divisor f P z < 0 := by
      have hzneq : (divisor f P z)⁻ ≠ 0 := by
        simpa [Function.locallyFinsuppWithin.negPart_apply] using hzsupport
      have hznot : ¬ 0 ≤ divisor f P z := by
        intro hzge
        exact hzneq (negPart_eq_zero.2 hzge)
      exact lt_of_not_ge hznot
    exact ⟨hzP, hzneg⟩
  · rintro ⟨hzP, hzneg⟩
    -- Negative divisor mass puts the point back into the negative-part support.
    have hzsupport : z ∈ (divisor f P)⁻.support := by
      change (divisor f P z)⁻ ≠ 0
      exact ne_of_gt (by
        simpa [Function.locallyFinsuppWithin.negPart_apply] using negPart_pos hzneg)
    exact (hpoles.mem_support_iff z).2 hzsupport

/-- Summing the divisor over a zero representative set recovers the total positive divisor mass. -/
theorem IsZeroRepresentativeSet.sum_divisor_eq_finsum_posPart
    {f : ℂ → ℂ} {P : Set ℂ} {roots : Finset ℂ}
    (hroots : IsZeroRepresentativeSet f P roots) :
    roots.sum (divisor f P) = ∑ᶠ z, (divisor f P)⁺ z := by
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
    roots.sum (divisor f P) = roots.sum (fun z ↦ (divisor f P z)⁺) := by
      -- On every chosen root representative, the divisor is already nonnegative.
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzpos : 0 < divisor f P z := (hroots.mem_iff z).1 hz |>.2
      exact (posPart_of_nonneg (le_of_lt hzpos)).symm
    _ = ∑ᶠ z, (divisor f P)⁺ z := by
      -- Replace the finite representative-set sum by the ambient positive-part `finsum`.
      symm
      exact finsum_eq_sum_of_support_subset _ hsupp

/-- Summing pole multiplicities over a pole representative set recovers the total pole divisor
mass. -/
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
      -- On every chosen pole representative, the negative part is exactly the pole multiplicity.
      refine Finset.sum_congr rfl ?_
      intro z hz
      have hzneg : divisor f P z < 0 := (hpoles.mem_iff z).1 hz |>.2
      exact (negPart_of_nonpos (le_of_lt hzneg)).symm
    _ = ∑ᶠ z, (divisor f P)⁻ z := by
      -- Replace the finite representative-set sum by the ambient negative-part `finsum`.
      symm
      exact finsum_eq_sum_of_support_subset _ hsupp

/-- Helper for Cartan section11 0011_Proposition_5_1: a period parallelogram is compact because it
is the affine image of the closed unit square. -/
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

/-- Helper for Cartan section11 0011_Proposition_5_1: translating a periodic function by one of its
periods preserves the complex derivative. -/
private theorem deriv_add_period_eq_of_periodic
    {g : ℂ → ℂ} {ω z : ℂ} (hperiodic : Function.Periodic g ω) :
    deriv g (z + ω) = deriv g z := by
  have htranslate : (fun w : ℂ ↦ g (w + ω)) = g := by
    funext w
    exact hperiodic w
  -- Compare the derivative of the translated function in the two canonical ways.
  calc
    deriv g (z + ω) = deriv (fun w : ℂ ↦ g (w + ω)) z := by
      symm
      simpa [add_comm] using (deriv_comp_add_const (f := g) (a := ω) (x := z))
    _ = deriv g z := by
      exact congrArg (fun F : ℂ → ℂ ↦ deriv F z) htranslate

/-- Helper for Cartan section11 0011_Proposition_5_1: a lattice period preserves the logarithmic
derivative. -/
private theorem logDeriv_add_period_eq_of_hasPeriodLattice
    {g : ℂ → ℂ} (L : PeriodPair) (hperiods : HasPeriodLattice L g)
    {ω z : ℂ} (hω : ω ∈ L.lattice) :
    logDeriv g (z + ω) = logDeriv g z := by
  -- Rewrite `logDeriv` as `deriv / value` and transport both pieces through periodicity.
  rw [logDeriv_apply, logDeriv_apply]
  simp [deriv_add_period_eq_of_periodic (hperiodic := fun w ↦ hperiods ω hω w),
    hperiods ω hω z]

/-- Helper for Cartan section11 0011_Proposition_5_1: translating a segment integral of a periodic
integrand by one period does not change the value. -/
private theorem curveIntegral_segment_translate_eq_of_periodic
    {φ : ℂ → ℂ} {a b ω : ℂ} (hperiodic : Function.Periodic φ ω) :
    ∫ᶜ z in Path.segment (a + ω) (b + ω), ((φ dz) z) =
      ∫ᶜ z in Path.segment a b, ((φ dz) z) := by
  rw [curveIntegral_segment, curveIntegral_segment]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro t _
  have hline :
      AffineMap.lineMap (a + ω) (b + ω) t = AffineMap.lineMap a b t + ω := by
    -- Translate the affine parameterization and collect the common period vector.
    simp [AffineMap.lineMap_apply, add_assoc, add_left_comm, add_comm]
  have hdiff : (b + ω) - (a + ω) = b - a := by
    -- Translation leaves the segment displacement unchanged.
    abel
  -- Periodicity removes the common translation from the segment integrand.
  simpa [Complex.scalarOneForm_apply, hline, hdiff, add_comm] using
    congrArg (fun c : ℂ ↦ c * (b - a)) (hperiodic (AffineMap.lineMap a b t))

/-- Helper for Cartan section11 0011_Proposition_5_1: unpacking a loop through
`toClosedPath.toPath` only inserts the endpoint cast forced by the closed-path packaging. -/
private theorem loopToClosedPathToPathEqCast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath =
      γ.cast (by simp [Path.toClosedPath])
        (by simp [Path.toClosedPath]) := by
  -- The closed-path packaging does not alter the underlying continuous map of a genuine loop.
  cases γ
  rfl

/-- Helper for Cartan section11 0011_Proposition_5_1: continuity of a scalar coefficient field
yields continuity of the associated complex-linear scalar `1`-form. -/
private theorem scalarOneForm_continuousOn
    {D : Set ℂ} {φ : ℂ → ℂ} (hφ : ContinuousOn φ D) :
    ContinuousOn (fun z ↦ (φ dz) z) D := by
  -- The scalar-one-form constructor is continuous in the scalar coefficient.
  simpa [Complex.scalarOneForm] using
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ).continuous₂.comp_continuousOn
      ((continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (1 : ℂ →L[ℂ] ℂ)) D).prodMk hφ)

/-- Helper for Cartan section11 0011_Proposition_5_1: on a nondegenerate segment, codiscrete
agreement with an already integrable scalar `1`-form transfers curve-integrability. -/
private theorem curveIntegrable_segment_of_codiscreteEq
    {φ ψ : ℂ → ℂ} {a b : ℂ} (hne : a ≠ b)
    (hψ : CurveIntegrable (fun z ↦ (ψ dz) z) (Path.segment a b))
    (hEq : φ =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] ψ) :
    CurveIntegrable (fun z ↦ (φ dz) z) (Path.segment a b) := by
  let A : Set ℂ := {z | φ z = ψ z}
  have hA : A ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
    -- Repackage codiscrete equality as a codiscrete good set of points.
    simpa [A, Filter.EventuallyEq] using hEq
  have hA_range : A ∈ Filter.codiscreteWithin (Set.range (Path.segment a b)) := by
    -- Restrict the codiscrete good set from the whole plane to the segment image.
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA ⊢
    intro z hz
    refine Filter.mem_of_superset (hA z (by simp)) ?_
    intro w hw
    rcases hw with hwA | hwEmpty
    · exact Or.inl hwA
    · simp at hwEmpty
  have hBadImage : (Set.range (Path.segment a b) \ A).Finite := by
    -- A codiscrete bad set meets the compact segment image in only finitely many points.
    exact (isCompact_range (Path.segment a b).continuous).finite_diff_of_mem_codiscreteWithin
      hA_range
  have hline_injective :
      Function.Injective (fun t : Set.uIoc (0 : ℝ) 1 ↦ AffineMap.lineMap a b (t : ℝ)) := by
    intro s t hst
    apply Subtype.ext
    rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := a) (p₁ := b) (c₁ := (s : ℝ))
      (c₂ := (t : ℝ))).mp hst with hab | hcoeff
    · exact (hne hab).elim
    · exact hcoeff
  let B : Set ℝ :=
    {t | t ∈ Set.uIoc (0 : ℝ) 1 ∧
      AffineMap.lineMap a b t ∈ Set.range (Path.segment a b) \ A}
  have hBadParamSubtype :
      {t : Set.uIoc (0 : ℝ) 1 |
          AffineMap.lineMap a b (t : ℝ) ∈ Set.range (Path.segment a b) \ A}.Finite := by
    -- Injectivity of the affine segment parameterization keeps the bad parameter set finite.
    exact hBadImage.preimage hline_injective.injOn
  have hBadParam : B.Finite := by
    have hImage : (Subtype.val '' {t : Set.uIoc (0 : ℝ) 1 |
        AffineMap.lineMap a b (t : ℝ) ∈ Set.range (Path.segment a b) \ A}).Finite := by
      exact hBadParamSubtype.image Subtype.val
    convert hImage using 1
    ext t
    constructor
    · intro ht
      refine ⟨⟨t, ht.1⟩, ?_, rfl⟩
      simpa [B] using ht.2
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, by simpa [B] using ht⟩
  have hParamEq :
      Filter.EventuallyEq (Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1))
        (fun t : ℝ ↦ ((φ dz) (AffineMap.lineMap a b t)) (b - a))
      (fun t : ℝ ↦ ((ψ dz) (AffineMap.lineMap a b t)) (b - a)) := by
    change
      {t : ℝ |
          ((φ dz) (AffineMap.lineMap a b t)) (b - a) =
            ((ψ dz) (AffineMap.lineMap a b t)) (b - a)} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    have hBadParam_cod :
        ({t : ℝ | t ∉ B} : Set ℝ) ∈
          Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1) :=
      compl_finite_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) 1) hBadParam
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hBadParam_cod
    intro t ht
    -- Away from the finitely many bad parameters, the two scalar coefficients agree on the
    -- segment point, so the pulled-back `1`-forms agree as well.
    refine Filter.mem_of_superset (hBadParam_cod t ht) ?_
    intro u hu
    rcases hu with huNotB | huOutside
    · by_cases huI : u ∈ Set.uIoc (0 : ℝ) 1
      · have huRange : AffineMap.lineMap a b u ∈ Set.range (Path.segment a b) := by
          have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
            simpa using (show u ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) from
              ⟨le_of_lt huI.1, huI.2⟩)
          refine ⟨⟨u, huIcc⟩, ?_⟩
          simp [Path.segment, AffineMap.lineMap_apply]
        have huA : AffineMap.lineMap a b u ∈ A := by
          by_contra huA
          exact huNotB ⟨huI, ⟨huRange, huA⟩⟩
        have huEq : φ (AffineMap.lineMap a b u) = ψ (AffineMap.lineMap a b u) := by
          simpa [A] using huA
        exact Or.inl (by simp [huEq])
      · exact Or.inr huI
    · exact Or.inr huOutside
  -- Rewrite the segment integrability statement to the scalar parameter integrand and transfer it
  -- across the codiscrete agreement.
  rw [curveIntegrable_segment] at hψ ⊢
  exact (intervalIntegrable_congr_codiscreteWithin hParamEq).mpr hψ

namespace PeriodPair

/-- Helper for Cartan section11 0011_Proposition_5_1: the period basis identifies a real pair
with the corresponding linear combination of the period generators. -/
private theorem basisPairHomeomorph_apply (L : PeriodPair) (p : ℝ × ℝ) :
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
      p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the inverse basis map through the standard `Fin 2` coordinates.
  calc
    (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm) p : ℂ) =
        L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) := by
          rfl
    _ = ∑ i : Fin 2,
          L.basis.equivFun
            (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i •
            L.basis i := by
          simpa using
            (L.basis.sum_equivFun
              (L.basis.equivFunL.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p))).symm
    _ = ∑ i : Fin 2, ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p) i • L.basis i := by
          congr with i
          exact congrArg (fun a : ℝ ↦ a • L.basis i)
            (congrFun
              (L.basis.equivFunL.apply_symm_apply
                ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm p)) i)
    _ = p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simp [Fin.sum_univ_two]

/-- Helper for Cartan section11 0011_Proposition_5_1: the real-affine period-coordinate
homeomorphism sends the unit square to the period parallelogram. -/
private def periodParallelogramCoordinateHomeomorph
    (L : PeriodPair) (z₀ : ℂ) : ℂ ≃ₜ ℂ :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        L.basis.equivFunL.symm).toHomeomorph).trans
      (Homeomorph.addLeft z₀))

/-- Helper for Cartan section11 0011_Proposition_5_1: the period-coordinate homeomorphism has the
expected affine formula in terms of the period basis. -/
private theorem periodParallelogramCoordinateHomeomorph_apply
    (L : PeriodPair) (z₀ z : ℂ) :
    L.periodParallelogramCoordinateHomeomorph z₀ z = z₀ + z.re • L.ω₁ + z.im • L.ω₂ := by
  -- Read the homeomorphism through the real and imaginary coordinates of `z`.
  change
    z₀ + (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm)
      (Complex.equivRealProd z) : ℂ) =
      z₀ + z.re • L.ω₁ + z.im • L.ω₂
  rw [L.basisPairHomeomorph_apply]
  simp [add_assoc]

/-- Helper for Cartan section11 0011_Proposition_5_1: the period coordinates also define a real
affine equivalence on `Plane`. -/
private def periodParallelogramCoordinateAffineEquiv
    (L : PeriodPair) (z₀ : ℂ) : Plane ≃ᴬ[ℝ] Plane :=
  let e : Plane ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans L.basis.equivFunL.symm
  (e.toContinuousAffineEquiv.trans (ContinuousAffineEquiv.constVAdd ℝ ℂ z₀)).trans
    Complex.equivRealProdCLM.toContinuousAffineEquiv

/-- Helper for Cartan section11 0011_Proposition_5_1: the real affine period-coordinate map sends
the pair `(t, u)` to the corresponding affine period combination. -/
private theorem periodParallelogramCoordinateAffineEquiv_apply
    (L : PeriodPair) (z₀ : ℂ) (p : Plane) :
    Complex.equivRealProdCLM.symm (L.periodParallelogramCoordinateAffineEquiv z₀ p) =
      z₀ + p.1 • L.ω₁ + p.2 • L.ω₂ := by
  -- Expand the affine equivalence through the period-basis coordinates.
  have hbasis :
      (L.basis.equivFunL.symm ![p.1, p.2] : ℂ) = p.1 • L.ω₁ + p.2 • L.ω₂ := by
    simpa using (L.basisPairHomeomorph_apply p)
  calc
    Complex.equivRealProdCLM.symm (L.periodParallelogramCoordinateAffineEquiv z₀ p) =
        (ContinuousAffineEquiv.constVAdd ℝ ℂ z₀) (L.basis.equivFunL.symm ![p.1, p.2]) := by
          simpa [periodParallelogramCoordinateAffineEquiv] using
            (Complex.equivRealProdCLM.left_inv
              ((ContinuousAffineEquiv.constVAdd ℝ ℂ z₀) (L.basis.equivFunL.symm ![p.1, p.2])))
    _ = z₀ + (L.basis.equivFunL.symm ![p.1, p.2] : ℂ) := by rfl
    _ = z₀ + p.1 • L.ω₁ + p.2 • L.ω₂ := by
          simpa [add_assoc] using congrArg (fun z : ℂ ↦ z₀ + z) hbasis

/-- Helper for Cartan section11 0011_Proposition_5_1: the `Plane` affine chart and the complex
homeomorphism describe the same period-coordinate change of variables. -/
private theorem periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph
    (L : PeriodPair) (z₀ : ℂ) (p : Plane) :
    Complex.equivRealProdCLM.symm (L.periodParallelogramCoordinateAffineEquiv z₀ p) =
      L.periodParallelogramCoordinateHomeomorph z₀ (Complex.equivRealProdCLM.symm p) := by
  -- Both coordinate owners expand to the same affine combination in the period basis.
  rw [L.periodParallelogramCoordinateAffineEquiv_apply,
    L.periodParallelogramCoordinateHomeomorph_apply]
  simp [Complex.equivRealProdCLM_symm_apply, add_assoc]

/-- Helper for Cartan section11 0011_Proposition_5_1: the explicit four-edge loop around a period
parallelogram. -/
private def periodParallelogramBoundaryPath (L : PeriodPair) (z₀ : ℂ) : Path z₀ z₀ :=
  let z₁ := z₀ + L.ω₁
  let z₂ := z₀ + L.ω₁ + L.ω₂
  let z₃ := z₀ + L.ω₂
  (Path.segment z₀ z₁).trans
    ((Path.segment z₁ z₂).trans
      ((Path.segment z₂ z₃).trans
        (Path.segment z₃ z₀)))

/-- Helper for Cartan section11 0011_Proposition_5_1: the period-parallelogram boundary loop is
the image of the standard unit-square boundary under the period-coordinate homeomorphism. -/
private theorem periodParallelogramBoundaryPath_eq_map_standardRectangle
    (L : PeriodPair) (z₀ : ℂ) :
      L.periodParallelogramBoundaryPath z₀ =
      ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).map
        (L.periodParallelogramCoordinateHomeomorph z₀).continuous).cast
        (by simpa using (L.periodParallelogramCoordinateHomeomorph_apply z₀ 0).symm)
        (by simpa using (L.periodParallelogramCoordinateHomeomorph_apply z₀ 0).symm) := by
  ext t
  -- Both paths follow the same four affine sides after transporting the standard rectangle by the
  -- period-coordinate homeomorphism.
  simp [periodParallelogramBoundaryPath, axisParallelRectangleBoundaryPath, Path.trans_apply,
    L.periodParallelogramCoordinateHomeomorph_apply, AffineMap.lineMap_apply]
  split_ifs <;> ring

/-- Helper for Cartan section11 0011_Proposition_5_1: on the bottom interval the slanted boundary
loop is the bottom affine edge of the period parallelogram. -/
private theorem periodParallelogramBoundaryPath_eqOn_bottom_side
    (L : PeriodPair) (z₀ : ℂ) :
    Set.EqOn (L.periodParallelogramBoundaryPath z₀).extend
      (fun t ↦ AffineMap.lineMap z₀ (z₀ + L.ω₁) (2 * t))
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  intro t ht
  have hmap :
      (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the global map-to-rectangle description at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have hrect :
      (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t =
        AffineMap.lineMap 0 (1 : ℂ) (2 * t) := by
    -- On the first parameter interval the standard rectangle path follows the bottom edge.
    simpa using axisParallelRectangleBoundaryPath_eqOn_bottom_side 0 (1 + Complex.I) ht
  calc
    (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := hmap
    _ =
        L.periodParallelogramCoordinateHomeomorph z₀
          (AffineMap.lineMap 0 (1 : ℂ) (2 * t)) := by rw [hrect]
    _ = AffineMap.lineMap z₀ (z₀ + L.ω₁) (2 * t) := by
      rw [L.periodParallelogramCoordinateHomeomorph_apply]
      simp [AffineMap.lineMap_apply]
      ring

/-- Helper for Cartan section11 0011_Proposition_5_1: on the right interval the slanted boundary
loop is the translated vertical affine edge of the period parallelogram. -/
private theorem periodParallelogramBoundaryPath_eqOn_right_side
    (L : PeriodPair) (z₀ : ℂ) :
    Set.EqOn (L.periodParallelogramBoundaryPath z₀).extend
      (fun t ↦ AffineMap.lineMap (z₀ + L.ω₁) (z₀ + L.ω₁ + L.ω₂) (4 * t - 2))
      (Set.Icc (1 / 2) (3 / 4)) := by
  intro t ht
  have hmap :
      (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the global map-to-rectangle description at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have hrect :
      (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t =
        AffineMap.lineMap (1 : ℂ) (1 + Complex.I) (4 * t - 2) := by
    -- On the second interval the standard rectangle path follows the right edge.
    simpa using axisParallelRectangleBoundaryPath_eqOn_right_side 0 (1 + Complex.I) ht
  calc
    (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := hmap
    _ =
        L.periodParallelogramCoordinateHomeomorph z₀
          (AffineMap.lineMap (1 : ℂ) (1 + Complex.I) (4 * t - 2)) := by rw [hrect]
    _ = AffineMap.lineMap (z₀ + L.ω₁) (z₀ + L.ω₁ + L.ω₂) (4 * t - 2) := by
      rw [L.periodParallelogramCoordinateHomeomorph_apply]
      simp [AffineMap.lineMap_apply]
      ring

/-- Helper for Cartan section11 0011_Proposition_5_1: on the top interval the slanted boundary
loop is the reversed top affine edge of the period parallelogram. -/
private theorem periodParallelogramBoundaryPath_eqOn_top_side
    (L : PeriodPair) (z₀ : ℂ) :
    Set.EqOn (L.periodParallelogramBoundaryPath z₀).extend
      (fun t ↦ AffineMap.lineMap (z₀ + L.ω₁ + L.ω₂) (z₀ + L.ω₂) (8 * t - 6))
      (Set.Icc (3 / 4) (7 / 8)) := by
  intro t ht
  have hmap :
      (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the global map-to-rectangle description at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have hrect :
      (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t =
        AffineMap.lineMap (1 + Complex.I) (Complex.I) (8 * t - 6) := by
    -- On the third interval the standard rectangle path follows the top edge.
    simpa using axisParallelRectangleBoundaryPath_eqOn_top_side 0 (1 + Complex.I) ht
  calc
    (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := hmap
    _ =
        L.periodParallelogramCoordinateHomeomorph z₀
          (AffineMap.lineMap (1 + Complex.I) (Complex.I) (8 * t - 6)) := by rw [hrect]
    _ = AffineMap.lineMap (z₀ + L.ω₁ + L.ω₂) (z₀ + L.ω₂) (8 * t - 6) := by
      rw [L.periodParallelogramCoordinateHomeomorph_apply]
      simp [AffineMap.lineMap_apply]
      ring

/-- Helper for Cartan section11 0011_Proposition_5_1: on the left interval the slanted boundary
loop is the reversed left affine edge of the period parallelogram. -/
private theorem periodParallelogramBoundaryPath_eqOn_left_side
    (L : PeriodPair) (z₀ : ℂ) :
    Set.EqOn (L.periodParallelogramBoundaryPath z₀).extend
      (fun t ↦ AffineMap.lineMap (z₀ + L.ω₂) z₀ (8 * t - 7))
      (Set.Icc (7 / 8) (1 : ℝ)) := by
  intro t ht
  have hmap :
      (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the global map-to-rectangle description at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have hrect :
      (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t =
        AffineMap.lineMap (Complex.I) 0 (8 * t - 7) := by
    -- On the final interval the standard rectangle path follows the left edge.
    simpa using axisParallelRectangleBoundaryPath_eqOn_left_side 0 (1 + Complex.I) ht
  calc
    (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := hmap
    _ =
        L.periodParallelogramCoordinateHomeomorph z₀
          (AffineMap.lineMap (Complex.I) 0 (8 * t - 7)) := by rw [hrect]
    _ = AffineMap.lineMap (z₀ + L.ω₂) z₀ (8 * t - 7) := by
      rw [L.periodParallelogramCoordinateHomeomorph_apply]
      simp [AffineMap.lineMap_apply]
      ring

/-- Helper for Cartan section11 0011_Proposition_5_1: the slanted boundary real curve is the
period-coordinate image of the standard rectangle boundary real curve. -/
private theorem periodParallelogramBoundary_realCurve_eq_standardRectangle
    (L : PeriodPair) (z₀ : ℂ) (t : ℝ) :
    ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t =
      L.periodParallelogramCoordinateAffineEquiv z₀
        (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
  apply (Complex.equivRealProdCLM.symm).injective
  -- Compare both plane-valued curves through the corresponding complex-valued paths.
  change (L.periodParallelogramBoundaryPath z₀).extend t =
    Complex.equivRealProdCLM.symm
      (L.periodParallelogramCoordinateAffineEquiv z₀
        (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t))
  have hmap :
      (L.periodParallelogramBoundaryPath z₀).extend t =
        L.periodParallelogramCoordinateHomeomorph z₀
          ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).extend t) := by
    -- Evaluate the path-level map theorem at the real parameter `t`.
    simpa [Path.extend_cast] using
      congrArg (fun γ : Path z₀ z₀ ↦ γ.extend t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  rw [hmap, L.periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph]
  rfl

/-- Helper for Cartan section11 0011_Proposition_5_1: every regular parameter on the slanted
boundary lies on one of the four open affine side intervals. -/
private theorem periodParallelogramBoundary_regularParameterCases
    (L : PeriodPair) (z₀ : ℂ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀) :
    t₀ ∈ Set.Ioo (0 : ℝ) (1 / 2) ∨
      t₀ ∈ Set.Ioo (1 / 2) (3 / 4) ∨
      t₀ ∈ Set.Ioo (3 / 4) (7 / 8) ∨
      t₀ ∈ Set.Ioo (7 / 8) (1 : ℝ) := by
  let e := L.periodParallelogramCoordinateAffineEquiv z₀
  have heDiff :
      DifferentiableAt ℝ (fun p : Plane ↦ e.symm p)
        (((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t₀) := by
    -- The inverse affine coordinate map is differentiable at every point.
    simpa [e] using
      (e.symm.toContinuousAffineMap.contDiff.differentiable one_ne_zero
        (((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t₀))
  have hrectDiffAux :
      DifferentiableWithinAt ℝ
        (fun t ↦ e.symm (((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t))
        (Set.Icc (0 : ℝ) 1) t₀ :=
    heDiff.comp_differentiableWithinAt t₀ hdiff
  have hrectDiff :
      DifferentiableWithinAt ℝ
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ := by
    -- Pull the regularity back to the standard rectangle boundary through the inverse affine map.
    refine hrectDiffAux.congr ?_ ?_
    · intro t ht
      have hcurve := L.periodParallelogramBoundary_realCurve_eq_standardRectangle z₀ t
      calc
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t =
            e.symm
              (e
                (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
                  t)) := by
              simp [e]
        _ = e.symm (((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t) := by
              rw [hcurve]
    · have hcurve := L.periodParallelogramBoundary_realCurve_eq_standardRectangle z₀ t₀
      calc
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t₀ =
            e.symm
              (e
                (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve)
                  t₀)) := by
              simp [e]
        _ = e.symm (((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t₀) := by
              rw [hcurve]
  -- The standard rectangle classifier now applies verbatim.
  simpa using
    axis_parallel_rectangle_boundary_regular_parameter_mem_side_interval
      0 (1 + Complex.I) (by norm_num) (by norm_num) ht₀ hrectDiff

/-- Helper for Cartan section11 0011_Proposition_5_1: the period-coordinate homeomorphism sends
the closed unit square to the period parallelogram. -/
private theorem periodParallelogram_eq_image_standardRectangle
    (L : PeriodPair) (z₀ : ℂ) :
    L.periodParallelogramCoordinateHomeomorph z₀ '' Complex.Rectangle 0 (1 + Complex.I) =
      L.periodParallelogram z₀ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : (0 ≤ w.re ∧ w.re ≤ 1) ∧ 0 ≤ w.im ∧ w.im ≤ 1 := by
      simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using hw
    refine ⟨w.re, w.im, hw'.1.1, hw'.1.2, hw'.2.1, hw'.2.2, ?_⟩
    -- Read the image point through the real and imaginary coordinates of `w`.
    simpa using L.periodParallelogramCoordinateHomeomorph_apply z₀ w
  · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
    refine ⟨t₁ + t₂ * Complex.I, ?_, ?_⟩
    · simpa [Complex.Rectangle, Complex.mem_reProdIm, Set.uIcc] using
        And.intro (And.intro ht₁0 ht₁1) (And.intro ht₂0 ht₂1)
    · -- The standard square point with coordinates `(t₁, t₂)` maps to the requested period-cell
      -- point.
      simp [L.periodParallelogramCoordinateHomeomorph_apply, Complex.add_re, Complex.add_im]

/-- Helper for Cartan section11 0011_Proposition_5_1: the explicit period-parallelogram boundary
loop is piecewise differentiable because it is a concatenation of four affine segments. -/
private theorem periodParallelogramBoundaryPath_isPiecewiseDifferentiable
    (L : PeriodPair) (z₀ : ℂ) :
    (L.periodParallelogramBoundaryPath z₀).IsPiecewiseDifferentiable := by
  let z₁ : ℂ := z₀ + L.ω₁
  let z₂ : ℂ := z₀ + L.ω₁ + L.ω₂
  let z₃ : ℂ := z₀ + L.ω₂
  have h₁ : (Path.segment z₀ z₁).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₀ z₁
  have h₂ : (Path.segment z₁ z₂).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₁ z₂
  have h₃ : (Path.segment z₂ z₃).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₂ z₃
  have h₄ : (Path.segment z₃ z₀).IsPiecewiseDifferentiable :=
    Path.segment_isPiecewiseDifferentiable z₃ z₀
  -- Reassociate the four affine segments through the generic piecewise-differentiable
  -- concatenation theorem.
  simpa [periodParallelogramBoundaryPath, z₁, z₂, z₃] using
    Path.IsPiecewiseDifferentiable.trans h₁
      (Path.IsPiecewiseDifferentiable.trans h₂
        (Path.IsPiecewiseDifferentiable.trans h₃ h₄))

/-- Helper for Cartan section11 0011_Proposition_5_1: equality of two points on the explicit
period-parallelogram boundary loop forces equality of the parameters, except for the endpoint
identification `0 ~ 1`. -/
private theorem periodParallelogramBoundaryPath_simple_eq_or_endpoints
    (L : PeriodPair) (z₀ : ℂ) {s t : I}
    (hst : L.periodParallelogramBoundaryPath z₀ s = L.periodParallelogramBoundaryPath z₀ t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hs :
      L.periodParallelogramBoundaryPath z₀ s =
        L.periodParallelogramCoordinateHomeomorph z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s) := by
    -- Read the slanted contour as the image of the standard rectangle boundary at the parameter
    -- `s`.
    simpa using
      congrArg (fun γ : Path z₀ z₀ ↦ γ s)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have ht :
      L.periodParallelogramBoundaryPath z₀ t =
        L.periodParallelogramCoordinateHomeomorph z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
    -- The same image formula holds at the parameter `t`.
    simpa using
      congrArg (fun γ : Path z₀ z₀ ↦ γ t)
        (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
  have hrect :
      axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s =
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t := by
    -- Injectivity of the period-coordinate homeomorphism reduces the parameter comparison to the
    -- already-solved axis-parallel rectangle case.
    apply (L.periodParallelogramCoordinateHomeomorph z₀).injective
    calc
      L.periodParallelogramCoordinateHomeomorph z₀
          (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) s) =
          L.periodParallelogramBoundaryPath z₀ s := hs.symm
      _ = L.periodParallelogramBoundaryPath z₀ t := hst
      _ =
          L.periodParallelogramCoordinateHomeomorph z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := ht
  -- Delegate the standard rectangle boundary simplicity to the existing coordinate proof.
  exact
    axis_parallel_rectangle_boundary_path_simple_eq_or_endpoints
      0 (1 + Complex.I) (by norm_num) (by norm_num) hrect

/-- Helper for Cartan section11 0011_Proposition_5_1: the range of the explicit boundary loop is
exactly the frontier of the period parallelogram. -/
private theorem periodParallelogramBoundaryPath_range_eq_frontier
    (L : PeriodPair) (z₀ : ℂ) :
    Set.range (L.periodParallelogramBoundaryPath z₀) = frontier (L.periodParallelogram z₀) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    have ht :
        L.periodParallelogramBoundaryPath z₀ t =
          L.periodParallelogramCoordinateHomeomorph z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
      -- Evaluate the boundary-path image formula at the chosen boundary parameter.
      simpa using
        congrArg (fun γ : Path z₀ z₀ ↦ γ t)
          (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
    have hrect :
        axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t ∈
          frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
      -- The standard rectangle boundary theorem identifies its path range with the frontier.
      rw [← axisParallelRectangleBoundaryPath_range_eq_frontier 0 (1 + Complex.I)]
      exact ⟨t, rfl⟩
    have himage :
        L.periodParallelogramCoordinateHomeomorph z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) ∈
          frontier (L.periodParallelogram z₀) := by
      -- Transport the frontier membership through the period-coordinate homeomorphism.
      have :
          L.periodParallelogramCoordinateHomeomorph z₀
              (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) ∈
            L.periodParallelogramCoordinateHomeomorph z₀ ''
              frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
        exact ⟨axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t, hrect, rfl⟩
      rwa [(L.periodParallelogramCoordinateHomeomorph z₀).image_frontier,
        L.periodParallelogram_eq_image_standardRectangle z₀] at this
    simpa [ht] using himage
  · intro hz
    have hz' : z ∈ frontier (L.periodParallelogram z₀) := hz
    have hz'' :
        z ∈
          L.periodParallelogramCoordinateHomeomorph z₀ ''
            frontier (Complex.Rectangle 0 (1 + Complex.I)) := by
      -- Pull the frontier point back through the coordinate homeomorphism.
      have hzImage :
          z ∈ frontier
            (L.periodParallelogramCoordinateHomeomorph z₀ ''
              Complex.Rectangle 0 (1 + Complex.I)) := by
        simpa [L.periodParallelogram_eq_image_standardRectangle z₀] using hz'
      rw [← (L.periodParallelogramCoordinateHomeomorph z₀).image_frontier] at hzImage
      exact hzImage
    rcases hz'' with ⟨w, hw, rfl⟩
    have hwRange : w ∈ Set.range (axisParallelRectangleBoundaryPath 0 (1 + Complex.I)) := by
      -- The axis-parallel boundary path covers the entire rectangle frontier.
      rw [axisParallelRectangleBoundaryPath_range_eq_frontier 0 (1 + Complex.I)]
      exact hw
    rcases hwRange with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    have ht :
        L.periodParallelogramBoundaryPath z₀ t =
          L.periodParallelogramCoordinateHomeomorph z₀
            (axisParallelRectangleBoundaryPath 0 (1 + Complex.I) t) := by
      -- Reuse the same pointwise image formula to recover the actual slanted boundary point.
      simpa using
        congrArg (fun γ : Path z₀ z₀ ↦ γ t)
          (L.periodParallelogramBoundaryPath_eq_map_standardRectangle z₀)
    exact ht

/-- Helper for Cartan section11 0011_Proposition_5_1: a boundary-straightening chart for the
standard unit rectangle transports along the period-coordinate affine map to a chart for the
period parallelogram boundary. -/
private theorem map_standardRectangle_boundary_chart
    (L : PeriodPair) (z₀ : ℂ) {t₀ : ℝ}
    {δ : OpenPartialHomeomorph Plane Plane}
    (hδ :
      IsBoundaryStraighteningAt (Complex.Rectangle 0 (1 + Complex.I))
        ((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t₀ δ) :
    IsBoundaryStraighteningAt (L.periodParallelogram z₀)
      ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t₀
      (δ.trans
        (L.periodParallelogramCoordinateAffineEquiv z₀).toHomeomorph.toOpenPartialHomeomorph) := by
  let e := L.periodParallelogramCoordinateAffineEquiv z₀
  let τ : OpenPartialHomeomorph Plane Plane := e.toHomeomorph.toOpenPartialHomeomorph
  have heCont : ContDiffOn ℝ 1 e (Set.univ : Set Plane) := by
    simpa using e.toContinuousAffineMap.contDiff.contDiffOn
  have heSymmCont : ContDiffOn ℝ 1 e.symm (Set.univ : Set Plane) := by
    simpa using e.symm.toContinuousAffineMap.contDiff.contDiffOn
  have heSymmTarget : ContDiffOn ℝ 1 e.symm ((δ.trans τ).target) := by
    exact heSymmCont.mono (by intro p hp; simp)
  refine
    { basePoint_mem_source := ?_
      source_subset := ?_
      contDiffOn := ?_
      contDiffOn_symm := ?_
      map_horizontal_axis := ?_
      isImage_horizontalAxis := ?_
      exterior_on_right := ?_
      interior_on_left := ?_ }
  · -- The transported chart keeps the same parameter-strip source because the affine target map
    -- is globally defined.
    simpa [τ, OpenPartialHomeomorph.trans_source] using hδ.basePoint_mem_source
  · intro p hp
    -- The source restriction in the parameter plane is unchanged by the global affine target map.
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp
    exact hδ.source_subset hpδ
  · -- The transported forward map is the composition of two affine `C¹` maps on the same source.
    simpa [τ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_apply,
      Function.comp_def]
      using
        (heCont.comp hδ.contDiffOn
          (by
            intro p hp
            simp))
  · -- The inverse transported chart is the inverse affine map composed with the original inverse.
    simpa [τ, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_apply,
      Function.comp_def]
      using
        (hδ.contDiffOn_symm.comp heSymmTarget
          (by
            intro p hp
            simpa [τ, OpenPartialHomeomorph.trans_target] using hp))
  · intro t ht
    have htδ : t ∈ δ.horizontalAxisDomain := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, τ, OpenPartialHomeomorph.trans_source]
        using ht
    -- On the horizontal axis, the transported chart is just the affine target map applied to the
    -- standard rectangle boundary point.
    calc
      (δ.trans τ) (t, 0) = τ (δ (t, 0)) := by
        simp [τ, OpenPartialHomeomorph.trans_apply]
      _ = e (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
        rw [hδ.map_horizontal_axis htδ]
        rfl
      _ = ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t := by
        simpa using (L.periodParallelogramBoundary_realCurve_eq_standardRectangle z₀ t).symm
  · -- The horizontal-axis image is determined by the transported forward chart formula.
    apply curve_image_is_horizontal_axis
    intro t ht
    have htδ : t ∈ δ.horizontalAxisDomain := by
      simpa [OpenPartialHomeomorph.horizontalAxisDomain, τ, OpenPartialHomeomorph.trans_source]
        using ht
    calc
      (δ.trans τ) (t, 0) = τ (δ (t, 0)) := by
        simp [τ, OpenPartialHomeomorph.trans_apply]
      _ = e (((axisParallelRectangleBoundaryPath 0 (1 + Complex.I)).toClosedPath.realCurve) t) := by
        rw [hδ.map_horizontal_axis htδ]
        rfl
      _ = ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t := by
        simpa using (L.periodParallelogramBoundary_realCurve_eq_standardRectangle z₀ t).symm
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases hz.1 with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp.1
    have hneg : p.2 < 0 := hp.2
    have hxImage :
        Complex.equivRealProdCLM.symm ((δ.trans τ) p) ∈
          L.periodParallelogramCoordinateHomeomorph z₀ ''
            (Complex.Rectangle 0 (1 + Complex.I)) := by
      rw [L.periodParallelogram_eq_image_standardRectangle z₀]
      exact hz.2
    have hxRect :
        Complex.equivRealProdCLM.symm (δ p) ∈ Complex.Rectangle 0 (1 + Complex.I) := by
      rcases hxImage with ⟨x, hx, hxEq⟩
      have hcoord :
          L.periodParallelogramCoordinateHomeomorph z₀
              (Complex.equivRealProdCLM.symm (δ p)) =
            Complex.equivRealProdCLM.symm ((δ.trans τ) p) := by
        simpa [τ, OpenPartialHomeomorph.trans_apply] using
          (L.periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph z₀ (δ p))
      have hxEq' :
          L.periodParallelogramCoordinateHomeomorph z₀ x =
            L.periodParallelogramCoordinateHomeomorph z₀
              (Complex.equivRealProdCLM.symm (δ p)) := by
        exact hxEq.trans hcoord.symm
      have : x = Complex.equivRealProdCLM.symm (δ p) :=
        (L.periodParallelogramCoordinateHomeomorph z₀).injective hxEq'
      simpa [this] using hx
    have hzRectImage :
        Complex.equivRealProdCLM.symm (δ p) ∈
          (Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {q : Plane | q.2 < 0}))) ∩
            Complex.Rectangle 0 (1 + Complex.I) := by
      refine ⟨?_, hxRect⟩
      refine ⟨δ p, ?_, rfl⟩
      exact ⟨p, ⟨hpδ, hneg⟩, rfl⟩
    exact Set.eq_empty_iff_forall_notMem.mp hδ.exterior_on_right
      (Complex.equivRealProdCLM.symm (δ p)) hzRectImage
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rcases hw with ⟨p, hp, rfl⟩
    have hpδ : p ∈ δ.source := by
      simpa [τ, OpenPartialHomeomorph.trans_source] using hp.1
    have hpos : 0 < p.2 := hp.2
    have hxRect :
        Complex.equivRealProdCLM.symm (δ p) ∈ interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      have hzRectImage :
          Complex.equivRealProdCLM.symm (δ p) ∈
            Complex.equivRealProdCLM.symm '' (δ '' (δ.source ∩ {q : Plane | 0 < q.2})) := by
        refine ⟨δ p, ?_, rfl⟩
        exact ⟨p, ⟨hpδ, hpos⟩, rfl⟩
      exact hδ.interior_on_left hzRectImage
    have hxImage :
        L.periodParallelogramCoordinateHomeomorph z₀
            (Complex.equivRealProdCLM.symm (δ p)) ∈
          L.periodParallelogramCoordinateHomeomorph z₀ ''
            interior (Complex.Rectangle 0 (1 + Complex.I)) := by
      exact ⟨Complex.equivRealProdCLM.symm (δ p), hxRect, rfl⟩
    have hcoord :
        L.periodParallelogramCoordinateHomeomorph z₀
            (Complex.equivRealProdCLM.symm (δ p)) =
          Complex.equivRealProdCLM.symm ((δ.trans τ) p) := by
      simpa [τ, OpenPartialHomeomorph.trans_apply] using
        (L.periodParallelogramCoordinateAffineEquiv_apply_eq_homeomorph z₀ (δ p))
    have hxInterior :
        Complex.equivRealProdCLM.symm ((δ.trans τ) p) ∈ interior (L.periodParallelogram z₀) := by
      rw [(L.periodParallelogramCoordinateHomeomorph z₀).image_interior,
        L.periodParallelogram_eq_image_standardRectangle z₀] at hxImage
      exact hcoord ▸ hxImage
    simpa [τ, OpenPartialHomeomorph.trans_apply] using hxInterior

/-- Helper for Cartan section11 0011_Proposition_5_1: every regular parameter on the explicit
period-parallelogram boundary should admit a boundary-straightening chart. -/
private theorem periodParallelogramBoundary_exists_boundary_straightening
    (L : PeriodPair) (z₀ : ℂ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hdiff :
      DifferentiableWithinAt ℝ ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀)
    (_hderiv :
      derivWithin ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve)
        (Set.Icc (0 : ℝ) 1) t₀ ≠ 0) :
    ∃ δ : OpenPartialHomeomorph Plane Plane,
      IsBoundaryStraighteningAt (L.periodParallelogram z₀)
        ((L.periodParallelogramBoundaryPath z₀).toClosedPath.realCurve) t₀ δ := by
  -- Route correction: the classifier is now reduced to the standard rectangle by the inverse
  -- period-coordinate affine map, so each branch reuses the existing rectangle chart and
  -- transports it to the slanted period parallelogram.
  rcases L.periodParallelogramBoundary_regularParameterCases z₀ ht₀ hdiff with
    htbottom | htright | httop | htleft
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_bottom_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htbottom
    refine ⟨_, L.map_standardRectangle_boundary_chart z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_right_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htright
    refine ⟨_, L.map_standardRectangle_boundary_chart z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_top_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) httop
    refine ⟨_, L.map_standardRectangle_boundary_chart z₀ hδ⟩
  · obtain ⟨δ, hδ⟩ :=
      axis_parallel_rectangle_boundary_left_branch_exists_boundary_chart
        0 (1 + Complex.I) (by norm_num) (by norm_num) htleft
    refine ⟨_, L.map_standardRectangle_boundary_chart z₀ hδ⟩

/-- Helper for Cartan section11 0011_Proposition_5_1: the explicit four-edge period-parallelogram
loop is the singleton oriented boundary family of the period cell. -/
private theorem periodParallelogramBoundary_isOrientedBoundaryOf
    (L : PeriodPair) (z₀ : ℂ) :
    IsOrientedBoundaryOf (L.periodParallelogram z₀)
      (fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) := by
  classical
  let Γ : Unit → ClosedPath ℂ := fun _ ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath
  change IsOrientedBoundaryOf (L.periodParallelogram z₀) Γ
  refine
    { isCompact := ?_
      piecewiseDifferentiable := ?_
      simple_loops := ?_
      pairwiseDisjoint_ranges := ?_
      iUnion_range_eq_frontier := ?_
      exists_boundary_chart_at_regular_point := ?_ }
  · -- Compactness was already reduced to the affine-image description of the period cell.
    exact periodParallelogram_isCompact L z₀
  · rintro ⟨⟩
    -- The singleton contour inherits the explicit piecewise-differentiable four-segment
    -- parametrization.
    simpa [Γ] using L.periodParallelogramBoundaryPath_isPiecewiseDifferentiable z₀
  · rintro ⟨⟩ s t hst
    -- Simplicity reduces to the transported rectangle-boundary injectivity statement.
    exact L.periodParallelogramBoundaryPath_simple_eq_or_endpoints z₀ hst
  · intro i j hij
    exact (hij rfl).elim
  · have hboundary :
        (⋃ i, Set.range ((Γ i : ClosedPath ℂ).toPath)) =
          Set.range (L.periodParallelogramBoundaryPath z₀) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        cases i
        simpa [Γ, Path.toClosedPath] using hi
      · intro hx
        refine Set.mem_iUnion.mpr ?_
        refine ⟨(), ?_⟩
        simpa [Γ, Path.toClosedPath] using hx
    -- Rewrite the singleton-family frontier equality back to the explicit loop range.
    simpa using hboundary.trans (L.periodParallelogramBoundaryPath_range_eq_frontier z₀)
  · rintro ⟨⟩ t₀ ht₀ hdiff hderiv
    -- The remaining local geometry is exactly the explicit boundary-straightening lemma above.
    exact L.periodParallelogramBoundary_exists_boundary_straightening z₀ ht₀ hdiff hderiv

/-- Helper for Cartan section11 0011_Proposition_5_1: once the period-parallelogram boundary is
recognized as the standard four translated edges, the opposite-edge logarithmic-derivative
integrals cancel in pairs. -/
private theorem logDeriv_periodParallelogramBoundaryIntegral_eq_zero
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ)) :
    ∫ᶜ z in (L.periodParallelogramBoundaryPath z₀).toClosedPath.toPath,
      ((logDeriv f dz) z) = 0 := by
  let z₁ : ℂ := z₀ + L.ω₁
  let z₂ : ℂ := z₀ + L.ω₁ + L.ω₂
  let z₃ : ℂ := z₀ + L.ω₂
  let gNF : ℂ → ℂ := toMeromorphicNFOn f Set.univ
  have hω₁ : Function.Periodic (logDeriv f) L.ω₁ := by
    -- The first lattice generator is a period of `logDeriv f`.
    intro z
    simpa [z₁, add_assoc] using
      logDeriv_add_period_eq_of_hasPeriodLattice
        (L := L) (g := f) hperiods (ω := L.ω₁) (z := z) L.ω₁_mem_lattice
  have hω₂ : Function.Periodic (logDeriv f) L.ω₂ := by
    -- The second lattice generator is a period of `logDeriv f`.
    intro z
    simpa [z₃, add_assoc, add_left_comm, add_comm] using
      logDeriv_add_period_eq_of_hasPeriodLattice
        (L := L) (g := f) hperiods (ω := L.ω₂) (z := z) L.ω₂_mem_lattice
  -- Route correction: normalize the loop to its four explicit affine edges before pairing the
  -- two translated vertical edges and the two translated horizontal edges.
  have hright_eq :
      ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv f dz) z) =
        ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z) := by
    -- The right edge is the `ω₁`-translate of the left edge.
    have hz₂ : z₀ + L.ω₂ + L.ω₁ = z₂ := by
      simp [z₂, add_left_comm, add_comm]
    calc
      ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv f dz) z) =
          ∫ᶜ z in Path.segment z₁ (z₀ + L.ω₂ + L.ω₁), ((logDeriv f dz) z) := by
            rw [hz₂]
      _ = ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z) := by
            simpa [z₁, z₃] using
              curveIntegral_segment_translate_eq_of_periodic
                (φ := logDeriv f) (a := z₀) (b := z₃) (ω := L.ω₁) hω₁
  have htop_eq :
      ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv f dz) z) =
        ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv f dz) z) := by
    -- The top edge is the `ω₂`-translate of the reversed bottom edge.
    simpa [z₁, z₂, z₃, add_assoc, add_left_comm, add_comm] using
      curveIntegral_segment_translate_eq_of_periodic
        (φ := logDeriv f) (a := z₁) (b := z₀) (ω := L.ω₂) hω₂
  have hω₁_ne : L.ω₁ ≠ 0 := by
    -- Each period basis vector is nonzero.
    simpa using L.basis.ne_zero 0
  have hω₂_ne : L.ω₂ ≠ 0 := by
    -- The second period basis vector is nonzero for the same reason.
    simpa using L.basis.ne_zero 1
  have hz₀z₁ : z₀ ≠ z₁ := by
    -- Distinct vertices differ by the nonzero first period.
    intro hz
    have : z₀ - z₁ = 0 := sub_eq_zero.mpr hz
    exact hω₁_ne (by simpa [z₁] using this)
  have hz₁z₂ : z₁ ≠ z₂ := by
    -- The right edge is nondegenerate because it moves by the nonzero second period.
    intro hz
    have : z₁ - z₂ = 0 := sub_eq_zero.mpr hz
    exact hω₂_ne (by simpa [z₁, z₂, add_assoc] using this)
  have hz₂z₃ : z₂ ≠ z₃ := by
    -- The top edge is nondegenerate because it moves by the nonzero first period.
    intro hz
    have : z₂ - z₃ = 0 := sub_eq_zero.mpr hz
    exact hω₁_ne (by simpa [z₂, z₃, add_assoc, add_left_comm, add_comm] using this)
  have hz₃z₀ : z₃ ≠ z₀ := by
    -- The left edge is nondegenerate because it moves by the nonzero second period.
    intro hz
    have : z₃ - z₀ = 0 := sub_eq_zero.mpr hz
    exact hω₂_ne (by simpa [z₃] using this)
  have hgNF : MeromorphicNFOn gNF Set.univ := by
    -- The owner normal form is meromorphic normal-form on the whole plane.
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn f Set.univ
  have hgNF_order :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt gNF z = (0 : WithTop ℤ) := by
    intro z hz
    -- On the boundary, the normal-form representative has the same order as the original
    -- meromorphic function.
    rw [meromorphicOrderAt_toMeromorphicNFOn hf.meromorphicOn (by simp)]
    exact hboundary z hz
  have hgNF_cont :
      ContinuousOn (logDeriv gNF) (frontier (L.periodParallelogram z₀)) := by
    -- Order zero on the whole frontier gives pointwise differentiability, hence continuity there.
    intro z hz
    exact
      (differentiableAt_logDeriv_of_meromorphicNFAt_order_zero
        (hgNF (by simp)) (hgNF_order z hz)).continuousAt.continuousWithinAt
  have hgNF_form_cont :
      ContinuousOn (fun z ↦ ((logDeriv gNF dz) z)) (frontier (L.periodParallelogram z₀)) :=
    scalarOneForm_continuousOn hgNF_cont
  have hcodiscreteEq :
      logDeriv f =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] logDeriv gNF := by
    -- The logarithmic derivative agrees codiscretely with the owner normal form on `Set.univ`.
    simpa [gNF] using logDeriv_toMeromorphicNFOn_eq_codiscrete (U := Set.univ) hf.meromorphicOn
  have hbottom_frontier :
      Set.range (Path.segment z₀ z₁) ⊆ frontier (L.periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have htHalf : ((t : ℝ) / 2) ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      constructor <;> linarith [t.2.1, t.2.2]
    have htHalfI : ((t : ℝ) / 2) ∈ I := by
      constructor
      · exact htHalf.1
      · linarith [htHalf.2]
    have hseg :
        Path.segment z₀ z₁ t = AffineMap.lineMap z₀ z₁ (t : ℝ) := by
      rw [← Path.extend_apply (γ := Path.segment z₀ z₁) t.2]
      exact Path.eqOn_extend_segment z₀ z₁ t.2
    have hside :
        (L.periodParallelogramBoundaryPath z₀) ⟨(t : ℝ) / 2, htHalfI⟩ =
          AffineMap.lineMap z₀ z₁ (t : ℝ) := by
      rw [← Path.extend_apply (γ := L.periodParallelogramBoundaryPath z₀) htHalfI]
      calc
        (L.periodParallelogramBoundaryPath z₀).extend ((t : ℝ) / 2) =
            AffineMap.lineMap z₀ z₁ (2 * ((t : ℝ) / 2)) := by
              simpa [z₁] using L.periodParallelogramBoundaryPath_eqOn_bottom_side z₀ htHalf
        _ = AffineMap.lineMap z₀ z₁ (t : ℝ) := by
              congr 1
              ring
    rw [← L.periodParallelogramBoundaryPath_range_eq_frontier z₀]
    refine ⟨⟨(t : ℝ) / 2, htHalfI⟩, ?_⟩
    simpa [hseg] using hside
  have hright_frontier :
      Set.range (Path.segment z₁ z₂) ⊆ frontier (L.periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have htRight : (((t : ℝ) + 2) / 4) ∈ Set.Icc (1 / 2 : ℝ) (3 / 4) := by
      constructor <;> linarith [t.2.1, t.2.2]
    have htRightI : (((t : ℝ) + 2) / 4) ∈ I := by
      constructor <;> linarith [htRight.1, htRight.2]
    have hseg :
        Path.segment z₁ z₂ t = AffineMap.lineMap z₁ z₂ (t : ℝ) := by
      rw [← Path.extend_apply (γ := Path.segment z₁ z₂) t.2]
      exact Path.eqOn_extend_segment z₁ z₂ t.2
    have hside :
        (L.periodParallelogramBoundaryPath z₀) ⟨((t : ℝ) + 2) / 4, htRightI⟩ =
          AffineMap.lineMap z₁ z₂ (t : ℝ) := by
      rw [← Path.extend_apply (γ := L.periodParallelogramBoundaryPath z₀) htRightI]
      calc
        (L.periodParallelogramBoundaryPath z₀).extend (((t : ℝ) + 2) / 4) =
            AffineMap.lineMap z₁ z₂ (4 * (((t : ℝ) + 2) / 4) - 2) := by
              simpa [z₁, z₂] using L.periodParallelogramBoundaryPath_eqOn_right_side z₀ htRight
        _ = AffineMap.lineMap z₁ z₂ (t : ℝ) := by
              congr 1
              ring
    rw [← L.periodParallelogramBoundaryPath_range_eq_frontier z₀]
    refine ⟨⟨((t : ℝ) + 2) / 4, htRightI⟩, ?_⟩
    simpa [hseg] using hside
  have htop_frontier :
      Set.range (Path.segment z₂ z₃) ⊆ frontier (L.periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have htTop : (((t : ℝ) + 6) / 8) ∈ Set.Icc (3 / 4 : ℝ) (7 / 8) := by
      constructor <;> linarith [t.2.1, t.2.2]
    have htTopI : (((t : ℝ) + 6) / 8) ∈ I := by
      constructor <;> linarith [htTop.1, htTop.2]
    have hseg :
        Path.segment z₂ z₃ t = AffineMap.lineMap z₂ z₃ (t : ℝ) := by
      rw [← Path.extend_apply (γ := Path.segment z₂ z₃) t.2]
      exact Path.eqOn_extend_segment z₂ z₃ t.2
    have hside :
        (L.periodParallelogramBoundaryPath z₀) ⟨((t : ℝ) + 6) / 8, htTopI⟩ =
          AffineMap.lineMap z₂ z₃ (t : ℝ) := by
      rw [← Path.extend_apply (γ := L.periodParallelogramBoundaryPath z₀) htTopI]
      calc
        (L.periodParallelogramBoundaryPath z₀).extend (((t : ℝ) + 6) / 8) =
            AffineMap.lineMap z₂ z₃ (8 * (((t : ℝ) + 6) / 8) - 6) := by
              simpa [z₂, z₃] using L.periodParallelogramBoundaryPath_eqOn_top_side z₀ htTop
        _ = AffineMap.lineMap z₂ z₃ (t : ℝ) := by
              congr 1
              ring
    rw [← L.periodParallelogramBoundaryPath_range_eq_frontier z₀]
    refine ⟨⟨((t : ℝ) + 6) / 8, htTopI⟩, ?_⟩
    simpa [hseg] using hside
  have hleft_frontier :
      Set.range (Path.segment z₃ z₀) ⊆ frontier (L.periodParallelogram z₀) := by
    intro z hz
    rcases hz with ⟨t, rfl⟩
    have htLeft : (((t : ℝ) + 7) / 8) ∈ Set.Icc (7 / 8 : ℝ) (1 : ℝ) := by
      constructor <;> linarith [t.2.1, t.2.2]
    have htLeftI : (((t : ℝ) + 7) / 8) ∈ I := by
      constructor <;> linarith [htLeft.1, htLeft.2]
    have hseg :
        Path.segment z₃ z₀ t = AffineMap.lineMap z₃ z₀ (t : ℝ) := by
      rw [← Path.extend_apply (γ := Path.segment z₃ z₀) t.2]
      exact Path.eqOn_extend_segment z₃ z₀ t.2
    have hside :
        (L.periodParallelogramBoundaryPath z₀) ⟨((t : ℝ) + 7) / 8, htLeftI⟩ =
          AffineMap.lineMap z₃ z₀ (t : ℝ) := by
      rw [← Path.extend_apply (γ := L.periodParallelogramBoundaryPath z₀) htLeftI]
      calc
        (L.periodParallelogramBoundaryPath z₀).extend (((t : ℝ) + 7) / 8) =
            AffineMap.lineMap z₃ z₀ (8 * (((t : ℝ) + 7) / 8) - 7) := by
              simpa [z₃] using L.periodParallelogramBoundaryPath_eqOn_left_side z₀ htLeft
        _ = AffineMap.lineMap z₃ z₀ (t : ℝ) := by
              congr 1
              ring
    rw [← L.periodParallelogramBoundaryPath_range_eq_frontier z₀]
    refine ⟨⟨((t : ℝ) + 7) / 8, htLeftI⟩, ?_⟩
    simpa [hseg] using hside
  have hbottomIntNF :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z₀ z₁) := by
    -- The normal-form logarithmic derivative is continuous along the bottom boundary edge.
    rw [curveIntegrable_segment]
    have hωAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z₀ z₁ t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hgNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hbottom_frontier ⟨⟨t, ht⟩, by simp [Path.segment, AffineMap.lineMap_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₀ z₁ t)) (z₁ - z₀)))
          (Set.Icc (0 : ℝ) 1) :=
      hωAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₀ z₁ t)) (z₁ - z₀)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hrightIntNF :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z₁ z₂) := by
    -- The same continuity package applies to the right edge.
    rw [curveIntegrable_segment]
    have hωAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z₁ z₂ t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hgNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hright_frontier ⟨⟨t, ht⟩, by simp [Path.segment, AffineMap.lineMap_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₁ z₂ t)) (z₂ - z₁)))
          (Set.Icc (0 : ℝ) 1) :=
      hωAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₁ z₂ t)) (z₂ - z₁)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have htopIntNF :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z₂ z₃) := by
    -- The same continuity package applies to the top edge.
    rw [curveIntegrable_segment]
    have hωAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z₂ z₃ t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hgNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact htop_frontier ⟨⟨t, ht⟩, by simp [Path.segment, AffineMap.lineMap_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₂ z₃ t)) (z₃ - z₂)))
          (Set.Icc (0 : ℝ) 1) :=
      hωAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₂ z₃ t)) (z₃ - z₂)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hleftIntNF :
      CurveIntegrable (fun z ↦ ((logDeriv gNF dz) z)) (Path.segment z₃ z₀) := by
    -- The same continuity package applies to the left edge.
    rw [curveIntegrable_segment]
    have hωAlong :
        ContinuousOn (fun t : ℝ ↦ ((logDeriv gNF dz) (AffineMap.lineMap z₃ z₀ t)))
          (Set.Icc (0 : ℝ) 1) := by
      refine hgNF_form_cont.comp (by fun_prop) ?_
      intro t ht
      exact hleft_frontier ⟨⟨t, ht⟩, by simp [Path.segment, AffineMap.lineMap_apply]⟩
    have hParam :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₃ z₀ t)) (z₀ - z₃)))
          (Set.Icc (0 : ℝ) 1) :=
      hωAlong.clm_apply continuousOn_const
    have hParamU :
        ContinuousOn
          (fun t : ℝ ↦ (((logDeriv gNF dz) (AffineMap.lineMap z₃ z₀ t)) (z₀ - z₃)))
          (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc, zero_le_one] using hParam
    exact hParamU.intervalIntegrable
  have hbottomInt :
      CurveIntegrable (fun z ↦ ((logDeriv f dz) z)) (Path.segment z₀ z₁) :=
    curveIntegrable_segment_of_codiscreteEq hz₀z₁ hbottomIntNF hcodiscreteEq
  have hrightInt :
      CurveIntegrable (fun z ↦ ((logDeriv f dz) z)) (Path.segment z₁ z₂) :=
    curveIntegrable_segment_of_codiscreteEq hz₁z₂ hrightIntNF hcodiscreteEq
  have htopInt :
      CurveIntegrable (fun z ↦ ((logDeriv f dz) z)) (Path.segment z₂ z₃) :=
    curveIntegrable_segment_of_codiscreteEq hz₂z₃ htopIntNF hcodiscreteEq
  have hleftInt :
      CurveIntegrable (fun z ↦ ((logDeriv f dz) z)) (Path.segment z₃ z₀) :=
    curveIntegrable_segment_of_codiscreteEq hz₃z₀ hleftIntNF hcodiscreteEq
  have hbottom_symm :
      ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv f dz) z) =
        -∫ᶜ z in Path.segment z₀ z₁, ((logDeriv f dz) z) := by
    -- Reversing the bottom edge flips the sign of its integral.
    simpa using curveIntegral_symm (ω := fun z ↦ ((logDeriv f dz) z)) (γ := Path.segment z₀ z₁)
  have hleft_symm :
      ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv f dz) z) =
        -∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z) := by
    -- Reversing the left edge flips the sign of its integral.
    simpa using curveIntegral_symm (ω := fun z ↦ ((logDeriv f dz) z)) (γ := Path.segment z₀ z₃)
  -- Expand the closed loop into its four affine sides and cancel the opposite translated pairs.
  calc
    ∫ᶜ z in (L.periodParallelogramBoundaryPath z₀).toClosedPath.toPath, ((logDeriv f dz) z) =
        ∫ᶜ z in L.periodParallelogramBoundaryPath z₀, ((logDeriv f dz) z) := by
          rw [loopToClosedPathToPathEqCast]
          simp [curveIntegral_cast]
    _ =
        ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv f dz) z) +
          ∫ᶜ z in Path.segment z₁ z₂, ((logDeriv f dz) z) +
            ∫ᶜ z in Path.segment z₂ z₃, ((logDeriv f dz) z) +
              ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv f dz) z) := by
          rw [periodParallelogramBoundaryPath, curveIntegral_trans hbottomInt
            (CurveIntegrable.trans hrightInt (CurveIntegrable.trans htopInt hleftInt))]
          rw [curveIntegral_trans hrightInt (CurveIntegrable.trans htopInt hleftInt)]
          rw [curveIntegral_trans htopInt hleftInt]
          ring
    _ =
        ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv f dz) z) +
          ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z) +
            ∫ᶜ z in Path.segment z₁ z₀, ((logDeriv f dz) z) +
              ∫ᶜ z in Path.segment z₃ z₀, ((logDeriv f dz) z) := by
          rw [hright_eq, htop_eq]
    _ =
        ∫ᶜ z in Path.segment z₀ z₁, ((logDeriv f dz) z) +
          ∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z) +
            (-∫ᶜ z in Path.segment z₀ z₁, ((logDeriv f dz) z)) +
              (-∫ᶜ z in Path.segment z₀ z₃, ((logDeriv f dz) z)) := by
          rw [hbottom_symm, hleft_symm]
    _ = 0 := by ring

end PeriodPair

/-- Helper for Cartan section11 0011_Proposition_5_1: boundary order zero forces the divisor to
vanish on the frontier of the period parallelogram. -/
private theorem divisor_eq_zero_on_frontier_of_boundary_order_zero
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    {z : ℂ} (hz : z ∈ frontier (L.periodParallelogram z₀)) :
    divisor f (L.periodParallelogram z₀) z = 0 := by
  have hzK : z ∈ L.periodParallelogram z₀ := by
    exact (periodParallelogram_isCompact L z₀).isClosed.frontier_subset hz
  -- Rewrite the divisor through the meromorphic order and apply the boundary regularity
  -- hypothesis.
  simpa [hboundary z hz] using (hf.meromorphicOn.divisor_apply hzK)

/-- Cartan section11 0011_Proposition_5_1. The total divisor sum of a meromorphic periodic
function on a boundary-regular period parallelogram vanishes. -/
theorem total_divisor_finsum_eq_zero_in_periodParallelogram
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ)) :
    ∑ᶠ z, divisor f (L.periodParallelogram z₀) z = 0 := by
  have hΓ :
      IsOrientedBoundaryOf (L.periodParallelogram z₀)
        (fun _ : Unit ↦ (L.periodParallelogramBoundaryPath z₀).toClosedPath) := by
    -- Package the explicit four-edge loop as the singleton oriented boundary family of the cell.
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

/-- Derived zero-versus-pole reformulation of Cartan section11 0011_Proposition_5_1. If `f` is
meromorphic on the whole complex plane and is periodic with respect to every element of the
lattice generated by `L`, then the positive and negative divisor contributions in a period
parallelogram have the same total multiplicity, provided no zero or pole lies on the boundary of
the parallelogram. -/
theorem zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    :
    ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁺ z =
      ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁻ z := by
  let P : Set ℂ := L.periodParallelogram z₀
  let D := divisor f P
  have hcompact : IsCompact P := by
    let e : ℝ × ℝ → ℂ := fun t ↦ z₀ + t.1 • L.ω₁ + t.2 • L.ω₂
    have he : Continuous e := by
      -- The affine-coordinate parametrization of the period cell is continuous.
      continuity
    have himage : e '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = P := by
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
    -- The compact-support `finsum` is the contour-theoretic total divisor sum, which is zero.
    calc
      Finset.sum s (fun z ↦ D z) = ∑ᶠ z, D z := by
        symm
        exact finsum_eq_sum_of_support_subset _ hsuppD
      _ = 0 := by
        simpa [D, P] using
          total_divisor_finsum_eq_zero_in_periodParallelogram L z₀ hf hperiods hboundary
  have hsumParts :
      Finset.sum s (fun z ↦ D⁺ z) - Finset.sum s (fun z ↦ D⁻ z) = 0 := by
    -- Sum the pointwise identity `D⁺ - D⁻ = D` over the common finite support finset.
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

/-- Finset representative-set reformulation of Proposition 5.1. -/
theorem zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram_finset
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods : HasPeriodLattice L f)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet f (L.periodParallelogram z₀) roots)
    (hpoles : IsPoleRepresentativeSet f (L.periodParallelogram z₀) poles) :
    roots.sum (divisor f (L.periodParallelogram z₀)) =
      poles.sum (fun z ↦ -divisor f (L.periodParallelogram z₀) z) := by
  rw [hroots.sum_divisor_eq_finsum_posPart, hpoles.sum_neg_divisor_eq_finsum_negPart]
  exact zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram
    L z₀ hf hperiods hboundary

/-- Derived exact-period reformulation of Proposition 5.1. -/
theorem zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram_of_periods_eq_lattice
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods_eq : ∀ ω : ℂ, Function.Periodic f ω ↔ ω ∈ L.lattice.toAddSubgroup)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ)) :
    ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁺ z =
      ∑ᶠ z, (divisor f (L.periodParallelogram z₀))⁻ z :=
  zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram L z₀ hf
    (fun ω hω ↦ (hperiods_eq ω).2 hω) hboundary

/-- Finset representative-set exact-period reformulation of Proposition 5.1. -/
theorem
    zero_multiplicity_sum_eq_pole_multiplicity_sum_finset_of_periods_eq_lattice
    {f : ℂ → ℂ} (L : PeriodPair) (z₀ : ℂ)
    (hf : Meromorphic f)
    (hperiods_eq : ∀ ω : ℂ, Function.Periodic f ω ↔ ω ∈ L.lattice.toAddSubgroup)
    (hboundary :
      ∀ z ∈ frontier (L.periodParallelogram z₀), meromorphicOrderAt f z = (0 : WithTop ℤ))
    (roots poles : Finset ℂ)
    (hroots : IsZeroRepresentativeSet f (L.periodParallelogram z₀) roots)
    (hpoles : IsPoleRepresentativeSet f (L.periodParallelogram z₀) poles) :
    roots.sum (divisor f (L.periodParallelogram z₀)) =
      poles.sum (fun z ↦ -divisor f (L.periodParallelogram z₀) z) := by
  rw [hroots.sum_divisor_eq_finsum_posPart, hpoles.sum_neg_divisor_eq_finsum_negPart]
  exact zero_multiplicity_sum_eq_pole_multiplicity_sum_in_period_parallelogram_of_periods_eq_lattice
    L z₀ hf hperiods_eq hboundary
