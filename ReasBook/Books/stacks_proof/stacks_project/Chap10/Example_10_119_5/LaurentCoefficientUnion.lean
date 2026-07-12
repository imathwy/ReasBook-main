import StacksProject_2024.Chap10.Example_10_119_5.CoefficientFractionField

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the coefficient-restricted Laurent series has
well-founded support. -/
lemma laurentSeries_restrictCoeff_isPWO_support
    (L : IntermediateField (k^[p]) k) (z : LaurentSeries k)
    (hz : ∀ n : ℤ, z.coeff n ∈ L) :
    (Function.support fun n : ℤ ↦ (⟨z.coeff n, hz n⟩ : L)).IsPWO := by
  -- The restricted support is contained in the original Laurent-series support.
  refine z.isPWO_support.mono ?_
  intro n hn hzero
  apply hn
  exact Subtype.ext hzero

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: restrict a Laurent series whose coefficients lie in
an intermediate field to a Laurent series over that field. -/
noncomputable def laurentSeries_restrictCoeff
    (L : IntermediateField (k^[p]) k) (z : LaurentSeries k)
    (hz : ∀ n : ℤ, z.coeff n ∈ L) :
    LaurentSeries L :=
  ⟨fun n ↦ ⟨z.coeff n, hz n⟩,
    laurentSeries_restrictCoeff_isPWO_support (k := k) (p := p) L z hz⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: mapping the coefficient-restricted Laurent series
back to `k` recovers the original series. -/
lemma laurentSeries_restrictCoeff_map
    (L : IntermediateField (k^[p]) k) (z : LaurentSeries k)
    (hz : ∀ n : ℤ, z.coeff n ∈ L) :
    (laurentSeries_restrictCoeff (k := k) (p := p) L z hz).map L.val.toRingHom = z := by
  -- Coefficient extensionality reduces the bridge to the subtype value projection.
  ext n
  rfl

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: apply a coefficient ring homomorphism to a Laurent
series coefficientwise as a ring homomorphism. -/
noncomputable def laurentSeriesMapRingHom {L : Type*} [Field L]
    (f : L →+* k) : LaurentSeries L →+* LaurentSeries k where
  toFun z := z.map f
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_add' := fun z w ↦ HahnSeries.map_add f.toAddMonoidHom (x := z) (y := w)
  map_mul' := fun z w ↦ HahnSeries.map_mul f.toNonUnitalRingHom (x := z) (y := w)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: coefficientwise Laurent maps have the expected
coefficient formula. -/
lemma laurentSeriesMapRingHom_coeff {L : Type*} [Field L]
    (f : L →+* k) (z : LaurentSeries L) (n : ℤ) :
    (laurentSeriesMapRingHom (k := k) f z).coeff n = f (z.coeff n) := by
  -- The ring hom was packaged around `HahnSeries.map`, whose coefficients are definitional.
  rfl

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: Laurent series over a fixed intermediate coefficient
field, viewed inside `LaurentSeries k`. -/
noncomputable def finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) : Subfield (LaurentSeries k) :=
  (laurentSeriesMapRingHom (k := k) L.val.toRingHom).fieldRange

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the fixed finite-coefficient Laurent subfield is exactly
the Laurent series whose coefficients all lie in that intermediate field. -/
lemma finiteCoeffLaurentSubfield_mem_iff_coeff_mem
    (L : IntermediateField (k^[p]) k) (z : LaurentSeries k) :
    z ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L ↔
      ∀ n : ℤ, z.coeff n ∈ L := by
  constructor
  · -- A series in the field range is the coefficientwise image of a series over `L`.
    rintro ⟨w, hw⟩ n
    rw [← hw]
    exact (w.coeff n).2
  · -- If every coefficient lies in `L`, restrict coefficients and map back to `k`.
    intro hz
    refine ⟨laurentSeries_restrictCoeff (k := k) (p := p) L z hz, ?_⟩
    simpa [finiteCoeffLaurentSubfield, laurentSeriesMapRingHom] using
      laurentSeries_restrictCoeff_map (k := k) (p := p) L z hz

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: enlarging the coefficient field enlarges the associated
Laurent coefficient subfield. -/
lemma finiteCoeffLaurentSubfield_mono
    {L M : IntermediateField (k^[p]) k} (hLM : L ≤ M) :
    finiteCoeffLaurentSubfield (k := k) (p := p) L ≤
      finiteCoeffLaurentSubfield (k := k) (p := p) M := by
  -- The coefficient criterion turns monotonicity into pointwise containment of coefficients.
  intro z hz
  rw [finiteCoeffLaurentSubfield_mem_iff_coeff_mem] at hz ⊢
  intro n
  exact hLM (hz n)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finitely many Laurent series with individually finite
coefficient fields have one common finite coefficient field. -/
lemma finiteCoeffLaurentSubfield_finset_common {ι : Type*}
    (s : Finset ι) (z : ι → LaurentSeries k)
    (hz : ∀ i ∈ s,
      ∃ L : IntermediateField (k^[p]) k,
        FiniteDimensional (k^[p]) L ∧
          z i ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L) :
    ∃ L : IntermediateField (k^[p]) k,
      FiniteDimensional (k^[p]) L ∧
        ∀ i ∈ s, z i ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L := by
  classical
  -- Induct over the finite support and take composita of the individual coefficient fields.
  revert hz
  refine Finset.induction_on s ?_ ?_
  · intro hz
    refine ⟨⊥, inferInstance, ?_⟩
    simp
  · intro a s has ih hz
    obtain ⟨Ls, hLsFinite, hLs⟩ := ih (by
      intro i hi
      exact hz i (Finset.mem_insert_of_mem hi))
    obtain ⟨La, hLaFinite, hLa⟩ := hz a (Finset.mem_insert_self a s)
    letI : FiniteDimensional (k^[p]) Ls := hLsFinite
    letI : FiniteDimensional (k^[p]) La := hLaFinite
    refine ⟨La ⊔ Ls, inferInstance, ?_⟩
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact finiteCoeffLaurentSubfield_mono (k := k) (p := p)
        (show La ≤ La ⊔ Ls from le_sup_left) hLa
    · exact finiteCoeffLaurentSubfield_mono (k := k) (p := p)
        (show Ls ≤ La ⊔ Ls from le_sup_right) (hLs i hi)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the union of all Laurent coefficient subfields whose
coefficient fields are finite over `k^p`. -/
noncomputable def finiteCoeffLaurentUnion : Subfield (LaurentSeries k) :=
  ⨆ L : {L : IntermediateField (k^[p]) k // FiniteDimensional (k^[p]) L},
    finiteCoeffLaurentSubfield (k := k) (p := p) L.1

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: every finite-coefficient Laurent subfield maps into the
union coefficient subfield. -/
lemma finiteCoeffLaurentSubfield_le_union
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L] :
    finiteCoeffLaurentSubfield (k := k) (p := p) L ≤
      finiteCoeffLaurentUnion (k := k) (p := p) := by
  -- The union is an indexed supremum, so each indexed finite coefficient field contributes by
  -- the lattice inclusion into that supremum.
  exact le_iSup
    (fun M : {L : IntermediateField (k^[p]) k // FiniteDimensional (k^[p]) L} ↦
      finiteCoeffLaurentSubfield (k := k) (p := p) M.1)
    ⟨L, inferInstance⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: membership in any finite coefficient Laurent subfield
gives membership in the union. -/
lemma finiteCoeffLaurentUnion_mem_of_mem_subfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    {z : LaurentSeries k}
    (hz : z ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L) :
    z ∈ finiteCoeffLaurentUnion (k := k) (p := p) := by
  -- Consume the previous inclusion as a one-line bridge for later codomain restrictions.
  exact finiteCoeffLaurentSubfield_le_union (k := k) (p := p) L hz

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: membership in the Laurent coefficient union is
equivalent to membership in one finite coefficient Laurent subfield. -/
lemma finiteCoeffLaurentUnion_mem_iff_exists_subfield
    (z : LaurentSeries k) :
    z ∈ finiteCoeffLaurentUnion (k := k) (p := p) ↔
      ∃ L : IntermediateField (k^[p]) k,
        FiniteDimensional (k^[p]) L ∧
          z ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L := by
  classical
  -- The finite coefficient Laurent subfields are directed under compositum.
  let ι := {L : IntermediateField (k^[p]) k // FiniteDimensional (k^[p]) L}
  have hnonempty : Nonempty ι :=
    ⟨⟨⊥, inferInstance⟩⟩
  letI : Nonempty ι := hnonempty
  have hdirected :
      Directed (· ≤ ·)
        (fun L : ι ↦ finiteCoeffLaurentSubfield (k := k) (p := p) L.1) := by
    intro L M
    letI : FiniteDimensional (k^[p]) L.1 := L.2
    letI : FiniteDimensional (k^[p]) M.1 := M.2
    refine ⟨⟨L.1 ⊔ M.1, inferInstance⟩, ?_, ?_⟩
    · exact finiteCoeffLaurentSubfield_mono (k := k) (p := p)
        (show L.1 ≤ L.1 ⊔ M.1 from le_sup_left)
    · exact finiteCoeffLaurentSubfield_mono (k := k) (p := p)
        (show M.1 ≤ L.1 ⊔ M.1 from le_sup_right)
  -- Convert the directed supremum to an ordinary existential over its finite stages.
  rw [finiteCoeffLaurentUnion]
  constructor
  · intro hz
    obtain ⟨L, hLz⟩ := (Subfield.mem_iSup_of_directed hdirected).1 hz
    exact ⟨L.1, L.2, hLz⟩
  · rintro ⟨L, hLfinite, hLz⟩
    letI : FiniteDimensional (k^[p]) L := hLfinite
    exact finiteCoeffLaurentUnion_mem_of_mem_subfield (k := k) (p := p) L hLz

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finitely many elements of the Laurent coefficient union
lie in one common finite coefficient Laurent subfield. -/
lemma finiteCoeffLaurentUnion_finset_common {ι : Type*}
    (s : Finset ι) (z : ι → LaurentSeries k)
    (hz : ∀ i ∈ s, z i ∈ finiteCoeffLaurentUnion (k := k) (p := p)) :
    ∃ L : IntermediateField (k^[p]) k,
      FiniteDimensional (k^[p]) L ∧
        ∀ i ∈ s, z i ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L := by
  -- First normalize each element of the finite set to a finite coefficient field, then take one
  -- finite compositum using the fixed-subfield common-field lemma.
  exact finiteCoeffLaurentSubfield_finset_common (k := k) (p := p) s z (by
    intro i hi
    exact (finiteCoeffLaurentUnion_mem_iff_exists_subfield (k := k) (p := p) (z i)).1
      (hz i hi))

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: powers of the Laurent uniformizer already come from
the coefficient subring. -/
lemma X_pow_mem_finitePthPowerCoefficientSubring (n : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ n ∈ A := by
  -- Subrings are closed under powers, and `X` itself was already put in `A`.
  exact pow_mem (X_mem_finitePthPowerCoefficientSubring k p) n

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the power-series part of a Laurent series over one
finite coefficient field belongs to the coefficient subring. -/
lemma powerSeriesPart_mem_finitePthPowerCoefficientSubring_of_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    {z : LaurentSeries k}
    (hz : z ∈ finiteCoeffLaurentSubfield (k := k) (p := p) L) :
    z.powerSeriesPart ∈ A := by
  -- The coefficients of `powerSeriesPart z` are just shifted Laurent coefficients of `z`.
  rw [finiteCoeffLaurentSubfield_mem_iff_coeff_mem] at hz
  refine hasFinitePthPowerCoefficientField_of_coeff_mem k p z.powerSeriesPart L ?_
  intro n
  rw [LaurentSeries.powerSeriesPart_coeff]
  exact hz (z.order + n)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a power series from `A` is a Laurent series in the union
coefficient subfield. -/
lemma coe_powerSeries_mem_finiteCoeffLaurentUnion (a : ↥A) :
    ((a : PowerSeries k) : LaurentSeries k) ∈
      finiteCoeffLaurentUnion (k := k) (p := p) := by
  -- The generated coefficient field of `a` is finite by membership in `A`; the Laurent coercion
  -- has no new coefficients beyond those of the original power series.
  let L := coefficientAdjoinOverPthPowers k p (a : PowerSeries k)
  letI : FiniteDimensional (k^[p]) L := a.2
  apply finiteCoeffLaurentUnion_mem_of_mem_subfield (k := k) (p := p) L
  rw [finiteCoeffLaurentSubfield_mem_iff_coeff_mem]
  intro n
  rw [PowerSeries.coeff_coe]
  by_cases hn : n < 0
  · simp [hn]
  · simpa [hn, L] using
      coeff_mem_coefficientAdjoinOverPthPowers k p (a : PowerSeries k) n.natAbs

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: every Laurent monomial with coefficient `1` lies in the
union coefficient subfield. -/
lemma single_one_mem_finiteCoeffLaurentUnion (n : ℤ) :
    (HahnSeries.single n (1 : k) : LaurentSeries k) ∈
      finiteCoeffLaurentUnion (k := k) (p := p) := by
  -- The monomial coefficients are only `0` and `1`, so they already lie in the bottom field.
  apply finiteCoeffLaurentUnion_mem_of_mem_subfield (k := k) (p := p) (⊥ : IntermediateField (k^[p]) k)
  rw [finiteCoeffLaurentSubfield_mem_iff_coeff_mem]
  intro m
  rw [HahnSeries.coeff_single]
  by_cases hm : m = n
  · simp [hm]
  · simp [hm]

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: inverses of Laurent images of elements of `A` remain in
the union coefficient subfield. -/
lemma inv_coe_powerSeries_mem_finiteCoeffLaurentUnion (a : ↥A) :
    (((a : PowerSeries k) : LaurentSeries k)⁻¹) ∈
      finiteCoeffLaurentUnion (k := k) (p := p) := by
  -- Once the element is in the union subfield, inverse-closure of subfields supplies the
  -- denominator piece needed by the localization route.
  exact (finiteCoeffLaurentUnion (k := k) (p := p)).inv_mem
    (coe_powerSeries_mem_finiteCoeffLaurentUnion (k := k) (p := p) a)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the inclusion `A → k((X))` lands in the union
coefficient subfield. -/
noncomputable def finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion :
    ↥A →+* finiteCoeffLaurentUnion (k := k) (p := p) :=
  (((algebraMap (PowerSeries k) (LaurentSeries k)).comp
      (algebraMap ↥A (PowerSeries k))).codRestrict
    (finiteCoeffLaurentUnion (k := k) (p := p))
    (fun a ↦ coe_powerSeries_mem_finiteCoeffLaurentUnion (k := k) (p := p) a))

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the direct inclusion of `A` into the union Laurent
subfield is injective. -/
lemma finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion_injective :
    Function.Injective
      (finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion (k := k) (p := p)) := by
  -- Forget to Laurent series, where the power-series embedding is injective.
  intro a b h
  apply Subtype.ext
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
  simpa [finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion] using
    congrArg
      (fun z : finiteCoeffLaurentUnion (k := k) (p := p) ↦ (z : LaurentSeries k)) h

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the localized direct map
`Frac(A) → finiteCoeffLaurentUnion`. -/
noncomputable def fractionRingToFiniteCoeffLaurentUnion :
    FractionRing ↥A →+* finiteCoeffLaurentUnion (k := k) (p := p) :=
  IsFractionRing.lift
    (finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion_injective (k := k) (p := p))

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the localized direct map is injective. -/
lemma fractionRingToFiniteCoeffLaurentUnion_injective :
    Function.Injective
      (fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)) := by
  -- A ring hom out of a field into a nontrivial semiring is injective.
  exact RingHom.injective (fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p))

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the localized direct map agrees with the source map on
elements of `A`. -/
lemma fractionRingToFiniteCoeffLaurentUnion_algebraMap (a : ↥A) :
    fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)
        (algebraMap ↥A (FractionRing ↥A) a) =
      finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion (k := k) (p := p) a := by
  -- This is the defining computation rule for the fraction-ring lift.
  simpa [fractionRingToFiniteCoeffLaurentUnion] using
    IsFractionRing.lift_algebraMap
      (finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion_injective (k := k) (p := p)) a

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the localized coefficient-ring map reaches every
finite-coefficient Laurent series. -/
lemma fractionRingToFiniteCoeffLaurentUnion_surjective :
    Function.Surjective
      (fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)) := by
  intro z
  obtain ⟨L, hLfinite, hzL⟩ :=
    (finiteCoeffLaurentUnion_mem_iff_exists_subfield (k := k) (p := p)
      (z : LaurentSeries k)).1 z.2
  letI : FiniteDimensional (k^[p]) L := hLfinite
  let fA : ↥A :=
    ⟨(z : LaurentSeries k).powerSeriesPart,
      powerSeriesPart_mem_finitePthPowerCoefficientSubring_of_finiteCoeffLaurentSubfield
        (k := k) (p := p) L hzL⟩
  by_cases hnonneg : 0 ≤ (z : LaurentSeries k).order
  · let n : ℕ := Int.natAbs (z : LaurentSeries k).order
    let numA : ↥A :=
      ⟨(PowerSeries.X : PowerSeries k) ^ n * (z : LaurentSeries k).powerSeriesPart,
        mul_mem (X_pow_mem_finitePthPowerCoefficientSubring (k := k) (p := p) n) fA.2⟩
    refine ⟨algebraMap ↥A (FractionRing ↥A) numA, ?_⟩
    -- For nonnegative order, the Laurent series is the Laurent image of `X^order * powerSeriesPart`.
    apply Subtype.ext
    have hmap := fractionRingToFiniteCoeffLaurentUnion_algebraMap (k := k) (p := p) numA
    calc
      ((fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)
          (algebraMap ↥A (FractionRing ↥A) numA) :
          finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k) =
          ((numA : PowerSeries k) : LaurentSeries k) := by
            simpa [finitePthPowerCoefficientSubringToFiniteCoeffLaurentUnion] using
              congrArg
                (fun w : finiteCoeffLaurentUnion (k := k) (p := p) ↦
                  (w : LaurentSeries k)) hmap
      _ = (HahnSeries.single (z : LaurentSeries k).order (1 : k) : LaurentSeries k) *
          (z : LaurentSeries k).powerSeriesPart := by
            have hn : ((n : ℕ) : ℤ) = (z : LaurentSeries k).order := by
              exact Int.natAbs_of_nonneg hnonneg
            simpa [numA, n, hn, map_mul, HahnSeries.ofPowerSeries_X_pow]
      _ = z := LaurentSeries.single_order_mul_powerSeriesPart (z : LaurentSeries k)
  · let n : ℕ := Int.natAbs (z : LaurentSeries k).order
    let denA : ↥A :=
      ⟨(PowerSeries.X : PowerSeries k) ^ n,
        X_pow_mem_finitePthPowerCoefficientSubring (k := k) (p := p) n⟩
    refine
      ⟨algebraMap ↥A (FractionRing ↥A) fA /
          algebraMap ↥A (FractionRing ↥A) denA, ?_⟩
    -- For negative order, divide the power-series part by the corresponding power of `X`.
    apply Subtype.ext
    have hfmap := fractionRingToFiniteCoeffLaurentUnion_algebraMap (k := k) (p := p) fA
    have hdmap := fractionRingToFiniteCoeffLaurentUnion_algebraMap (k := k) (p := p) denA
    have hnonpos : (z : LaurentSeries k).order ≤ 0 := le_of_not_ge hnonneg
    have hn : ((n : ℕ) : ℤ) = -((z : LaurentSeries k).order) := by
      simpa [n] using Int.ofNat_natAbs_of_nonpos hnonpos
    have hden_ne :
        (HahnSeries.single (-((z : LaurentSeries k).order)) (1 : k) :
          LaurentSeries k) ≠ 0 := by
      exact HahnSeries.single_ne_zero one_ne_zero
    calc
      ((fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)
          (algebraMap ↥A (FractionRing ↥A) fA /
            algebraMap ↥A (FractionRing ↥A) denA) :
          finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k) =
          ((fA : PowerSeries k) : LaurentSeries k) /
            ((denA : PowerSeries k) : LaurentSeries k) := by
            simp only [map_div₀]
            rw [hfmap, hdmap]
            rfl
      _ = ((z : LaurentSeries k).powerSeriesPart : LaurentSeries k) /
          (HahnSeries.single (-((z : LaurentSeries k).order)) (1 : k) :
            LaurentSeries k) := by
            simp [fA, denA, n, hn, HahnSeries.ofPowerSeries_X_pow]
      _ = z := by
            rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
            rw [div_eq_iff hden_ne]
            rw [mul_comm]
