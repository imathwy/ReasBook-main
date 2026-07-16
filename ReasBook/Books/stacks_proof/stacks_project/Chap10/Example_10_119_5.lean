import stacks_proof.stacks_project.Chap10.Example_10_119_5.Index

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

section SourceFacing

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finite-dimensionality over `Frac(A)` transports to
finite-dimensionality of Laurent series over the finite-coefficient union field. -/
private lemma finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_of_fractionRing_finiteDimensional
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := by
  -- View the usual Laurent equivalence as semilinear over the direct localized coefficient map.
  let σ : FractionRing ↥A →+* finiteCoeffLaurentUnion (k := k) (p := p) :=
    fractionRingToFiniteCoeffLaurentUnion (k := k) (p := p)
  letI : Algebra (FractionRing ↥A) (finiteCoeffLaurentUnion (k := k) (p := p)) :=
    σ.toAlgebra
  letI : RingHomSurjective σ :=
    ⟨fractionRingToFiniteCoeffLaurentUnion_surjective (k := k) (p := p)⟩
  let e : FractionRing (PowerSeries k) ≃ₐ[PowerSeries k] LaurentSeries k :=
    FractionRing.algEquiv (PowerSeries k) (LaurentSeries k)
  let L : FractionRing (PowerSeries k) →ₛₗ[σ] LaurentSeries k :=
    { toFun := e
      map_add' := by
        intro x y
        exact map_add e x y
      map_smul' := by
        intro c x
        -- The compatibility lemma turns scalar multiplication by `c` into scalar multiplication
        -- by its finite-coefficient-union image.
        have hscalar :=
          fractionRingToFiniteCoeffLaurentUnion_laurent_compatible (k := k) (p := p) c
        calc
          e (c • x) =
              e (algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k)) c * x) := by
                rw [Algebra.smul_def]
          _ = e (algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k)) c) * e x := by
                rw [map_mul]
          _ = ((σ c : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k) * e x := by
                rw [← hscalar]
          _ = σ c • e x := by
                simpa [smul_eq_mul] using
                  (Subfield.smul_def (σ c) (e x)).symm }
  -- Finite generation descends along the surjective semilinear Laurent equivalence.
  letI : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := hfd
  exact Module.Finite.of_surjective L e.surjective

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finite coefficient-field extensions do not make
`k / k^p` finite-dimensional when it was infinite-dimensional over `k^p`. -/
private lemma not_finiteDimensional_over_finitePthPowerIntermediate
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional L k := by
  -- A finite `L`-basis of `k`, together with finite dimensionality of `L / k^p`, would give a
  -- finite `k^p`-basis of `k`, contradicting the hypothesis.
  intro hLk
  letI : FiniteDimensional L k := hLk
  letI : IsScalarTower (k^[p]) L k :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact hnfd (FiniteDimensional.trans (k^[p]) L k)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: constants that are linearly independent over a fixed
intermediate coefficient field remain independent over the corresponding Laurent-series field. -/
private lemma linearIndependent_laurentSeries_const_of_linearIndependent
    (L : IntermediateField (k^[p]) k) {v : ℕ → k}
    (hv : LinearIndependent L v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L)
      (fun i : ℕ ↦ (HahnSeries.C (v i) : LaurentSeries k)) := by
  classical
  -- Coefficientwise extraction turns a Laurent relation into an `L`-linear relation in `k`.
  rw [linearIndependent_iff']
  intro s g hsum i hi
  apply Subtype.ext
  ext n
  let S : Subfield (LaurentSeries k) :=
    finiteCoeffLaurentSubfield (k := k) (p := p) L
  let c : ℕ → L := fun j ↦
    ⟨((g j : S) : LaurentSeries k).coeff n,
      (finiteCoeffLaurentSubfield_mem_iff_coeff_mem (k := k) (p := p) L
        (((g j : S) : LaurentSeries k))).1 (g j).2 n⟩
  have hcoeff_relation : ∑ j ∈ s, (c j : k) * v j = 0 := by
    -- Taking the `n`th Laurent coefficient of the relation leaves only scalar coefficients
    -- multiplying the constant series entries.
    have hcoeff := congrArg (fun z : LaurentSeries k ↦ z.coeff n) hsum
    simpa [S, c, Subfield.smul_def, HahnSeries.C_apply] using hcoeff
  have hc_zero : c i = 0 :=
    (linearIndependent_iff'.1 hv s c hcoeff_relation) i hi
  -- Since this holds for every coefficient, the original Laurent scalar is zero.
  simpa [S, c] using congrArg (fun x : L ↦ (x : k)) hc_zero

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: for each fixed finite coefficient field, there is a
countable Laurent-series family linearly independent over its Laurent-series subfield. -/
private lemma exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  -- First choose constants in `k` independent over `L`, then view them as constant Laurent
  -- series using the coefficient-extraction helper.
  obtain ⟨v, hv⟩ :=
    exists_nat_linearIndependent_of_not_finiteDimensional
      (F := L) (E := k)
      (not_finiteDimensional_over_finitePthPowerIntermediate (k := k) (p := p) L hnfd)
  exact ⟨fun i ↦ (HahnSeries.C (v i) : LaurentSeries k),
    linearIndependent_laurentSeries_const_of_linearIndependent (k := k) (p := p) L hv⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the initial finite segment of a countable independent
family remains linearly independent. -/
private lemma linearIndependent_finInitialSegment_of_nat
    {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    {v : ℕ → E} (hv : LinearIndependent F v) (r : ℕ) :
    LinearIndependent F (fun i : Fin r ↦ v i.1) := by
  -- Restrict the countable independent family along the injective inclusion `Fin r → ℕ`.
  exact hv.comp (fun i : Fin r ↦ i.1) (by
    intro i j hij
    exact Fin.ext hij)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: over each fixed finite coefficient Laurent subfield,
there are independent Laurent families of every finite size. -/
private lemma exists_fin_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  -- First use the fixed-subfield countable family, then keep only the requested finite segment.
  obtain ⟨v, hv⟩ :=
    exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentSubfield
      (k := k) (p := p) L hnfd
  exact ⟨fun i ↦ v i.1, linearIndependent_finInitialSegment_of_nat hv r⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a finite Laurent family independent over every fixed
finite coefficient Laurent subfield is independent over their directed union. -/
private lemma linearIndependent_fin_finiteCoeffLaurentUnion_of_forall_finiteCoeffLaurentSubfield
    {r : ℕ} (v : Fin r → LaurentSeries k)
    (hv : ∀ (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L],
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v) :
    LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  classical
  -- Normalize any finite relation over the union to coefficients in one finite Laurent subfield.
  rw [linearIndependent_iff']
  intro s g hsum i hi
  obtain ⟨L, hLfinite, hLcommon⟩ :=
    finiteCoeffLaurentUnion_finset_common (k := k) (p := p) s
      (fun j ↦ ((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k))
      (by
        intro j _hj
        exact (g j).2)
  letI : FiniteDimensional (k^[p]) L := hLfinite
  let S : Subfield (LaurentSeries k) := finiteCoeffLaurentSubfield (k := k) (p := p) L
  let gL : Fin r → S := fun j ↦
    if hj : j ∈ s then
      ⟨((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k),
        hLcommon j hj⟩
    else 0
  have hterm (j : Fin r) (hj : j ∈ s) : gL j • v j = g j • v j := by
    -- Scalar multiplication is multiplication in `LaurentSeries k` for both subfields.
    dsimp [gL]
    rw [dif_pos hj]
    simp [Subfield.smul_def]
  have hsumL : ∑ j ∈ s, gL j • v j = 0 := by
    -- Rewrite the original relation with all coefficients in the common finite subfield.
    calc
      ∑ j ∈ s, gL j • v j = ∑ j ∈ s, g j • v j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j hj
      _ = 0 := hsum
  have hgL_zero : gL i = 0 :=
    (linearIndependent_iff'.1 (hv L) s gL hsumL) i hi
  -- Coercing the common-subfield zero coefficient proves the original union coefficient is zero.
  apply Subtype.ext
  have hval :=
    congrArg (fun x : S ↦ (x : LaurentSeries k)) hgL_zero
  simpa [gL, hi] using hval

/-- Helper for Chap10 Example 10 119 5: finite generic rank of the power-series fraction field
forces the coefficient field extension `k / k^p` to be finite-dimensional. -/
private lemma finitePthPowerCoefficientField_finiteDimensional_of_fractionRing_finiteDimensional
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    FiniteDimensional (k^[p]) k := by
  -- Route correction: the adic-completeness route was false, so use the contrapositive through
  -- Laurent series and the theorem-local finite-span obstruction.
  by_contra hnfd
  have hLaurentFinite :
      FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) :=
    finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_of_fractionRing_finiteDimensional
      (k := k) (p := p) hfd
  exact
    (not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_spanEscape
      (k := k) (p := p) hnfd) hLaurentFinite

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: if the coefficient field extension is finite, then
`A = k[[X]]` and the ambient power-series module is finite over `A`. -/
private lemma moduleFinite_powerSeries_of_finitePthPowerCoefficientField
    (hfin : FiniteDimensional (k^[p]) k) :
    Module.Finite ↥A (PowerSeries k) := by
  -- In the finite coefficient-field branch, every power series has coefficients in one finite
  -- intermediate field, so the inclusion `A → k[[X]]` is onto.
  have hsurj : Function.Surjective (Algebra.linearMap ↥A (PowerSeries k)) := by
    intro f
    refine ⟨⟨f, finitePthPowerCoefficientSubring_mem_of_finiteDimensional k p hfin f⟩, ?_⟩
    rfl
  -- A surjective linear map from the rank-one finite module `A` exhibits `k[[X]]` as finite.
  exact Module.Finite.of_surjective (Algebra.linearMap ↥A (PowerSeries k)) hsurj

/-- Helper for Chap10 Example 10 119 5: finite fraction-field degree forces `k[[X]]` to be
finite over the coefficient DVR `A`. -/
private lemma moduleFinite_powerSeries_of_fractionRing_finiteDimensional_from_generic_rank
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    Module.Finite ↥A (PowerSeries k) := by
  -- Route correction: the proposed adic-completeness pivot is false because the completion of
  -- `A` is `k[[X]]`, not `A` itself.  The remaining clean route is to show finite generic rank
  -- already forces `k / k^p` finite; then `A` equals the whole power-series ring.
  exact moduleFinite_powerSeries_of_finitePthPowerCoefficientField k p
    (finitePthPowerCoefficientField_finiteDimensional_of_fractionRing_finiteDimensional
      (k := k) (p := p) hfd)

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree makes the fraction
field extension `Frac(A) ⊆ Frac(k[[X]])` infinite-dimensional without using Laurent independent
families. -/
private lemma finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional_from_coefficients
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := by
  -- A finite generic-rank hypothesis would make `k[[X]]` finite over `A`, contradicting the
  -- coefficient-field non-finiteness theorem.
  intro hfd
  exact not_moduleFinite_powerSeries_over_finitePthPowerCoefficientSubring k p hnfd
    (moduleFinite_powerSeries_of_fractionRing_finiteDimensional_from_generic_rank
      (k := k) (p := p) hfd)

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree makes Laurent
series infinite-dimensional over the directed union of finite coefficient Laurent subfields. -/
private lemma not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_coefficients
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := by
  -- Route correction: avoid the circular independent-family route.  A hypothetical finite
  -- Laurent extension transports back to finite generic rank over `Frac(A)`, contradicting the
  -- coefficient-field obstruction isolated above.
  intro hfd
  exact finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional_from_coefficients
    (k := k) (p := p) hnfd
    (fractionRing_finiteDimensional_of_laurentSeries_finiteDimensional
      (k := k) (p := p) hfd)

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree supplies finite
families of any prescribed size that are linearly independent over the finite-coefficient Laurent
union. -/
private lemma exists_fin_linearIndependent_over_finiteCoeffLaurentUnion
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- First obtain a countable independent family from the non-finite-dimensional Laurent
  -- obstruction, then keep the requested finite initial segment.
  obtain ⟨v, hv⟩ :=
    exists_nat_linearIndependent_of_not_finiteDimensional
      (F := finiteCoeffLaurentUnion (k := k) (p := p)) (E := LaurentSeries k)
      (not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_coefficients
        (k := k) (p := p) hnfd)
  exact ⟨fun i : Fin r ↦ v i.1, linearIndependent_finInitialSegment_of_nat hv r⟩

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree makes Laurent series
infinite-dimensional over the finite-coefficient Laurent union. -/
private lemma not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := by
  -- The public local obstruction is now the single missing coefficient-grid input.
  exact not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_coefficients
    (k := k) (p := p) hnfd

/-- Helper for Chap10 Example 10 119 5: the Laurent infinite-dimensionality obstruction gives
a countable independent family over the finite-coefficient union. -/
private lemma exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentUnion_core
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- Choose a countable subfamily from a vector-space basis of the infinite-dimensional Laurent
  -- extension over the finite-coefficient union.
  exact exists_nat_linearIndependent_of_not_finiteDimensional
    (F := finiteCoeffLaurentUnion (k := k) (p := p)) (E := LaurentSeries k)
    (not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion (k := k) (p := p) hnfd)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: linear independence over the finite-coefficient union
restricts to any fixed finite coefficient Laurent subfield. -/
private lemma linearIndependent_finiteCoeffLaurentSubfield_of_union
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    {v : ℕ → LaurentSeries k}
    (hv : LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  classical
  -- Promote a finite relation over the smaller coefficient field to one over the union field.
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  let S : Subfield (LaurentSeries k) :=
    finiteCoeffLaurentSubfield (k := k) (p := p) L
  let U : Subfield (LaurentSeries k) := finiteCoeffLaurentUnion (k := k) (p := p)
  have hSU : S ≤ U :=
    finiteCoeffLaurentSubfield_le_union (k := k) (p := p) L
  let gU : ℕ → U := fun j ↦
    if hj : j ∈ s then ⟨((g j : S) : LaurentSeries k), hSU (g j).2⟩ else 0
  have hterm (j : ℕ) (hj : j ∈ s) : gU j • v j = g j • v j := by
    -- Scalar multiplication by the promoted coefficient is the same Laurent-series product.
    simp [gU, hj, U, Subfield.smul_def]
  have hsumU : ∑ j ∈ s, gU j • v j = 0 := by
    -- Rewrite the original relation after promotion to the union coefficient field.
    calc
      ∑ j ∈ s, gU j • v j = ∑ j ∈ s, g j • v j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j hj
      _ = 0 := hsum
  have hgU_zero : gU i = 0 := hv s gU hsumU i hi
  -- Coercing the promoted zero coefficient back to Laurent series proves the original
  -- coefficient vanishes in the fixed subfield.
  apply Subtype.ext
  have hval := congrArg (fun x : U ↦ (x : LaurentSeries k)) hgU_zero
  simpa [gU, hi, S, U] using hval

/-- Helper for Chap10 Example 10 119 5: the remaining fixed-stage Laurent-series construction.
It produces one countable family that is linearly independent over every finite coefficient
Laurent subfield. -/
private lemma exists_laurentSeries_family_linearIndependent_over_all_finiteCoeffLaurentSubfields
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      ∀ (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L],
        LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  -- Route correction: instead of choosing constants separately for each finite coefficient field,
  -- choose one family independent over the directed union and then restrict scalars.
  obtain ⟨v, hv⟩ :=
    exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentUnion_core
      (k := k) (p := p) hnfd
  refine ⟨v, ?_⟩
  intro L hLfinite
  letI : FiniteDimensional (k^[p]) L := hLfinite
  exact linearIndependent_finiteCoeffLaurentSubfield_of_union (k := k) (p := p) L hv

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: linear independence over every finite coefficient
Laurent subfield implies linear independence over their directed union. -/
private lemma linearIndependent_finiteCoeffLaurentUnion_of_forall_finiteCoeffLaurentSubfield
    (v : ℕ → LaurentSeries k)
    (hv : ∀ (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L],
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v) :
    LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  classical
  -- A finite relation over the union has all scalar coefficients in one finite Laurent subfield.
  rw [linearIndependent_iff']
  intro s g hsum i hi
  obtain ⟨L, hLfinite, hLcommon⟩ :=
    finiteCoeffLaurentUnion_finset_common (k := k) (p := p) s
      (fun j ↦ ((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k))
      (by
        intro j _hj
        exact (g j).2)
  letI : FiniteDimensional (k^[p]) L := hLfinite
  let S : Subfield (LaurentSeries k) := finiteCoeffLaurentSubfield (k := k) (p := p) L
  let gL : ℕ → S := fun j ↦
    if hj : j ∈ s then
      ⟨((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k),
        hLcommon j hj⟩
    else 0
  have hterm (j : ℕ) (hj : j ∈ s) : gL j • v j = g j • v j := by
    -- On the common finite subfield, scalar multiplication is the same Laurent-series
    -- multiplication as scalar multiplication by the original union coefficient.
    dsimp [gL]
    rw [dif_pos hj]
    simp [Subfield.smul_def]
  have hsumL : ∑ j ∈ s, gL j • v j = 0 := by
    -- Rewrite the relation with coefficients in the common finite subfield.
    calc
      ∑ j ∈ s, gL j • v j = ∑ j ∈ s, g j • v j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j hj
      _ = 0 := hsum
  have hgL_zero : gL i = 0 :=
    (linearIndependent_iff'.1 (hv L) s gL hsumL) i hi
  -- Coercing the zero coefficient back to the union subfield proves the original coefficient
  -- vanishes.
  apply Subtype.ext
  have hval :=
    congrArg (fun x : S ↦ (x : LaurentSeries k)) hgL_zero
  simpa [gL, hi] using hval

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree supplies a countable
Laurent-series family linearly independent over the finite-coefficient union field. -/
private lemma exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentUnion
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- Route correction: reduce the union-level statement to fixed finite coefficient fields first,
  -- then use the directed-union adapter so scalar normalization is handled only once.
  obtain ⟨v, hv⟩ :=
    exists_laurentSeries_family_linearIndependent_over_all_finiteCoeffLaurentSubfields
      (k := k) (p := p) hnfd
  exact ⟨v,
    linearIndependent_finiteCoeffLaurentUnion_of_forall_finiteCoeffLaurentSubfield
      (k := k) (p := p) v hv⟩

/-- Helper for Chap10 Example 10 119 5: the intended Laurent-series obstruction shows that
infinite degree of `k / k^p` rules out finite fraction-field degree. -/
private lemma finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional_direct
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := by
  -- A finite fraction-field degree would make Laurent series finite-dimensional over the
  -- finite-coefficient union field.
  intro hfd
  have hLaurentFinite :
      FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) :=
    finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_of_fractionRing_finiteDimensional
      (k := k) (p := p) hfd
  -- The independent Laurent family from the infinite coefficient-field hypothesis contradicts
  -- finite dimensionality over that same union field.
  exact
    (not_finiteDimensional_of_nat_linearIndependent
      (F := finiteCoeffLaurentUnion (k := k) (p := p)) (E := LaurentSeries k)
      (exists_laurentSeries_linearIndependent_over_finiteCoeffLaurentUnion
        (k := k) (p := p) hnfd)) hLaurentFinite

/-- Helper for Chap10 Example 10 119 5: finite fraction-field degree gives a nonzero conductor
for the fraction-field image of `k[[X]]`. -/
lemma powerSeriesFractionSubalgebra_exists_nonzero_conductor_of_fractionRing_finiteDimensional
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    ∃ c : ↥A, c ≠ 0 ∧
      ∀ z : FractionRing (PowerSeries k), z ∈ powerSeriesFractionSubalgebra k p →
        ∃ a : ↥A,
          algebraMap ↥A (FractionRing (PowerSeries k)) a =
            algebraMap ↥A (FractionRing (PowerSeries k)) c * z := by
  -- Route correction: replace the missing Krull-Akizuki conductor theorem by a dichotomy on the
  -- coefficient extension.  In the finite branch `A = k[[X]]`; in the infinite branch the direct
  -- Laurent obstruction contradicts `hfd`.
  classical
  by_cases hfin : FiniteDimensional (k^[p]) k
  · refine ⟨1, one_ne_zero, ?_⟩
    intro z hz
    rw [powerSeriesFractionSubalgebra] at hz
    rcases hz with ⟨f, rfl⟩
    -- With `c = 1`, the conductor witness is just the coefficient-ring element represented by
    -- the chosen power series.
    let a : ↥A := ⟨f, finitePthPowerCoefficientSubring_mem_of_finiteDimensional k p hfin f⟩
    refine ⟨a, ?_⟩
    simpa [a, powerSeriesFractionAlgHom] using
      finitePthPowerCoefficientSubring_algebraMap_fractionRing_apply k p a
  · exact False.elim
      ((finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional_direct k p hfin) hfd)

/-- Helper for Chap10 Example 10 119 5: finite fraction-field degree gives one nonzero
coefficient-ring denominator which sends all ambient power series back into `A`. -/
lemma exists_nonzero_conductor_powerSeries_of_fractionRing_finiteDimensional
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    ∃ c : ↥A, c ≠ 0 ∧
      ∀ f : PowerSeries k, ∃ a : ↥A,
        algebraMap ↥A (PowerSeries k) a =
          algebraMap ↥A (PowerSeries k) c * f := by
  -- Route correction: the fraction-field image conductor is now supplied by the finite/infinite
  -- coefficient-field split, and this proof pulls it back to an identity in `k[[X]]`.
  letI : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := hfd
  obtain ⟨c, hc_ne, hcond⟩ :=
    powerSeriesFractionSubalgebra_exists_nonzero_conductor_of_fractionRing_finiteDimensional
      k p hfd
  refine ⟨c, hc_ne, ?_⟩
  intro f
  -- Apply the fraction-field conductor to the image of the chosen power series.
  have hf_mem :
      algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) f ∈
        powerSeriesFractionSubalgebra k p := by
    change powerSeriesFractionAlgHom k p f ∈ powerSeriesFractionSubalgebra k p
    rw [powerSeriesFractionSubalgebra]
    exact AlgHom.mem_range_self (powerSeriesFractionAlgHom k p) f
  obtain ⟨a, ha_frac⟩ :=
    hcond (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) f) hf_mem
  refine ⟨a, ?_⟩
  -- Injectivity of the power-series fraction map pulls the conductor identity back to `k[[X]]`.
  apply IsFractionRing.injective (PowerSeries k) (FractionRing (PowerSeries k))
  calc
    algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
        (algebraMap ↥A (PowerSeries k) a) =
      algebraMap ↥A (FractionRing (PowerSeries k)) a := by
        rfl
    _ =
      algebraMap ↥A (FractionRing (PowerSeries k)) c *
        algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) f := ha_frac
    _ =
      algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
        (algebraMap ↥A (PowerSeries k) c * f) := by
        rw [map_mul]
        rfl

/-- Helper for Chap10 Example 10 119 5: finite fraction-field degree forces the ambient
integral power-series ring to be finite over the coefficient DVR. -/
lemma moduleFinite_powerSeries_of_fractionRing_finiteDimensional
    (hfd : FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k))) :
    Module.Finite ↥A (PowerSeries k) := by
  -- Route correction: the finite-rank separated-submodule route was over-general.  The stable
  -- proof now passes through the source-facing conductor statement.
  exact moduleFinite_powerSeries_of_nonzero_conductor k p
    (exists_nonzero_conductor_powerSeries_of_fractionRing_finiteDimensional k p hfd)

/-- Helper for Chap10 Example 10 119 5: the fraction-field extension has infinite degree when
`k / k^p` has infinite degree. -/
lemma finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := by
  -- The public wrapper now delegates to the direct Laurent obstruction instead of routing back
  -- through the conductor/module-finiteness bridge.
  exact finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional_direct k p hnfd

/-- Helper for Chap10 Example 10 119 5: infinite degree of `k / k^p` gives a countable
`Frac(A)`-linearly independent family in `Frac(k[[X]])`. -/
private theorem finitePthPowerCoefficientSubring_fractionRing_exists_linearIndependent
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → FractionRing (PowerSeries k),
      LinearIndependent (FractionRing ↥A) v := by
  -- Route correction: avoid the previous Laurent scalar-normal-form route. It is enough to
  -- prove the fraction-field extension is not finite-dimensional and then choose a countable
  -- independent family abstractly.
  exact exists_nat_linearIndependent_of_not_finiteDimensional
    (finitePthPowerCoefficientSubring_fractionRing_not_finiteDimensional k p hnfd)

-- Proof sketch: every element of `Frac(k[[x]])` becomes a `p^n`th power over `Frac(A)` after
-- clearing coefficients, because `A` contains exactly the power series whose coefficient field is
-- finite over `k^p`; choosing coefficients with unbounded `k^p`-degree forces the induced
-- fraction-field extension to be non-finite-dimensional.
/-- If `k` has infinite degree over `k^p`, then the inclusion
`Frac(A) ⊂ Frac(k[[x]])` is an infinite purely inseparable extension. -/
theorem finitePthPowerCoefficientSubring_fractionRing_infinite_purelyInseparable
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    IsPurelyInseparable (FractionRing ↥A) (FractionRing (PowerSeries k)) ∧
      ¬ FiniteDimensional (FractionRing ↥A) (FractionRing (PowerSeries k)) := by
  constructor
  · -- The purely inseparable part follows from the pointwise `p`th-power containment in `A`.
    exact finitePthPowerCoefficientSubring_fractionRing_isPurelyInseparable k p
  · -- The remaining source-facing construction is now isolated as a linearly independent family.
    exact not_finiteDimensional_of_nat_linearIndependent
      (finitePthPowerCoefficientSubring_fractionRing_exists_linearIndependent k p hnfd)

end SourceFacing


section AdjoinedRing

variable (f : PowerSeries k)

local notation "R" => finitePthPowerCoefficientAdjoinSubring k p f

-- Proof sketch: after `x`-adic completion, the adjoined element satisfies a purely inseparable
-- polynomial over the completion of `A`, so the completed algebra acquires nilpotents and cannot
-- be reduced.
/-- Example 10.119.5: if `A ⊆ k[[x]]` is the coefficient subring above and `f ∉ A`, then the ring
`R = A[f]` has nonreduced completion at its maximal ideal. -/
@[stacks 00PB]
theorem finitePthPowerCoefficientAdjoinSubring_completion_not_reduced
    (hf : f ∉ A) :
    ¬ IsReduced (AdicCompletion (maximalIdeal ↥R) ↥R) := by
  -- The source proof produces an explicit nonzero `p`-nilpotent in the completed ring.
  obtain ⟨z, hz, hzpow⟩ := completion_exists_nonzero_p_nilpotent_of_not_mem
    (k := k) (p := p) (f := f) hf
  -- Any reduced ring kills nilpotents, so this witness excludes reducedness.
  exact not_isReduced_of_exists_ne_zero_pow_eq_zero hz hzpow

end AdjoinedRing
