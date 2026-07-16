import stacks_proof.stacks_project.Chap10.Example_10_119_5

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: finite coefficient-field extensions preserve the
infinite-dimensionality of `k` after changing scalars from `k^p` to the finite intermediate
field. -/
lemma not_finiteDimensional_over_finitePthPowerIntermediate_of_base
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional L k := by
  -- A finite `L`-basis of `k`, together with finite dimensionality of `L / k^p`, would give a
  -- finite `k^p`-basis of `k`.
  intro hLk
  letI : FiniteDimensional L k := hLk
  letI : IsScalarTower (k^[p]) L k :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact hnfd (FiniteDimensional.trans (k^[p]) L k)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: constants that are linearly independent over a fixed
intermediate coefficient field remain independent over the corresponding Laurent-series
subfield. -/
lemma linearIndependent_constLaurentSeries_of_linearIndependent
    (L : IntermediateField (k^[p]) k) {v : ℕ → k}
    (hv : LinearIndependent L v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L)
      (fun i : ℕ ↦ (HahnSeries.C (v i) : LaurentSeries k)) := by
  classical
  -- Extracting each Laurent coefficient turns a Laurent relation into an `L`-linear relation
  -- among the original constants.
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
    -- Only the constant Laurent coefficient of each vector contributes after coefficient
    -- extraction.
    have hcoeff := congrArg (fun z : LaurentSeries k ↦ z.coeff n) hsum
    simpa [S, c, Subfield.smul_def, HahnSeries.C_apply] using hcoeff
  have hc_zero : c i = 0 :=
    (linearIndependent_iff'.1 hv s c hcoeff_relation) i hi
  -- Vanishing of every Laurent coefficient forces the original scalar coefficient to vanish.
  simpa [S, c] using congrArg (fun x : L ↦ (x : k)) hc_zero

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: for each fixed finite coefficient field, there is a
countable Laurent-series family linearly independent over its Laurent-series subfield. -/
lemma exists_constLaurentSeries_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  -- Choose constants in `k` independent over `L`, then regard them as constant Laurent series.
  obtain ⟨v, hv⟩ :=
    exists_nat_linearIndependent_of_not_finiteDimensional
      (F := L) (E := k)
      (not_finiteDimensional_over_finitePthPowerIntermediate_of_base (k := k) (p := p) L hnfd)
  exact ⟨fun i ↦ (HahnSeries.C (v i) : LaurentSeries k),
    linearIndependent_constLaurentSeries_of_linearIndependent (k := k) (p := p) L hv⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: restricting a countable independent family to an
initial finite segment preserves linear independence. -/
lemma linearIndependent_natRestrict_fin
    {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    {v : ℕ → E} (hv : LinearIndependent F v) (r : ℕ) :
    LinearIndependent F (fun i : Fin r ↦ v i.1) := by
  -- The inclusion `Fin r → ℕ` is injective, so linear independence pulls back.
  exact hv.comp (fun i : Fin r ↦ i.1) (by
    intro i j hij
    exact Fin.ext hij)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a countable independent family over the Laurent
coefficient union supplies independent finite initial segments of every size. -/
lemma exists_fin_linearIndependent_of_nat_finiteCoeffLaurentUnion
    (h :
      ∃ v : ℕ → LaurentSeries k,
        LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v)
    (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- Restrict the countable independent family along `Fin r → ℕ`.
  obtain ⟨v, hv⟩ := h
  exact ⟨fun i : Fin r ↦ v i.1, linearIndependent_natRestrict_fin hv r⟩

/-- Helper for Chap10 Example 10 119 5: arbitrarily large finite independent families rule out
finite-dimensionality of a vector space. -/
lemma not_finiteDimensional_of_forall_fin_linearIndependent
    {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    (h : ∀ r : ℕ, ∃ v : Fin r → E, LinearIndependent F v) :
    ¬ FiniteDimensional F E := by
  -- In a finite-dimensional space, an independent family indexed by one more than the finrank
  -- violates the standard finrank bound.
  intro hfinite
  letI : FiniteDimensional F E := hfinite
  obtain ⟨v, hv⟩ := h (Module.finrank F E + 1)
  have hle :
      Fintype.card (Fin (Module.finrank F E + 1)) ≤ Module.finrank F E :=
    hv.fintype_card_le_finrank
  exact Nat.not_succ_le_self (Module.finrank F E) (by simpa using hle)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: over any finite intermediate coefficient field,
infinite degree over `k^p` supplies coefficient blocks of every finite size. -/
lemma exists_coeffBlockLinearIndependent_over_finitePthPowerIntermediate
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ b : Fin r → k, LinearIndependent L b := by
  -- First choose a countable `L`-independent family in `k`, then keep the requested finite
  -- initial block for the later sparse Laurent construction.
  obtain ⟨b, hb⟩ :=
    exists_nat_linearIndependent_of_not_finiteDimensional
      (F := L) (E := k)
      (not_finiteDimensional_over_finitePthPowerIntermediate_of_base (k := k) (p := p) L hnfd)
  exact ⟨fun i : Fin r ↦ b i.1, linearIndependent_natRestrict_fin hb r⟩

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: over each fixed finite coefficient Laurent subfield,
there are independent Laurent families of every finite size. -/
lemma exists_constLaurentSeries_fin_linearIndependent_over_finiteCoeffLaurentSubfield
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  -- The finite family is the requested initial segment of the countable constant family.
  obtain ⟨v, hv⟩ :=
    exists_constLaurentSeries_linearIndependent_over_finiteCoeffLaurentSubfield
      (k := k) (p := p) L hnfd
  exact ⟨fun i ↦ v i.1, linearIndependent_natRestrict_fin hv r⟩

/-- Helper for Chap10 Example 10 119 5: finite Laurent dimension over the coefficient union
would force forbidden finite generation of `k[[X]]` over the coefficient DVR. -/
lemma not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_genericRank
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := by
  -- Transport a hypothetical finite Laurent extension to finite generic rank, then use the
  -- integral-closure bridge to obtain module-finiteness, contradicting the coefficient theorem.
  intro hfd
  exact not_moduleFinite_powerSeries_over_finitePthPowerCoefficientSubring k p hnfd
    (moduleFinite_powerSeries_of_fractionRing_finiteDimensional
      (k := k) (p := p)
      (fractionRing_finiteDimensional_of_laurentSeries_finiteDimensional
        (k := k) (p := p) hfd))

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree provides a countable
Laurent family over the directed finite-coefficient union. -/
lemma exists_nat_linearIndependent_over_finiteCoeffLaurentUnion_direct
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ∃ v : ℕ → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- The non-finite-dimensional Laurent obstruction supplies a countable independent family by
  -- the standard vector-space consequence.
  exact exists_nat_linearIndependent_of_not_finiteDimensional
    (F := finiteCoeffLaurentUnion (k := k) (p := p)) (E := LaurentSeries k)
    (not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_genericRank
      (k := k) (p := p) hnfd)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: a finite Laurent family that is independent over every
finite coefficient Laurent subfield is independent over the directed union. -/
lemma linearIndependent_fin_finiteCoeffLaurentUnion_of_uniform_finiteCoeffLaurentSubfield
    {r : ℕ} (v : Fin r → LaurentSeries k)
    (hv : ∀ (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L],
      LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v) :
    LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  classical
  -- A finite relation over the union has all scalar coefficients in one finite Laurent
  -- subfield, where the assumed fixed-stage linear independence applies.
  rw [linearIndependent_iff']
  intro s g hsum i hi
  obtain ⟨L, hLfinite, hLcommon⟩ :=
    finiteCoeffLaurentUnion_finset_common (k := k) (p := p) s
      (fun j ↦ ((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k))
      (by
        intro j hj
        exact (g j).2)
  letI : FiniteDimensional (k^[p]) L := hLfinite
  let S : Subfield (LaurentSeries k) := finiteCoeffLaurentSubfield (k := k) (p := p) L
  let gL : Fin r → S := fun j ↦
    if hj : j ∈ s then
      ⟨((g j : finiteCoeffLaurentUnion (k := k) (p := p)) : LaurentSeries k),
        hLcommon j hj⟩
    else 0
  have hterm (j : Fin r) (hj : j ∈ s) : gL j • v j = g j • v j := by
    -- Scalar multiplication is ambient Laurent multiplication for both coefficient subfields.
    dsimp [gL]
    rw [dif_pos hj]
    simp [Subfield.smul_def]
  have hsumL : ∑ j ∈ s, gL j • v j = 0 := by
    -- Rewrite the original relation after moving all coefficients to the common finite stage.
    calc
      ∑ j ∈ s, gL j • v j = ∑ j ∈ s, g j • v j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j hj
      _ = 0 := hsum
  have hgL_zero : gL i = 0 :=
    (linearIndependent_iff'.1 (hv L) s gL hsumL) i hi
  -- Coercion to Laurent series detects equality of the original union coefficient with zero.
  apply Subtype.ext
  have hval := congrArg (fun x : S ↦ (x : LaurentSeries k)) hgL_zero
  simpa [gL, hi] using hval

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: linear independence over the directed union restricts
to every finite coefficient Laurent subfield. -/
lemma linearIndependent_finiteCoeffLaurentSubfield_of_finiteCoeffLaurentUnion
    (L : IntermediateField (k^[p]) k) [FiniteDimensional (k^[p]) L]
    {ι : Type*} {v : ι → LaurentSeries k}
    (hv : LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v) :
    LinearIndependent (finiteCoeffLaurentSubfield (k := k) (p := p) L) v := by
  classical
  -- Promote any finite relation over the smaller Laurent coefficient field to a relation over
  -- the union field, where the given linear independence applies.
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hsum i hi
  let S : Subfield (LaurentSeries k) := finiteCoeffLaurentSubfield (k := k) (p := p) L
  let U : Subfield (LaurentSeries k) := finiteCoeffLaurentUnion (k := k) (p := p)
  have hSU : S ≤ U := finiteCoeffLaurentSubfield_le_union (k := k) (p := p) L
  let gU : ι → U := fun j ↦
    if hj : j ∈ s then ⟨((g j : S) : LaurentSeries k), hSU (g j).2⟩ else 0
  have hterm (j : ι) (hj : j ∈ s) : gU j • v j = g j • v j := by
    -- The promoted coefficient has the same Laurent-series value, so the scalar actions agree.
    simp [gU, hj, U, Subfield.smul_def]
  have hsumU : ∑ j ∈ s, gU j • v j = 0 := by
    -- Rewrite the original smaller-field relation as a union-field relation.
    calc
      ∑ j ∈ s, gU j • v j = ∑ j ∈ s, g j • v j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hterm j hj
      _ = 0 := hsum
  have hgU_zero : gU i = 0 :=
    hv s gU hsumU i hi
  -- Forgetting the promoted coefficient back to Laurent series detects the original scalar.
  apply Subtype.ext
  have hval := congrArg (fun x : U ↦ (x : LaurentSeries k)) hgU_zero
  simpa [gU, hi, S, U] using hval

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree supplies finite
families of any prescribed size that are linearly independent over the finite-coefficient Laurent
union. -/
lemma exists_fin_linearIndependent_over_finiteCoeffLaurentUnion_direct
    (hnfd : ¬ FiniteDimensional (k^[p]) k) (r : ℕ) :
    ∃ v : Fin r → LaurentSeries k,
      LinearIndependent (finiteCoeffLaurentUnion (k := k) (p := p)) v := by
  -- Route correction: the finite-family statement is only a consequence of the countable
  -- sparse-family obstruction; ordinary fixed-subfield constant families are not uniform enough
  -- over the directed union.
  exact exists_fin_linearIndependent_of_nat_finiteCoeffLaurentUnion (k := k) (p := p)
    (exists_nat_linearIndependent_over_finiteCoeffLaurentUnion_direct (k := k) (p := p) hnfd)
    r

/-- Helper for Chap10 Example 10 119 5: infinite coefficient-field degree prevents Laurent
series from being finite-dimensional over the directed union of finite coefficient Laurent
subfields. -/
lemma not_finiteDimensional_laurentSeries_over_finiteCoeffLaurentUnion_from_spanEscape
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ FiniteDimensional (finiteCoeffLaurentUnion (k := k) (p := p)) (LaurentSeries k) := by
  -- Once the finite independent families are available for every size, the contradiction is the
  -- abstract finrank bound isolated above.
  exact not_finiteDimensional_of_forall_fin_linearIndependent
    (F := finiteCoeffLaurentUnion (k := k) (p := p)) (E := LaurentSeries k)
    (exists_fin_linearIndependent_over_finiteCoeffLaurentUnion_direct (k := k) (p := p) hnfd)

end
