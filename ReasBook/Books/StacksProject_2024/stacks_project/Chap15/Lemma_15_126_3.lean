import StacksProject_2024.Chap10.Definition_10_60_10
import StacksProject_2024.Chap10.Proposition_10_60_9
import StacksProject_2024.Chap10.Lemma_10_60_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open Ideal.Quotient (eq_zero_iff_mem)

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.126.3: every element of the maximal ideal of a quotient local ring lifts
to an element of the maximal ideal upstairs. -/
private theorem exists_maximalIdeal_lift_of_quotient_maximalIdeal (I : Ideal R)
    [IsLocalRing (R ⧸ I)]
    (x : maximalIdeal (R ⧸ I)) :
    ∃ y : maximalIdeal R, Ideal.Quotient.mk I (y : R) = x := by
  let π : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  -- Pull the quotient element back through the image description of the maximal ideal.
  have hxmap : (x : R ⧸ I) ∈ Ideal.map π (maximalIdeal R) := by
    rw [IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]
    exact x.property
  rcases (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).1 hxmap with
    ⟨y, hy, hxy⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  simpa [π] using hxy

/-- Helper for Lemma 15.126.3: adjoining a head generator splits the parameter ideal into the head
singleton span and the tail parameter ideal. -/
private theorem parameterIdeal_cons {d : ℕ} (f : maximalIdeal R) (z : Fin d → maximalIdeal R) :
    parameterIdeal (Fin.cons f z) =
      Ideal.span ({(f : R)} : Set R) ⊔ parameterIdeal z := by
  have hrange :
      Set.range (fun i : Fin (d + 1) ↦ (((Fin.cons f z : Fin (d + 1) → maximalIdeal R) i) : R)) =
        insert (f : R) (Set.range fun i : Fin d ↦ (z i : R)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
    · intro hx
      rcases hx with rfl | hx
      · exact ⟨0, rfl⟩
      · rcases hx with ⟨j, rfl⟩
        exact ⟨j.succ, rfl⟩
  -- Rewrite the head-tail range as an inserted singleton and expand the resulting span.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span, hrange, Ideal.span_insert]

/-- Helper for Lemma 15.126.3: if a tail in `R` lifts a tail in `S`, then the induced parameter
ideals map to one another under the ring homomorphism `π : R →+* S`. -/
private theorem map_parameterIdeal_of_lift {S : Type*} [CommRing S] [IsLocalRing S] {d : ℕ}
    (π : R →+* S) (z : Fin d → maximalIdeal R) (x : Fin d → maximalIdeal S)
    (hz : ∀ i, π (z i : R) = x i) :
    Ideal.map π (parameterIdeal z) = parameterIdeal x := by
  have hrange :
      π '' Set.range (fun i : Fin d ↦ (z i : R)) =
        Set.range fun i : Fin d ↦ (x i : S) := by
    ext y
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hz i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, hz i⟩
  -- Both parameter ideals are spans of the corresponding finite ranges.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span, Ideal.map_span]
  simpa [hrange]

/-- Helper for Lemma 15.126.3: if the image of an ideal in a quotient ring is an ideal of
definition, then the original ideal is an ideal of definition as soon as it contains the quotient
kernel. -/
private theorem isIdealOfDefinition_of_quotient_map_isIdealOfDefinition (I J : Ideal R)
    [IsLocalRing (R ⧸ I)]
    (hIJ : I ≤ J) (hdef : (Ideal.map (Ideal.Quotient.mk I) J).IsIdealOfDefinition) :
    J.IsIdealOfDefinition := by
  let π : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  letI : IsLocalHom π := IsLocalHom.of_surjective π Ideal.Quotient.mk_surjective
  have hcomap_map : Ideal.comap π (Ideal.map π J) = J := by
    rw [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective]
    refine sup_eq_left.mpr ?_
    intro x hx
    exact hIJ <| eq_zero_iff_mem.mp <| by
      simpa [π, Ideal.mem_comap, Ideal.mem_bot] using hx
  -- Pull the quotient radical equality back along the surjective quotient map.
  rw [Ideal.IsIdealOfDefinition] at hdef ⊢
  calc
    J.radical = Ideal.comap π (Ideal.map π J).radical := by
      rw [Ideal.comap_radical, hcomap_map]
    _ = Ideal.comap π (maximalIdeal (R ⧸ I)) := by rw [hdef]
    _ = maximalIdeal R := IsLocalRing.maximalIdeal_comap π

/-- Helper for Lemma 15.126.3: a system of parameters in `R / (f)` lifts to an ordered system of
parameters in `R` whose head is `f`. -/
private theorem exists_systemOfParameters_cons_of_quotient_systemOfParameters {d : ℕ}
    (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span ({(f : R)} : Set R))]
    {x : Fin d → maximalIdeal (R ⧸ Ideal.span ({(f : R)} : Set R))}
    (hx : IsSystemOfParameters x) :
    ∃ z : Fin d → maximalIdeal R, IsSystemOfParameters (Fin.cons f z) := by
  let I : Ideal R := Ideal.span ({(f : R)} : Set R)
  let π : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  classical
  -- Lift each quotient parameter individually into the maximal ideal upstairs.
  have hlift : ∀ i, ∃ y : maximalIdeal R, π (y : R) = x i := by
    intro i
    simpa [I, π] using exists_maximalIdeal_lift_of_quotient_maximalIdeal I (x i)
  choose z hz using hlift
  have hfzero : π (f : R) = 0 := by
    apply eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  have hmapHead : Ideal.map π (Ideal.span ({(f : R)} : Set R)) = ⊥ := by
    rw [Ideal.map_span, Set.image_singleton]
    simpa [hfzero]
  have hmapCons : Ideal.map π (parameterIdeal (Fin.cons f z)) = parameterIdeal x := by
    -- The quotient kills the head element and preserves the lifted tail parameter ideal.
    rw [parameterIdeal_cons, Ideal.map_sup, hmapHead,
      map_parameterIdeal_of_lift π z x hz]
    simp
  have hkernel_le : I ≤ parameterIdeal (Fin.cons f z) := by
    dsimp [I]
    refine Ideal.span_le.mpr ?_
    intro x hx
    simp at hx
    rcases hx with rfl
    exact Ideal.subset_span ⟨0, rfl⟩
  have hdef : (parameterIdeal (Fin.cons f z)).IsIdealOfDefinition := by
    -- Pull the ideal-of-definition property back from the quotient parameter ideal.
    apply isIdealOfDefinition_of_quotient_map_isIdealOfDefinition I
      (parameterIdeal (Fin.cons f z)) hkernel_le
    rw [hmapCons]
    exact hx.2
  refine ⟨z, ?_⟩
  exact ⟨hdim, hdef⟩

/-- Helper for Lemma 15.126.3: the positive `(k + 1)`-st power of an element of the maximal ideal
still lies in the maximal ideal. -/
private theorem pow_succ_mem_maximalIdeal {k : ℕ} (x : maximalIdeal R) :
    ((x : R) ^ (k + 1)) ∈ maximalIdeal R := by
  have hxpow : (x : R) ^ (k + 1) ∈ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_mem_pow x.property (k + 1)
  simpa using
    (Ideal.pow_le_pow_right (show 1 ≤ k + 1 by exact Nat.succ_le_succ (Nat.zero_le k)) hxpow :
      (x : R) ^ (k + 1) ∈ maximalIdeal R ^ 1)

/-- Helper for Lemma 15.126.3: the positive `(k + 1)`-st power of an element of the maximal ideal
lies in `(maximalIdeal R)^k`. -/
private theorem pow_succ_mem_maximalIdeal_pow {k : ℕ} (x : maximalIdeal R) :
    ((x : R) ^ (k + 1)) ∈ maximalIdeal R ^ k := by
  have hxpow : (x : R) ^ (k + 1) ∈ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_mem_pow x.property (k + 1)
  exact (Ideal.pow_le_pow_right (Nat.le_succ k)) hxpow

/-- Helper for Lemma 15.126.3: repackage a positive power of a maximal-ideal element as another
element of the maximal ideal. -/
private abbrev maximalIdeal_power_element (k : ℕ) (x : maximalIdeal R) : maximalIdeal R :=
  ⟨(x : R) ^ (k + 1), pow_succ_mem_maximalIdeal (k := k) x⟩

/-- Helper for Lemma 15.126.3: replace each tail parameter by its positive `(k + 1)`-st power. -/
private abbrev powered_tail {d : ℕ} (k : ℕ) (z : Fin d → maximalIdeal R) :
    Fin d → maximalIdeal R :=
  fun i ↦ maximalIdeal_power_element k (z i)

/-- Helper for Lemma 15.126.3: the parameter ideal generated by the powered tail is contained in
the original tail parameter ideal. -/
private theorem parameterIdeal_powered_tail_le {d k : ℕ} (z : Fin d → maximalIdeal R) :
    parameterIdeal (powered_tail k z) ≤ parameterIdeal z := by
  -- Each powered generator already lies in the ideal generated by the original tail.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  have hmem : (z i : R) ∈ Ideal.span (Set.range fun j : Fin d ↦ (z j : R)) := by
    exact Ideal.subset_span ⟨i, rfl⟩
  simpa [powered_tail, maximalIdeal_power_element] using
    Ideal.pow_mem_of_mem _ hmem (k + 1) (Nat.succ_pos k)

/-- Helper for Lemma 15.126.3: every original tail generator lies in the radical of the ideal
generated by its positive powers. -/
private theorem parameterIdeal_tail_le_radical_powered_tail {d k : ℕ}
    (z : Fin d → maximalIdeal R) :
    parameterIdeal z ≤ (parameterIdeal (powered_tail k z)).radical := by
  -- Each original generator enters the radical because its `(k + 1)`-st power is a new generator.
  rw [parameterIdeal_eq_span, parameterIdeal_eq_span]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Ideal.mem_radical_iff).2 ?_
  refine ⟨k + 1, ?_⟩
  simpa [powered_tail, maximalIdeal_power_element] using
    (Ideal.subset_span ⟨i, rfl⟩ :
      ((powered_tail k z i : R)) ∈
        Ideal.span (Set.range fun j : Fin d ↦ ((powered_tail k z j : R))))

/-- Helper for Lemma 15.126.3: an ideal sandwiched between an ideal of definition and its
radical is again an ideal of definition. -/
private theorem isIdealOfDefinition_of_le_of_le_radical (J I : Ideal R)
    (hJI : J ≤ I) (hIJrad : I ≤ J.radical) (hI : I.IsIdealOfDefinition) :
    J.IsIdealOfDefinition := by
  -- Compare radicals on both sides of the sandwich and use the defining radical equality of `I`.
  rw [Ideal.IsIdealOfDefinition] at hI ⊢
  refine le_antisymm ?_ ?_
  · exact (Ideal.radical_mono hJI).trans (by simpa [hI])
  · simpa [hI] using Ideal.radical_mono hIJrad

/-- Helper for Lemma 15.126.3: raising each tail parameter to a positive power forces the tail
into `(maximalIdeal R)^k` without changing the radical of the full parameter ideal. -/
private theorem exists_tail_in_maximalIdeal_pow_of_systemOfParameters_cons {d k : ℕ}
    (f : maximalIdeal R) (z : Fin d → maximalIdeal R)
    (hz : IsSystemOfParameters (Fin.cons f z)) :
    ∃ y : Fin d → maximalIdeal R,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ j, (y j : R) ∈ maximalIdeal R ^ k := by
  -- Route correction: compare the tail parameter ideals first, then add the common head `f` once.
  let y := powered_tail k z
  have htail_le : parameterIdeal y ≤ parameterIdeal z := by
    -- The powered tail generates a smaller ideal because each powered entry already lies upstairs.
    simpa [y] using parameterIdeal_powered_tail_le (k := k) z
  have htail_rad : parameterIdeal z ≤ (parameterIdeal y).radical := by
    -- The original tail lies in the radical since each generator has a positive power in `y`.
    simpa [y] using parameterIdeal_tail_le_radical_powered_tail (k := k) z
  have hfull_le : parameterIdeal (Fin.cons f y) ≤ parameterIdeal (Fin.cons f z) := by
    -- After splitting off the head generator, only the tail inclusion remains.
    rw [parameterIdeal_cons, parameterIdeal_cons]
    exact sup_le_sup_left htail_le _
  have hfull_rad :
      parameterIdeal (Fin.cons f z) ≤ (parameterIdeal (Fin.cons f y)).radical := by
    -- The common head is already in the larger full ideal, and the tail maps into its radical.
    rw [parameterIdeal_cons, parameterIdeal_cons]
    refine sup_le_iff.2 ?_
    constructor
    · exact (le_sup_left : Ideal.span ({(f : R)} : Set R) ≤
        Ideal.span ({(f : R)} : Set R) ⊔ parameterIdeal y).trans Ideal.le_radical
    · exact htail_rad.trans <|
        Ideal.radical_mono (le_sup_right : parameterIdeal y ≤
          Ideal.span ({(f : R)} : Set R) ⊔ parameterIdeal y)
  have hdef : (parameterIdeal (Fin.cons f y)).IsIdealOfDefinition := by
    -- Transfer the ideal-of-definition clause across the radical sandwich.
    exact isIdealOfDefinition_of_le_of_le_radical
      (parameterIdeal (Fin.cons f y)) (parameterIdeal (Fin.cons f z))
      hfull_le hfull_rad hz.2
  refine ⟨y, ?_⟩
  constructor
  · -- The dimension clause is unchanged, and the ideal-of-definition clause was transported above.
    exact ⟨hz.1, hdef⟩
  · intro j
    -- Each powered entry lands in `(maximalIdeal R)^k` by the standard power-membership lemma.
    simpa [y, powered_tail, maximalIdeal_power_element] using
      pow_succ_mem_maximalIdeal_pow (k := k) (z j)

-- Domain-style sampling:
-- * primary domain: systems of parameters in Noetherian local rings, with minimal-prime
--   avoidance and one-step dimension reduction;
-- * sampled owner declarations: `IsSystemOfParameters`, `parameterIdeal`,
--   `generatedIdeal_clause_iff_exists_systemOfParameters`,
--   `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`.
--
-- Source/core/bridge triage:
-- * source-facing: the lemma asserts that an element `f` outside all minimal primes can be
--   extended, in first-position order, to a system of parameters whose tail lies in a prescribed
--   power of the maximal ideal;
-- * core/canonical: `IsSystemOfParameters` is the owner abstraction for the chosen parameter
--   family, so the primitive data should be the ordered tail `y : Fin d → maximalIdeal R`, with
--   the full family derived as `Fin.cons f y`;
-- * bridge/view: minimal-prime avoidance should use the chapter's canonical membership-style
--   owner surface `∀ p ∈ minimalPrimes R, (f : R) ∉ p`, and
--   the existence step in the quotient should be read through the owner theorem
--   `generatedIdeal_clause_iff_exists_systemOfParameters` rather than through a lower-level
--   generated-ideal witness package.
-- Proof sketch: if `d = 0`, use the one-term parameter family `Fin.cons f` and the tail condition
-- is vacuous. Otherwise, Lemma `ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes`
-- lowers the quotient dimension to `d`, and the owner-level existence clause from Proposition
-- `10.60.9`, packaged by `generatedIdeal_clause_iff_exists_systemOfParameters`, supplies a
-- length-`d` system of parameters in `R / (f)`. Lift those parameters to `R`, then replace each
-- lift by its `k`-th power so that the tail lands in `(maximalIdeal R)^k` without changing the
-- generated radical.
/-- Lemma 15.126.3: write `dim R = d + 1`. If `f : maximalIdeal R` avoids every minimal prime of
`R`, then there exist `d` further parameters in `(maximalIdeal R)^k` whose ordered extension
`Fin.cons f y` is a system of parameters. This is the source-facing ordered `Fin.cons` form of
adjoining further parameters in `(maximalIdeal R)^k` to the specified element `f`. -/
theorem exists_systemOfParameters_cons_mem_maximalIdeal_pow_of_not_mem_minimalPrimes
    {d k : ℕ} (hdim : ringKrullDim R = d.succ) (f : maximalIdeal R)
    (hmin : ∀ p ∈ minimalPrimes R, (f : R) ∉ p) :
    ∃ y : Fin d → maximalIdeal R,
      IsSystemOfParameters (Fin.cons f y) ∧
        ∀ j, (y j : R) ∈ maximalIdeal R ^ k := by
  let S := R ⧸ Ideal.span ({(f : R)} : Set R)
  have hspan_le :
      Ideal.span ({(f : R)} : Set R) ≤ maximalIdeal R := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    simp at hx
    simpa [hx] using f.property
  have hspan_ne_top : Ideal.span ({(f : R)} : Set R) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hspan_le
  letI : IsLocalRing S := by
    let _ : Nontrivial S := Ideal.Quotient.nontrivial_iff.2 <| by
      simpa [S] using hspan_ne_top
    simpa [S] using
      (IsLocalRing.of_surjective'
        (Ideal.Quotient.mk (Ideal.span ({(f : R)} : Set R))) Ideal.Quotient.mk_surjective :
        IsLocalRing S)
  have hquot :
      ringKrullDim R = ringKrullDim S + 1 := by
    simpa [S] using
      ringKrullDim_eq_ringKrullDim_quotient_span_singleton_add_one_of_not_mem_minimalPrimes
        (R := R) (f : R) f.property hmin
  have hdimS : ringKrullDim S = d := by
    simpa [Nat.succ_eq_add_one] using hquot.symm.trans hdim
  have hclause :
      ((∃ x : Fin d → maximalIdeal S, (parameterIdeal x).IsIdealOfDefinition) ∧
        ∀ n : ℕ, n < d →
          ¬ ∃ x : Fin n → maximalIdeal S, (parameterIdeal x).IsIdealOfDefinition) := by
    -- The quotient ring has dimension `d`, so Proposition 10.60.9 supplies a generating clause.
    exact ((local_noetherian_ring_dimension_tfae (R := S) d).out 0 2).mp hdimS
  have hsopClause :
      ((∃ x : Fin d → maximalIdeal S, IsSystemOfParameters x) ∧
        ∀ n : ℕ, n < d →
          ¬ ∃ x : Fin n → maximalIdeal S, (parameterIdeal x).IsIdealOfDefinition) := by
    -- Translate the generated-ideal clause into the owner predicate `IsSystemOfParameters`.
    exact (generatedIdeal_clause_iff_exists_systemOfParameters (R := S) hdimS).mp hclause
  rcases hsopClause.1 with ⟨x, hx⟩
  rcases exists_systemOfParameters_cons_of_quotient_systemOfParameters hdim f hx with ⟨z, hz⟩
  exact exists_tail_in_maximalIdeal_pow_of_systemOfParameters_cons f z hz

end
