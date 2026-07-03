import Mathlib.Data.List.TFAE
import stacks_project.Chap10.Definition_10_60_10
import stacks_project.Chap10.Proposition_10_60_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal PrimeSpectrum IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem parameterIdeal_fin1_eq_span (x : Fin 1 → maximalIdeal R) :
    parameterIdeal x = span ({(x 0 : R)} : Set R) := by
  rw [parameterIdeal_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  · intro hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨0, rfl⟩

omit [IsNoetherianRing R] in
private theorem exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition :
    (∃ x : Fin 1 → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
      ∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal := by
  constructor
  · rintro ⟨x, hxdef⟩
    refine ⟨parameterIdeal x, hxdef, ?_⟩
    refine ⟨(x 0 : R), ?_⟩
    change parameterIdeal x = span ({(x 0 : R)} : Set R)
    exact parameterIdeal_fin1_eq_span x
  · rintro ⟨I, hdef, hI⟩
    let _ : I.IsPrincipal := hI
    obtain ⟨x, hxI⟩ := Submodule.IsPrincipal.principal I
    have hx𝔪 : x ∈ maximalIdeal R := by
      rw [← hdef]
      have hxrad : x ∈ I.radical := by
        rw [hxI]
        exact Ideal.le_radical (Ideal.subset_span (by simp : x ∈ ({x} : Set R)))
      simpa using hxrad
    let x' : Fin 1 → maximalIdeal R := fun _ ↦ ⟨x, hx𝔪⟩
    refine ⟨x', ?_⟩
    simpa [x', hxI, parameterIdeal_fin1_eq_span x'] using hdef

omit [IsNoetherianRing R] in
private theorem no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition :
    (∀ n : ℕ, n < 1 →
      ¬ ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
        ¬ (⊥ : Ideal R).IsIdealOfDefinition := by
  constructor
  · intro h hbot
    apply h 0 (by decide)
    refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
    simpa [parameterIdeal_eq_span] using hbot
  · intro hbot n hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    subst hn0
    rintro ⟨x, hx⟩
    exact hbot <| by simpa [parameterIdeal_eq_span] using hx

omit [IsNoetherianRing R] in
private theorem one_generator_parameterIdeal_clause_iff :
    ((∃ x : Fin 1 → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ∧
      ∀ n : ℕ, n < 1 →
        ¬ ∃ x : Fin n → maximalIdeal R, (parameterIdeal x).IsIdealOfDefinition) ↔
      ((∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal) ∧
        ¬ (⊥ : Ideal R).IsIdealOfDefinition) := by
  constructor
  · rintro ⟨hexists, hmin⟩
    exact ⟨
      exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition.mp hexists,
      no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition.mp hmin
    ⟩
  · rintro ⟨hexists, hbot⟩
    exact ⟨
      exists_parameterIdeal_fin1_iff_exists_principal_idealOfDefinition.mpr hexists,
      no_parameterIdeal_lt_one_iff_bot_not_isIdealOfDefinition.mpr hbot
    ⟩

omit [IsNoetherianRing R] in
private theorem zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition (x : R) :
    zeroLocus ({x} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R)) ↔
      (span ({x} : Set R)).IsIdealOfDefinition := by
  have hclosed :
      ({closedPoint R} : Set (PrimeSpectrum R)) =
        PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
    simp [PrimeSpectrum.zeroLocus_eq_singleton, IsLocalRing.closedPoint]
  constructor
  · intro hxzero
    rw [Ideal.IsIdealOfDefinition]
    have hzero :
        PrimeSpectrum.zeroLocus (span ({x} : Set R) : Set R) =
          PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
      rw [PrimeSpectrum.zeroLocus_span]
      exact hxzero.trans hclosed
    simpa [Ideal.IsIdealOfDefinition, (maximalIdeal.isMaximal R).isPrime.radical] using
      (PrimeSpectrum.zeroLocus_eq_iff.mp hzero)
  · intro hxdef
    have hzero :
        PrimeSpectrum.zeroLocus (span ({x} : Set R) : Set R) =
          PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
      refine PrimeSpectrum.zeroLocus_eq_iff.mpr ?_
      simpa [Ideal.IsIdealOfDefinition, (maximalIdeal.isMaximal R).isPrime.radical] using hxdef
    rw [← PrimeSpectrum.zeroLocus_span]
    exact hzero.trans hclosed.symm

-- Source/core/bridge triage:
-- * source-facing: clauses `(3)` and `(4)` keep the textbook witness `x : R`;
-- * core/canonical: clauses `(1)` and `(2)` come from the source-facing owner theorem
--   `local_noetherian_ring_dimension_tfae 1`;
-- * bridge/view: clause `(5)` rewrites the one-generator case of clause `(3)` into the canonical
--   ideal predicate `IsIdealOfDefinition` together with
--   `IsPrincipal`. The extra hypothesis `¬ (⊥ : Ideal R).IsIdealOfDefinition` is exactly the
--   `n = 0` minimality clause and excludes the nilpotent zero-dimensional case. The source-facing
--   clause predicates below package these conjunction-heavy clauses so the public theorem surface
--   stays atomic.
/-- The source-facing clause asserting that a nonnilpotent element cuts out exactly the closed
point of `Spec R`. -/
def ExistsNonnilpotentClosedPointDefiningElement (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ x : R, ¬ IsNilpotent x ∧ zeroLocus ({x} : Set R) = ({closedPoint R} : Set (PrimeSpectrum R))

/-- The source-facing clause asserting that a nonnilpotent element generates an ideal of
definition. -/
def ExistsNonnilpotentIdealOfDefinitionGenerator (R : Type u) [CommRing R] [IsLocalRing R] :
    Prop :=
  ∃ x : R, ¬ IsNilpotent x ∧ (span ({x} : Set R)).IsIdealOfDefinition

/-- The canonical existence clause asserting that some ideal of definition is principal. -/
def ExistsPrincipalIdealOfDefinition (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ I : Ideal R, I.IsIdealOfDefinition ∧ I.IsPrincipal

/-- The minimality clause asserting that the zero ideal is not an ideal of definition. -/
def ZeroIdealNotIdealOfDefinition (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ¬ (⊥ : Ideal R).IsIdealOfDefinition

/-- The canonical clause combining the existence of a principal ideal of definition with the
exclusion of the zero-dimensional nilpotent case. -/
def OneDimensionalPrincipalIdealCriterion (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: the geometric closed-point clause is equivalent to asking for a
nonnilpotent generator of an ideal of definition. -/
private theorem
    exists_nonnilpotent_closed_point_defining_element_iff_exists_nonnilpotent_idealOfDefinition_generator :
    ExistsNonnilpotentClosedPointDefiningElement R ↔
      ExistsNonnilpotentIdealOfDefinitionGenerator R := by
  constructor
  · rintro ⟨x, hx, hxzero⟩
    -- The same witness `x` converts the vanishing-locus condition into the radical condition.
    refine ⟨x, hx, ?_⟩
    exact (zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition x).mp hxzero
  · rintro ⟨x, hx, hxdef⟩
    -- Reversing the same rewrite recovers the closed-point description of `V(x)`.
    refine ⟨x, hx, ?_⟩
    exact (zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition x).mpr hxdef

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: if the zero ideal is an ideal of definition, then every element of
the maximal ideal is nilpotent. -/
private theorem nilpotent_of_mem_maximalIdeal_of_zeroIdeal_isIdealOfDefinition
    {x : R} (hbot : (⊥ : Ideal R).IsIdealOfDefinition) (hx : x ∈ maximalIdeal R) :
    IsNilpotent x := by
  -- The zero ideal having maximal radical places `x` in `√(0)`.
  have hxrad : x ∈ (⊥ : Ideal R).radical := by
    rw [Ideal.IsIdealOfDefinition] at hbot
    simpa [hbot] using hx
  -- Membership in `√(0)` is exactly nilpotence.
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hxrad
  exact ⟨n, by simpa [Ideal.mem_bot] using hn⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.60.8: the principal ideal-of-definition criterion is equivalent to the
existence of a nonnilpotent generator of an ideal of definition. -/
private theorem
    exists_nonnilpotent_idealOfDefinitionGenerator_iff_oneDimensionalPrincipalIdealCriterion :
    ExistsNonnilpotentIdealOfDefinitionGenerator R ↔
      OneDimensionalPrincipalIdealCriterion R := by
  constructor
  · rintro ⟨x, hx, hxdef⟩
    change ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R
    refine ⟨?_, ?_⟩
    · -- The displayed ideal of definition is principal by construction.
      refine ⟨Ideal.span ({x} : Set R), hxdef, ?_⟩
      exact ⟨x, rfl⟩
    · -- If `(0)` were an ideal of definition, the same element would become nilpotent.
      change ¬ (⊥ : Ideal R).IsIdealOfDefinition
      intro hbot
      have hx𝔪 : x ∈ maximalIdeal R := by
        rw [← hxdef]
        exact Ideal.le_radical (Ideal.subset_span (by simp : x ∈ ({x} : Set R)))
      exact hx <|
        nilpotent_of_mem_maximalIdeal_of_zeroIdeal_isIdealOfDefinition hbot hx𝔪
  · intro hcriterion
    change ExistsPrincipalIdealOfDefinition R ∧ ZeroIdealNotIdealOfDefinition R at hcriterion
    rcases hcriterion with ⟨⟨I, hIdef, hIprincipal⟩, hbot⟩
    let _ : I.IsPrincipal := hIprincipal
    obtain ⟨x, hxI⟩ := Submodule.IsPrincipal.principal I
    have hspan_def : (Ideal.span ({x} : Set R)).IsIdealOfDefinition := by
      -- Rewriting the chosen generator identifies the given principal ideal with `(x)`.
      simpa [hxI] using hIdef
    refine ⟨x, ?_, hspan_def⟩
    intro hxnil
    apply hbot
    rw [Ideal.IsIdealOfDefinition]
    have hspan_radical_eq_bot :
        (Ideal.span ({x} : Set R)).radical = (⊥ : Ideal R).radical := by
      obtain ⟨n, hn⟩ := hxnil
      apply le_antisymm
      · -- Nilpotence of `x` shows that `√((x))` is contained in `√(0)`.
        have hxrad_bot : x ∈ (⊥ : Ideal R).radical := by
          exact Ideal.mem_radical_iff.mpr ⟨n, by simpa [Ideal.mem_bot] using hn⟩
        have hspan_le :
            Ideal.span ({x} : Set R) ≤ (⊥ : Ideal R).radical :=
          (Ideal.span_singleton_le_iff_mem (I := (⊥ : Ideal R).radical) (x := x)).2 hxrad_bot
        calc
          (Ideal.span ({x} : Set R)).radical ≤ ((⊥ : Ideal R).radical).radical :=
            Ideal.radical_mono hspan_le
          _ = (⊥ : Ideal R).radical := Ideal.radical_idem _
      · -- The reverse inclusion is automatic from `(0) ≤ (x)`.
        exact Ideal.radical_mono bot_le
    calc
      (⊥ : Ideal R).radical = (Ideal.span ({x} : Set R)).radical := hspan_radical_eq_bot.symm
      _ = maximalIdeal R := by
        simpa [Ideal.IsIdealOfDefinition] using hspan_def

-- Proof sketch: specialize Proposition 10.60.9 at `d = 1`, rewrite the source-facing one-element
-- parameter-ideal clause using the private equivalences above, and then compare the vanishing-locus
-- and principal-generator formulations through `zeroLocus_singleton_eq_closedPoint_iff_isIdealOfDefinition`.
/-- Lemma 10.60.8: for a Noetherian local ring `R`, the following are equivalent: `dim(R) = 1`,
`d(R) = 1`, there is a nonnilpotent element whose vanishing locus is exactly the closed point,
there is a nonnilpotent element whose principal ideal has radical the maximal ideal, and there is a
principal ideal of definition while the zero ideal is not an ideal of definition. -/
theorem one_dimensional_local_ring_tfae :
    List.TFAE
      [ ringKrullDim R = 1
      , hilbertSamuelPolynomialDegree R R = 1
      , ExistsNonnilpotentClosedPointDefiningElement R
      , ExistsNonnilpotentIdealOfDefinitionGenerator R
      , OneDimensionalPrincipalIdealCriterion R
      ] := by
  have howner := local_noetherian_ring_dimension_tfae (R := R) 1
  -- The owner theorem already identifies the dimension and Hilbert-Samuel clauses.
  tfae_have 1 ↔ 2 := howner.out 0 1
  -- Rewriting the owner one-generator clause yields the source-facing principal criterion.
  tfae_have 1 ↔ 5 := by
    simpa [OneDimensionalPrincipalIdealCriterion, ExistsPrincipalIdealOfDefinition,
      ZeroIdealNotIdealOfDefinition] using
      (howner.out 0 2).trans one_generator_parameterIdeal_clause_iff
  -- The two source formulations keep the same witness `x` and only rewrite the meaning of `V(x)`.
  tfae_have 3 ↔ 4 :=
    exists_nonnilpotent_closed_point_defining_element_iff_exists_nonnilpotent_idealOfDefinition_generator
  -- The final bridge packages the textbook principal-ideal criterion into the source-facing form.
  tfae_have 4 ↔ 5 :=
    exists_nonnilpotent_idealOfDefinitionGenerator_iff_oneDimensionalPrincipalIdealCriterion
  tfae_finish

end
