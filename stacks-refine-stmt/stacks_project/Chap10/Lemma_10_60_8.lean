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
      ] := sorry

end
