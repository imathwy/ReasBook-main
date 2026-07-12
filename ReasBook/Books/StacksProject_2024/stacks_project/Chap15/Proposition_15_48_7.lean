import Mathlib
import StacksProject_2024.Chap10.Lemma_10_120_18
import StacksProject_2024.Chap10.Lemma_10_121_8
import StacksProject_2024.Chap10.Lemma_10_160_2
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Proposition_10_162_16
import StacksProject_2024.Chap15.Definition_15_47_1
import StacksProject_2024.Chap15.Lemma_15_10_5
import StacksProject_2024.Chap15.Lemma_15_47_3
import StacksProject_2024.Chap15.Lemma_15_47_6
import StacksProject_2024.Chap15.Lemma_15_48_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of the chapter owner `IsJ2Ring`, together with the standard
  complete-local, one-dimensional local, Nagata, Dedekind, and finite-type stability sources for
  the `J-2` property;
- sampled owner declarations of the same kind:
  `IsJ2Ring`,
  `isJ2Ring_iff_forall_finiteType_isJ1`,
  `NagataRing`,
  `IsCompleteLocalRing`;
- best owner abstraction: the public surface should stay on the canonical owner `IsJ2Ring`; pure
  specialization clauses such as the field and integer cases should use direct recall or instance
  inference rather than parallel local wrapper declarations;
- primitive vs. derived: the primitive public data are the ambient ring hypotheses for each source
  clause. The `J-1` conclusions for finite type algebras are derived from `IsJ2Ring`, so this file
  should not introduce any auxiliary data packaging around them.

Source/core/bridge triage:
- `source-facing`: the six proposition clauses listing concrete sources of `IsJ2Ring`;
- `core/canonical`: the chapter owner `IsJ2Ring`;
- `bridge/view`: the Dedekind/Nagata/complete-local specializations and the finite-type stability
  theorem.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.48.7 (1): fields are `J-2`. -/
#check (inferInstance : IsJ2Ring K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/-- Helper for Proposition 15.48.7: a finite product of complete local rings is complete local as
soon as the total product is a domain. -/
theorem isCompleteLocalRing_pi_of_isDomain
    {ι : Type*} [Fintype ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, IsCompleteLocalRing (S i)] [IsDomain ((i : ι) → S i)] :
    IsCompleteLocalRing ((i : ι) → S i) := by
  sorry

/-- Helper for Proposition 15.48.7: a finite domain over a Noetherian complete local ring is
`J-0`. -/
theorem isJ0Ring_of_finite_domain_over_noetherian_completeLocalRing
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A] [IsDomain A] :
    IsJ0Ring A :=
by
  sorry

/-- Proposition 15.48.7 (1): a Noetherian complete local ring is `J-2`. -/
-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra is a finite
-- product of Noetherian complete local rings, so by Lemma `15.47.3` it suffices to handle the
-- domain case. That domain case is Lemma `15.48.6`.
instance isJ2Ring_of_noetherian_completeLocalRing : IsJ2Ring R := by
  sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Proposition 15.48.7: the generic localization of a domain is a regular local ring,
because it identifies with the fraction field. -/
theorem isRegularLocalRing_localizationAtPrime_bot_of_isDomain
    {A : Type v} [CommRing A] [IsDomain A] :
    IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) := by
  sorry

/-- Helper for Proposition 15.48.7: a finite algebra over a local ring has only finitely many
maximal ideals, since every maximal ideal lies over the unique maximal ideal of the base. -/
theorem finite_maximalSpectrum_of_moduleFinite_local
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A] :
    Finite (MaximalSpectrum A) := by
  sorry

/-- Helper for Proposition 15.48.7: a finite family of closed points in a prime spectrum is a
closed subset. -/
theorem isClosed_of_finite_subset_closedPoints
    {A : Type v} [CommRing A] {X : Set (PrimeSpectrum A)}
    (hXfinite : X.Finite) (hXclosed : X ⊆ closedPoints (PrimeSpectrum A)) :
    IsClosed X := by
  sorry

/-- Helper for Proposition 15.48.7: a finite domain over a one-dimensional Noetherian local ring
is `J-0`. -/
theorem isJ0Ring_of_finite_domain_over_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
    [IsDomain A] :
    IsJ0Ring A :=
by
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  letI : Finite (MaximalSpectrum A) :=
    finite_maximalSpectrum_of_moduleFinite_local (R := R) (A := A)
  have hdim_le : ringKrullDim R ≤ 1 := by
    simpa [hdim]
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim_le
  -- Route correction: the remaining source-faithful step is to show that every nonregular prime
  -- is maximal, so the singular locus is a finite union of closed points.
  -- TODO: pass to the quotient domain `R / ker(R → A)`, localize at a maximal ideal above a
  -- nonmaximal nonzero prime, and contradict `Ring.KrullDimLE 1` via
  -- `two_le_ringKrullDim_of_zero_lt_lt_maximalIdeal`; then close `J-1` using the finite closed
  -- singular locus and conclude `J-0` by `isJ0Ring_of_isJ1Ring_domain`.
  sorry

-- Proof sketch: use condition `(3)` of Lemma `15.47.6`. Any finite `R`-algebra has finite
-- spectrum; because the regular locus is stable under generalization, it is open, so every finite
-- `R`-algebra is `J-1`.
/-- Proposition 15.48.7 (3): a Noetherian local ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_noetherian_local_ring_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := by
  sorry

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

/-- Helper for Proposition 15.48.7: a one-dimensional Nagata ring supplies the clause `(4)`
`J-0` model for every finite purely inseparable residue-field extension. -/
theorem exists_j0_model_of_purelyInseparable_extension_for_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1)
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [FiniteDimensional p.ResidueField L] [IsPurelyInseparable p.ResidueField L] :
    let _ : Algebra R L :=
      RingHom.toAlgebra
        ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
    let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (_ : IsDomain A) (_ : Algebra A L) (_ : IsScalarTower R A L)
      (_ : IsFractionRing A L),
      IsJ0Ring A :=
by
  let _ : Algebra R L :=
    RingHom.toAlgebra
      ((algebraMap p.ResidueField L).comp (algebraMap R p.ResidueField))
  let _ : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  by_cases hpmax : p.IsMaximal
  · -- In the maximal branch, the field extension itself is the required finite `J-0` model.
    letI : Module.Finite R p.ResidueField := inferInstance
    letI : Module.Finite R L := Module.Finite.trans p.ResidueField L
    letI : Algebra L L := inferInstance
    letI : IsScalarTower R L L := by infer_instance
    letI : IsFractionRing L L := IsFractionRing.idem L L
    letI : IsJ0Ring L := isJ0Ring_of_isRegularRing L
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance⟩
  · -- TODO: in the nonmaximal branch, first show that `p` is minimal in dimension one, then pass
    -- to `R / p`, use Nagata finiteness of the normalization in `L`, identify the normalization as
    -- a one-dimensional normal domain, and conclude regularity and hence `J-0`.
    let _ := hdim
    let _ := hpmax
    sorry

-- Proof sketch: use condition `(4)` of Lemma `15.47.6`. For a prime `p` and a finite purely
-- inseparable extension of its residue field, if `p` is maximal then the extension ring is finite
-- over a field and hence regular; if `p` is minimal, the Nagata property makes the integral
-- closure finite, and in dimension `1` that normal domain is regular.
/-- Proposition 15.48.7 (4): a Nagata ring of Krull dimension `1` is `J-2`. -/
theorem isJ2Ring_of_nagataRing_dimension_one
    (hdim : ringKrullDim R = 1) : IsJ2Ring R := by
  sorry

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Helper for Proposition 15.48.7: a nonfield Dedekind domain has Krull dimension `1`. -/
theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField
    (hR : ¬ IsField R) :
    ringKrullDim R = 1 :=
by
  sorry

/-- Proposition 15.48.7 (5): a Dedekind domain whose fraction field has characteristic zero is
`J-2`. -/
-- Proof sketch: such a ring is Nagata by Proposition `10.162.16`, and a Dedekind domain has
-- Krull dimension `1`; apply the one-dimensional Nagata case.
instance isJ2Ring_of_isDedekindDomain_of_fractionRing_charZero : IsJ2Ring R := by
  sorry

end

section

/- Proposition 15.48.7 (2): the ring of integers `ℤ` is `J-2`, by the Dedekind-domain
characteristic-zero instance above. -/
#check (inferInstance : IsJ2Ring ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Proposition 15.48.7 (6): finite type ring extensions of `J-2` rings are `J-2`. -/
-- Proof sketch: if `T` is a finite type `S`-algebra, then by transitivity it is a finite type
-- `R`-algebra. Since `R` is `J-2`, the ring `T` is `J-1`, so `S` satisfies the defining `J-2`
-- condition.
theorem isJ2Ring_of_finiteType [IsJ2Ring R] [Algebra.FiniteType R S] :
    IsJ2Ring S := by
  sorry

end
