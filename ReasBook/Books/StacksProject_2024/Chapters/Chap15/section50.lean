import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_50_1 (from Chap15) -/
open Algebra IsLocalRing

universe u

section

/-- The completion of the localization `R_𝔭` at its maximal ideal. -/
abbrev CompletedLocalizationAtPrime (R : Type u) [CommRing R] (p : PrimeSpectrum R) : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal)

notation:max "R̂_[" p "]" => CompletedLocalizationAtPrime _ p

namespace CompletedLocalizationAtPrime

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R'] [Algebra.FiniteType R R']

/-- The canonical map on completed localizations induced by a prime `p'` of `R'` lying over `p`
in the intrinsic prime-spectrum sense `PrimeSpectrum.comap (algebraMap R R') p' = p`. -/
noncomputable abbrev map (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p) :
    R̂_[p] →+* R̂_[p'] :=
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  maximalIdealCompletionMap
    (Localization.localRingHom p.asIdeal p'.asIdeal (algebraMap R R')
      (by
        simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hp).symm))

end

end CompletedLocalizationAtPrime

/-- Definition 15.50.1: a ring `R` is a `G`-ring if `R` is Noetherian and, for every prime `p`
of `R`, the canonical map from the local ring `R_p` to its maximal-ideal-adic completion is a
regular ring map. -/
class IsGRing (R : Type u) [CommRing R] : Prop extends IsNoetherianRing R where
  /-- For every prime `p`, the completion map from `R_p` to its maximal-ideal-adic completion is
  regular. -/
  regular_localization_completion (p : PrimeSpectrum R) :
    (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])).IsRegularRingMap

variable {R : Type u} [CommRing R]

/-- The `G`-ring condition is exactly regularity of the completion map at every prime
localization. -/
theorem isGRing_iff_forall_regular_localization_completion [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p : PrimeSpectrum R,
        (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])).IsRegularRingMap :=
  ⟨fun h p ↦ h.regular_localization_completion p,
    fun h ↦ { regular_localization_completion := h }⟩

section

variable (K : Type u) [Field K]

-- Proof sketch: a field is Noetherian, and for its unique prime the localization is again the
-- field; the completion at the zero maximal ideal identifies with the field, so the completion map
-- is the identity regular morphism.
/-- A field is a `G`-ring. -/
instance : IsGRing K := sorry

end

end

/-! ### Lemma_15_50_2 (from Chap15) -/
open Algebra

universe u

section

variable (R : Type u) [CommRing R]

/- Domain triage:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `IsPRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `SatisfiesPPrimePairCondition`;
- best owner abstraction: the canonical completion owner `CompletedLocalizationAtPrime`, exposed on
  the theorem surface through the textbook notation `R̂_[p]`, together with the chapter owners
  `IsGRing` and `IsPRing`;
- primitive data: a commutative ring `R`, with Noetherianity supplied by the owner hypotheses
  `IsGRing R` or `IsPRing Algebra.IsGeometricallyRegularProperty R`, and a prime pair `q ≤ p`;
- derived API: geometric regularity of the formal fiber `q.asIdeal.Fiber (R̂_[p])`.

Layering:
- the numbered lemma is `source-facing`;
- `IsGRing`, `IsPRing`, and `CompletedLocalizationAtPrime` are the `core/canonical` owners;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/

namespace Algebra

/-- The Chapter 15 `FieldAlgebraProperty` corresponding to geometric regularity. -/
abbrev IsGeometricallyRegularProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsGeometricallyRegular k A

instance isGeometricallyRegular_hasPropertyA :
    IsGeometricallyRegularProperty.HasPropertyA where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hP
    sorry

instance isGeometricallyRegular_hasPropertyB :
    IsGeometricallyRegularProperty.HasPropertyB where
  localizationCriterion := by
    intro k A _ _ _ _
    sorry

/-- Geometric regularity satisfies Chapter 15 axiom `(C)`. -/
instance isGeometricallyRegular_hasPropertyC :
    IsGeometricallyRegularProperty.HasPropertyC where
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hB q
    sorry

/-- Geometric regularity satisfies Chapter 15 axiom `(D)`. -/
instance isGeometricallyRegular_hasPropertyD :
    IsGeometricallyRegularProperty.HasPropertyD where
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    sorry

/-- Geometric regularity satisfies Chapter 15 axiom `(E)`. -/
instance isGeometricallyRegular_hasPropertyE :
    IsGeometricallyRegularProperty.HasPropertyE where
  separableBaseChange k k' A := by
    intro _ _ _ _ _ _ _ _ hA
    exact (isGeometricallyRegular_iff_of_isSeparable : _ ↔ _).1 hA

end Algebra

/-- The `G`-ring owner is the `P`-ring owner specialized to geometric regularity of formal fibers. -/
theorem isGRing_iff_isPRing_isGeometricallyRegularProperty :
    IsGRing R ↔ IsPRing Algebra.IsGeometricallyRegularProperty R := by
  constructor
  · intro hR
    letI : IsNoetherianRing R := hR.toIsNoetherian
    refine { satisfiesPFormalFiberCondition := ?_ }
    intro p q
    letI : RingHom.IsRegularRingMap (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])) :=
      hR.regular_localization_completion p
    let hreg :
        RingHom.IsRegularRingMap (algebraMap (Localization.AtPrime p.asIdeal) (R̂_[p])) :=
      inferInstance
    simpa [Algebra.IsGeometricallyRegularProperty] using hreg.isGeometricallyRegular_fiber q
  · intro hP
    letI : IsNoetherianRing R := hP.toIsNoetherian
    refine isGRing_iff_forall_regular_localization_completion.2 ?_
    intro p
    exact
      { toFlat :=
          RingHom.flat_algebraMap_iff.mpr <|
            (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
              (Localization.AtPrime p.asIdeal)).flat
        isGeometricallyRegular_fiber := by
          simpa [Algebra.IsGeometricallyRegularProperty] using
            hP.satisfiesPFormalFiberCondition p }

/-- A Noetherian local ring is a `G`-ring exactly when its formal fibers are geometrically
regular. -/
theorem isGRing_iff_localFormalFibersHaveProperty
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsGRing A ↔ LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty A := by
  sorry

-- Proof sketch: specialize the generic prime-pair criterion for `P`-rings from Lemma `15.51.1`
-- to geometric regularity, then translate the owner back from `IsPRing` to `IsGRing`.
/-- Lemma 15.50.2: for a Noetherian ring `R`, the `G`-ring condition is equivalent to requiring
that for every inclusion of primes `𝔮 ⊆ 𝔭`, the canonical `κ(𝔮)`-algebra `R̂_𝔭 ⊗[R] κ(𝔮)`,
equivalently
`((R ⧸ 𝔮)_𝔭^ ∧) ⊗[R ⧸ 𝔮] κ(𝔮)`, is geometrically regular over `κ(𝔮)`. -/
theorem isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ p q : PrimeSpectrum R, ∀ _hqp : q.asIdeal ≤ p.asIdeal,
        IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := by
  have hprimePair :
      IsPRing Algebra.IsGeometricallyRegularProperty R ↔
        SatisfiesPPrimePairCondition Algebra.IsGeometricallyRegularProperty R :=
    isPRing_iff_satisfiesPPrimePairCondition
  simpa [Algebra.IsGeometricallyRegularProperty, SatisfiesPPrimePairCondition] using
    (isGRing_iff_isPRing_isGeometricallyRegularProperty R).trans hprimePair

end

/-! ### Lemma_15_50_3 (from Chap15) -/
open Algebra

universe u

/- Domain triage:
- primary domain: quasi-finite maps and geometric regularity of formal fibers in commutative
  algebra;
- sampled owner declarations:
  `IsGRing`,
  `IsRegularRingMap`,
  `IsGeometricallyRegular`,
  `IsPRing`,
  `completed_localization_formalFiber_hasProperty_of_quasiFiniteAt`;
- best owner abstraction: the generic `FieldAlgebraProperty` transfer package from
  `Lemma_15_51_3`, specialized to the canonical field-algebra owner
  `IsGeometricallyRegular`, with the source-facing ring owner `IsPRing`;
- primitive data: the owner theorem
  `completed_localization_formalFiber_hasProperty_of_quasiFiniteAt` and the `G`-ring owner
  `IsGRing`;
- derived API: the geometric-regularity specializations in this file.

Layering:
- clauses (1) and (2) are `source-facing` specializations;
- the `FieldAlgebraProperty` transfer theorems are the `core/canonical` owner;
- the geometric-regularity specialization is a `bridge/view`.
-/

section

variable {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R']

-- Proof sketch: use Lemma `10.124.3` to split `R̂_[p] ⊗[R] R'` as `R̂_[p'] × B` under the
-- quasi-finite hypothesis at `p'`. After tensoring with `κ(q')`, the target formal fibre becomes
-- a direct factor of the base change of the source formal fibre along `κ(q) → κ(q')`. Then apply
-- stability of geometric regularity under field extension from Lemma `10.166.1`.
/-- Lemma 15.50.3 (1): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
`q' ⊆ p'` lies over `q`, the map is quasi-finite at `p'`, and the formal fibre
`(R_p)^∧ ⊗[R] κ(q)` is geometrically regular over `κ(q)`, then the formal fibre
`(R'_(p'))^∧ ⊗[R'] κ(q')` is geometrically regular over `κ(q')`. -/
theorem completed_localization_formalFiber_isGeometricallyRegular_of_quasiFiniteAt
    (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R R') q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hgeom :
      IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) :
    IsGeometricallyRegular q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p'])) := by
  simpa [IsGeometricallyRegularProperty] using
    completed_localization_formalFiber_hasProperty_of_quasiFiniteAt
      IsGeometricallyRegularProperty p q p' q' hp hq hqp' hgeom

-- Proof sketch: specialize the prime-pair companion of the generic quasi-finite transfer theorem
-- from `Lemma_15_51_3` to the field-algebra property `IsGeometricallyRegular`.
/-- Lemma 15.50.3 (2): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
the map is quasi-finite at `p'`, and every formal fibre of `R_p` is geometrically regular, then
every formal fibre of `R'_(p')` is geometrically regular. -/
theorem completed_localization_formalFibers_areGeometricallyRegular_of_quasiFiniteAt
    (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hgeom :
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
        IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) :
    ∀ q' : PrimeSpectrum R', q'.asIdeal ≤ p'.asIdeal →
      IsGeometricallyRegular q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p'])) := by
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  exact
    (isPRing_localizationAtPrime_iff p').1 <|
      completed_localization_formalFibers_haveProperty_of_quasiFiniteAt
        IsGeometricallyRegularProperty p p' hp <|
          (isPRing_localizationAtPrime_iff p).2 hgeom

end

-- Proof sketch: a quasi-finite finite-type algebra over a Noetherian ring is again Noetherian.
-- For each prime `p'` of `R'`, let `p` be its image in `R`. The `G`-ring hypothesis on `R`
-- says that every formal fibre of `R_p` is geometrically regular. Apply clause (2) to the local
-- map `R_p → R'_(p')` to obtain geometric regularity of every formal fibre of `R'_(p')`, which
-- is exactly the defining condition for `R'` to be a `G`-ring.
/-- Lemma 15.50.3 (3): if `R → R'` is quasi-finite and `R` is a `G`-ring, then `R'` is a
`G`-ring. -/
theorem isGRing_of_quasiFinite
    {R : Type u} {R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    [Algebra.FiniteType R R'] [Algebra.QuasiFinite R R'] [IsGRing R] :
    IsGRing R' := by
  have hGR : IsGRing R := inferInstance
  letI : IsNoetherianRing R := hGR.toIsNoetherian
  letI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  exact
    (isGRing_iff_isPRing_isGeometricallyRegularProperty R').2 <|
      isPRing_of_quasiFinite IsGeometricallyRegularProperty <|
        (isGRing_iff_isPRing_isGeometricallyRegularProperty R).1 hGR

/-! ### Lemma_15_50_4 (from Chap15) -/
open Algebra

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: `G`-rings and regularity of formal fibres under finite free base change;
- sampled owner declarations:
  `Ideal.Fiber`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`,
  `isGRing_of_finiteType`,
  `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv`;
- best owner abstraction: the chapter owner `IsGRing`, with the source-facing finite-free
  regular-formal-fibre criterion as the theorem surface and the canonical fiber owner
  `Ideal.Fiber`; Lemma `15.50.2` is only the bridge to geometric regularity;
- primitive data: the Noetherian ring `R` and a finite free `R`-algebra `S`;
- derived API: the owner-level companion criterion `IsGRing S`.

Layering:
- the numbered lemma is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
-- Proof sketch: for the forward implication, finite free algebras are finite type, so the
-- source-facing finite-type transfer theorem `isGRing_of_finiteType` makes every such algebra a
-- `G`-ring; Lemma
-- `15.50.2` then upgrades each formal fibre to geometric regularity, hence to ordinary
-- regularity. Conversely, to prove that `R` is a `G`-ring it is enough by Lemma `15.50.2` to show
-- geometric regularity of each formal fibre of `R`. By Definition `10.166.2`, that geometric
-- regularity is tested after finite purely inseparable residue-field extensions, and
-- `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv` realizes those extensions by
-- finite free algebras. The resulting formal fibres of the finite free algebra localize the
-- corresponding tensor base changes of the original formal fibre, so the assumed regularity of all
-- finite-free formal fibres forces the needed geometric regularity.
/-- Lemma 15.50.4: for a Noetherian commutative ring `R`, `R` is a `G`-ring if and only if every
finite free `R`-algebra has regular formal fibre rings. -/
theorem isGRing_iff_forall_finiteFree :
    IsGRing R ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
        (p q : PrimeSpectrum S) (hqp : q.asIdeal ≤ p.asIdeal),
          IsRegularRing (q.asIdeal.Fiber (R̂_[p])) := by
  refine ⟨?_, ?_⟩
  · intro hR S _ _ _ _ p q hqp
    letI : IsGRing R := hR
    letI : Algebra.FiniteType R S := Module.Finite.finiteType S
    have hS : IsGRing S := by
      exact isGRing_of_finiteType R
    letI : IsGRing S := hS
    letI : IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) :=
      (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular S).1 hS p q hqp
    exact isRegularRing_of_isGeometricallyRegular q.asIdeal.ResidueField
      (q.asIdeal.Fiber (R̂_[p]))
  · intro hfiniteFree
    refine (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular R).2 ?_
    intro p q hqp
    rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
    intro K _ _ _ _
    obtain ⟨S, _, _, _, _, hqSPrime, hqSLiesOver, hResidue⟩ := by
      simpa using
        (exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv q.asIdeal K)
    letI : (q.asIdeal.map (algebraMap R S)).IsPrime := hqSPrime
    letI : (q.asIdeal.map (algebraMap R S)).LiesOver q.asIdeal := hqSLiesOver
    rcases hResidue with ⟨eK⟩
    let _ :
        (q.asIdeal.map (algebraMap R S)).ResidueField ≃ₐ[q.asIdeal.ResidueField] K := eK
    sorry

end

/-! ### Lemma_15_50_5 (from Chap15) -/
open scoped TensorProduct
open Algebra

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]
variable (n : ℕ)

local notation "A" => mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable (𝔭 : PrimeSpectrum A)

/- Domain triage:
- primary domain: mixed power-series/polynomial rings, completed localizations, and geometric
  regularity of generic formal fibers in commutative algebra;
- sampled owner declarations:
  `mixedPowerSeriesPolynomialRing`,
  `CompletedLocalizationAtPrime`,
  `IsGeometricallyRegular`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: this numbered lemma is `source-facing`, while the public surface should
  use the canonical chapter owners `mixedPowerSeriesPolynomialRing` and `R̂_[𝔭]`; the prime-pair
  formal-fiber criterion from Lemma `15.50.2` is only a `bridge/view`;
- primitive data: the ambient ring
  `A = mixedPowerSeriesPolynomialRing (Fin n) (Fin n) k`, a fraction field `K` of `A`, and a
  prime `𝔭 : Spec A`;
- derived API: geometric regularity of the generic formal fiber `R̂_[𝔭] ⊗[A] K`.
-/
-- Proof sketch: use the characteristic-`p` criterion for geometric regularity over the field `K`
-- by testing finite purely inseparable extensions `L/K`. Realize such an `L` as the fraction
-- field of a finite purely inseparable extension of the mixed power-series/polynomial ring,
-- reduce by induction to the degree-`p` case, identify the base change of the completed
-- localization with an `AdjoinRoot (X ^ p - f)` over a regular intermediate ring, and then apply
-- the derivation-extension and regularity criteria from Lemmas `15.48.1`, `15.48.4`, and
-- `15.48.5`.
/-- Lemma 15.50.5: let `A = k[[x_1, ..., x_n]][y_1, ..., y_n]` over a field `k` of
characteristic `p`, and let `K` be a fraction field of `A`. For every prime `𝔭` of `A`, the
generic formal fiber `(A_𝔭)^∧ ⊗[A] K` is geometrically regular over `K`. -/
theorem mixedPowerSeriesPolynomialRing_formalFiber_fractionRing_isGeometricallyRegular
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    : IsGeometricallyRegular K (R̂_[𝔭] ⊗[A] K) := sorry

end

end

/-! ### Proposition_15_50_6 (from Chap15) -/
universe u

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Domain triage:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: the chapter owner predicate `IsGRing`, with the completed localization
  owner `R̂_[p]` and the prime-pair criterion from Lemma `15.50.2` only as supporting bridge API;
- primitive data: the ring `R` together with the Noetherian and complete-local hypotheses;
- derived API: the formal-fiber regularity statements used to prove the owner instance below.

Layering:
- this proposition is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
/-- Proposition 15.50.6: a Noetherian complete local ring is a `G`-ring. -/
-- Proof sketch: by Lemma `15.50.2`, it is enough to check geometric regularity of the formal
-- fibres over minimal primes. Quotient by a minimal prime to reduce to the domain case, choose a
-- regular complete local subring from Cohen structure, descend the `G`-ring property along the
-- resulting finite quasi-finite map using Lemma `15.50.3`, and then handle the regular complete
-- local source by the characteristic-zero regularity argument together with the positive
-- characteristic power-series case from Lemma `15.50.5`.
instance : IsGRing R := sorry

end

/-! ### Lemma_15_50_7 (from Chap15) -/
open Algebra

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: `G`-rings, formal fibers, and locality at maximal ideals in Noetherian
  commutative algebra;
- sampled owner declarations:
  `IsGRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `Algebra.IsGeometricallyRegularProperty`,
  `LocalFormalFibersHaveProperty`,
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- best owner abstraction: the source-facing theorem remains about `IsGRing`, but the canonical
  owner layer underneath is `IsPRing Algebra.IsGeometricallyRegularProperty`; the maximal-ideal
  formulation should therefore reuse the public owner API
  `isGRing_iff_localFormalFibersHaveProperty` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal` instead of duplicating it locally;
- primitive data: only the Noetherian commutative ring `R`;
- derived API: the `P`-ring and local-formal-fiber reformulations of the `G`-ring condition.

Layering:
- `isGRing_iff_forall_localizationAtMaximal_isGRing` is `source-facing`;
- `IsGRing` and `IsPRing Algebra.IsGeometricallyRegularProperty` are the `core/canonical`
  owners;
- the maximal-localization formulation is the `bridge/view`, mediated by
  `LocalFormalFibersHaveProperty`.
-/
-- Proof sketch: specialize the canonical maximal-ideal criterion for `P`-rings from
-- `Lemma_15_51_4` to the field-algebra property `IsGeometricallyRegularProperty`. The auxiliary
-- owner `LocalFormalFibersHaveProperty` on each local ring `R_𝔪` is equivalent to `IsGRing R_𝔪`
-- by the public owner bridge `isGRing_iff_localFormalFibersHaveProperty`.
/-- Lemma 15.50.7: for a Noetherian ring `R`, `R` is a `G`-ring if and only if every localization
`R_𝔪` at a maximal ideal is a `G`-ring, equivalently every `R_𝔪` has geometrically regular formal
fibers. -/
theorem isGRing_iff_forall_localizationAtMaximal_isGRing :
    IsGRing R ↔ ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := by
  have hlocal :
      IsPRing Algebra.IsGeometricallyRegularProperty R ↔
        ∀ m : MaximalSpectrum R,
          LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty
            (Localization.AtPrime m.asIdeal) :=
    isPRing_iff_localFormalFibersHaveProperty_atMaximal
      Algebra.IsGeometricallyRegularProperty
  have hmax :
      (∀ m : MaximalSpectrum R,
        LocalFormalFibersHaveProperty Algebra.IsGeometricallyRegularProperty
          (Localization.AtPrime m.asIdeal)) ↔
      ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := by
    constructor
    · intro h m
      exact
        (isGRing_iff_localFormalFibersHaveProperty
          (Localization.AtPrime m.asIdeal)).2 (h m)
    · intro h m
      exact
        (isGRing_iff_localFormalFibersHaveProperty
          (Localization.AtPrime m.asIdeal)).1 (h m)
  exact (isGRing_iff_isPRing_isGeometricallyRegularProperty R).trans hlocal |>.trans hmax

end

/-! ### Lemma_15_50_8 (from Chap15) -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsGRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: local commutative algebra of `G`-rings under henselization and strict
  henselization;
* sampled owner declarations of the same kind:
  `IsGRing`,
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `isGRing_iff_forall_localizationAtMaximal_isGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
* best owner abstraction: `IsGRing` is the `core/canonical` owner, while
  `IsHenselizationOf` / `IsStrictHenselizationOf` provide only the ambient chosen algebra
  objects; this file should therefore contribute canonical instances for those owners rather than
  parallel named wrapper theorems;
* primitive data: the local `G`-ring `R` together with a chosen henselization or strict
  henselization;
* derived API: the transferred `IsGRing` instances on those canonical algebra objects.

Source/core/bridge triage:
* `source-facing`: the two transferred `G`-ring assertions from Lemma 15.50.8;
* `core/canonical`: `IsGRing`;
* `bridge/view`: the henselization owners and the local-maximal-ideal criterion from
  Lemma `15.50.7`.
-/
-- Proof sketch: by Lemma `15.50.7`, it suffices to check that each localization of `Rh` at a
-- maximal ideal is a `G`-ring. For a prime of `Rh` over `p ⊂ R`, Lemma `15.45.13` identifies the
-- residue-field extension as separable algebraic over `κ(p)`, Lemma `15.45.3` identifies the
-- completion of `Rh` with the completion of `R`, and Algebra Lemma `10.166.6` transfers
-- geometric regularity of the formal fiber from `κ(p)` to the residue field upstairs.
/-- Lemma 15.50.8 (1): if `R` is a Noetherian local `G`-ring, then any henselization `Rh` of `R`
is a `G`-ring. -/
instance : IsGRing Rh := sorry

-- Proof sketch: again use Lemma `15.50.7` to reduce to the local criterion. For a prime of a
-- strict henselization over `p ⊂ R`, Lemma `15.45.13` gives a separable algebraic residue-field
-- extension over `κ(p)`. Lemma `15.45.3` and Proposition `15.49.2` show that the completion map
-- from `R^∧` to `(R^sh)^∧` is regular, and Lemma `15.41.4` then propagates regularity to the
-- formal fibers over `κ(p)`. Algebra Lemma `10.166.6` upgrades this to geometric regularity over
-- the residue field of the prime of `R^sh`.
/-- Lemma 15.50.8 (2): if `R` is a Noetherian local `G`-ring, then any strict henselization `Rsh`
of `R` is a `G`-ring. -/
instance : IsGRing Rsh := sorry

end

/-! ### Lemma_15_50_9 (from Chap15) -/
open Algebra IsLocalRing
open scoped Polynomial

universe u

section

variable {A : Type u} [CommRing A]

local instance polynomial_isGRing [IsGRing A] : IsGRing A[X] :=
  by
    exact isGRing_of_finiteType A

/- Domain-style sampling:
- primary domain: `G`-rings, completed localizations, and geometric regularity of formal fibers in
  the polynomial case over a Noetherian complete local base;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_of_finiteType`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`;
- best owner abstraction: `IsGRing` is the `core/canonical` owner for the proof route, while the
  numbered lemma itself is the `source-facing` maximal/prime-pair specialization in `A[X]`;
- primitive data for the source-facing theorem: a Noetherian complete local ring `A`, a maximal
  ideal `q : MaximalSpectrum A[X]`, and a prime `r : PrimeSpectrum A[X]` with
  `r ⊆ q`;
- derived API: geometric regularity of the formal fiber
  `r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])`;
- the proof should reuse the finite-type transfer theorem `isGRing_of_finiteType` and the prime-pair
  criterion from Lemma `15.50.2` directly, rather than keeping a parallel local specialization.
-/
/-- Lemma 15.50.9: for a Noetherian complete local ring `A`, every prime pair `r ⊆ q` in `A[X]`
with `q` maximal has geometrically regular formal fiber
`r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])` over `κ(r)`.

In the source's positive-characteristic complete-local-domain situation, the extra hypotheses are
already absorbed by the canonical `IsGRing` instance on Noetherian complete local rings, so the
public statement keeps only the genuine inputs used by the owner-level transfer
`isGRing_of_finiteType` together with the prime-pair criterion from Lemma `15.50.2`. -/
theorem polynomial_completedLocalization_formalFiber_isGeometricallyRegular
    [IsNoetherianRing A] [IsCompleteLocalRing A]
    (q : MaximalSpectrum A[X]) (r : PrimeSpectrum A[X])
    (hr_le : r.asIdeal ≤ q.asIdeal) :
    IsGeometricallyRegular r.asIdeal.ResidueField
      (r.asIdeal.Fiber (R̂_[q.toPrimeSpectrum])) := by
  exact
    (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular A[X]).1
      (inferInstance : IsGRing A[X]) q.toPrimeSpectrum r hr_le

end

/-! ### Proposition_15_50_10 (from Chap15) -/
universe u v

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S]

/- Domain triage:
- primary domain: permanence of `G`-rings under essentially finite type algebra maps in
  commutative algebra;
- sampled owner declarations:
  `IsGRing`,
  `IsPRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `isPRing_of_essFiniteType`;
- best owner abstraction: the source-facing `G`-ring proposition should be a thin specialization of
  the canonical owner theorem `isPRing_of_essFiniteType` through the bridge
  `IsGRing R ↔ IsPRing Algebra.IsGeometricallyRegularProperty R`, rather than a parallel
  typeclass-driven wrapper;
- primitive data: commutative rings `R` and `S`, an `R`-algebra structure on `S`, an essentially
  finite type hypothesis, and the owner hypothesis `[IsGRing R]`;
- derived API: the resulting owner assertion `IsGRing S`.

Source/core/bridge triage:
- `source-facing`: the permanence statement for `G`-rings;
- `core/canonical`: `IsGRing`, `IsPRing`, and `isPRing_of_essFiniteType`;
- `bridge/view`: `isGRing_iff_isPRing_isGeometricallyRegularProperty`.
-/
-- Proof sketch: specialize the generic essentially-finite-type permanence theorem for `P`-rings
-- to the field-algebra property `Algebra.IsGeometricallyRegularProperty`, then translate back
-- through the canonical owner bridge `IsGRing ↔ IsPRing Algebra.IsGeometricallyRegularProperty`.
/-- Proposition 15.50.10: an essentially finite type algebra over a `G`-ring is again a
`G`-ring. -/
theorem isGRing_of_essFiniteType [IsGRing R] :
    IsGRing S := sorry

end

/-! ### Remark_15_50_11 (from Chap15) -/
universe u

section

/- 
Domain sampling:
* Primary domain: commutative algebra of `G`-rings and adic completion.
* Owner declarations inspected in this domain:
  - `IsGRing`
  - `CompletedLocalizationAtPrime`
  - `isGRing_iff_forall_regular_localization_completion`
  - `AdicCompletion`
* Best owner abstraction: the chapter owner predicate `IsGRing R` on a commutative ring `R`,
  together with the canonical completion owner `AdicCompletion I R`.
* Source/core/bridge triage:
  - `source-facing`: adic completion does not preserve the `G`-ring property in general;
  - `core/canonical`: `IsGRing R` and `AdicCompletion I R`;
  - `bridge/view`: the existential counterexample formulation below.
* Primitive vs. derived: the primitive data are the commutative ring `R` and the ideal `I : Ideal R`;
  the facts that `R` is a `G`-ring and `AdicCompletion I R` is not are derived properties and should
  not be presented as separate primitive existential data.
-/

-- Proof sketch: use the counterexample cited in the remark, due to Nishimura and generalized by
-- Dumitrescu. It gives a `G`-ring `R` together with an ideal `I ⊆ R` whose `I`-adic completion is
-- not again a `G`-ring.
/-- Companion existential counterexample form of Remark 15.50.11. -/
theorem exists_gRing_ideal_with_adicCompletion_not_gRing :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      IsGRing R ∧ ¬ IsGRing (AdicCompletion I R) := sorry

/-- Remark 15.50.11: adic completion does not preserve the `G`-ring property in general. -/
theorem adicCompletion_not_preserves_isGRing :
    ¬ ∀ (R : Type u) (_ : CommRing R) (I : Ideal R), IsGRing R → IsGRing (AdicCompletion I R) := by
  intro h
  obtain ⟨R, hR, I, hGR, hnotGR⟩ := exists_gRing_ideal_with_adicCompletion_not_gRing
  exact hnotGR (h R hR I hGR)

end

/-! ### Proposition_15_50_12 (from Chap15) -/
universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of `G`-rings and their permanence properties;
- sampled owner declarations of the same kind:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `isGRing_of_essFiniteType`,
  the complete-local `IsGRing` instance from Proposition `15.50.6`;
- best owner abstraction: the chapter owner class `IsGRing`;
- primitive vs. derived:
  the primitive public data are the ambient ring/algebra hypotheses in each source clause;
  the field and complete-local examples are direct owner recall, the Dedekind-domain clause is a
  source-facing owner instance, and the finite-type clause is only a thin source-facing
  specialization of the canonical essentially-finite-type transfer theorem.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain and finite-type clauses recorded in this proposition;
- `core/canonical`: `IsGRing` and `isGRing_of_essFiniteType`;
- `bridge/view`: the finite-type specialization and the `ℤ` specialization of the
  Dedekind-domain characteristic-zero instance.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.50.12: fields are `G`-rings. This is the canonical field instance from
Definition `15.50.1`. -/
#check (inferInstance : IsGRing K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.50.12: a Noetherian complete local ring is a `G`-ring. This is the
canonical instance supplied by Proposition `15.50.6`. -/
#check (inferInstance : IsGRing R)

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

-- Proof sketch: a Dedekind domain is Noetherian and has Krull dimension at most `1`. Localizing
-- at a nonzero prime gives a discrete valuation ring, whose completion is again a discrete
-- valuation ring, so the defining formal fibres are geometrically regular; the zero prime gives
-- the fraction field case.
/-- Proposition 15.50.12: a Dedekind domain whose fraction field has characteristic zero is a
`G`-ring. -/
instance isGRing_of_isDedekindDomain_of_fractionRing_charZero : IsGRing R := sorry

end

section

/- Proposition 15.50.12: the ring of integers `ℤ` is a `G`-ring, by the
Dedekind-domain characteristic-zero instance above. -/
#check (inferInstance : IsGRing ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras are essentially finite type, so this is the finite-type
-- specialization of Proposition `15.50.10`.
/-- Proposition 15.50.12: a finite type algebra over a `G`-ring is again a `G`-ring. -/
theorem isGRing_of_finiteType [IsGRing R] [Algebra.FiniteType R S] : IsGRing S := by
  letI : Algebra.EssFiniteType R S := inferInstance
  exact isGRing_of_essFiniteType R

end

/-! ### Lemma_15_50_13 (from Chap15) -/
universe u

section

variable (A : Type u) [CommRing A]

variable [HenselianLocalRing A]

/- Domain-style sampling:
- primary domain: henselian local rings, `G`-rings, and filtered direct limits in commutative
  algebra;
- sampled owner declarations:
  `HenselianLocalRing`,
  `IsGRing`,
  `Ring.DirectLimit`,
  `directedSystem_directLimit_henselianLocalRing`;
- best owner abstraction: the stagewise notions are already owned canonically by
  `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`; there is no reusable
  chapter owner for the full filtered-colimit presentation, so the source-facing item should be
  the explicit existential theorem rather than a one-off wrapper `Prop`;
- primitive data: the filtered index type, stage rings, transition maps, their local-hom
  property, and the direct-limit comparison isomorphism to `A`;
- derived API: henselianity of the direct limit is already owned upstream by
  `directedSystem_directLimit_henselianLocalRing`.

Source/core/bridge triage:
- `source-facing`: `exists_filtered_colimit_of_henselian_local_grings`;
- `core/canonical`: `HenselianLocalRing`, `IsGRing`, `IsLocalHom`, and `Ring.DirectLimit`;
- `bridge/view`: the chosen filtered diagram and comparison isomorphism presenting `A` as that
  direct limit.
-/

-- Proof sketch: write `A` as a filtered colimit of finite type `ℤ`-algebras, localize each stage
-- at the prime lying under the maximal ideal of `A`, and use Proposition `15.50.12` to make those
-- localized stages into local `G`-rings. Lemma `15.12.5` identifies the henselization of `A` with
-- the filtered colimit of the henselizations of the stages, and Lemma `15.50.8` shows those
-- henselizations are again `G`-rings.
/-- Lemma 15.50.13: a henselian local ring is a filtered colimit of a directed system of henselian
local `G`-rings with local transition maps. -/
theorem exists_filtered_colimit_of_henselian_local_grings :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirectedOrder ι)
      (stage : ι → Type u) (_ : ∀ i : ι, CommRing (stage i))
      (_ : ∀ i : ι, HenselianLocalRing (stage i))
      (_ : ∀ i : ι, IsGRing (stage i))
      (map : ∀ i j : ι, i ≤ j → stage i →+* stage j)
      (_ : DirectedSystem stage (fun i j hij ↦ map i j hij))
      (e : Ring.DirectLimit stage (fun i j hij ↦ map i j hij) ≃+* A),
      ∀ i j (hij : i ≤ j), IsLocalHom (map i j hij) := by
  sorry

end

/-! ### Lemma_15_50_14 (from Chap15) -/
namespace Algebra

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/- Domain-style sampling:
* primary domain: regular ring maps, `G`-rings, and adic completions in commutative algebra;
* sampled owner declarations of the same kind:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `IsRegularRingMap`,
  `isRegularRingMap_local_tfae`;
* best owner abstraction: the numbered item is a `bridge/view` recall, with `IsGRing` and
  `IsRegularRingMap` as the core/canonical owners;
* bridge/view: localization of `A → AdicCompletion I A` at maximal ideals of the completion,
  compared with the canonical completion maps already packaged by `IsGRing`.

Primitive data are only the ring `A`, the ideal `I`, and the owner hypothesis `[IsGRing A]`. The
maximal-ideal localization/completion comparisons are derived implementation detail and should not
be promoted to a separate public wrapper. The canonical owner-level bridge is the instance
`(algebraMap A (AdicCompletion I A)).IsRegularRingMap`, so the numbered item should be a direct
recall of that bridge rather than a second exact-interface theorem.
-/
-- Proof sketch: use the local criterion `isRegularRingMap_local_tfae` for the map
-- `A → AdicCompletion I A`. For a maximal ideal `m'` of `AdicCompletion I A` lying over
-- `m ⊂ A`, compare the localized map `A_m → (AdicCompletion I A)_(m')` with the canonical
-- completion map `A_m → CompletedLocalizationAtPrime m`. The latter is exactly the owner field
-- `IsGRing.regular_localization_completion m`, and the faithfully flat comparison from
-- `(AdicCompletion I A)_(m')` to its maximal-ideal completion lets one descend regularity back to
-- `A_m → (AdicCompletion I A)_(m')`.
/-- The canonical owner-level bridge: the `I`-adic completion map of a `G`-ring is regular. -/
instance [IsGRing A] : (algebraMap A (AdicCompletion I A)).IsRegularRingMap := by
  sorry

variable [IsGRing A]

/- Lemma 15.50.14: if `A` is a `G`-ring and `A^∧` is the `I`-adic completion of `A`, then the
canonical map `A → A^∧` is regular. This is the canonical instance above. -/
#check (inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)

end

end Algebra

/-! ### Lemma_15_50_15 (from Chap15) -/
open Algebra
open RingPairCat

universe u

section

variable {A : Type u} [CommRing A] [IsGRing A]
variable (I : Ideal A)

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/- Domain triage:
- primary domain: `G`-rings and the canonical pair-henselization owner in Chapter 15;
- sampled owner declarations:
  `IsGRing`,
  `isGRing_iff_isPRing_isGeometricallyRegularProperty`,
  `RingPairCat.henselizationRing`,
  `isPRing_henselizationRing`;
- best owner abstraction: the source-facing `G`-ring statement should reuse the canonical
  `P`-ring permanence theorem `isPRing_henselizationRing`, specialized to
  `Algebra.IsGeometricallyRegularProperty` through its Chapter 15 owner instances, rather than
  carrying a parallel local proof shell;
- primitive data: a commutative ring `A`, an ideal `I`, and the owner hypothesis `[IsGRing A]`;
- derived API: the `G`-ring instance on `henselizationRing (pairOfIdeal I)`.

Source/core/bridge triage:
- `source-facing`: the `G`-ring permanence statement for pair henselizations;
- `core/canonical`: `IsGRing`, `IsPRing`, and the pair-henselization owner
  `henselizationRing (pairOfIdeal I)`;
- `bridge/view`: the equivalence
  `isGRing_iff_isPRing_isGeometricallyRegularProperty` together with the separable-base-field
  invariance `isGeometricallyRegular_iff_of_isSeparable`. -/
/-- Lemma 15.50.15: if `A` is a `G`-ring and `(A^h, I^h)` is the chosen henselization of the pair
`(A, I)`, then the henselization ring `A^h` is a `G`-ring. -/
instance pairHenselization_isGRing :
    IsGRing (henselizationRing (pairOfIdeal I)) := by
  refine
    (isGRing_iff_isPRing_isGeometricallyRegularProperty
      (henselizationRing (pairOfIdeal I))).2 ?_
  refine
    isPRing_henselizationRing
      I
      IsGeometricallyRegularProperty
      ((isGRing_iff_isPRing_isGeometricallyRegularProperty A).1 inferInstance)

end
