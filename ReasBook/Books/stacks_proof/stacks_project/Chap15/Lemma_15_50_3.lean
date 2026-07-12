import StacksProject_2024.Chap15.Lemma_15_50_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

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
@[stacks 07PP]
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
@[stacks 07PP]
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
@[stacks 07PP]
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
