import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing Polynomial
open scoped TensorProduct

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

local notation "κ" => ResidueField R

/-
Domain-style sampling:
- primary domain: henselian local rings and their source-facing factorization, étale-neighborhood,
  and finite-type decomposition criteria;
- sampled owner and bridge declarations in this domain:
  `HenselianLocalRing`,
  `HenselianLocalRing.TFAE`,
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`,
  and the chapter recall `Definition 10.153.1`;
- best owner abstraction:
  the core owner is `HenselianLocalRing R`;
  this file is `source-facing` because Lemma `10.153.3` records the larger textbook `List.TFAE`,
  while the later factorization and étale clauses are bridge criteria around that owner;
- primitive data vs. derived API:
  the owner predicate `HenselianLocalRing R` is primitive at the canonical layer,
  the nonmonic simple-root condition and the decomposition predicates are source-facing criteria,
  while any extracted equivalences back to `HenselianLocalRing` are derived bridge API.

Source/core/bridge triage:
- `source-facing`: the 13-way `List.TFAE` and the nonmonic simple-root lifting clause;
- `core/canonical`: `HenselianLocalRing`;
- `bridge/view`: the coprime-factorization, étale-retraction, and decomposition clauses.

The sampled owner theorem `HenselianLocalRing.TFAE` already provides the canonical monic
simple-root criterion. The present file keeps the textbook nonmonic formulation as
source-facing content rather than replacing it by a second owner-level wrapper.
-/

/-- The condition that simple roots of arbitrary residue polynomials lift to roots in `R`. -/
def simple_root_lift_property : Prop :=
  ∀ f : R[X], ∀ a0 : κ,
    aeval a0 f = 0 →
    aeval a0 (f.derivative) ≠ 0 →
    ∃ a : R, f.IsRoot a ∧ residue R a = a0

/-- The condition that coprime factorizations of monic residue polynomials lift to factorizations
of the original monic polynomial. -/
def monic_coprime_factorization_lift_property : Prop :=
  ∀ f : R[X], f.Monic →
    ∀ g0 h0 : κ[X],
      f.map (residue R) = g0 * h0 →
      IsCoprime g0 h0 →
      ∃ g h : R[X],
        f = g * h ∧
        g.map (residue R) = g0 ∧
        h.map (residue R) = h0

/-- The condition that monic coprime factorizations of residue polynomials lift with the degree of
the chosen factor preserved. -/
def monic_coprime_factorization_lift_with_degree_property : Prop :=
  ∀ f : R[X], f.Monic →
    ∀ g0 h0 : κ[X],
      f.map (residue R) = g0 * h0 →
      IsCoprime g0 h0 →
      ∃ g h : R[X],
        f = g * h ∧
        g.map (residue R) = g0 ∧
        h.map (residue R) = h0 ∧
        g.natDegree = g0.natDegree

/-- The condition that coprime factorizations of residue polynomials lift for arbitrary
polynomials. -/
def coprime_factorization_lift_property : Prop :=
  ∀ f : R[X],
    ∀ g0 h0 : κ[X],
      f.map (residue R) = g0 * h0 →
      IsCoprime g0 h0 →
      ∃ g h : R[X],
        f = g * h ∧
        g.map (residue R) = g0 ∧
        h.map (residue R) = h0

/-- The condition that arbitrary coprime factorizations of residue polynomials lift with degree
control on one factor. -/
def coprime_factorization_lift_with_degree_property : Prop :=
  ∀ f : R[X],
    ∀ g0 h0 : κ[X],
      f.map (residue R) = g0 * h0 →
      IsCoprime g0 h0 →
      ∃ g h : R[X],
        f = g * h ∧
        g.map (residue R) = g0 ∧
        h.map (residue R) = h0 ∧
        g.natDegree = g0.natDegree

/-- The condition that every étale neighbourhood with the same residue field above the maximal
ideal admits an `R`-algebra retraction to `R`. -/
def etale_retraction_exists_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal),
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq) →
      Nonempty (S →ₐ[R] R)

/-- The condition that every étale neighbourhood with the same residue field above the maximal
ideal admits a unique retraction whose inverse image of the maximal ideal is the chosen prime. -/
def etale_retraction_unique_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal),
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq) →
      ∃! τ : S →ₐ[R] R, q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R)

/-- A commutative ring is a product of local rings if it is ring-isomorphic to a product of local
commutative rings indexed by a finite type. -/
def has_local_ring_product_decomposition (S : Type v) [CommRing S] : Prop :=
  ∃ (ι : Type v) (_ : Finite ι) (A : ι → Type v)
    (instAComm : ∀ i, CommRing (A i))
    (instALocal : ∀ i, IsLocalRing (A i)),
    letI : ∀ i, CommRing (A i) := instAComm
    letI : ∀ i, IsLocalRing (A i) := instALocal
    Nonempty (S ≃+* ∀ i, A i)

/-- A commutative ring is a finite product of local rings if it is ring-isomorphic to a finite
cartesian product of local commutative rings. -/
def has_finite_local_ring_product_decomposition (S : Type v) [CommRing S] : Prop :=
  ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type v)
    (instAComm : ∀ i, CommRing (A i))
    (instALocal : ∀ i, IsLocalRing (A i)),
    letI : ∀ i, CommRing (A i) := instAComm
    letI : ∀ i, IsLocalRing (A i) := instALocal
    Nonempty (S ≃+* ∀ i, A i)

/-- Every irreducible component of the special fiber has dimension at least `1`, expressed through
the local rings at the minimal primes of the fiber. -/
def special_fiber_minimal_primes_positive_dimensional
    (B : Type v) [CommRing B] [Algebra R B] : Prop :=
  ∀ p : PrimeSpectrum (κ ⊗[R] B),
    p.asIdeal ∈ minimalPrimes (κ ⊗[R] B) →
    1 ≤ ringKrullDim (Localization.AtPrime p.asIdeal)

/-- The condition that every finite `R`-algebra splits as a product of local rings. -/
def finite_algebra_local_product_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S],
    has_local_ring_product_decomposition S

/-- The condition that every finite `R`-algebra splits as a finite product of local rings. -/
def finite_algebra_finite_local_product_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S],
    has_finite_local_ring_product_decomposition S

/-- The condition that a finite type `R`-algebra splits into a finite part and a remainder that is
not quasi-finite at any prime above the maximal ideal. -/
def finite_type_algebra_split_finite_nonQuasiFinite_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        ∀ q : PrimeSpectrum B,
          maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal →
          ¬ Algebra.QuasiFiniteAt R q.asIdeal

/-- The condition that a finite type `R`-algebra splits into a finite part and a remainder whose
special fiber has only positive-dimensional irreducible components. -/
def finite_type_algebra_split_finite_positive_dimensional_fiber_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        special_fiber_minimal_primes_positive_dimensional R B

/-- The condition that a quasi-finite `R`-algebra splits into a finite part and a remainder with
zero special fiber. -/
def quasi_finite_algebra_split_finite_zero_special_fiber_property : Prop :=
  ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S],
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        Subsingleton (κ ⊗[R] B)

-- Proof sketch: combine the canonical henselian simple-root formulation with the standard
-- coprime-factorization lifting criteria, the étale-neighbourhood retraction characterizations,
-- and the finite / finite-type / quasi-finite decomposition criteria cited in the textbook.
/-- Lemma 10.153.3: for a local ring `R`, the following are equivalent: `R` is henselian; simple
roots over the residue field lift; coprime factorizations of residue polynomials lift in monic and
nonmonic forms, with or without degree control; étale neighborhoods with unchanged residue field
admit retractions; finite and finite-type `R`-algebras admit the indicated local-product
decompositions; and quasi-finite `R`-algebras split off a finite part with zero special-fiber
remainder. -/
theorem henselian_local_ring_tfae :
    List.TFAE
      [ HenselianLocalRing R
      , simple_root_lift_property R
      , monic_coprime_factorization_lift_property R
      , monic_coprime_factorization_lift_with_degree_property R
      , coprime_factorization_lift_property R
      , coprime_factorization_lift_with_degree_property R
      , etale_retraction_exists_property R
      , etale_retraction_unique_property R
      , finite_algebra_local_product_property R
      , finite_algebra_finite_local_product_property R
      , finite_type_algebra_split_finite_nonQuasiFinite_property R
      , finite_type_algebra_split_finite_positive_dimensional_fiber_property R
      , quasi_finite_algebra_split_finite_zero_special_fiber_property R
      ] := sorry

end
