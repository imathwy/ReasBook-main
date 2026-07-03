import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_153_1 (from Chap10) -/
open IsLocalRing

universe u

section

/- Definition 10.153.1: the Stacks notion of a henselian local ring is the canonical mathlib
class `HenselianLocalRing`, characterized by Hensel lifting for simple roots in the residue
field. -/
#check HenselianLocalRing

variable (R : Type u) [CommRing R]

/-- A local ring is strictly henselian if it is henselian and its
residue field is separably algebraically closed. -/
class StrictHenselianLocalRing : Prop extends HenselianLocalRing R, IsSepClosed (ResidueField R)

variable (K : Type u) [Field K] [IsSepClosed K]

-- Proof sketch: a separably closed field is henselian by the canonical field instance, and its
-- residue field identifies with the field itself, so the strict henselian structure is the
-- expected one.
/-- A separably closed field is strictly henselian. -/
instance : StrictHenselianLocalRing K := by
  let e : ResidueField K ≃+* K :=
    (Ideal.quotEquivOfEq ((maximalIdeal K).eq_bot_of_prime)).trans (RingEquiv.quotientBot K)
  refine { toHenselianLocalRing := inferInstance, toIsSepClosed := ?_ }
  refine ⟨fun p hp ↦ ?_⟩
  refine Polynomial.Splits.of_splits_map e.toRingHom ?_ ?_
  · exact IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map
  · intro a ha
    exact ⟨e.symm a, by simp⟩

end

/-! ### Lemma_10_153_2 (from Chap10) -/
universe u

open IsLocalRing Polynomial

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

-- Proof sketch: write `f(a + (b - a)) - f(a)` as
-- `f.derivative.eval a * (b - a) + c * (b - a)^2`. Since `a ≡ b [SMOD maximalIdeal R]`,
-- the difference `b - a` lies in `maximalIdeal R`. The hypothesis
-- `f.derivative.eval a ∉ maximalIdeal R` makes `f.derivative.eval a` a unit in the local ring,
-- and then factoring out `b - a` shows the remaining factor is also a unit, forcing `b - a = 0`.
/-- Lemma 10.153.2: if `a` and `b` are roots of a polynomial over a local ring, are congruent
modulo the maximal ideal, and the derivative at `a` is not in the maximal ideal, then `a = b`. -/
lemma eq_of_polynomial_roots_congruent_of_derivative_not_mem_maximalIdeal
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (hab : a ≡ b [SMOD maximalIdeal R])
    (hder : f.derivative.eval a ∉ maximalIdeal R) :
    a = b := by
  let d := b - a
  have hd : d ∈ maximalIdeal R := SModEq.sub_mem.mp hab.symm
  obtain ⟨c, hc⟩ := binomExpansion f a d
  have hfactor : f.derivative.eval a * d + c * d ^ 2 = (f.derivative.eval a + c * d) * d := by
    dsimp [d]
    ring
  have hsum : 0 = f.derivative.eval a * d + c * d ^ 2 := by
    simpa [d, ha.eq_zero, hb.eq_zero, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hc
  have hrootEq : (f.derivative.eval a + c * d) * d = 0 := by
    rw [hfactor] at hsum
    exact hsum.symm
  have hunit_der : IsUnit (f.derivative.eval a) := notMem_maximalIdeal.mp hder
  have hunit : IsUnit (f.derivative.eval a + c * d) := by
    rw [← residue_ne_zero_iff_isUnit]
    have hd_res : residue R d = 0 := (residue_eq_zero_iff d).2 hd
    simpa [map_add, map_mul, hd_res] using
      (residue_ne_zero_iff_isUnit (f.derivative.eval a)).2 hunit_der
  have hd_zero : d = 0 := hunit.mul_right_eq_zero.mp hrootEq
  exact (sub_eq_zero.mp hd_zero).symm

end

/-! ### Lemma_10_153_3 (from Chap10) -/
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

/-! ### Lemma_10_153_4 (from Chap10) -/
universe u v

open IsLocalRing

/-
Domain-style sampling:
- primary domain: henselian local rings, finite and quasi-finite commutative algebra maps, and
  localization at primes over the maximal ideal;
- sampled owner declarations in this domain:
  `HenselianLocalRing`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.QuasiFinite`,
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFinite`;
- best owner abstraction:
  the core/canonical owners are `HenselianLocalRing` and the quasi-finite owners
  `Algebra.QuasiFiniteAt` / `Algebra.QuasiFinite`, while this file is source-facing where the
  Stacks wording explicitly bundles finite type together with those local/global quasi-finite
  hypotheses;
- primitive data vs. derived API:
  the primitive input is the henselian local base together with finite, local, or
  finite-type-quasi-finite algebra hypotheses; the local-henselian and finite-localization
  conclusions are derived API around those owners.

Source/core/bridge triage:
- `source-facing`: the finite-product decomposition and the henselian/finiteness conclusions for
  localizations over the maximal ideal;
- `core/canonical`: `HenselianLocalRing`, `Algebra.QuasiFiniteAt`, `Algebra.QuasiFinite`;
- `bridge/view`: the chapter source-facing finite-type packages
  `Algebra.FiniteType.QuasiFiniteAt` and `Algebra.FiniteType.QuasiFinite`, which this file should
  reuse instead of restating their component hypotheses separately.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: apply Lemma `10.153.3` to decompose a finite `R`-algebra into a finite product of
-- local rings. Each factor is finite over `R`, local, and hence henselian by the local case below.
/-- Lemma 10.153.4 (1): if `(R, 𝔪, κ)` is a henselian local ring and `R → S` is finite, then `S`
is a finite product of henselian local rings, each finite over `R`. -/
theorem exists_pi_algEquiv_henselianLocalRing_of_finite
    [HenselianLocalRing R] [Module.Finite R S] :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instAHenselian : ∀ i, HenselianLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i)),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, HenselianLocalRing (A i) := instAHenselian
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      Nonempty (S ≃ₐ[R] ∀ i, A i) := sorry

-- Proof sketch: localize the finite product decomposition from clause (1) at the unique maximal
-- ideal of `S`; only one factor survives, so a finite local `R`-algebra is one of the henselian
-- local factors occurring there.
/-- Lemma 10.153.4 (2): if `(R, 𝔪, κ)` is henselian, `R → S` is finite, and `S` is local, then
`S` is a henselian local ring. -/
theorem finite_local_henselianLocalRing
    [HenselianLocalRing R] [Module.Finite R S] [IsLocalRing S] :
    HenselianLocalRing S := sorry

-- Proof sketch: for a finite ring map between local rings, every element of `R` whose image in
-- `S` is a unit is already a unit in `R`; equivalently, the inverse image of the maximal ideal of
-- `S` is the maximal ideal of `R`.
/-- Lemma 10.153.4 (3): if `R → S` is a finite ring map and `S` is local, then `R → S` is a local
ring map. -/
theorem algebraMap_isLocalHom_of_finite_local
    [Module.Finite R S] [IsLocalRing S] :
    IsLocalHom (algebraMap R S) := sorry

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: use Lemma `10.153.3` to split `S` near the maximal ideal of `R` into a finite
-- part and a complementary part with no quasi-finite primes above `𝔪`; the chosen prime `q`
-- lies on the finite part, and its localization is then a local finite `R`-algebra, hence
-- henselian by clause (2).
/-- Lemma 10.153.4 (4): if `(R, 𝔪, κ)` is henselian, `R → S` is finite type, `q` lies over `𝔪`,
and `R → S` is quasi-finite at `q`, then `S_q` is henselian. -/
theorem localizationAtPrime_henselianLocalRing_of_quasiFiniteAt_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q.asIdeal) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: in the decomposition from the previous clause, the localization `S_q` is a
-- localization of the finite factor `A` at a maximal ideal, so it remains finite over `R`.
/-- Lemma 10.153.4 (5): if `(R, 𝔪, κ)` is henselian, `R → S` is finite type, `q` lies over `𝔪`,
and `R → S` is quasi-finite at `q`, then `S_q` is finite over `R`. -/
theorem moduleFinite_localizationAtPrime_of_quasiFiniteAt_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q.asIdeal) :
    Module.Finite R (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: a quasi-finite morphism is quasi-finite at every prime, so clause (4) applies to
-- each prime of `S` lying over the maximal ideal of `R`.
/-- Lemma 10.153.4 (6): if `(R, 𝔪, κ)` is henselian and `R → S` is quasi-finite, then `S_q` is
henselian for every prime `q` of `S` lying over `𝔪`. -/
theorem localizationAtPrime_henselianLocalRing_of_quasiFinite_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    HenselianLocalRing (Localization.AtPrime q.asIdeal) := sorry

-- Proof sketch: combine the global quasi-finite hypothesis with clause (5) at the chosen prime
-- `q` lying over the maximal ideal of `R`.
/-- Lemma 10.153.4 (7): if `(R, 𝔪, κ)` is henselian and `R → S` is quasi-finite, then `S_q` is
finite over `R` for every prime `q` of `S` lying over `𝔪`. -/
theorem moduleFinite_localizationAtPrime_of_quasiFinite_over_maximalIdeal
    [HenselianLocalRing R]
    (q : PrimeSpectrum S)
    (hq : Ideal.comap (algebraMap R S) q.asIdeal = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    Module.Finite R (Localization.AtPrime q.asIdeal) := sorry

end

/-! ### Lemma_10_153_5 (from Chap10) -/
open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [HenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-
Domain-style sampling:
- primary domain: henselian local rings, quasi-finite loci, and finite-type product decompositions;
- sampled owner declarations in the chapter/domain:
  `has_finite_local_ring_product_decomposition`,
  `finite_type_algebra_split_finite_nonQuasiFinite_property`,
  `henselian_local_ring_tfae`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction:
  the canonical owner for the first splitting step is
  `finite_type_algebra_split_finite_nonQuasiFinite_property R`,
  while the actual decomposition object is owned by `AlgEquiv`;
- primitive data:
  a finite type `R`-algebra `S`;
- derived API:
  the finite factor, the non-quasi-finite remainder, and the further finite-product decomposition
  of the finite factor into local finite `R`-algebras; the remainder clause is stated by the
  canonical owner `Algebra.QuasiFiniteAt`.

Source/core/bridge triage:
- `source-facing`: the theorem `finite_type_algebra_decomposition_henselian_local`, which keeps the
  textbook decomposition into explicit local finite factors indexed by a finite type;
- `core/canonical`: `finite_type_algebra_split_finite_nonQuasiFinite_property R`;
- `bridge/view`: the passage from that owner clause to the explicit `Fintype`-indexed product using
  `exists_pi_algEquiv_henselianLocalRing_of_finite`.
-/

-- Proof sketch: first use the canonical owner theorem
-- `henselian_local_ring_tfae` at clause `10` to split `S` as a finite `R`-algebra factor times a
-- remainder with no quasi-finite point over `maximalIdeal R`. Then apply
-- `exists_pi_algEquiv_henselianLocalRing_of_finite` to the finite factor and compose the two
-- `AlgEquiv`s at the same `Fintype`-indexed product level.
/-- Lemma 10.153.5: any finite type algebra over a henselian local ring decomposes as a finite
product of local finite `R`-algebras together with a remainder on which `R → B` is not
quasi-finite at any prime lying over the maximal ideal of `R`. -/
lemma finite_type_algebra_decomposition_henselian_local :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal := by
  have hsplit : finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R :=
    ((henselian_local_ring_tfae.{u, v, v, v, v, v, v, v} R).out 0 10 rfl rfl).mp
      (show HenselianLocalRing R from inferInstance)
  obtain ⟨A, _, _, _, B, _, _, ⟨eAB⟩, hB⟩ :=
    hsplit S
  have hAprod :
      ∃ (ι : Type v) (_ : Fintype ι) (A' : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A' i))
        (instAAlg : ∀ i, Algebra R (A' i))
        (instAHenselian : ∀ i, HenselianLocalRing (A' i))
        (instAFinite : ∀ i, Module.Finite R (A' i)),
        letI : ∀ i, CommRing (A' i) := instAComm
        letI : ∀ i, Algebra R (A' i) := instAAlg
        letI : ∀ i, HenselianLocalRing (A' i) := instAHenselian
        letI : ∀ i, Module.Finite R (A' i) := instAFinite
        Nonempty (A ≃ₐ[R] ∀ i, A' i) :=
    exists_pi_algEquiv_henselianLocalRing_of_finite
  obtain ⟨ι, instFintype, A', instAComm, instAAlg, instAHenselian, instAFinite, ⟨eA⟩⟩ :=
    hAprod
  letI : Fintype ι := instFintype
  letI : ∀ i, HenselianLocalRing (A' i) := instAHenselian
  refine ⟨ι, instFintype, A', instAComm, instAAlg, ?_, instAFinite, B,
    inferInstance, inferInstance, ?_⟩
  · intro i
    infer_instance
  · let instAComm' : ∀ i, CommRing (A' i) := instAComm
    let instAAlg' : ∀ i, Algebra R (A' i) := instAAlg
    let instALocal' : ∀ i, IsLocalRing (A' i) := fun i ↦ inferInstance
    let instAFinite' : ∀ i, Module.Finite R (A' i) := instAFinite
    letI : ∀ i, CommRing (A' i) := instAComm'
    letI : ∀ i, Algebra R (A' i) := instAAlg'
    letI : ∀ i, IsLocalRing (A' i) := instALocal'
    letI : ∀ i, Module.Finite R (A' i) := instAFinite'
    refine ⟨eAB.trans <| AlgEquiv.prodCongr eA (AlgEquiv.refl : B ≃ₐ[R] B), ?_⟩
    intro q hq
    exact hB q hq.symm

end

/-! ### Lemma_10_153_6 (from Chap10) -/
open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.FiniteType R S]

/-
Domain-style sampling:
- primary domain: strictly henselian local rings, finite-type algebra decompositions, and
  residue-field extensions of finite local factors;
- sampled owner declarations in the chapter/domain:
  `finite_type_algebra_decomposition_henselian_local`,
  `algebraMap_isLocalHom_of_finite_local`,
  `StrictHenselianLocalRing`,
  `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`;
- best owner abstraction:
  the source-facing decomposition owner is already
  `finite_type_algebra_decomposition_henselian_local`; strict henselianity only adds derived
  residue-field consequences on its finite local factors;
- primitive data:
  the `Fintype`-indexed local finite factor decomposition and the remainder `B`;
- derived API:
  the canonical local-hom instance on each factor, finite-dimensionality of the induced
  residue-field extension, and its purely inseparable refinement over the separably closed residue
  field.

Source/core/bridge triage:
- `source-facing`: the strengthened decomposition theorem below;
- `core/canonical`: `finite_type_algebra_decomposition_henselian_local`,
  `algebraMap_isLocalHom_of_finite_local`, and the canonical residue-field finiteness and
  algebraicity instances;
- `bridge/view`: specializing strict henselianity of `R` to residue-field statements on each finite
  local factor produced by the henselian decomposition.
-/

-- Proof sketch: start from the canonical henselian decomposition of Lemma `10.153.5`. For each
-- finite local factor `A i`, Lemma `10.153.4 (3)` gives that `R → A i` is local, so the induced
-- residue-field extension is finite-dimensional by the canonical residue-field instance. Since
-- `ResidueField R` is separably closed, algebraicity of that extension upgrades it to a purely
-- inseparable extension. The local-hom fact is used only as internal instance scaffolding for the
-- residue-field statements, not as a separate public output. The non-quasi-finite remainder term
-- is exactly the one from the owner decomposition.
/-- Lemma 10.153.6: over a strictly henselian local ring `R`, any finite type `R`-algebra `S`
decomposes as a finite product of local finite `R`-algebras whose residue fields are finite purely
inseparable extensions of `ResidueField R`, together with a remainder on which `R → B` is not
quasi-finite at any prime lying over the maximal ideal of `R`. -/
lemma finite_type_algebra_decomposition_strictly_henselian_local :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      letI : ∀ i, IsLocalHom (algebraMap R (A i)) := fun i ↦
        show IsLocalHom (algebraMap R (A i)) from algebraMap_isLocalHom_of_finite_local
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, FiniteDimensional (ResidueField R) (ResidueField (A i))) ∧
        (∀ i, IsPurelyInseparable (ResidueField R) (ResidueField (A i))) ∧
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal := by
  let decompProp : Prop :=
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        ∀ q : PrimeSpectrum B,
          Ideal.comap (algebraMap R B) q.asIdeal = maximalIdeal R →
            ¬ Algebra.QuasiFiniteAt R q.asIdeal
  have hdecomp : decompProp := finite_type_algebra_decomposition_henselian_local
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, hB⟩ := hdecomp
  letI : Fintype ι := instFintype
  letI : ∀ i, CommRing (A i) := instAComm
  letI : ∀ i, Algebra R (A i) := instAAlg
  letI : ∀ i, IsLocalRing (A i) := instALocal
  letI : ∀ i, Module.Finite R (A i) := instAFinite
  letI : ∀ i, IsLocalHom (algebraMap R (A i)) := fun i ↦
    show IsLocalHom (algebraMap R (A i)) from algebraMap_isLocalHom_of_finite_local
  refine ⟨ι, instFintype, A, instAComm, instAAlg, instALocal, instAFinite, B, instBComm,
    instBAlg, e, ?_, ?_, hB⟩
  · intro i
    infer_instance
  · intro i
    letI : Algebra.IsAlgebraic (ResidueField R) (ResidueField (A i)) := inferInstance
    infer_instance

end

/-! ### Lemma_10_153_7 (from Chap10) -/
open CategoryTheory
open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R]

/- Domain-style sampling:
- primary domain: finite étale algebras and reduction modulo an ideal;
- sampled owner declarations:
  `finiteEtaleAlgebraProperty`,
  `finiteEtaleAlgebras`,
  `quotientCommAlgFunctor`,
  `quotientFiniteEtaleAlgebraFunctor`,
  `quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing`;
- best owner abstraction: the canonical ambient owner is `CommAlgCat A`, with the finite étale
  category realized as the full subcategory `finiteEtaleAlgebras A` and the reduction functor as
  the restriction of the Chapter 15 owner `quotientCommAlgFunctor`;
- primitive data vs. derived API: the primitive data is an object of `CommAlgCat A` together with
  finiteness and étaleness, while the Chapter 10 "special fiber" construction is only the
  specialization `I = maximalIdeal R`, hence a bridge/view rather than a second owner.

Source/core/bridge triage:
- `source-facing`: Lemma 10.153.7, phrased as the special-fiber equivalence for a henselian local
  ring;
- `core/canonical`: Chapter 15's quotient reduction functor modulo an ideal and its henselian-pair
  equivalence theorem;
- `bridge/view`: the specialization `I = maximalIdeal R`, with `R ⧸ maximalIdeal R`
  definitionally equal to `ResidueField R`.
-/

variable [HenselianLocalRing R]

/-- Lemma 10.153.7: for a henselian local ring `R`, the special-fiber functor
`S ↦ S / maximalIdeal R • S`, formalized by base change to `ResidueField R`, is an equivalence
from the category of finite étale extensions of `R` to the category of finite étale algebras over
`ResidueField R`. -/
theorem finiteEtaleSpecialFiberFunctor_isEquivalence_of_henselianLocalRing :
    Functor.IsEquivalence (quotientFiniteEtaleAlgebraFunctor (maximalIdeal R)) := by
  simpa using quotientFiniteEtaleAlgebraFunctor_isEquivalence_of_henselianRing (maximalIdeal R)

end

/-! ### Lemma_10_153_8 (from Chap10) -/
open IsLocalRing

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [StrictHenselianLocalRing R]
variable [CommRing S] [Algebra R S] [Algebra.Unramified R S]

/- Domain-style sampling:
- primary domain: strictly henselian local rings, unramified finite-type algebra maps, and the
  finite/non-quasi-finite product decomposition near the maximal ideal;
- sampled owner declarations in this domain:
  `finite_type_algebra_decomposition_henselian_local`,
  `exists_pi_algEquiv_henselianLocalRing_of_finite`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.QuasiFiniteAt`;
- best owner abstraction:
  the decomposition owner remains the henselian-local splitting theorem
  `finite_type_algebra_decomposition_henselian_local`, itself organized around the canonical
  owner `finite_type_algebra_split_finite_nonQuasiFinite_property R`; the present lemma is the
  source-facing strictly-henselian strengthening that upgrades the finite local factors to
  surjective `R`-algebras and removes primes of the remainder over `maximalIdeal R`;
- primitive data:
  a strictly henselian local ring `R` and an unramified `R`-algebra `S`;
- derived API:
  the source-facing decomposition with surjective factors and no prime of the remainder over
  `maximalIdeal R`; the local/finite factor data from Lemma `10.153.5` belong only to a separate
  strengthening theorem.

Source/core/bridge triage:
- `source-facing`: `exists_product_decomposition_surjective_factors_of_unramified`;
- `core/canonical`: `finite_type_algebra_split_finite_nonQuasiFinite_property R` and
  `Algebra.QuasiFiniteAt`;
- `bridge/view`: `exists_product_decomposition_surjective_local_finite_factors_of_unramified`,
  which keeps the local/finite factor data needed for the proof route while the main theorem stays
  source-facing.
-/

-- Proof sketch for the strengthening theorem below: start from the henselian finite-type product
-- decomposition of Lemma `10.153.5`. Each local finite factor `Aᵢ` remains unramified over `R`,
-- so Lemma `10.151.5` makes its residue field a finite separable extension of the residue field of
-- `R`. Since `R` is strictly henselian, that residue field is separably closed, hence the
-- extension is trivial. Nakayama's lemma then upgrades the induced residue-field isomorphism to
-- surjectivity of `R → Aᵢ`. For the remainder `B`, unramified maps are quasi-finite, so the
-- non-quasi-finite alternative from Lemma `10.153.5` rules out primes of `B` over the maximal
-- ideal of `R`.
/-- A strengthening of Lemma `10.153.8` that retains the local and finite factor data coming from
Lemma `10.153.5`. This is a bridge/view theorem; the source-facing main theorem below forgets that
extra structure. -/
theorem exists_product_decomposition_surjective_local_finite_factors_of_unramified :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (instALocal : ∀ i, IsLocalRing (A i))
      (instAFinite : ∀ i, Module.Finite R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      letI : ∀ i, IsLocalRing (A i) := instALocal
      letI : ∀ i, Module.Finite R (A i) := instAFinite
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  sorry

/-- Lemma 10.153.8: if `(R, 𝔪, κ)` is a strictly henselian local ring and `R → S` is unramified,
then `S` decomposes as a finite product `A₁ × ... × Aₙ × B` where each `R → Aᵢ` is surjective
and no prime of `B` lies over the maximal ideal `𝔪` of `R`. -/
theorem exists_product_decomposition_surjective_factors_of_unramified
    :
    ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
      (instAComm : ∀ i, CommRing (A i))
      (instAAlg : ∀ i, Algebra R (A i))
      (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R (A i) := instAAlg
      ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
        (∀ i, Function.Surjective (algebraMap R (A i))) ∧
          ∀ q : PrimeSpectrum B,
            Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R := by
  have h :
      ∃ (ι : Type v) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R (A i))
        (instALocal : ∀ i, IsLocalRing (A i))
        (instAFinite : ∀ i, Module.Finite R (A i))
        (B : Type v) (_ : CommRing B) (_ : Algebra R B),
        letI : ∀ i, CommRing (A i) := instAComm
        letI : ∀ i, Algebra R (A i) := instAAlg
        letI : ∀ i, IsLocalRing (A i) := instALocal
        letI : ∀ i, Module.Finite R (A i) := instAFinite
        ∃ _ : S ≃ₐ[R] ((i : ι) → A i) × B,
          (∀ i, Function.Surjective (algebraMap R (A i))) ∧
            ∀ q : PrimeSpectrum B,
              Ideal.comap (algebraMap R B) q.asIdeal ≠ maximalIdeal R :=
    exists_product_decomposition_surjective_local_finite_factors_of_unramified
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, _, _, B, instBComm, instBAlg, e, hsurj, hB⟩ := h
  exact ⟨ι, instFintype, A, instAComm, instAAlg, B, instBComm, instBAlg, e, hsurj, hB⟩

end

/-! ### Lemma_10_153_9 (from Chap10) -/
universe u

section

open IsLocalRing

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R]

-- Proof sketch: `IsCompleteLocalRing R` is the chapter owner for a complete local ring, so it
-- supplies the maximal-ideal adic completeness needed for the canonical mathlib instance
-- `IsAdicComplete.henselianRing`. Specializing that instance to `maximalIdeal R` gives the
-- required Hensel lifting statement for a local ring directly.
/-- Lemma 10.153.9: a local ring that is complete for the `maximalIdeal`-adic topology, i.e. a
complete local ring in the sense of Definition 10.160.1, is henselian. -/
instance localRing_henselian_of_isCompleteLocalRing : HenselianLocalRing R where
  is_henselian f hf a₀ ha₀ hderiv := by
    let _ : HenselianRing R (maximalIdeal R) := inferInstance
    exact HenselianRing.is_henselian f hf a₀ ha₀ (IsUnit.map (Ideal.Quotient.mk _) hderiv)

end

/-! ### Lemma_10_153_10 (from Chap10) -/
universe u

open IsLocalRing

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-
Domain-style sampling:
- primary domain: henselian local rings and zero-dimensional finite algebras over a local base;
- sampled owner declarations in this domain:
  `HenselianLocalRing`,
  `henselian_local_ring_tfae`,
  `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime`,
  `maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent`;
- best owner abstraction:
  the canonical owner is `HenselianLocalRing R`, and the decisive bridge clause is
  `finite_algebra_finite_local_product_property R` from `henselian_local_ring_tfae`;
- primitive data:
  the local-ring structure on `R` together with the canonical zero-dimensional owner
  `Ring.KrullDimLE 0 R`;
- derived API:
  zero-dimensionality of finite `R`-algebras, locally nilpotent Jacobson radicals, and the
  canonical product decomposition indexed by `MaximalSpectrum`.

Source/core/bridge triage:
- `source-facing`: `localRing_henselian_of_krullDimLE_zero`;
- `core/canonical`: `HenselianLocalRing R`;
- `bridge/view`: `localRing_henselian_of_ringKrullDim_eq_zero`, together with the finite-algebra
  product criterion from `henselian_local_ring_tfae` and the canonical product decomposition
  `maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent`.
-/

-- Proof sketch: by Lemma `10.153.3`, it is enough to show that every finite `R`-algebra is a
-- product of local rings. For a finite `R`-algebra `S`, all primes of `S` lie over the maximal
-- ideal of `R`; because `R` has Krull dimension at most `0`, these primes admit no strict
-- inclusions, so they are all maximal. The intersection of the finitely many maximal ideals is
-- nilpotent, and Lemma `10.53.5` then yields the required product decomposition.
/-- Lemma 10.153.10, owner-level form: a zero-dimensional local ring is henselian, stated using
the canonical zero-dimensional owner hypothesis `[Ring.KrullDimLE 0 R]`. -/
theorem localRing_henselian_of_krullDimLE_zero [Ring.KrullDimLE 0 R] :
    HenselianLocalRing R := by
  let l : List Prop := [
    HenselianLocalRing R,
    @simple_root_lift_property.{u} R _ _,
    @monic_coprime_factorization_lift_property.{u} R _ _,
    @monic_coprime_factorization_lift_with_degree_property.{u} R _ _,
    @coprime_factorization_lift_property.{u} R _ _,
    @coprime_factorization_lift_with_degree_property.{u} R _ _,
    @etale_retraction_exists_property.{u, u} R _ _,
    @etale_retraction_unique_property.{u, u} R _ _,
    @finite_algebra_local_product_property.{u, u} R _,
    @finite_algebra_finite_local_product_property.{u, u} R _,
    @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, u} R _ _,
    @finite_type_algebra_split_finite_positive_dimensional_fiber_property.{u, u} R _ _,
    @quasi_finite_algebra_split_finite_zero_special_fiber_property.{u, u} R _ _
  ]
  have htfae : List.TFAE l := by
    simpa [l] using (@henselian_local_ring_tfae.{u, u} R _ _)
  have hfinite (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] :
      has_finite_local_ring_product_decomposition S := by
    have hdimS : Ring.KrullDimLE 0 S := Ring.KrullDimLE.mk₀ fun J hJ ↦ by
      letI : J.IsPrime := hJ
      letI : (Ideal.comap (algebraMap R S) J).IsMaximal := by
        rw [Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
          (Ideal.comap (algebraMap R S) J)]
        exact maximalIdeal.isMaximal R
      have hcomap : (Ideal.comap (algebraMap R S) J).IsMaximal := inferInstance
      exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hcomap
    letI : Algebra.QuasiFinite R S :=
      (RingHom.quasiFinite_algebraMap : (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S).mp <|
        RingHom.QuasiFinite.of_finite
          <| RingHom.finite_algebraMap.mpr inferInstance
    have hfin : Finite (MaximalSpectrum S) := by
      have hprimesOver : ((maximalIdeal R).primesOver S).Finite :=
        Algebra.QuasiFinite.finite_primesOver (maximalIdeal R)
      have hmax : { J : Ideal S | J.IsMaximal }.Finite := hprimesOver.subset fun J hJ ↦ by
        letI : J.IsMaximal := hJ
        letI : J.IsPrime := hJ.isPrime
        refine ⟨hJ.isPrime, ⟨?_⟩⟩
        simpa [Ideal.under_def] using
          (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
            (Ideal.comap (algebraMap R S) J)).symm
      exact (MaximalSpectrum.equivSubtype S).finite_iff.mpr hmax
    have hjac : (Ring.jacobson S).IsLocallyNilpotent := by
      rw [Ideal.isLocallyNilpotent_iff]
      intro x hx
      rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero S] at hx
      exact mem_nilradical.mp hx
    let _ : Fintype (MaximalSpectrum S) := Fintype.ofFinite (MaximalSpectrum S)
    refine ⟨MaximalSpectrum S, inferInstance, fun J ↦ Localization.AtPrime J.asIdeal,
      fun _ ↦ inferInstance, fun _ ↦ inferInstance, ?_⟩
    exact ⟨maximalSpectrum_toPiLocalizationEquiv_of_finite_of_jacobson_locallyNilpotent hfin hjac⟩
  exact (htfae.out 0 9 rfl rfl).mpr hfinite

/-- Lemma 10.153.10, textbook wording: if `ringKrullDim R = 0`, then the local ring `R` is
henselian. This is the thin bridge from the source equality form to the owner theorem
`localRing_henselian_of_krullDimLE_zero`. -/
theorem localRing_henselian_of_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) :
    HenselianLocalRing R := by
  let _ : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact localRing_henselian_of_krullDimLE_zero R

end

/-! ### Lemma_10_153_11 (from Chap10) -/
universe u v w

open IsLocalRing

section

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S] [Algebra.Etale R A]

/- Domain-style sampling:
- primary domain: henselian local rings, étale neighborhoods, and residue-field controlled lifts
  of points to henselian local targets;
- sampled owner declarations in the surrounding chapter/domain:
  `HenselianLocalRing`,
  `etale_retraction_unique_property`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- best owner abstraction:
  the core owner is the henselian étale-retraction criterion
  `etale_retraction_unique_property`, while the present file is `source-facing`, recording the
  textbook étale-algebra specialization before the later ind-étale generalization of
  Lemma `10.154.6`;
- primitive data vs. derived API:
  the primitive source-facing inputs are the étale `R`-algebra `A`, the chosen prime `q`, and the
  compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` inducing that residue-field map.

Source/core/bridge triage:
- `source-facing`: the present étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S` together with `etale_retraction_unique_property S`;
- `bridge/view`: the passage from the chosen prime and residue-field map on `A` to the unique
  `R`-algebra point of `A` valued in the henselian local ring `S`.
-/

-- Proof sketch: base change the étale `R`-algebra `A` along `R → S` to obtain the étale
-- `S`-algebra `A ⊗[R] S`. The prime `q` together with the chosen residue-field map `τ` determines
-- a prime of `A ⊗[R] S` over `maximalIdeal S` whose residue field is the same as that of `S`.
-- Apply the unique étale-neighborhood retraction characterization of henselian local rings from
-- Lemma `10.153.3` to get a unique `S`-algebra retraction `A ⊗[R] S → S`, then compose it with
-- the canonical map `A → A ⊗[R] S`.
/-- Lemma 10.153.11: let `R → S` be a ring map with `S` henselian local. If `R → A` is étale,
`q` is a prime of `A` whose contraction is the contraction of `maximalIdeal S`, and
`τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the common residue field
`κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose inverse image of
`maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
lemma existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := sorry

end

/-! ### Lemma_10_153_12 (from Chap10) -/
open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [StrictHenselianLocalRing R] [StrictHenselianLocalRing S]
variable (φ : R →+* S) [IsLocalHom φ]
variable {n : ℕ}

/-
Domain-style sampling:
* primary domain: points of étale algebras over strictly henselian local rings;
* sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `henselian_local_ring_tfae`,
  `etale_retraction_unique_property`,
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* best owner abstraction:
  for `A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`, the core owner is the étale
  `R`-algebra `A`; the two polynomial zero loci are only the source-facing presentations of the
  `R`- and `S`-points of that owner algebra;
* primitive data vs. derived API:
  the primitive data are the equations `P i` and the owner hypothesis `[Algebra.Etale R A]`;
  the solution sets are derived from algebra maps out of `A` by the quotient universal property of
  `MvPolynomial.aeval`, not additional primitive structure.

Source/core/bridge triage:
* `source-facing`: the coordinate zero-locus bijection theorem below;
* `core/canonical`: `StrictHenselianLocalRing`, the henselian clause
  `etale_retraction_unique_property`, and the field-level classification
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* `bridge/view`: identifying a common zero of `P` with an `R`-algebra map from the presented
  quotient, and similarly after applying `φ` to coefficients.
-/

-- Proof sketch: for an étale `R`-algebra `A`, the map on point sets `A(R) → A(S)` induced by the
-- local homomorphism `φ : R →+* S` is bijective over strictly henselian local rings. One proves
-- this by applying Lemma `10.153.3`, through the canonical owner clause
-- `etale_retraction_unique_property`, to pass from `A`-points over `R` and `S` to points over the
-- residue fields of `R` and `S`; then `Algebra.Etale.iff_exists_algEquiv_prod` identifies the
-- residue-field base change of `A` with a finite product of copies of the corresponding separably
-- closed residue field.
/-- Owner-level point statement for Lemma 10.153.12: if `φ : R →+* S` is a local homomorphism
between strictly henselian local rings and `A` is an étale `R`-algebra, then composition with `φ`
induces a bijection `A(R) ≃ A(S)`, formalized as a bijection on `R`-algebra maps
`A →ₐ[R] R` and `A →ₐ[R] S`. -/
theorem strictlyHenselian_localHom_bijective_pointMap_of_etale
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective (fun f : A →ₐ[R] R ↦ (Algebra.ofId R S).comp f) := sorry

-- The coordinate zero-locus statement is the source-facing bridge obtained by identifying common
-- zeros of `P` with `R`- and `S`-points of the étale quotient
-- `R[x_1, ..., x_n] / (P_1, ..., P_n)` via `MvPolynomial.aeval` and `Ideal.Quotient.liftₐ`.
/-- Lemma 10.153.12: for a local homomorphism `φ : R →+* S` between strictly henselian local
rings, if `R[x_1, ..., x_n] / (P_1, ..., P_n)` is étale over `R`, then applying `φ`
coordinatewise gives a bijection between the common zero locus of the `P_i` in `R^n` and the
common zero locus of the coefficientwise images `P_i^φ` in `S^n`. -/
theorem strictlyHenselian_localHom_bijOn_zeroLocus_of_etale_mvPolynomial_quotient
    (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.BijOn
      (fun r ↦ φ ∘ r)
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := sorry

end

/-! ### Lemma_10_153_13 (from Chap10) -/
universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: Chapter 10 owner predicates for Mittag-Leffler modules and internal direct-sum
  decompositions of modules;
- sampled declarations of the same kind:
  `Module.IsDirectSumOfCountablyGenerated` from `Definition_10_84_1`,
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `DirectSum.IsInternal.submodule_iSupIndep`,
  `DirectSum.IsInternal.submodule_iSup_eq_top`,
  and mathlib's canonical bridge
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`;
- best owner abstraction: the DecidableEq-free existence of a family of submodules with
  `iSupIndep`, supremum `⊤`, and finitely presented summands; `DirectSum.IsInternal` is only a
  bridge/view because its use on a family indexed by `ι` requires a proof-only `[DecidableEq ι]`;
- primitive data: an index type, a family of submodules, independence of that family, total
  supremum, and finite presentation of each summand;
- derived API: the companion bridge theorem below converting to and from `DirectSum.IsInternal`;
- layer: `IsDirectSumOfFinitePresentation` is `source-facing`, while the internal-direct-sum
  criterion is a `bridge/view`.
-/

variable (R M)

/-- An `R`-module is a direct sum of finitely presented submodules. -/
def IsDirectSumOfFinitePresentation : Prop :=
  ∃ (ι : Type w) (A : ι → Submodule R M),
    iSupIndep A ∧ iSup A = (⊤ : Submodule R M) ∧ ∀ i, Module.FinitePresentation R (A i)

-- Proof sketch: use the canonical mathlib criterion
-- `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` to translate between the public
-- DecidableEq-free owner and the internal-direct-sum view.
/-- `Module.IsDirectSumOfFinitePresentation` is equivalent to the existence of an internal
direct-sum decomposition by finitely presented submodules. This companion theorem keeps
`DirectSum.IsInternal` as a bridge view, not as the owner predicate, because it requires a
proof-only `DecidableEq` witness on the index type. -/
theorem isDirectSumOfFinitePresentation_iff_exists_internal :
    IsDirectSumOfFinitePresentation.{u, v, w} R M ↔
      ∃ (ι : Type w) (_ : DecidableEq ι) (A : ι → Submodule R M),
        DirectSum.IsInternal A ∧ ∀ i, Module.FinitePresentation R (A i) := by
  constructor
  · rintro ⟨ι, A, hindep, htop, hfp⟩
    classical
    refine ⟨ι, inferInstance, A, ?_, hfp⟩
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩
  · rintro ⟨ι, _, A, hA, hfp⟩
    rcases (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hA with
      ⟨hindep, htop⟩
    exact ⟨ι, A, hindep, htop, hfp⟩

section

variable [CommRing R]
variable [HenselianLocalRing R]

-- Proof sketch: for each generator of `M`, use the finite-presentation factorization lemma and the
-- henselian splitting argument from the textbook to split off a finitely presented direct summand
-- containing that generator; iterate over a countable generating family and identify `M` with the
-- internal direct sum of the resulting finitely presented summands.
/-- Lemma 10.153.13: over a henselian local ring, every countably generated Mittag-Leffler module
is an internal direct sum of finitely presented `R`-submodules. This is the canonical Lean form of
the textbook statement that such a module is a direct sum of finitely presented modules. -/
theorem isDirectSumOfFinitePresentation_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
    (hcg : CountablyGenerated R M) (hML : MittagLeffler R M) :
    IsDirectSumOfFinitePresentation R M := sorry

end

end

end Module
