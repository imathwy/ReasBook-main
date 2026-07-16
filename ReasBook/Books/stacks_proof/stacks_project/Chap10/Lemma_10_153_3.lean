import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Quotient
import stacks_proof.stacks_project.Chap10.Definition_10_122_3
import stacks_proof.stacks_project.Chap10.Lemma_10_122_11
import stacks_proof.stacks_project.Chap10.Lemma_10_143_13
import stacks_proof.stacks_project.Chap10.Proposition_10_144_4
import stacks_proof.stacks_project.Chap10.Lemma_10_145_3
import stacks_proof.stacks_project.Chap10.Lemma_10_153_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Algebra.FiniteType Algebra.TensorProduct IsLocalRing Polynomial
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

Semantic recall note: `lean_leansearch` returned `HenselianLocalRing.TFAE`, confirming that the
canonical owner is the henselian-local-ring criterion and that this file should keep the
source-facing extra clauses only as bridge criteria around that owner.
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

/-- The condition that arbitrary coprime factorizations of residue polynomials lift with the
degree of a chosen nonzero factor preserved, matching the normalization step used in the source
proof of clause `(1) → (6)`. -/
def coprime_factorization_lift_with_degree_property : Prop :=
  ∀ f : R[X],
    ∀ g0 h0 : κ[X],
      g0 ≠ 0 →
      f.map (residue R) = g0 * h0 →
      IsCoprime g0 h0 →
      ∃ g h : R[X],
        f = g * h ∧
        g.map (residue R) = g0 ∧
        h.map (residue R) = h0 ∧
        g.degree = g0.degree

/-- The condition that every étale neighbourhood with the same residue field above the maximal
ideal admits an `R`-algebra retraction to `R`. -/
def etale_retraction_exists_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal),
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq) →
      Nonempty (S →ₐ[R] R)

/-- The condition that every étale neighbourhood with the same residue field above the maximal
ideal admits a unique retraction whose inverse image of the maximal ideal is the chosen prime. -/
def etale_retraction_unique_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal),
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq) →
      ∃! τ : S →ₐ[R] R, q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R)

/-- A commutative ring is a product of local rings if it is ring-isomorphic to a cartesian product
of local commutative rings. -/
def has_local_ring_product_decomposition (S : Type (max u v)) [CommRing S] : Prop :=
  ∃ (ι : Type (max u v)) (A : ι → Type (max u v))
    (instAComm : ∀ i, CommRing (A i))
    (instALocal : ∀ i, IsLocalRing (A i)),
    letI : ∀ i, CommRing (A i) := instAComm
    letI : ∀ i, IsLocalRing (A i) := instALocal
    Nonempty (S ≃+* ∀ i, A i)

/-- A commutative ring is a finite product of local rings if it is ring-isomorphic to a finite
cartesian product of local commutative rings. -/
def has_finite_local_ring_product_decomposition (S : Type (max u v)) [CommRing S] : Prop :=
  ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
    (instAComm : ∀ i, CommRing (A i))
    (instALocal : ∀ i, IsLocalRing (A i)),
    letI : ∀ i, CommRing (A i) := instAComm
    letI : ∀ i, IsLocalRing (A i) := instALocal
    Nonempty (S ≃+* ∀ i, A i)

/-- Every irreducible component of the special fiber has dimension at least `1`, expressed through
the quotient rings by the minimal primes of the fiber. -/
def special_fiber_minimal_primes_positive_dimensional
    (B : Type v) [CommRing B] [Algebra R B] : Prop :=
  ∀ p : PrimeSpectrum (κ ⊗[R] B),
    p.asIdeal ∈ minimalPrimes (κ ⊗[R] B) →
    1 ≤ ringKrullDim ((κ ⊗[R] B) ⧸ p.asIdeal)

/-- The condition that every finite `R`-algebra splits as a product of local rings. -/
def finite_algebra_local_product_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Module.Finite R S],
    @has_local_ring_product_decomposition.{u, v} S _

/-- The condition that every finite `R`-algebra splits as a finite product of local rings. -/
def finite_algebra_finite_local_product_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Module.Finite R S],
    @has_finite_local_ring_product_decomposition.{u, v} S _

/-- The condition that a finite type `R`-algebra splits into a finite part and a remainder that is
not quasi-finite at any prime above the maximal ideal. -/
def finite_type_algebra_split_finite_nonQuasiFinite_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        ∀ q : PrimeSpectrum B,
          maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal →
          ¬ Algebra.QuasiFiniteAt R q.asIdeal

/-- The condition that a finite type `R`-algebra splits into a finite part and a remainder whose
special fiber has only positive-dimensional irreducible components. -/
def finite_type_algebra_split_finite_positive_dimensional_fiber_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        special_fiber_minimal_primes_positive_dimensional R B

/-- The condition that a quasi-finite `R`-algebra splits into a finite part and a remainder with
zero special fiber. -/
def quasi_finite_algebra_split_finite_zero_special_fiber_property : Prop :=
  ∀ (S : Type (max u v)) [CommRing S] [Algebra R S], Algebra.FiniteType.QuasiFinite R S →
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        Subsingleton (κ ⊗[R] B)

/-- Helper for Chap10 Lemma 10 153 3: forgetting the degree condition leaves a monic coprime
factorization lifting statement. -/
lemma monicCoprimeFactorizationLift_of_withDegree :
    monic_coprime_factorization_lift_with_degree_property R →
      monic_coprime_factorization_lift_property R := by
  -- Proof comment: unpack the stronger source clause and discard the final degree witness.
  intro h f hf g0 h0 hfac hcop
  obtain ⟨g, h', hmul, hg, hh, _hdeg⟩ := h f hf g0 h0 hfac hcop
  exact ⟨g, h', hmul, hg, hh⟩

/-- Helper for Chap10 Lemma 10 153 3: an arbitrary coprime factorization lift specializes
immediately to the monic case. -/
lemma monicCoprimeFactorizationLift_of_arbitrary :
    coprime_factorization_lift_property R →
      monic_coprime_factorization_lift_property R := by
  -- Proof comment: the source arbitrary-polynomial clause is stronger than the monic one, so we
  -- simply reuse it on the monic input.
  intro h f hf g0 h0 hfac hcop
  exact h f g0 h0 hfac hcop

/-- Helper for Chap10 Lemma 10 153 3: the arbitrary with-degree lifting clause specializes to the
monic with-degree clause. -/
lemma monicCoprimeFactorizationLiftWithDegree_of_arbitrary :
    coprime_factorization_lift_with_degree_property R →
      monic_coprime_factorization_lift_with_degree_property R := by
  -- Proof comment: the arbitrary with-degree clause is already strong enough for the monic
  -- source clause; we specialize it to the monic input and then convert the resulting degree
  -- equality into a `natDegree` equality because the chosen residue factor is nonzero.
  intro h f hf g0 h0 hfac hcop
  have hg0_ne : g0 ≠ 0 := by
    intro hg0_zero
    have hfmap : (f.map (residue R)).Monic := hf.map (residue R)
    exact hfmap.ne_zero (by simpa [hg0_zero] using hfac)
  obtain ⟨g, h', hmul, hg, hh, hdeg⟩ := h f g0 h0 hg0_ne hfac hcop
  have hg_ne : g ≠ 0 := by
    intro hg_zero
    exact hg0_ne (by simpa [hg_zero] using hg.symm)
  have hnat : g.natDegree = g0.natDegree := by
    apply WithBot.coe_injective
    simpa [Polynomial.degree_eq_natDegree hg_ne, Polynomial.degree_eq_natDegree hg0_ne] using hdeg
  exact ⟨g, h', hmul, hg, hh, hnat⟩

/-- Helper for Chap10 Lemma 10 153 3: forgetting the degree witness still yields arbitrary
coprime-factorization lifting. -/
lemma coprimeFactorizationLift_of_withDegree :
    coprime_factorization_lift_with_degree_property R →
      coprime_factorization_lift_property R := by
  intro h f g0 h0 hfac hcop
  by_cases hg0 : g0 = 0
  · have hh0_unit : IsUnit h0 := by
      rcases hcop with ⟨a, b, hab⟩
      have hab' : b * h0 = 1 := by
        simpa [hg0] using hab
      exact IsUnit.of_mul_eq_one_right _ hab'
    have hh0_ne : h0 ≠ 0 := by
      exact hh0_unit.ne_zero
    obtain ⟨hLift, gLift, hmul, hh, hg, _hdeg⟩ :=
      h f h0 g0 hh0_ne (by simpa [mul_comm] using hfac) hcop.symm
    -- Proof comment: when the chosen factor is zero, coprimeness forces the complementary factor
    -- to be a unit, so we lift the swapped factorization and then swap the lifted factors back.
    exact ⟨gLift, hLift, by simpa [mul_comm] using hmul, hg, hh⟩
  · obtain ⟨g, h', hmul, hg, hh, _hdeg⟩ := h f g0 h0 hg0 hfac hcop
    -- Proof comment: in the nonzero case we simply drop the final degree witness.
    exact ⟨g, h', hmul, hg, hh⟩

/-- Helper for Chap10 Lemma 10 153 3: arbitrary simple-root lifting specializes to the canonical
monic simple-root criterion in `HenselianLocalRing.TFAE`. -/
lemma henselian_of_simpleRootLiftProperty :
    simple_root_lift_property R → HenselianLocalRing R := by
  intro h
  -- Proof comment: the source-facing arbitrary-polynomial clause is stronger than mathlib's
  -- monic simple-root owner criterion, so we feed it directly into the canonical TFAE.
  exact ((HenselianLocalRing.TFAE R).out 1 0).mp <| by
    intro f hf a0 hroot hder
    exact h f a0 hroot hder

/-- Helper for Chap10 Lemma 10 153 3: a simple residue root gives the corresponding linear
factorization and coprime quotient over the residue field. -/
lemma simpleRootResidueFactorization {K : Type u} [Field K] (p : K[X]) (a0 : K)
    (hroot : p.IsRoot a0) (hderiv : p.derivative.eval a0 ≠ 0) :
    p = (Polynomial.X - Polynomial.C a0) * (p /ₘ (Polynomial.X - Polynomial.C a0)) ∧
      IsCoprime (Polynomial.X - Polynomial.C a0)
        (p /ₘ (Polynomial.X - Polynomial.C a0)) := by
  constructor
  · -- Proof comment: divisibility by the monic linear factor is exactly the root condition.
    exact (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  · -- Proof comment: nonvanishing derivative at the root makes the linear factor coprime to the
    -- remaining quotient.
    exact Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero p a0 hderiv

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: over a field, scaling a nonzero polynomial by the inverse
of its leading coefficient produces a monic polynomial. -/
lemma monic_normalizeByLeadingCoeff
    {K : Type u} [Field K] {p : K[X]} (hp : p ≠ 0) :
    (Polynomial.C p.leadingCoeff⁻¹ * p).Monic := by
  -- Proof comment: multiplying by the inverse leading coefficient forces the new leading
  -- coefficient to be `1`.
  refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
  exact inv_mul_cancel₀ (by simpa using (Polynomial.leadingCoeff_ne_zero : p.leadingCoeff ≠ 0 ↔ p ≠ 0).2 hp)

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: the same normalization does not change the degree of a
nonzero polynomial over a field. -/
lemma natDegree_normalizeByLeadingCoeff
    {K : Type u} [Field K] {p : K[X]} (hp : p ≠ 0) :
    (Polynomial.C p.leadingCoeff⁻¹ * p).natDegree = p.natDegree := by
  -- Proof comment: the scalar used for normalization is a unit, so multiplication by it
  -- preserves natDegree.
  refine Polynomial.natDegree_C_mul_of_isUnit ?_ p
  exact isUnit_iff_ne_zero.mpr <|
    inv_ne_zero (by
      simpa using (Polynomial.leadingCoeff_ne_zero : p.leadingCoeff ≠ 0 ↔ p ≠ 0).2 hp)

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: over a field, a nonzero coprime factorization can be
rescaled to a monic coprime factorization without changing the two factor degrees. -/
lemma normalizeResidueFactorizationToMonicPair
    {K : Type u} [Field K] {g h : K[X]}
    (hg : g ≠ 0) (hh : h ≠ 0) (hcop : IsCoprime g h) :
    let g' : K[X] := Polynomial.C g.leadingCoeff⁻¹ * g
    let h' : K[X] := Polynomial.C h.leadingCoeff⁻¹ * h
    g'.Monic ∧
      h'.Monic ∧
      IsCoprime g' h' ∧
      g'.natDegree = g.natDegree ∧
      h'.natDegree = h.natDegree ∧
      g' * h' = Polynomial.C ((g * h).leadingCoeff)⁻¹ * (g * h) := by
  let g' : K[X] := Polynomial.C g.leadingCoeff⁻¹ * g
  let h' : K[X] := Polynomial.C h.leadingCoeff⁻¹ * h
  have hg' : g'.Monic := by
    -- Proof comment: scaling by the inverse leading coefficient makes the first factor monic.
    simpa [g'] using monic_normalizeByLeadingCoeff (K := K) hg
  have hh' : h'.Monic := by
    -- Proof comment: the same normalization makes the complementary factor monic.
    simpa [h'] using monic_normalizeByLeadingCoeff (K := K) hh
  have hdeg_g' : g'.natDegree = g.natDegree := by
    -- Proof comment: normalization by a unit does not change the degree.
    simpa [g'] using natDegree_normalizeByLeadingCoeff (K := K) hg
  have hdeg_h' : h'.natDegree = h.natDegree := by
    -- Proof comment: the same degree preservation holds for the complementary factor.
    simpa [h'] using natDegree_normalizeByLeadingCoeff (K := K) hh
  have hcop' : IsCoprime g' h' := by
    rcases hcop with ⟨a, b, hab⟩
    refine ⟨Polynomial.C g.leadingCoeff * a, Polynomial.C h.leadingCoeff * b, ?_⟩
    -- Proof comment: rescaling the Bezout coefficients exactly cancels the normalization factors.
    have hgcancel : (Polynomial.C g.leadingCoeff : K[X]) * Polynomial.C g.leadingCoeff⁻¹ = 1 := by
      rw [Polynomial.C_mul']
      simp [Polynomial.leadingCoeff_ne_zero.mpr hg]
    have hhcancel : (Polynomial.C h.leadingCoeff : K[X]) * Polynomial.C h.leadingCoeff⁻¹ = 1 := by
      rw [Polynomial.C_mul']
      simp [Polynomial.leadingCoeff_ne_zero.mpr hh]
    calc
      (Polynomial.C g.leadingCoeff * a) * g' + (Polynomial.C h.leadingCoeff * b) * h'
          = a * g + b * h := by
              dsimp [g', h']
              calc
                (Polynomial.C g.leadingCoeff * a) * (Polynomial.C g.leadingCoeff⁻¹ * g) +
                    (Polynomial.C h.leadingCoeff * b) * (Polynomial.C h.leadingCoeff⁻¹ * h)
                    = (((Polynomial.C g.leadingCoeff : K[X]) * Polynomial.C g.leadingCoeff⁻¹) *
                        (a * g)) +
                      (((Polynomial.C h.leadingCoeff : K[X]) * Polynomial.C h.leadingCoeff⁻¹) *
                        (b * h)) := by
                          ring
                _ = a * g + b * h := by simp [hgcancel, hhcancel]
      _ = 1 := hab
  have hprod :
      g' * h' = Polynomial.C ((g * h).leadingCoeff)⁻¹ * (g * h) := by
    have hlead :
        (g * h).leadingCoeff = g.leadingCoeff * h.leadingCoeff := by
      simpa [hg, hh] using Polynomial.leadingCoeff_mul g h
    have hscalar :
        (Polynomial.C g.leadingCoeff⁻¹ : K[X]) * Polynomial.C h.leadingCoeff⁻¹ =
          Polynomial.C ((g * h).leadingCoeff)⁻¹ := by
      ext n
      by_cases hn : n = 0
      · subst hn
        rw [Polynomial.C_mul']
        simp [Polynomial.coeff_C, hlead]
        field_simp [Polynomial.leadingCoeff_ne_zero.mpr hg, Polynomial.leadingCoeff_ne_zero.mpr hh]
      · simpa [Polynomial.coeff_C, hn]
    -- Proof comment: multiplying the normalized factors is the same as normalizing the product.
    calc
      g' * h' =
          ((Polynomial.C g.leadingCoeff⁻¹ : K[X]) * Polynomial.C h.leadingCoeff⁻¹) * (g * h) := by
        dsimp [g', h']
        ring
      _ = Polynomial.C ((g * h).leadingCoeff)⁻¹ * (g * h) := by
        rw [hscalar]
  exact ⟨hg', hh', hcop', hdeg_g', hdeg_h', hprod⟩

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: a degree-one polynomial with unit leading coefficient has
an explicit root. -/
lemma existsRootOfNatDegreeOneOfIsUnitLeadingCoeff
    {g : R[X]} (hdeg : g.natDegree = 1) (hunit : IsUnit (g.coeff 1)) :
    ∃ a : R, g.IsRoot a := by
  obtain ⟨u, hu⟩ := hunit
  refine ⟨-(↑u⁻¹ : R) * g.coeff 0, ?_⟩
  have hshape : g = C (g.coeff 1) * X + C (g.coeff 0) := by
    -- Proof comment: degree at most one gives the standard `c₁ X + c₀` normal form.
    exact Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
  -- Proof comment: after replacing the leading coefficient by the chosen unit, evaluation at
  -- `-u⁻¹ c₀` is a one-line ring simplification.
  rw [IsRoot.def, hshape]
  rw [← hu]
  simp

/-- Helper for Chap10 Lemma 10 153 3: if `g` reduces to `X - C a0`, then the coefficient of `X`
in `g` is already a unit of the local base ring. -/
lemma coeffOne_isUnit_of_linearResidueFactor
    {g : R[X]} {a0 : κ}
    (hgmap : g.map (residue R) = Polynomial.X - Polynomial.C a0) :
    IsUnit (g.coeff 1) := by
  have hcoeff_one : residue R (g.coeff 1) = 1 := by
    -- Proof comment: compare the coefficient of `X` in the reduced linear factor identity.
    simpa using congrArg (fun p : κ[X] ↦ p.coeff 1) hgmap
  -- Proof comment: a nonzero residue class in a local ring comes from a unit.
  exact (residue_ne_zero_iff_isUnit (g.coeff 1)).mp (by
    rw [hcoeff_one]
    exact one_ne_zero)

/-- Helper for Chap10 Lemma 10 153 3: a lifted degree-one factor reducing to `X - C a0` has a
root whose residue is `a0`. -/
lemma existsRootOfLinearResidueFactor
    {g : R[X]} {a0 : κ}
    (hgmap : g.map (residue R) = Polynomial.X - Polynomial.C a0)
    (hdeg : g.natDegree = 1) :
    ∃ a : R, g.IsRoot a ∧ residue R a = a0 := by
  have hunit : IsUnit (g.coeff 1) := coeffOne_isUnit_of_linearResidueFactor R hgmap
  obtain ⟨a, ha⟩ := existsRootOfNatDegreeOneOfIsUnitLeadingCoeff R hdeg hunit
  refine ⟨a, ha, ?_⟩
  have hmapRoot : (g.map (residue R)).IsRoot (residue R a) := by
    -- Proof comment: mapping the root equation to the residue field makes `residue a` a root of
    -- the mapped polynomial.
    rw [IsRoot.def]
    rw [Polynomial.eval_map_apply]
    exact congrArg (residue R) (IsRoot.def.mp ha)
  rw [hgmap] at hmapRoot
  -- Proof comment: the only root of `X - C a0` is `a0`, giving the desired residue equality.
  exact sub_eq_zero.mp (by simpa [Polynomial.IsRoot] using hmapRoot)

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: over a domain, any factor of a monic polynomial has unit
leading coefficient. -/
lemma isUnit_leadingCoeff_of_dvd_monic
    [IsDomain R] {f g : R[X]} (hf : f.Monic) (hdiv : g ∣ f) :
    IsUnit g.leadingCoeff := by
  -- Route correction: the blocker was a normal-form issue, not a missing premise. Mathlib already
  -- provides the required leading-coefficient theorem once the domain hypothesis is explicit.
  simpa using Polynomial.Monic.isUnit_leadingCoeff_of_dvd hf hdiv

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: over a domain, the quotient by a factor of a monic
polynomial is finite over the base ring after unit-normalizing that factor to a monic polynomial.
-/
lemma finite_quotient_of_dvd_monic
    [IsDomain R] {f g : R[X]} (hf : f.Monic) (hdiv : g ∣ f) :
    Module.Finite R (R[X] ⧸ Ideal.span ({g} : Set R[X])) := by
  let hu : IsUnit g.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic R hf hdiv
  let g' : R[X] := hu.unit⁻¹ • g
  have hg' : g'.Monic := by
    -- Proof comment: rescaling by the inverse unit leading coefficient puts the divisor into the
    -- monic normal form expected by the standard quotient API.
    simpa [g'] using monic_of_isUnit_leadingCoeff_inv_smul hu
  have hspan :
      Ideal.span ({g'} : Set R[X]) = Ideal.span ({g} : Set R[X]) := by
    -- Proof comment: multiplying a generator by a unit does not change the principal ideal, so
    -- the normalized quotient is canonically the same quotient ring.
    rw [show g' = hu.unit⁻¹ • g by rfl, Units.smul_def, Polynomial.smul_eq_C_mul]
    simpa using
      Ideal.span_singleton_mul_left_unit (isUnit_C.mpr (Units.isUnit _)) g
  let e :
      (R[X] ⧸ Ideal.span ({g'} : Set R[X])) ≃ₐ[R]
        (R[X] ⧸ Ideal.span ({g} : Set R[X])) :=
    Ideal.quotientEquivAlgOfEq R hspan
  letI : Module.Finite R (R[X] ⧸ Ideal.span ({g'} : Set R[X])) := hg'.finite_quotient
  exact Module.Finite.equiv e.toLinearEquiv

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: over a domain, the quotient by a factor of a monic
polynomial is free over the base ring after the same unit normalization. -/
lemma free_quotient_of_dvd_monic
    [IsDomain R] {f g : R[X]} (hf : f.Monic) (hdiv : g ∣ f) :
    Module.Free R (R[X] ⧸ Ideal.span ({g} : Set R[X])) := by
  let hu : IsUnit g.leadingCoeff := isUnit_leadingCoeff_of_dvd_monic R hf hdiv
  let g' : R[X] := hu.unit⁻¹ • g
  have hg' : g'.Monic := by
    -- Proof comment: the same unit normalization reduces the free-quotient claim to the monic
    -- polynomial case handled in mathlib.
    simpa [g'] using monic_of_isUnit_leadingCoeff_inv_smul hu
  have hspan :
      Ideal.span ({g'} : Set R[X]) = Ideal.span ({g} : Set R[X]) := by
    -- Proof comment: quotienting by associated principal generators gives equivalent modules.
    rw [show g' = hu.unit⁻¹ • g by rfl, Units.smul_def, Polynomial.smul_eq_C_mul]
    simpa using
      Ideal.span_singleton_mul_left_unit (isUnit_C.mpr (Units.isUnit _)) g
  let e :
      (R[X] ⧸ Ideal.span ({g'} : Set R[X])) ≃ₐ[R]
        (R[X] ⧸ Ideal.span ({g} : Set R[X])) :=
    Ideal.quotientEquivAlgOfEq R hspan
  letI : Module.Free R (R[X] ⧸ Ideal.span ({g'} : Set R[X])) := hg'.free_quotient
  exact Module.Free.of_equiv e.toLinearEquiv

/-- Helper for Chap10 Lemma 10 153 3: the strongest arbitrary coprime-factorization clause implies
simple-root lifting for arbitrary polynomials. -/
lemma simpleRootLiftProperty_of_coprimeFactorizationLiftWithDegree :
    coprime_factorization_lift_with_degree_property R → simple_root_lift_property R := by
  -- Proof comment: factor the reduced polynomial by the linear factor `X - C a0`, lift that
  -- factorization with degree control, and then read off a root from the lifted degree-one factor.
  intro h f a0 hroot hderiv
  have hroot' : (f.map (residue R)).IsRoot a0 := by
    rw [Polynomial.IsRoot]
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hroot
  have hderiv' : (f.map (residue R)).derivative.eval a0 ≠ 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.derivative_map] using
      hderiv
  have hlin_ne : (Polynomial.X - Polynomial.C a0 : κ[X]) ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : κ[X] ↦ p.coeff 1) hzero
    simpa using hcoeff
  obtain ⟨hfac, hcop⟩ :=
    simpleRootResidueFactorization (f.map (residue R)) a0 hroot' hderiv'
  obtain ⟨g, h', hmul, hg, hh, hdeg⟩ :=
    h f (Polynomial.X - Polynomial.C a0)
      ((f.map (residue R)) /ₘ (Polynomial.X - Polynomial.C a0)) hlin_ne hfac hcop
  have hgdeg : g.degree = 1 := by
    simpa [Polynomial.degree_X_sub_C] using hdeg
  have hgnat : g.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some hgdeg
  obtain ⟨a, ha, ha0⟩ := existsRootOfLinearResidueFactor R hg hgnat
  have hfa : f.IsRoot a := by
    rw [IsRoot, hmul, Polynomial.eval_mul, ha]
    simp
  exact ⟨a, hfa, ha0⟩

/-- Helper for Chap10 Lemma 10 153 3: uniqueness of an étale retraction certainly implies
existence. -/
lemma etaleRetractionExists_of_unique :
    @etale_retraction_unique_property.{u, v} R _ _ →
      @etale_retraction_exists_property.{u, v} R _ _ := by
  -- Proof comment: unpack the unique retraction and retain only the witness.
  intro h S _ _ _ q hq hκ
  obtain ⟨τ, _hτ, _huniq⟩ := h S q hq hκ
  exact ⟨τ⟩

/-- Helper for Chap10 Lemma 10 153 3: the unique étale-retraction clause applies directly to a
chosen étale `R`-algebra in the ambient universe `Type (max u v)`. -/
lemma etaleRetractionUnique_apply
    (h : @etale_retraction_unique_property.{u, v} R _ _)
    {S : Type (max u v)} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq)) :
    ∃! τ : S →ₐ[R] R, q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R) := by
  -- Proof comment: `Type u` is cumulative into `Type (max u v)`, so the clause `(8)` owner can
  -- be applied to `S` without introducing any `ULift` transport.
  simpa using h S q hq hκ

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: a finite `R`-algebra is automatically finite type and
quasi-finite in the bundled source-facing sense. -/
lemma moduleFinite_finiteTypeQuasiFinite
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    Algebra.FiniteType.QuasiFinite R S := by
  let hFinite : (algebraMap R S).Finite := RingHom.finite_algebraMap.mpr inferInstance
  letI : Algebra.QuasiFinite R S :=
    (RingHom.quasiFinite_algebraMap).mp (RingHom.QuasiFinite.of_finite hFinite)
  -- Proof comment: the finite algebra map already provides the canonical quasi-finite owner, and
  -- the bundled source-facing condition just packages that with finite type.
  exact QuasiFinite.of_quasiFinite inferInstance

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: quasi-finiteness at a prime is preserved when restricting
scalars along a tower `A → B → C`. -/
lemma quasiFiniteAt_of_restrictScalars_local
    {A : Type u} {B : Type v} {C : Type*}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (r : PrimeSpectrum C) (hAC : Algebra.QuasiFiniteAt A r.asIdeal) :
    Algebra.QuasiFiniteAt B r.asIdeal := by
  letI : Algebra.QuasiFiniteAt A r.asIdeal := hAC
  -- Proof comment: after localizing at `r`, the quasi-finite algebra remains quasi-finite when
  -- we simply forget part of the scalar structure along the tower.
  change Algebra.QuasiFinite B (Localization.AtPrime r.asIdeal)
  exact Algebra.QuasiFinite.of_restrictScalars A B (Localization.AtPrime r.asIdeal)

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: a globally quasi-finite algebra is quasi-finite at each of
its primes. -/
lemma quasiFiniteAt_of_quasiFinite
    {B : Type v} [CommRing B] [Algebra R B] [Algebra.QuasiFinite R B]
    (q : PrimeSpectrum B) :
    Algebra.QuasiFiniteAt R q.asIdeal := by
  -- Proof comment: localizing a quasi-finite algebra at a prime preserves quasi-finiteness.
  change Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal)
  exact Algebra.QuasiFinite.of_isLocalization q.asIdeal.primeCompl

/-- Helper for Chap10 Lemma 10 153 3: if a quasi-finite algebra has no quasi-finite point above
the closed point, then its owner-level closed fiber is the zero ring. -/
lemma subsingletonClosedFiber_of_forall_not_quasiFiniteAt
    {B : Type v} [CommRing B] [Algebra R B] [Algebra.QuasiFinite R B]
    (hB : ∀ q : PrimeSpectrum B,
      maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal →
        ¬ Algebra.QuasiFiniteAt R q.asIdeal) :
    Subsingleton ((maximalIdeal R).Fiber B) := by
  let e := PrimeSpectrum.primesOverOrderIsoFiber R B (maximalIdeal R)
  have hEmpty : IsEmpty (PrimeSpectrum ((maximalIdeal R).Fiber B)) := by
    refine ⟨fun qf ↦ ?_⟩
    let qB : (maximalIdeal R).primesOver B := e.symm qf
    let q : PrimeSpectrum B := ⟨qB.1, inferInstance⟩
    have hq : maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal := by
      simpa [q, Ideal.under_def] using qB.1.over_def (maximalIdeal R)
    exact hB q hq (quasiFiniteAt_of_quasiFinite R q)
  exact (PrimeSpectrum.isEmpty_iff_subsingleton).mp hEmpty

/-- Helper for Chap10 Lemma 10 153 3: once a quasi-finite algebra `S` splits as `A × B`, any
remainder `B` with no quasi-finite point above `maximalIdeal R` has subsingleton closed fiber. -/
lemma subsingletonFiber_of_splitNonQuasiFiniteRemainder
    {S A B : Type v} [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra.QuasiFinite R S]
    (e : S ≃ₐ[R] A × B)
    (hB : ∀ q : PrimeSpectrum B,
      maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal →
        ¬ Algebra.QuasiFiniteAt R q.asIdeal) :
    Subsingleton ((maximalIdeal R).Fiber B) := by
  let φ : S →ₐ[R] B := (AlgHom.snd R A B).comp e
  have hφsurj : Function.Surjective φ := by
    -- Proof comment: the second projection of the product decomposition is visibly surjective.
    intro b
    refine ⟨e.symm (0, b), ?_⟩
    simp [φ]
  letI : Algebra.QuasiFinite R B := Algebra.QuasiFinite.of_surjective_algHom φ hφsurj
  -- Proof comment: now reuse the closed-fiber emptiness criterion on the quasi-finite factor `B`.
  exact subsingletonClosedFiber_of_forall_not_quasiFiniteAt R hB

/-- Helper for Chap10 Lemma 10 153 3: the source `11 → 13` descent works as soon as the input
quasi-finite algebra also carries the finite-type hypothesis needed to invoke clause `(11)`. -/
lemma splitFiniteTypeQuasiFiniteHasSubsingletonFiber
    {S : Type (max u v)} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S]
    (h :
      @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R _ _) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        Subsingleton ((maximalIdeal R).Fiber B) := by
  obtain ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, hs, hB⟩ := h S
  letI : CommRing A := instAComm
  letI : Algebra R A := instAAlg
  letI : Module.Finite R A := instAFinite
  letI : CommRing B := instBComm
  letI : Algebra R B := instBAlg
  obtain ⟨e⟩ := hs
  refine ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, ⟨e⟩, ?_⟩
  -- Proof comment: the new reusable factor-level helper isolates the source descent step.
  exact subsingletonFiber_of_splitNonQuasiFiniteRemainder R e hB

/-- Helper for Chap10 Lemma 10 153 3: the closed fiber `((maximalIdeal R).Fiber B)` identifies
with `κ ⊗[R] B`, so subsingleton closed fiber already means zero special fiber in clause `(13)`. -/
lemma zeroSpecialFiberSubsingleton_of_closedFiberSubsingleton
    {B : Type v} [CommRing B] [Algebra R B]
    (hB : Subsingleton ((maximalIdeal R).Fiber B)) :
    Subsingleton (κ ⊗[R] B) := by
  let eκRing : (maximalIdeal R).ResidueField ≃+* κ :=
    (RingEquiv.ofBijective
      (algebraMap κ (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm
  let eκ : (maximalIdeal R).ResidueField ≃ₐ[R] κ :=
    { toRingEquiv := eκRing
      commutes' := fun a ↦ by
        -- Proof comment: both residue-field models send `a : R` to its residue class.
        rw [show algebraMap R (maximalIdeal R).ResidueField a =
          algebraMap κ (maximalIdeal R).ResidueField (residue R a) by rfl]
        exact eκRing.apply_symm_apply (residue R a) }
  let e : (maximalIdeal R).Fiber B ≃ₐ[R] (κ ⊗[R] B) :=
    Algebra.TensorProduct.congr eκ (AlgEquiv.refl : B ≃ₐ[R] B)
  letI : Subsingleton ((maximalIdeal R).Fiber B) := hB
  -- Proof comment: transport the subsingleton closed fiber across the tensor-product equivalence.
  exact Function.Injective.subsingleton e.symm.injective

/-- Helper for Chap10 Lemma 10 153 3: under the polynomial-tensor equivalence, the tensor-side
principal ideal generated by `g` becomes the principal ideal generated by `g.map (residue R)`. -/
lemma closedFiber_polynomialQuotientIdeal_map_eq_span (g : R[X]) :
    Ideal.span ({g.map (residue R)} : Set κ[X]) =
      Ideal.map ((polyEquivTensor' R κ).symm : κ ⊗[R] R[X] ≃ₐ[κ] κ[X]).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] κ ⊗[R] R[X])
          (Ideal.span ({g} : Set R[X]))) := by
  -- Proof comment: the tensor-product polynomial normal form carries the single generator `g`
  -- exactly to its coefficientwise residue-field reduction.
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton <| by
    rw [Algebra.TensorProduct.includeRight_apply]
    -- Proof comment: the right tensor inclusion becomes coefficientwise scalar extension.
    calc
      Polynomial.map (residue R) g = (1 : κ) • Polynomial.map (algebraMap R κ) g := by
        simp [ResidueField.algebraMap_eq]
      _ = ((polyEquivTensor' R κ).symm : κ ⊗[R] R[X] ≃ₐ[κ] κ[X]) (1 ⊗ₜ[R] g) := by
        symm
        simpa using
          polyEquivTensor_symm_apply_tmul_eq_smul (1 : κ) g

/-- Helper for Chap10 Lemma 10 153 3: the closed fiber of the polynomial quotient
`R[X] ⧸ (g)` is the quotient of `κ[X]` by the reduced polynomial `g.map (residue R)`. -/
noncomputable def closedFiber_polynomialQuotientEquiv (g : R[X]) :
    κ ⊗[R] (R[X] ⧸ Ideal.span ({g} : Set R[X])) ≃ₐ[κ]
      κ[X] ⧸ Ideal.span ({g.map (residue R)} : Set κ[X]) :=
  let tensorIdeal : Ideal (κ ⊗[R] R[X]) :=
    Ideal.map
      (Algebra.TensorProduct.includeRight : R[X] →ₐ[R] κ ⊗[R] R[X])
      (Ideal.span ({g} : Set R[X]))
  let eQuot :
      κ ⊗[R] (R[X] ⧸ Ideal.span ({g} : Set R[X])) ≃ₐ[κ]
        (κ ⊗[R] R[X]) ⧸ tensorIdeal :=
    Algebra.TensorProduct.tensorQuotientEquiv κ (R[X]) κ
      (Ideal.span ({g} : Set R[X]))
  let polyEquiv : κ ⊗[R] R[X] ≃ₐ[κ] κ[X] := (polyEquivTensor' R κ).symm
  let targetIdeal : Ideal κ[X] := Ideal.span ({g.map (residue R)} : Set κ[X])
  let ePoly :
      ((κ ⊗[R] R[X]) ⧸ tensorIdeal) ≃ₐ[κ]
        κ[X] ⧸ targetIdeal :=
    Ideal.quotientEquivAlg tensorIdeal targetIdeal polyEquiv <|
      by
        simpa [tensorIdeal, targetIdeal] using
          closedFiber_polynomialQuotientIdeal_map_eq_span R g
  -- Proof comment: first move the quotient through tensor product, then rewrite the transported
  -- principal ideal via the polynomial base-change equivalence.
  eQuot.trans ePoly

/-- Helper for Chap10 Lemma 10 153 3: once a quasi-finite finite-type algebra splits as in
clause `(11)`, the remainder already has zero special fiber in the clause `(13)` sense. -/
lemma splitFiniteTypeQuasiFiniteHasZeroSpecialFiber
    {S : Type (max u v)} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S]
    (h :
      @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R _ _) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        Subsingleton (κ ⊗[R] B) := by
  have hspl :
      ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
        (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
        Nonempty (S ≃ₐ[R] A × B) ∧
          Subsingleton ((maximalIdeal R).Fiber B) :=
    splitFiniteTypeQuasiFiniteHasSubsingletonFiber R h
  obtain ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, hs, hB⟩ := hspl
  letI : CommRing A := instAComm
  letI : Algebra R A := instAAlg
  letI : Module.Finite R A := instAFinite
  letI : CommRing B := instBComm
  letI : Algebra R B := instBAlg
  refine ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, hs, ?_⟩
  -- Proof comment: rewrite the maximal-ideal fiber returned by the finite-type helper as the
  -- ordinary special fiber `κ ⊗[R] B`.
  exact zeroSpecialFiberSubsingleton_of_closedFiberSubsingleton R hB

/-- Helper for Chap10 Lemma 10 153 3: the source-faithful bundled quasi-finite hypothesis
`Algebra.FiniteType.QuasiFinite R S` is exactly what is needed to convert clause `(11)` into the
zero-special-fiber splitting route of clause `(13)`. -/
lemma splitBundledFiniteTypeQuasiFiniteHasZeroSpecialFiber
    {S : Type (max u v)} [CommRing S] [Algebra R S]
    (hS : Algebra.FiniteType.QuasiFinite R S)
    (h :
      @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R _ _) :
    ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
      (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
      Nonempty (S ≃ₐ[R] A × B) ∧
        Subsingleton (κ ⊗[R] B) := by
  letI : Algebra.FiniteType R S := hS.finiteType
  letI : Algebra.QuasiFinite R S := hS.toQuasiFinite
  -- Proof comment: the bundled source owner supplies exactly the two instances needed by the
  -- finite-type helper proved just above.
  have hspl :
      ∃ (A : Type (max u v)) (_ : CommRing A) (_ : Algebra R A) (_ : Module.Finite R A)
        (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B),
        Nonempty (S ≃ₐ[R] A × B) ∧
          Subsingleton (κ ⊗[R] B) :=
    splitFiniteTypeQuasiFiniteHasZeroSpecialFiber R h
  exact hspl

/-- Helper for Chap10 Lemma 10 153 3: over a finite type algebra over a field, a quasi-finite
point is a minimal prime whose irreducible component is zero-dimensional. -/
private lemma minimalPrime_and_zeroDimQuotient_of_quasiFiniteAt
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (q : PrimeSpectrum A)
    [Algebra.QuasiFiniteAt K q.asIdeal] :
    q.asIdeal ∈ minimalPrimes A ∧ ringKrullDim (A ⧸ q.asIdeal) = 0 := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : IsJacobsonRing A :=
    @isJacobsonRing_of_finiteType K A _ _ inferInstance inferInstance inferInstance
  have hopen : IsOpen ({q} : Set (PrimeSpectrum A)) :=
    (@Algebra.QuasiFiniteAt.isClopen_singleton
      K A _ _ _ q inferInstance inferInstance inferInstance).isOpen
  have hclosedStable :
      IsClosed ({q} : Set (PrimeSpectrum A)) ∧
        StableUnderGeneralization ({q} : Set (PrimeSpectrum A)) :=
    ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
      0 2 rfl rfl).mp hopen
  have hmin : q.asIdeal ∈ minimalPrimes A := by
    rw [PrimeSpectrum.stableUnderGeneralization_singleton] at hclosedStable
    exact hclosedStable.2
  have hmax : q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hclosedStable.1
  letI : q.asIdeal.IsMaximal := hmax
  letI : Field (A ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  letI : Nontrivial (A ⧸ q.asIdeal) := by
    exact (Ideal.Quotient.nontrivial_iff).2 q.isPrime.ne_top
  have hdim0 : Ring.KrullDimLE 0 (A ⧸ q.asIdeal) := by
    infer_instance
  refine ⟨hmin, ?_⟩
  exact (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp hdim0

/-- Helper for Chap10 Lemma 10 153 3: over a finite type algebra over a field, a minimal prime
with zero-dimensional irreducible component is quasi-finite. -/
private lemma quasiFiniteAt_of_minimalPrime_and_zeroDimQuotient
    {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (q : PrimeSpectrum A)
    (hqmin : q.asIdeal ∈ minimalPrimes A)
    (hdim : ringKrullDim (A ⧸ q.asIdeal) = 0) :
    Algebra.QuasiFiniteAt K q.asIdeal := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : IsJacobsonRing A :=
    @isJacobsonRing_of_finiteType K A _ _ inferInstance inferInstance inferInstance
  letI : Nontrivial (A ⧸ q.asIdeal) := by
    exact (Ideal.Quotient.nontrivial_iff).2 q.isPrime.ne_top
  letI : Ring.KrullDimLE 0 (A ⧸ q.asIdeal) :=
    (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr hdim
  letI : IsDomain (A ⧸ q.asIdeal) := Ideal.Quotient.isDomain q.asIdeal
  have hfield : IsField (A ⧸ q.asIdeal) := Ring.KrullDimLE.isField_of_isDomain
  have hmax : q.asIdeal.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient q.asIdeal).mpr hfield
  have hclosed : IsClosed ({q} : Set (PrimeSpectrum A)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hmax
  have hopen : IsOpen ({q} : Set (PrimeSpectrum A)) := by
    -- Proof comment: in the Jacobson finite-type setting, a closed minimal point is already an
    -- open singleton.
    refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
      2 0 rfl rfl).mp ?_
    refine ⟨hclosed, ?_⟩
    rw [PrimeSpectrum.stableUnderGeneralization_singleton]
    exact hqmin
  exact Algebra.QuasiFiniteAt.of_isOpen_singleton q hopen

/-- Helper for Chap10 Lemma 10 153 3: for a finite type `R`-algebra `B`, quasi-finiteness at a
prime `q` over `maximalIdeal R` is equivalent to quasi-finiteness at the corresponding prime of
the closed fiber `((maximalIdeal R).Fiber B)`. -/
lemma quasiFiniteAt_iff_quasiFiniteAt_closedFiberPrime
    {B : Type v} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (q : PrimeSpectrum B)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal) :
    let pR : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
    let qf : PrimeSpectrum (pR.asIdeal.Fiber B) :=
      PrimeSpectrum.preimageEquivFiber R B pR
        ⟨q, by
          apply PrimeSpectrum.ext
          simpa using hq.symm⟩
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt pR.asIdeal.ResidueField qf.asIdeal := by
  let pR : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  let qf : PrimeSpectrum (pR.asIdeal.Fiber B) :=
    PrimeSpectrum.preimageEquivFiber R B pR
      ⟨q, by
        apply PrimeSpectrum.ext
        simpa using hq.symm⟩
  have hqf :
      Ideal.comap (includeRight : B →ₐ[R] pR.asIdeal.Fiber B).toRingHom qf.asIdeal = q.asIdeal := by
    -- Proof comment: the chosen fiber prime contracts back to the original prime `q`.
    change
      ((PrimeSpectrum.preimageEquivFiber R B pR).symm qf).1.asIdeal = q.asIdeal
    exact congrArg
      (fun x : PrimeSpectrum.comap (algebraMap R B) ⁻¹' {pR} ↦ x.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber R B pR).symm_apply_apply
        ⟨q, by
          apply PrimeSpectrum.ext
          simpa using hq.symm⟩)
  constructor
  · intro hqfin
    letI : Algebra.QuasiFiniteAt R q.asIdeal := hqfin
    -- Proof comment: base change to the residue field identifies the closed-fiber prime with the
    -- original prime over `maximalIdeal R`.
    exact Algebra.QuasiFiniteAt.baseChange q.asIdeal qf.asIdeal (by
      simpa using hqf.symm)
  · intro hqff
    letI : q.asIdeal.LiesOver (maximalIdeal R) := ⟨by
      simpa [Ideal.under_def] using hq⟩
    letI : Algebra.QuasiFiniteAt pR.asIdeal.ResidueField qf.asIdeal := hqff
    -- Proof comment: quasi-finiteness over the residue field descends back to quasi-finiteness of
    -- the original prime over `R`.
    exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
      (maximalIdeal R) q.asIdeal qf.asIdeal (by
        simpa using hqf)

/-- Helper for Chap10 Lemma 10 153 3: for a finite type `R`-algebra `B`, the source condition
that no prime of `B` above `maximalIdeal R` is quasi-finite is equivalent to saying that every
minimal prime of the closed fiber `((maximalIdeal R).Fiber B)` has positive-dimensional quotient.
-/
lemma closedFiberNonQuasiFinite_iff_positiveDimensional
    {B : Type v} [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    (∀ q : PrimeSpectrum B,
        maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal →
          ¬ Algebra.QuasiFiniteAt R q.asIdeal) ↔
      ∀ p : PrimeSpectrum ((maximalIdeal R).Fiber B),
        p.asIdeal ∈ minimalPrimes ((maximalIdeal R).Fiber B) →
          1 ≤ ringKrullDim (((maximalIdeal R).Fiber B) ⧸ p.asIdeal) := by
  let pR : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  constructor
  · intro h p hpmin
    by_contra hdimPos
    letI : Nontrivial (((maximalIdeal R).Fiber B) ⧸ p.asIdeal) :=
      (Ideal.Quotient.nontrivial_iff).2 p.isPrime.ne_top
    have hdim0 : ringKrullDim (((maximalIdeal R).Fiber B) ⧸ p.asIdeal) = 0 := by
      -- Proof comment: on a prime quotient over the closed fiber, failing positive dimension means
      -- the quotient has dimension zero.
      apply le_antisymm
      · exact le_of_not_gt (by
          simpa [WithBot.one_le_iff_pos] using hdimPos)
      · exact ringKrullDim_nonneg_of_nontrivial
    have hpqf :
        Algebra.QuasiFiniteAt pR.asIdeal.ResidueField p.asIdeal :=
      quasiFiniteAt_of_minimalPrime_and_zeroDimQuotient
        p hpmin hdim0
    let qp : PrimeSpectrum.comap (algebraMap R B) ⁻¹' {pR} :=
      (PrimeSpectrum.preimageEquivFiber R B pR).symm p
    let q : PrimeSpectrum B := qp.1
    have hq :
        maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal := by
      -- Proof comment: the inverse image of the closed-fiber prime is a prime of `B` over the
      -- maximal ideal by construction of `PrimeSpectrum.preimageEquivFiber`.
      simpa [pR, q, qp] using congrArg PrimeSpectrum.asIdeal qp.2.symm
    have hqp :
        (⟨q, by
            apply PrimeSpectrum.ext
            simpa [pR, q, qp] using hq.symm⟩ :
          PrimeSpectrum.comap (algebraMap R B) ⁻¹' {pR}) = qp := by
      apply Subtype.ext
      rfl
    let qf : PrimeSpectrum (pR.asIdeal.Fiber B) :=
      (PrimeSpectrum.preimageEquivFiber R B pR) <|
        ⟨q, by
          apply PrimeSpectrum.ext
          simpa [pR, q, qp] using hq.symm⟩
    have hqf_eq :
        qf = p := by
      calc
        qf = (PrimeSpectrum.preimageEquivFiber R B pR) qp := by
          simpa [qf, hqp]
        _ = p := by
          exact (PrimeSpectrum.preimageEquivFiber R B pR).apply_symm_apply p
    have hqfqf : Algebra.QuasiFiniteAt pR.asIdeal.ResidueField qf.asIdeal := by
      -- Proof comment: make the reconstructed fiber prime explicit so the quasi-finite transport
      -- lemma sees exactly the same normal form on both sides.
      simpa [qf, hqf_eq] using hpqf
    have hqqf : Algebra.QuasiFiniteAt R q.asIdeal := by
      -- Proof comment: transfer quasi-finiteness back from the closed fiber to the original prime
      -- over `maximalIdeal R`.
      exact (quasiFiniteAt_iff_quasiFiniteAt_closedFiberPrime R q hq).2 hqfqf
    exact h q hq hqqf
  · intro h q hq hqqf
    let qf : PrimeSpectrum (pR.asIdeal.Fiber B) :=
      (PrimeSpectrum.preimageEquivFiber R B pR) <|
        ⟨q, by
          apply PrimeSpectrum.ext
          simpa [pR] using hq.symm⟩
    have hqfqf :
        Algebra.QuasiFiniteAt pR.asIdeal.ResidueField qf.asIdeal :=
      (quasiFiniteAt_iff_quasiFiniteAt_closedFiberPrime R q hq).1 hqqf
    letI : Algebra.QuasiFiniteAt pR.asIdeal.ResidueField qf.asIdeal := hqfqf
    obtain ⟨hqfmin, hdim0⟩ :=
      (minimalPrime_and_zeroDimQuotient_of_quasiFiniteAt :
        (q : PrimeSpectrum (pR.asIdeal.Fiber B)) →
          [Algebra.QuasiFiniteAt pR.asIdeal.ResidueField q.asIdeal] →
            q.asIdeal ∈ minimalPrimes (pR.asIdeal.Fiber B) ∧
              ringKrullDim ((pR.asIdeal.Fiber B) ⧸ q.asIdeal) = 0) qf
    -- Proof comment: a quasi-finite closed-fiber prime is exactly a minimal prime with
    -- zero-dimensional quotient, contradicting the positive-dimensional target clause.
    have hpos : 1 ≤ ringKrullDim (((maximalIdeal R).Fiber B) ⧸ qf.asIdeal) := h qf hqfmin
    rw [hdim0] at hpos
    have hnot : ¬ ((1 : WithBot ℕ∞) ≤ 0) := by decide
    exact hnot hpos

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 3: a finite-indexed product decomposition is already a
product decomposition once we forget only the `Fintype` structure on the same index type. -/
lemma hasLocalRingProductDecomposition_of_hasFiniteLocalRingProductDecomposition
    {S : Type (max u w)} [CommRing S]
    (hS : @has_finite_local_ring_product_decomposition.{u, w} S _) :
    @has_local_ring_product_decomposition.{u, w} S _ := by
  rcases hS with ⟨ι, _instFintype, A, instAComm, instALocal, hS⟩
  exact ⟨ι, A, instAComm, instALocal, hS⟩

/-- Helper for Chap10 Lemma 10 153 3: a finite algebra over the local base has only finitely many
maximal ideals. -/
lemma finiteMaximalSpectrum_of_moduleFinite
    {S : Type (max u w)} [CommRing S] [Algebra R S] [Module.Finite R S] :
    Finite (MaximalSpectrum S) := by
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : Algebra.QuasiFinite R S :=
    (RingHom.quasiFinite_algebraMap).mp <|
      RingHom.QuasiFinite.of_finite <| RingHom.finite_algebraMap.mpr inferInstance
  let f : MaximalSpectrum S → Σ m : MaximalSpectrum R, m.asIdeal.primesOver S := fun M ↦ by
    let m : MaximalSpectrum R := ⟨Ideal.comap (algebraMap R S) M.asIdeal,
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M.asIdeal⟩
    letI : M.asIdeal.LiesOver m.asIdeal := ⟨by
      simpa [Ideal.under_def, m]⟩
    exact ⟨m, Ideal.primesOver.mk m.asIdeal M.asIdeal⟩
  have hf : Function.Injective f := by
    intro M N hMN
    have hIdeal : M.asIdeal = N.asIdeal := by
      simpa [f] using congrArg (fun q ↦ q.2.1) hMN
    exact MaximalSpectrum.ext hIdeal
  let _ : Subsingleton (MaximalSpectrum R) := ⟨fun m n ↦
    MaximalSpectrum.ext <| by
      rw [IsLocalRing.eq_maximalIdeal m.isMaximal, IsLocalRing.eq_maximalIdeal n.isMaximal]⟩
  let _ : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  let _ : ∀ m : MaximalSpectrum R, Fintype (m.asIdeal.primesOver S) := fun m ↦
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver m.asIdeal)
  let _ : Fintype (Σ m : MaximalSpectrum R, m.asIdeal.primesOver S) := inferInstance
  -- Proof comment: the local base contributes only one maximal ideal, and quasi-finiteness makes
  -- the finite algebra have finitely many primes above it.
  exact Finite.of_injective f hf

/-- Helper for Chap10 Lemma 10 153 3: finiteness of the maximal spectrum is preserved by a ring
equivalence. -/
lemma finiteMaximalSpectrum_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    [Finite (MaximalSpectrum A)] :
    Finite (MaximalSpectrum B) := by
  let eMax : MaximalSpectrum B ≃ MaximalSpectrum A := by
    refine
      { toFun := fun m ↦ ⟨Ideal.comap e m.asIdeal, inferInstance⟩
        invFun := fun m ↦ ⟨Ideal.map e m.asIdeal, inferInstance⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.map_comap_of_surjective e e.surjective
    · intro m
      apply MaximalSpectrum.ext
      simpa using m.asIdeal.comap_map_of_bijective e e.bijective
  -- Proof comment: transport maximal ideals across the ring equivalence and then package the
  -- resulting equivalence as finiteness of the target maximal spectrum.
  exact Finite.of_equiv (MaximalSpectrum A) eMax.symm

/-- Helper for Chap10 Lemma 10 153 3: for a finite `R`-algebra, an arbitrary product
decomposition by local rings upgrades to a finite product decomposition. -/
lemma hasFiniteLocalRingProductDecomposition_of_hasLocalRingProductDecomposition
    {S : Type (max u w)} [CommRing S] [Algebra R S] [Module.Finite R S]
    (hS : @has_local_ring_product_decomposition.{u, w} S _) :
    @has_finite_local_ring_product_decomposition.{u, w} S _ := by
  classical
  -- Route correction: the old statement without the local-base hypothesis was false for infinite
  -- product bases. Over a local base, finite generation forces only finitely many product factors.
  rcases hS with ⟨ι, A, instAComm, instALocal, hS⟩
  obtain ⟨e⟩ := hS
  have hfinMaxS : Finite (MaximalSpectrum S) := finiteMaximalSpectrum_of_moduleFinite R
  have hfinMaxPi : Finite (MaximalSpectrum ((i : ι) → A i)) := by
    letI : Finite (MaximalSpectrum S) := hfinMaxS
    exact finiteMaximalSpectrum_of_ringEquiv e
  have hfinι : Finite ι := by
    let f : ι → MaximalSpectrum ((i : ι) → A i) := fun i ↦
      ⟨Ideal.comap (Pi.evalRingHom A i) (IsLocalRing.maximalIdeal (A i)),
        Ideal.IsMaximal.comap_piEvalRingHom
          (inferInstance : (IsLocalRing.maximalIdeal (A i)).IsMaximal)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      let ei : (k : ι) → A k := Function.update (fun _ ↦ 0) i (1 : A i)
      have hei : ei ∉ (f i).asIdeal := by
        -- Proof comment: evaluating the indicator element at its distinguished coordinate gives
        -- `1`, which cannot lie in the maximal ideal of a local ring.
        simpa [f, ei] using
          (Ideal.ne_top_iff_one.mp (IsLocalRing.maximalIdeal.ne_top (A i)))
      have hej : ei ∈ (f j).asIdeal := by
        -- Proof comment: every other coordinate of the same indicator element is `0`, hence lies
        -- in the corresponding maximal ideal.
        show ¬ IsUnit (Pi.evalRingHom A j ei)
        simpa [Pi.evalRingHom, ei, show j ≠ i by
          exact fun h ↦ hne h.symm]
      exact hei ((congrArg MaximalSpectrum.asIdeal hij).symm ▸ hej)
    letI : Finite (MaximalSpectrum ((i : ι) → A i)) := hfinMaxPi
    exact Finite.of_injective f hf
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Proof comment: once the index type is finite, the original product decomposition already has
  -- the exact witness required by the finite-product predicate.
  exact ⟨ι, inferInstance, A, instAComm, instALocal, ⟨e⟩⟩

/-- Helper for Chap10 Lemma 10 153 3: a finite product decomposition is in particular a product
decomposition indexed by a finite type. -/
lemma localProduct_of_finiteLocalProduct :
    @finite_algebra_finite_local_product_property.{u, v} R _ →
      @finite_algebra_local_product_property.{u, v} R _ := by
  -- Proof comment: forget only the `Fintype` witness on the same product index after unpacking
  -- the source finite-product clause.
  intro h S _ _ _
  rcases h S with ⟨ι, _instFintype, A, instAComm, instALocal, hS⟩
  exact ⟨ι, A, instAComm, instALocal, hS⟩

/-- Helper for Chap10 Lemma 10 153 3: a product decomposition indexed by a finite type can be
upgraded to the finite-product formulation by choosing a `Fintype` structure. -/
lemma finiteLocalProduct_of_localProduct :
    @finite_algebra_local_product_property.{u, v} R _ →
      @finite_algebra_finite_local_product_property.{u, v} R _ := by
  -- Proof comment: apply the fixed-universe converter to each finite `R`-algebra in the source
  -- property package, without rebinding the witness type.
  intro h S _ _ _
  exact hasFiniteLocalRingProductDecomposition_of_hasLocalRingProductDecomposition R (h S)

/-- Helper for Chap10 Lemma 10 153 3: a finite module over the local base is already zero once its
special fiber `κ ⊗[R] M` is zero. -/
lemma subsingleton_of_finite_subsingletonSpecialFiber
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Subsingleton (κ ⊗[R] M)) :
    Subsingleton M := by
  -- Proof comment: this is exactly the local Nakayama criterion recorded by
  -- `IsLocalRing.subsingleton_tensorProduct`.
  exact (show Subsingleton (κ ⊗[R] M) ↔ Subsingleton M from
      IsLocalRing.subsingleton_tensorProduct).mp hM

/-- Helper for Chap10 Lemma 10 153 3: if an `R`-algebra is flat and isomorphic to a binary
product, then the left factor is flat over `R`. -/
lemma flat_of_algEquiv_prod_left
    {S A B : Type v} [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Module.Flat R S]
    (e : S ≃ₐ[R] A × B) :
    Module.Flat R A := by
  letI : Module.Flat R (A × B) := Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  -- Proof comment: the left factor is a retract of the product through the standard inclusion and
  -- projection, and retracts of flat modules stay flat.
  exact Module.Flat.of_retract
    (LinearMap.inl R A B)
    (LinearMap.fst R A B)
    (by ext x <;> rfl)

/-- Helper for Chap10 Lemma 10 153 3: a `κ`-algebra map from a finite product to the field `κ`
factors through one coordinate projection. -/
lemma fieldValuedAlgHom_factorsThroughFiniteLocalProductComponent
    {ι : Type v} [Fintype ι] [Nonempty ι] [DecidableEq ι] {A : ι → Type v}
    [∀ i, CommRing (A i)] [∀ i, Algebra κ (A i)]
    (φ : (∀ i, A i) →ₐ[κ] κ) :
    ∃ i : ι, ∃ ψ : A i →ₐ[κ] κ, φ = ψ.comp (Pi.evalAlgHom κ A i) := by
  classical
  let e : ι → (∀ j, A j) := fun i ↦ Pi.single i (1 : A i)
  have hsum : ∑ i, e i = 1 := by
    -- Proof comment: the standard orthogonal idempotents of the product sum to the identity.
    ext i
    simp [e]
  have hexists :
      ∃ i : ι, φ (e i) ≠ 0 := by
    -- Proof comment: after applying `φ` to the idempotent decomposition of `1`, at least one
    -- summand must survive because their sum is `1` in the field `κ`.
    by_contra h
    have hzero : ∀ i : ι, φ (e i) = 0 := by
      simpa using h
    have hone : (1 : κ) = 0 := by
      calc
        (1 : κ) = φ (∑ i, e i) := by rw [hsum, map_one]
        _ = ∑ i, φ (e i) := by rw [map_sum]
        _ = 0 := by simp [hzero]
    exact one_ne_zero hone
  obtain ⟨i, hi⟩ := hexists
  have hi_one : φ (e i) = 1 := by
    -- Proof comment: the chosen image is a nonzero idempotent of the field `κ`, hence it is `1`.
    have hidem :
        φ (e i) * φ (e i) = φ (e i) := by
      calc
        φ (e i) * φ (e i) = φ (e i * e i) := by
          symm
          exact map_mul φ (e i) (e i)
        _ = φ (e i) := by
          congr 1
          ext k
          by_cases hk : k = i
          · subst hk
            simp [e]
          · simp [e, hk]
    by_contra hne
    exact hi <| eq_zero_of_mul_eq_self_right hne hidem
  let ψ : A i →ₐ[κ] κ :=
    { toFun := fun a ↦ φ (Pi.single i a)
      map_one' := by
        -- Proof comment: the chosen idempotent acts as the identity through `φ`.
        simpa [e] using hi_one
      map_mul' := fun a b ↦ by
        -- Proof comment: multiplication is preserved because `Pi.single i` is multiplicative on
        -- the chosen coordinate.
        calc
          φ (Pi.single i (a * b)) = φ (Pi.single i a * Pi.single i b) := by
            congr 1
            ext j
            by_cases hj : j = i
            · subst hj
              simp
            · simp [Pi.single_eq_of_ne hj]
          _ = φ (Pi.single i a) * φ (Pi.single i b) := by
            rw [map_mul]
      map_zero' := by
        -- Proof comment: zero in the chosen factor maps to zero in the field.
        simp
      map_add' := fun a b ↦ by
        -- Proof comment: addition is also coordinatewise on the product.
        calc
          φ (Pi.single i (a + b)) = φ (Pi.single i a + Pi.single i b) := by
            congr 1
            ext j
            by_cases hj : j = i
            · subst hj
              simp
            · simp [Pi.single_eq_of_ne hj]
          _ = φ (Pi.single i a) + φ (Pi.single i b) := by
            rw [map_add]
      commutes' := fun c ↦ by
        -- Proof comment: scalars act diagonally on the product, and the chosen idempotent has
        -- image `1`, so the induced coordinate map remains a `κ`-algebra morphism.
        calc
          φ (Pi.single i (algebraMap κ (A i) c)) =
              φ ((algebraMap κ (∀ j, A j) c) * e i) := by
                congr 1
                ext j
                by_cases hj : j = i
                · subst hj
                  simp [e]
                · simp [e, hj]
          _ = φ (algebraMap κ (∀ j, A j) c) * φ (e i) := by
                rw [map_mul]
          _ = algebraMap κ κ c := by
                simp [AlgHom.commutes, hi_one] }
  refine ⟨i, ψ, ?_⟩
  ext x
  -- Proof comment: every product element is killed away from the chosen coordinate because the
  -- other idempotents map to `0` under `φ`.
  calc
    φ x = 1 * φ x := by simp
    _ = φ (e i) * φ x := by rw [hi_one]
    _ = φ (e i * x) := by
          symm
          exact map_mul φ (e i) x
    _ = φ (Pi.single i (x i)) := by
          congr 1
          ext j
          by_cases hj : j = i
          · subst hj
            simp [e]
          · simp [e, hj]
    _ = ψ (x i) := rfl

/-- Helper for Chap10 Lemma 10 153 3: for a finite flat module over the local base, every stalk
has the same rank as the stalk at the closed point. -/
lemma rankAtStalk_eq_closedPoint_of_finiteFlat
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.rankAtStalk M ⟨maximalIdeal R, inferInstance⟩ := by
  -- Proof comment: localize at the closed point and compare both stalks after base change to the
  -- local ring `R_(maximalIdeal R)`, where a finite flat module becomes free of constant rank.
  let S := Localization.AtPrime (maximalIdeal R)
  let hMaxLoc : IsLocalization.AtPrime S (maximalIdeal R) := inferInstance
  let pLoc : PrimeSpectrum S :=
    ⟨Ideal.map (algebraMap R S) p.asIdeal,
      @Ideal.isPrime_map_of_isLocalizationAtPrime
        R _ (maximalIdeal R) inferInstance S _ _ hMaxLoc p.asIdeal p.isPrime
        (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal)⟩
  have hpLoc_comap : PrimeSpectrum.comap (algebraMap R S) pLoc = p := by
    -- Proof comment: the prime of `Spec(R_(maximalIdeal R))` cut out by `p` contracts back to `p`.
    apply PrimeSpectrum.ext
    simpa [S, pLoc] using
      (@Ideal.under_map_of_isLocalizationAtPrime
        R _ (maximalIdeal R) inferInstance S _ _ hMaxLoc p.asIdeal p.isPrime
        (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal))
  have hclosed_comap :
      PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S) =
        ⟨maximalIdeal R, inferInstance⟩ := by
    -- Proof comment: the closed point of `Spec(R_(maximalIdeal R))` contracts to the maximal
    -- ideal of the original local ring.
    apply PrimeSpectrum.ext
    simpa [S] using
      (show
        Ideal.comap (algebraMap R (Localization.AtPrime (maximalIdeal R)))
            (IsLocalRing.maximalIdeal (Localization.AtPrime (maximalIdeal R))) =
          maximalIdeal R from
        Localization.AtPrime.comap_maximalIdeal)
  let T := TensorProduct R S M
  have hpBase : Module.rankAtStalk T pLoc = Module.rankAtStalk M p := by
    -- Proof comment: stalk rank is compatible with base change along localization.
    calc
      Module.rankAtStalk T pLoc =
          Module.rankAtStalk M (PrimeSpectrum.comap (algebraMap R S) pLoc) := by
              simpa [S] using
                (show Module.rankAtStalk (S ⊗[R] M) pLoc =
                    Module.rankAtStalk M (PrimeSpectrum.comap (algebraMap R S) pLoc) from
                  Module.rankAtStalk_baseChange pLoc)
      _ = Module.rankAtStalk M p := by
            rw [hpLoc_comap]
  have hclosedBase :
      Module.rankAtStalk T (IsLocalRing.closedPoint S) =
        Module.rankAtStalk M ⟨maximalIdeal R, inferInstance⟩ := by
    -- Proof comment: the same base-change formula identifies the stalk at the closed point.
    calc
      Module.rankAtStalk T (IsLocalRing.closedPoint S) =
          Module.rankAtStalk M
            (PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S)) := by
              simpa [S] using
                (show Module.rankAtStalk (S ⊗[R] M) (IsLocalRing.closedPoint S) =
                    Module.rankAtStalk M
                      (PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S)) from
                  Module.rankAtStalk_baseChange (IsLocalRing.closedPoint S))
      _ = Module.rankAtStalk M ⟨maximalIdeal R, inferInstance⟩ := by
            rw [hclosed_comap]
  letI : Module.Free S T := Module.free_of_flat_of_isLocalRing
  have hpFree : Module.rankAtStalk T pLoc = Module.finrank S T := by
    -- Proof comment: over the localized closed-point ring, finite flat modules are free and
    -- therefore have constant stalk rank.
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free : Module.rankAtStalk T = _) pLoc
  have hclosedFree : Module.rankAtStalk T (IsLocalRing.closedPoint S) = Module.finrank S T := by
    -- Proof comment: evaluate the same constant-rank formula at the closed point.
    exact congrFun
      (Module.rankAtStalk_eq_finrank_of_free : Module.rankAtStalk T = _)
      (IsLocalRing.closedPoint S)
  calc
    Module.rankAtStalk M p = Module.rankAtStalk T pLoc := by
          symm
          exact hpBase
    _ = Module.finrank S T := hpFree
    _ = Module.rankAtStalk T (IsLocalRing.closedPoint S) := by
          symm
          exact hclosedFree
    _ = Module.rankAtStalk M ⟨maximalIdeal R, inferInstance⟩ := hclosedBase

/-- Helper for Chap10 Lemma 10 153 3: a finite flat `R`-algebra whose closed fiber has dimension
`1` is already `R` as an `R`-algebra. -/
lemma algEquivOfFiniteFlatClosedFiberOneDim
    {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Flat R A]
    (hfinrank : Module.finrank κ (κ ⊗[R] A) = 1) :
    Nonempty (A ≃ₐ[R] R) := by
  letI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  have hfinrankA : Module.finrank R A = 1 := by
    -- Proof comment: base-changing a finite free module to the residue field preserves its rank.
    have htensor : Module.finrank κ (κ ⊗[R] A) = Module.finrank R A := by
      simpa using
        (show Module.finrank κ (κ ⊗[R] A) = Module.finrank κ κ * Module.finrank R A from
          Module.finrank_tensorProduct)
    rw [← htensor]
    exact hfinrank
  have hbij : Function.Bijective (algebraMap R A) := by
    -- Proof comment: a finite free rank-one algebra has bijective structure map.
    exact Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrankA
  -- Proof comment: package the bijective algebra map as an algebra equivalence and invert it to
  -- obtain the source-facing direction `A ≃ₐ[R] R`.
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId R A) hbij).symm⟩

/-- Helper for Chap10 Lemma 10 153 3: a chosen root `r : R` of the defining polynomial of a
standard-étale presentation, with denominator value a unit, determines a unique section to `R`
that sends the standard coordinate to `r`. -/
lemma standardEtalePresentation_existsUniqueSection_of_root
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) {r : R}
    (hf : P.f.eval r = 0) (hg : IsUnit (P.g.eval r)) :
    ∃! τ : S →ₐ[R] R, τ P.x = r := by
  -- Proof comment: the standard-étale universal property gives the section once the chosen
  -- coordinate satisfies the defining equation and inverts the denominator.
  let hmap : P.P.HasMap r := by
    constructor
    · simpa [Polynomial.aeval_def] using hf
    · simpa [Polynomial.aeval_def] using hg
  let τ : S →ₐ[R] R := (P.P.lift r hmap).comp P.equivRing.toAlgHom
  have hτx : τ P.x = r := by
    -- Proof comment: by construction the section sends the standard coordinate to `r`.
    change (P.P.lift r hmap) (P.equivRing P.x) = r
    rw [P.equivRing_x]
    exact P.P.lift_X r hmap
  refine ⟨τ, hτx, ?_⟩
  · -- Proof comment: any two sections out of a standard-étale presentation agree once they agree
    -- on the chosen coordinate.
    intro τ' hτ'
    apply P.hom_ext
    exact hτ'.trans hτx.symm

/-- Helper for Chap10 Lemma 10 153 3: a bijective residue-field map at a closed point identifies
`κ` with that closed point's residue field as an `R`-algebra. -/
noncomputable def closedPointResidueFieldAlgEquiv
    {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq)) :
    κ ≃ₐ[R] q.asIdeal.ResidueField := by
  -- Proof comment: first identify `κ = R / maximalIdeal R` with the residue field at the maximal
  -- ideal, then compose with the given bijective closed-point residue-field map.
  let eResidue :
      κ ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofBijective
      (show κ →ₐ[R] (maximalIdeal R).ResidueField from
        IsScalarTower.toAlgHom R (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  let eClosed :
      (maximalIdeal R).ResidueField ≃ₐ[R] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq)
      hκ
  exact eResidue.trans eClosed

/-- Helper for Chap10 Lemma 10 153 3: a bijective residue-field map at a closed point of a
standard-étale presentation determines the corresponding simple residue root and the denominator
nonvanishing condition in `κ`. -/
lemma standardEtaleClosedPointRootData
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq)) :
    ∃ a0 : κ,
      aeval a0 (P.f.map (residue R)) = 0 ∧
      aeval a0 ((P.f.derivative).map (residue R)) ≠ 0 ∧
      aeval a0 (P.g.map (residue R)) ≠ 0 := by
  -- Proof comment: this packages the residue-field transport data needed to run the standard
  -- étale chart argument for `1 → 8`.
  let e := closedPointResidueFieldAlgEquiv R q hq hκ
  let xq : q.asIdeal.ResidueField := algebraMap S q.asIdeal.ResidueField P.x
  let a0 : κ := e.symm xq
  have hxq : P.P.HasMap xq := by
    -- Proof comment: reduce the standard-étale relations for `P.x` modulo the chosen closed
    -- point to obtain the defining root and denominator conditions in its residue field.
    simpa [xq] using
      P.hasMap.map
        (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
  refine ⟨a0, ?_, ?_, ?_⟩
  · have hfκ : aeval a0 P.f = 0 := by
      -- Proof comment: transport the residue-field root equation back along the closed-point
      -- residue-field equivalence.
      apply e.injective
      rw [map_zero]
      calc
        e (aeval a0 P.f) = aeval (e a0) P.f := by
          symm
          exact Polynomial.aeval_algHom_apply e a0 P.f
        _ = aeval xq P.f := by simp [a0, xq]
        _ = 0 := hxq.1
    change (P.f.map (residue R)).eval a0 = 0
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using hfκ
  · intro hzero
    have hzero' : aeval a0 P.f.derivative = 0 := by
      change Polynomial.eval₂ (residue R) a0 P.f.derivative = 0
      simpa [Polynomial.aeval_def, Polynomial.eval_map] using hzero
    have hxzero : aeval xq P.f.derivative = 0 := by
      -- Proof comment: any vanishing of the transported derivative would contradict the
      -- standard-étale invertibility of `f'` at the closed point.
      calc
        aeval xq P.f.derivative = e (aeval a0 P.f.derivative) := by
          symm
          calc
            e (aeval a0 P.f.derivative) = aeval (e a0) P.f.derivative := by
              symm
              exact Polynomial.aeval_algHom_apply e a0 P.f.derivative
            _ = aeval xq P.f.derivative := by simp [a0, xq]
        _ = 0 := by rw [hzero', map_zero]
    exact (hxq.isUnit_derivative_f.ne_zero hxzero)
  · intro hzero
    have hzero' : aeval a0 P.g = 0 := by
      change Polynomial.eval₂ (residue R) a0 P.g = 0
      simpa [Polynomial.aeval_def, Polynomial.eval_map] using hzero
    have hxzero : aeval xq P.g = 0 := by
      -- Proof comment: the same transport shows that the chosen closed-point coordinate cannot
      -- annihilate the inverted denominator.
      calc
        aeval xq P.g = e (aeval a0 P.g) := by
          symm
          calc
            e (aeval a0 P.g) = aeval (e a0) P.g := by
              symm
              exact Polynomial.aeval_algHom_apply e a0 P.g
            _ = aeval xq P.g := by simp [a0, xq]
        _ = 0 := by rw [hzero', map_zero]
    exact (hxq.2.ne_zero hxzero)

/-- Helper for Chap10 Lemma 10 153 3: if a section of a standard-étale presentation sends the
standard coordinate to the closed-point coordinate determined by a bijective residue-field map,
then its pullback of `maximalIdeal R` is exactly that closed point. -/
lemma standardEtaleSectionComap_eq_closedPoint
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    {τ : S →ₐ[R] R}
    (hτ :
      residue R (τ P.x) =
        (closedPointResidueFieldAlgEquiv R q hq hκ).symm
          (algebraMap S q.asIdeal.ResidueField P.x)) :
    q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R) := by
  let e := closedPointResidueFieldAlgEquiv R q hq hκ
  let σ₁ : S →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R S q.asIdeal.ResidueField
  let σ₂ : S →ₐ[R] q.asIdeal.ResidueField :=
    e.toAlgHom.comp ((Algebra.ofId R κ).comp τ)
  have hσx : σ₂ P.x = σ₁ P.x := by
    -- Proof comment: the assumed residue-coordinate equality says exactly that the two maps to
    -- the closed-point residue field agree on the distinguished standard-étale generator.
    calc
      σ₂ P.x = e (residue R (τ P.x)) := by
        simp [σ₂, ResidueField.algebraMap_eq]
      _ = algebraMap S q.asIdeal.ResidueField P.x := by
        rw [hτ]
        simp [e]
      _ = σ₁ P.x := by
        simp [σ₁]
  have hσ : σ₂ = σ₁ := P.hom_ext hσx
  have hker₂ :
      RingHom.ker (σ₂ : S →+* q.asIdeal.ResidueField) =
        Ideal.comap (τ : S →+* R) (maximalIdeal R) := by
    ext x
    -- Proof comment: an element lands in the kernel of `σ₂` exactly when its `τ`-image has zero
    -- residue class in `κ`, i.e. lies in the maximal ideal.
    constructor
    · intro hx
      have hzero : residue R (τ x) = 0 := by
        apply e.injective
        simpa [σ₂, ResidueField.algebraMap_eq] using hx
      exact
        (maximalIdeal R).algebraMap_residueField_eq_zero.mp
          (by simpa [ResidueField.algebraMap_eq] using hzero)
    · intro hx
      have hzero : residue R (τ x) = 0 := by
        simpa [ResidueField.algebraMap_eq] using
          (maximalIdeal R).algebraMap_residueField_eq_zero.mpr hx
      simpa [σ₂, ResidueField.algebraMap_eq, hzero]
  have hker₁ :
      RingHom.ker (σ₁ : S →+* q.asIdeal.ResidueField) = q.asIdeal := by
    ext x
    change algebraMap S q.asIdeal.ResidueField x = 0 ↔ x ∈ q.asIdeal
    simpa using
      (Ideal.algebraMap_residueField_eq_zero :
        algebraMap S q.asIdeal.ResidueField x = 0 ↔ x ∈ q.asIdeal)
  calc
    q.asIdeal = RingHom.ker (σ₁ : S →+* q.asIdeal.ResidueField) := hker₁.symm
    _ = RingHom.ker (σ₂ : S →+* q.asIdeal.ResidueField) := by rw [hσ]
    _ = Ideal.comap (τ : S →+* R) (maximalIdeal R) := hker₂

/-- Helper for Chap10 Lemma 10 153 3: a section whose pullback of `maximalIdeal R` is the chosen
closed point sends the standard coordinate to the corresponding residue-class coordinate. -/
lemma standardEtaleSection_residue_eq_closedPointCoordinate
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    {τ : S →ₐ[R] R}
    (hτ : q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R)) :
    residue R (τ P.x) =
      (closedPointResidueFieldAlgEquiv R q hq hκ).symm
        (algebraMap S q.asIdeal.ResidueField P.x) := by
  let e := closedPointResidueFieldAlgEquiv R q hq hκ
  apply e.injective
  have hclass :
      algebraMap S q.asIdeal.ResidueField P.x =
        algebraMap S q.asIdeal.ResidueField (algebraMap R S (τ P.x)) := by
    -- Proof comment: the chosen section and the closed point define the same residue class
    -- because their difference lies in the contracted prime `q`.
    apply sub_eq_zero.mp
    have hmem : P.x - algebraMap R S (τ P.x) ∈ q.asIdeal := by
      rw [hτ]
      change τ (P.x - algebraMap R S (τ P.x)) ∈ maximalIdeal R
      simp
    simpa [map_sub] using Ideal.algebraMap_residueField_eq_zero.mpr hmem
  -- Proof comment: after transporting through the closed-point residue-field equivalence, the
  -- section value and the distinguished closed-point coordinate become the same class in `κ(q)`.
  calc
    e (residue R (τ P.x)) = algebraMap R q.asIdeal.ResidueField (τ P.x) := by
      change
        Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq
          (algebraMap R (maximalIdeal R).ResidueField (τ P.x)) = _
      simp
    _ = algebraMap S q.asIdeal.ResidueField (algebraMap R S (τ P.x)) := by
      simp [IsScalarTower.algebraMap_eq R S q.asIdeal.ResidueField]
    _ = algebraMap S q.asIdeal.ResidueField P.x := hclass.symm
    _ = e (e.symm (algebraMap S q.asIdeal.ResidueField P.x)) := by
      simpa using (e.apply_symm_apply (algebraMap S q.asIdeal.ResidueField P.x)).symm

/-- Helper for Chap10 Lemma 10 153 3: on a standard-étale chart, two retractions with the same
closed point coincide. -/
lemma standardEtaleSection_eq_of_sameClosedPoint
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    {τ₁ τ₂ : S →ₐ[R] R}
    (hτ₁ : q.asIdeal = Ideal.comap (τ₁ : S →+* R) (maximalIdeal R))
    (hτ₂ : q.asIdeal = Ideal.comap (τ₂ : S →+* R) (maximalIdeal R)) :
    τ₁ = τ₂ := by
  let e := closedPointResidueFieldAlgEquiv R q hq hκ
  let xq : q.asIdeal.ResidueField := algebraMap S q.asIdeal.ResidueField P.x
  have hxq : P.P.HasMap xq := by
    -- Proof comment: reducing the standard-étale relations modulo the chosen closed point gives
    -- the root and denominator data for the closed-point coordinate.
    simpa [xq] using
      P.hasMap.map (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
  have hcoord₁ :
      residue R (τ₁ P.x) = e.symm xq :=
    standardEtaleSection_residue_eq_closedPointCoordinate R P q hq hκ hτ₁
  have hcoord₂ :
      residue R (τ₂ P.x) = e.symm xq :=
    standardEtaleSection_residue_eq_closedPointCoordinate R P q hq hκ hτ₂
  have hresEq : residue R (τ₁ P.x) = residue R (τ₂ P.x) := by
    rw [hcoord₁, hcoord₂]
  have hroot₁ : P.f.IsRoot (τ₁ P.x) := by
    -- Proof comment: each section sends the distinguished coordinate to a root of the defining
    -- polynomial because `P.x` already satisfies the standard-étale equation in `S`.
    rw [Polynomial.IsRoot]
    calc
      aeval (τ₁ P.x) P.f = τ₁ (aeval P.x P.f) := by
        exact Polynomial.aeval_algHom_apply τ₁ P.x P.f
      _ = 0 := by
        simpa using congrArg τ₁ P.hasMap.1
  have hroot₂ : P.f.IsRoot (τ₂ P.x) := by
    -- Proof comment: the same polynomial relation holds for the second section.
    rw [Polynomial.IsRoot]
    calc
      aeval (τ₂ P.x) P.f = τ₂ (aeval P.x P.f) := by
        exact Polynomial.aeval_algHom_apply τ₂ P.x P.f
      _ = 0 := by
        simpa using congrArg τ₂ P.hasMap.1
  have hresDeriv₁ : residue R (eval (τ₁ P.x) P.f.derivative) ≠ 0 := by
    -- Proof comment: transport the closed-point nonvanishing of `f'` back along the residue-field
    -- comparison determined by the first section.
    intro hzero
    have hzeroκ : aeval (residue R (τ₁ P.x)) P.f.derivative = 0 := by
      simpa [Polynomial.aeval_def, Polynomial.eval_map] using hzero
    have hxzero : aeval xq P.f.derivative = 0 := by
      calc
        aeval xq P.f.derivative = e (aeval (residue R (τ₁ P.x)) P.f.derivative) := by
          symm
          calc
            e (aeval (residue R (τ₁ P.x)) P.f.derivative) =
                aeval (e (residue R (τ₁ P.x))) P.f.derivative := by
              symm
              exact Polynomial.aeval_algHom_apply e (residue R (τ₁ P.x)) P.f.derivative
            _ = aeval xq P.f.derivative := by
              rw [hcoord₁]
              simp [xq]
        _ = 0 := by rw [hzeroκ, map_zero]
    exact hxq.isUnit_derivative_f.ne_zero hxzero
  have hder₁ : eval (τ₁ P.x) P.f.derivative ∉ maximalIdeal R := by
    -- Proof comment: nonzero residue class in a local ring is equivalent to being a unit, hence
    -- to avoiding the maximal ideal.
    rw [IsLocalRing.notMem_maximalIdeal]
    exact (residue_ne_zero_iff_isUnit _).mp hresDeriv₁
  have hcongr : τ₁ P.x ≡ τ₂ P.x [SMOD maximalIdeal R] := by
    -- Proof comment: equal residues mean the two lifted roots are congruent modulo the maximal
    -- ideal, which is the congruence input for Lemma `10.153.2`.
    exact SModEq.sub_mem.mpr <|
      (residue_eq_zero_iff (τ₁ P.x - τ₂ P.x)).mp <| by
        simpa [map_sub, hresEq]
  have hxEq : τ₁ P.x = τ₂ P.x :=
    eq_of_polynomial_roots_congruent_of_derivative_not_mem_maximalIdeal
      hroot₁ hroot₂ hcongr hder₁
  -- Proof comment: the standard-étale presentation is generated by the distinguished coordinate,
  -- so equality there forces equality of the two sections.
  exact P.hom_ext hxEq

/-- Helper for Chap10 Lemma 10 153 3: localizing away from an element outside a chosen closed
point transports that point, its contraction to `maximalIdeal R`, and the residue-field
bijection to the localized algebra. -/
lemma localizationAwayClosedPointTransport
    {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    {f : S} (hfq : f ∉ q.asIdeal) :
    ∃ qf : PrimeSpectrum (Localization.Away f),
      ∃ hqfS : PrimeSpectrum.comap (algebraMap S (Localization.Away f)) qf = q,
      ∃ hqf :
        maximalIdeal R = Ideal.comap (algebraMap R (Localization.Away f)) qf.asIdeal,
        Function.Bijective
          (Ideal.ResidueField.mapₐ (maximalIdeal R) qf.asIdeal
            (Algebra.ofId R (Localization.Away f)) hqf) := by
  have hq_mem_range :
      q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
    -- Proof comment: a prime of the away localization exists exactly above primes where the
    -- localized denominator avoids the chosen prime.
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa [PrimeSpectrum.mem_basicOpen] using hfq
  rcases hq_mem_range with ⟨qf, hqfS⟩
  have hqfS_ideal :
      Ideal.comap (algebraMap S (Localization.Away f)) qf.asIdeal = q.asIdeal := by
    simpa using congrArg PrimeSpectrum.asIdeal hqfS
  have hqf :
      maximalIdeal R = Ideal.comap (algebraMap R (Localization.Away f)) qf.asIdeal := by
    -- Proof comment: contract the transported prime first to `S`, then to the local base.
    calc
      maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal := hq
      _ = Ideal.comap (algebraMap R S)
            (Ideal.comap (algebraMap S (Localization.Away f)) qf.asIdeal) := by
              rw [hqfS_ideal]
      _ = Ideal.comap (algebraMap R (Localization.Away f)) qf.asIdeal := by
              rfl
  have hqfκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ q.asIdeal qf.asIdeal
          (IsScalarTower.toAlgHom R S (Localization.Away f)) hqfS_ideal.symm) := by
    -- Proof comment: localization maps are surjective on stalks, so they induce bijections on
    -- residue fields at matching primes.
    exact
      (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers f)
        (Localization.Away f)).residueFieldMap_bijective q.asIdeal qf.asIdeal hqfS_ideal.symm
  have hcomp :
      Ideal.ResidueField.mapₐ (maximalIdeal R) qf.asIdeal
          (Algebra.ofId R (Localization.Away f)) hqf =
        (Ideal.ResidueField.mapₐ q.asIdeal qf.asIdeal
            (IsScalarTower.toAlgHom R S (Localization.Away f)) hqfS_ideal.symm).comp
          (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq) := by
    -- Proof comment: both residue-field maps are the same after precomposing with the structural
    -- map from `R`, so the residue-field extensionality lemma identifies them.
    apply Ideal.ResidueField.algHom_ext
    exact AlgHom.ext fun x ↦ by
      simp [AlgHom.comp_apply]
  refine ⟨qf, hqfS, hqf, ?_⟩
  rw [hcomp]
  exact hqfκ.comp hκ

/-- Helper for Chap10 Lemma 10 153 3: henselian local rings satisfy the unique étale-retraction
criterion at closed points with unchanged residue field. -/
lemma standardEtaleRetractionUnique_of_henselian
    {S : Type v} [CommRing S] [Algebra R S]
    (P : StandardEtalePresentation R S) (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    (hHens : HenselianLocalRing R) :
    ∃! τ : S →ₐ[R] R, q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R) := by
  let e := closedPointResidueFieldAlgEquiv R q hq hκ
  let xq : q.asIdeal.ResidueField := algebraMap S q.asIdeal.ResidueField P.x
  let a0 : κ := e.symm xq
  have hxq : P.P.HasMap xq := by
    -- Proof comment: reducing the standard-étale relations at the chosen closed point produces
    -- the defining root and denominator data for the closed-point coordinate.
    simpa [xq] using
      P.hasMap.map (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
  have hf0 : aeval a0 P.f = 0 := by
    -- Proof comment: transport the root relation on `xq` back through the residue-field
    -- equivalence to obtain an actual residue root of the defining polynomial.
    apply e.injective
    rw [map_zero]
    calc
      e (aeval a0 P.f) = aeval (e a0) P.f := by
        symm
        exact Polynomial.aeval_algHom_apply e a0 P.f
      _ = aeval xq P.f := by simp [a0, xq]
      _ = 0 := hxq.1
  have hder0 : aeval a0 P.f.derivative ≠ 0 := by
    intro hzero
    have hxzero : aeval xq P.f.derivative = 0 := by
      -- Proof comment: a vanishing derivative at the transported residue root would contradict
      -- the standard-étale invertibility of `f'` at the closed point.
      calc
        aeval xq P.f.derivative = e (aeval a0 P.f.derivative) := by
          symm
          calc
            e (aeval a0 P.f.derivative) = aeval (e a0) P.f.derivative := by
              symm
              exact Polynomial.aeval_algHom_apply e a0 P.f.derivative
            _ = aeval xq P.f.derivative := by simp [a0, xq]
        _ = 0 := by rw [hzero, map_zero]
    exact hxq.isUnit_derivative_f.ne_zero hxzero
  have hg0 : aeval a0 P.g ≠ 0 := by
    intro hzero
    have hxzero : aeval xq P.g = 0 := by
      -- Proof comment: the denominator remains invertible at the chosen closed point, so its
      -- residue cannot vanish after transport back to `κ`.
      calc
        aeval xq P.g = e (aeval a0 P.g) := by
          symm
          calc
            e (aeval a0 P.g) = aeval (e a0) P.g := by
              symm
              exact Polynomial.aeval_algHom_apply e a0 P.g
            _ = aeval xq P.g := by simp [a0, xq]
        _ = 0 := by rw [hzero, map_zero]
    exact hxq.2.ne_zero hxzero
  have hSimple :
      ∀ f : R[X], f.Monic → ∀ b0 : κ,
        aeval b0 f = 0 →
        aeval b0 f.derivative ≠ 0 →
        ∃ b : R, f.IsRoot b ∧ residue R b = b0 :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp hHens
  obtain ⟨a, haRoot, haResid⟩ := hSimple P.f P.P.monic_f a0 hf0 hder0
  have hgResidue : residue R (P.g.eval a) ≠ 0 := by
    -- Proof comment: substitute the lifted residue root into the reduced denominator and rewrite
    -- the resulting residue evaluation back to the closed-point nonvanishing statement.
    have hgResidue' : Polynomial.eval₂ (residue R) (residue R a) P.g ≠ 0 := by
      simpa [Polynomial.aeval_def, haResid] using hg0
    simpa [Polynomial.eval₂_at_apply] using hgResidue'
  have hgUnit : IsUnit (P.g.eval a) := by
    -- Proof comment: nonvanishing of the transported denominator in the residue field upgrades
    -- to a unit in the local base.
    exact (residue_ne_zero_iff_isUnit (P.g.eval a)).mp hgResidue
  obtain ⟨τ, hτx, _hτuniqx⟩ :
      ∃! τ : S →ₐ[R] R, τ P.x = a :=
    standardEtalePresentation_existsUniqueSection_of_root R P
      (by simpa [IsRoot] using haRoot) hgUnit
  have hτcoord :
      residue R (τ P.x) =
        (closedPointResidueFieldAlgEquiv R q hq hκ).symm
          (algebraMap S q.asIdeal.ResidueField P.x) := by
    -- Proof comment: the constructed section sends the standard coordinate to the lifted root,
    -- whose residue class is exactly the chosen closed-point coordinate.
    calc
      residue R (τ P.x) = residue R a := by simpa [hτx]
      _ = a0 := haResid
      _ = e.symm (algebraMap S q.asIdeal.ResidueField P.x) := by rfl
  have hτq : q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R) :=
    standardEtaleSectionComap_eq_closedPoint R P q hq hκ hτcoord
  refine ⟨τ, hτq, ?_⟩
  intro τ' hτ'
  -- Proof comment: once both sections contract `maximalIdeal R` to the same closed point, the
  -- standard-étale uniqueness lemma identifies them.
  exact standardEtaleSection_eq_of_sameClosedPoint R P q hq hκ hτ' hτq

/-- Helper for Chap10 Lemma 10 153 3: a retraction to the local base localizes uniquely at any
element outside the chosen closed point, and the localized retraction still contracts to the
transported closed point. -/
lemma localizeRetractionAtClosedPoint
    {S : Type v} [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) {f : S} {τ : S →ₐ[R] R}
    (hτ : q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R))
    (hfq : f ∉ q.asIdeal)
    {qf : PrimeSpectrum (Localization.Away f)}
    (hqfS : PrimeSpectrum.comap (algebraMap S (Localization.Away f)) qf = q) :
    ∃ τf : Localization.Away f →ₐ[R] R,
      τf.comp (IsScalarTower.toAlgHom R S (Localization.Away f)) = τ ∧
        qf.asIdeal = Ideal.comap (τf : Localization.Away f →+* R) (maximalIdeal R) := by
  have hτf_unit : IsUnit (τ f) := by
    -- Proof comment: because `f` stays outside the chosen closed point, its image under the
    -- retraction avoids the maximal ideal and is therefore a unit in the local base.
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    exact hfq <| by simpa [hτ] using hmem
  have hunits : ∀ y : Submonoid.powers f, IsUnit (τ y) := by
    rintro ⟨y, ⟨n, rfl⟩⟩
    simpa [map_pow] using hτf_unit.pow n
  let τf : Localization.Away f →ₐ[R] R := IsLocalization.liftAlgHom hunits
  have hτf_comp :
      τf.comp (IsScalarTower.toAlgHom R S (Localization.Away f)) = τ := by
    -- Proof comment: the localized map is characterized by agreeing with the original
    -- retraction on the source algebra.
    ext x
    simpa [τf] using IsLocalization.lift_eq hunits x
  let qτf : PrimeSpectrum (Localization.Away f) :=
    ⟨Ideal.comap (τf : Localization.Away f →+* R) (maximalIdeal R), inferInstance⟩
  have hqτfS : PrimeSpectrum.comap (algebraMap S (Localization.Away f)) qτf = q := by
    -- Proof comment: contracting the localized pullback of `maximalIdeal R` recovers the original
    -- closed point because the localized map extends `τ`.
    ext x
    change τf (algebraMap S (Localization.Away f) x) ∈ maximalIdeal R ↔ x ∈ q.asIdeal
    have hx :
        τf (algebraMap S (Localization.Away f) x) = τ x := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun φ : S →ₐ[R] R ↦ φ x) hτf_comp
    rw [hx]
    simpa [hτ]
  have hqEq : qτf = qf := by
    -- Proof comment: localization away from one element is an open embedding on spectra, so a
    -- localized closed point is determined by its contraction to `S`.
    exact
      (PrimeSpectrum.localization_away_isOpenEmbedding
          (Localization.Away f) f).toIsEmbedding.injective
        (hqτfS.trans hqfS.symm)
  refine ⟨τf, hτf_comp, ?_⟩
  simpa [qτf] using congrArg PrimeSpectrum.asIdeal hqEq.symm

/-- Helper for Chap10 Lemma 10 153 3: henselian local rings satisfy the unique étale-retraction
criterion at closed points with unchanged residue field. -/
lemma etaleRetractionUnique_of_henselian :
    HenselianLocalRing R →
      @etale_retraction_unique_property.{u, v} R _ _ := by
  intro hHens S _ _ _ q hq hκ
  -- Route correction: the old route tried to descend a chart retraction globally. The actual
  -- source-faithful proof only needs one chart-local theorem plus localization of any competing
  -- global retraction.
  have hEtaleAt : Algebra.IsEtaleAt R q.asIdeal := by
    -- Proof comment: an étale algebra is étale at every prime, so the chosen closed point admits
    -- a standard-étale basic-open neighborhood.
    have hall : Algebra.etaleLocus R S = Set.univ :=
      (Algebra.etaleLocus_eq_univ_iff_etale).2 inferInstance
    have hmem : q ∈ Algebra.etaleLocus R S := by
      simpa [hall]
    simpa [Algebra.mem_etaleLocus_iff] using hmem
  letI : Algebra.IsEtaleAt R q.asIdeal := hEtaleAt
  obtain ⟨f, hfq, hfstd⟩ :=
    @Algebra.IsEtaleAt.exists_isStandardEtale R S _ _ _ q.asIdeal inferInstance inferInstance
      hEtaleAt
  letI : Algebra.IsStandardEtale R (Localization.Away f) := hfstd
  obtain ⟨qf, hqfS, hqf, hκf⟩ :=
    localizationAwayClosedPointTransport R q hq hκ hfq
  let hP : Nonempty (StandardEtalePresentation R (Localization.Away f)) := inferInstance
  let P : StandardEtalePresentation R (Localization.Away f) := hP.some
  obtain ⟨τf, hτf_qf, huniqf⟩ :=
    standardEtaleRetractionUnique_of_henselian R P qf hqf hκf hHens
  let τ : S →ₐ[R] R := τf.comp (IsScalarTower.toAlgHom R S (Localization.Away f))
  have hτq : q.asIdeal = Ideal.comap (τ : S →+* R) (maximalIdeal R) := by
    -- Proof comment: existence is just precomposition of the unique localized retraction with
    -- the chart map `S → S[1/f]`.
    calc
      q.asIdeal = Ideal.comap (algebraMap S (Localization.Away f)) qf.asIdeal := by
        simpa using (congrArg PrimeSpectrum.asIdeal hqfS).symm
      _ = Ideal.comap (algebraMap S (Localization.Away f))
            (Ideal.comap (τf : Localization.Away f →+* R) (maximalIdeal R)) := by
              rw [hτf_qf]
      _ = Ideal.comap
            (((τf : Localization.Away f →+* R).comp
              (algebraMap S (Localization.Away f))))
            (maximalIdeal R) := by
              rw [Ideal.comap_comap]
      _ = Ideal.comap (τ : S →+* R) (maximalIdeal R) := rfl
  refine ⟨τ, hτq, ?_⟩
  intro τ' hτ'
  obtain ⟨τf', hτf'_comp, hτf'_qf⟩ :=
    localizeRetractionAtClosedPoint R q hτ' hfq hqfS
  have hEqf : τf' = τf := huniqf τf' hτf'_qf
  ext x
  -- Proof comment: equality of localized retractions pulls back to equality on `S` by evaluating
  -- both maps on the canonical image of `x` in the chart localization.
  calc
    τ' x = τf' (algebraMap S (Localization.Away f) x) := by
      symm
      simpa [AlgHom.comp_apply] using
        congrArg (fun φ : S →ₐ[R] R ↦ φ x) hτf'_comp
    _ = τf (algebraMap S (Localization.Away f) x) := by rw [hEqf]
    _ = τ x := rfl

/-- Helper for Chap10 Lemma 10 153 3: every element of the closed fiber over the maximal ideal
is the image of an element of the original algebra. -/
lemma closedFiber_includeRight_surjective
    {S : Type v} [CommRing S] [Algebra R S] :
    Function.Surjective
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (maximalIdeal R).Fiber S) := by
  -- Proof comment: this is the special-fiber surjectivity input used to choose an idempotent
  -- separator for the distinguished closed point.
  simpa using
    (show Function.Surjective (includeRight : S →ₐ[R] (maximalIdeal R).Fiber S) from
      includeRight_surjective S ((maximalIdeal R).algebraMap_residueField_surjective))

/-- Helper for Chap10 Lemma 10 153 3: on an étale algebra, two retractions cutting out the same
closed point are equal. -/
lemma etaleRetractionSubsingleton_of_sameClosedPoint
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (q : PrimeSpectrum S)
    (hq : maximalIdeal R = Ideal.comap (algebraMap R S) q.asIdeal)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) q.asIdeal (Algebra.ofId R S) hq))
    {τ₁ τ₂ : S →ₐ[R] R}
    (hτ₁ : q.asIdeal = Ideal.comap (τ₁ : S →+* R) (maximalIdeal R))
    (hτ₂ : q.asIdeal = Ideal.comap (τ₂ : S →+* R) (maximalIdeal R)) :
    τ₁ = τ₂ := by
  have hEtaleAt : Algebra.IsEtaleAt R q.asIdeal := by
    -- Proof comment: an étale algebra is étale at every prime, so the chosen closed point admits
    -- a standard-étale basic-open neighborhood.
    have hall : Algebra.etaleLocus R S = Set.univ :=
      (Algebra.etaleLocus_eq_univ_iff_etale).2 inferInstance
    have hmem : q ∈ Algebra.etaleLocus R S := by
      simpa [hall]
    simpa [Algebra.mem_etaleLocus_iff] using hmem
  letI : Algebra.IsEtaleAt R q.asIdeal := hEtaleAt
  obtain ⟨f, hfq, hfstd⟩ :=
    @Algebra.IsEtaleAt.exists_isStandardEtale R S _ _ _ q.asIdeal inferInstance inferInstance
      hEtaleAt
  letI : Algebra.IsStandardEtale R (Localization.Away f) := hfstd
  obtain ⟨qf, hqfS, hqf, hκf⟩ :=
    localizationAwayClosedPointTransport R q hq hκ hfq
  obtain ⟨τf₁, hτf₁_comp, hτf₁_qf⟩ :=
    localizeRetractionAtClosedPoint R q hτ₁ hfq hqfS
  obtain ⟨τf₂, hτf₂_comp, hτf₂_qf⟩ :=
    localizeRetractionAtClosedPoint R q hτ₂ hfq hqfS
  let hP : Nonempty (StandardEtalePresentation R (Localization.Away f)) := inferInstance
  let P : StandardEtalePresentation R (Localization.Away f) := hP.some
  have hEqf : τf₁ = τf₂ :=
    standardEtaleSection_eq_of_sameClosedPoint R P qf hqf hκf hτf₁_qf hτf₂_qf
  ext x
  -- Proof comment: equality of the localized sections pulls back to equality on `S` by evaluating
  -- both maps after the canonical localization map.
  calc
    τ₁ x = τf₁ (algebraMap S (Localization.Away f) x) := by
      symm
      simpa [AlgHom.comp_apply] using
        congrArg (fun φ : S →ₐ[R] R ↦ φ x) hτf₁_comp
    _ = τf₂ (algebraMap S (Localization.Away f) x) := by rw [hEqf]
    _ = τ₂ x := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun φ : S →ₐ[R] R ↦ φ x) hτf₂_comp

/-- Helper for Chap10 Lemma 10 153 3: the unique étale-retraction clause descends coprime
factorizations with degree control from the étale neighborhood furnished by Lemma `10.143.13`. -/
-- TODO: first normalize the chosen nonzero residue factor by its leading coefficient so that the
-- monic étale lifting theorem applies; the new helpers `monic_normalizeByLeadingCoeff` and
-- `natDegree_normalizeByLeadingCoeff` isolate exactly this interface step before descending the
-- lifted factorization along the retraction `R' →ₐ[R] R`.
lemma coprimeFactorizationLiftWithDegree_of_etaleRetractionUnique :
    @etale_retraction_unique_property.{u, v} R _ _ →
      @coprime_factorization_lift_with_degree_property.{u} R _ _ := by
  intro h f g0 h0 hg0 hfac hcop
  by_cases hh0 : h0 = 0
  · have hg0_unit : IsUnit g0 := by
      -- Proof comment: when the complementary residue factor vanishes, coprimeness says the
      -- chosen factor is already a unit, so the lift can be taken trivially.
      simpa [hh0, isCoprime_zero_right] using hcop
    obtain ⟨c, hcunit, rfl⟩ := Polynomial.isUnit_iff.mp hg0_unit
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
    have hres : residue R r = c := by
      simpa [ResidueField.algebraMap_eq] using hr
    have hrunit : IsUnit r := by
      apply (residue_ne_zero_iff_isUnit r).mp
      rw [hres]
      exact hcunit.ne_zero
    obtain ⟨u, rfl⟩ := hrunit
    let g : R[X] := Polynomial.C (↑u : R)
    let h' : R[X] := Polynomial.C (↑(u⁻¹) : R) * f
    have hfzero : f.map (residue R) = 0 := by
      -- Proof comment: the residue factorization collapses to zero once the complementary factor
      -- is zero.
      simpa [hh0] using hfac
    refine ⟨g, h', ?_, ?_, ?_, ?_⟩
    · -- Proof comment: multiplying by the lifted constant unit and its inverse gives back `f`.
      dsimp [g, h']
      have hC :
          (Polynomial.C (↑u : R) : R[X]) * Polynomial.C (↑(u⁻¹) : R) = 1 := by
        rw [Polynomial.C_mul']
        simp
      calc
        f = 1 * f := by simp
        _ = ((Polynomial.C (↑u : R) : R[X]) * Polynomial.C (↑(u⁻¹) : R)) * f := by
          rw [← hC]
        _ = Polynomial.C (↑u : R) * (Polynomial.C (↑(u⁻¹) : R) * f) := by
          simp [mul_assoc]
    · -- Proof comment: the lifted unit reduces to the original unit polynomial `g0`.
      dsimp [g]
      simp [hres]
    · -- Proof comment: the complementary factor still reduces to zero because `f` does.
      dsimp [h']
      rw [Polynomial.map_mul, hfzero]
      simpa [hh0]
    · -- Proof comment: both the lifted factor and its residue are nonzero constants, so both
      -- degrees are zero.
      dsimp [g]
      simp [Units.ne_zero, hcunit.ne_zero]
  · -- TODO: in the genuine nonzero branch, normalize `f` and the chosen residue factor by their
    -- leading coefficients, apply the monic étale lifting theorem upstairs, retract along clause
    -- `(8)`, and then undo the unit scalings while preserving the degree witness.
    let g0' : κ[X] := Polynomial.C g0.leadingCoeff⁻¹ * g0
    let h0' : κ[X] := Polynomial.C h0.leadingCoeff⁻¹ * h0
    have hnorm :
        g0'.Monic ∧
          h0'.Monic ∧
          IsCoprime g0' h0' ∧
          g0'.natDegree = g0.natDegree ∧
          h0'.natDegree = h0.natDegree ∧
          g0' * h0' = Polynomial.C ((g0 * h0).leadingCoeff)⁻¹ * (g0 * h0) := by
      simpa [g0', h0'] using
        normalizeResidueFactorizationToMonicPair (K := κ) (g := g0) (h := h0) hg0 hh0 hcop
    have hg0_monic : g0'.Monic := hnorm.1
    have hh0_monic : h0'.Monic := hnorm.2.1
    have hcop_monic : IsCoprime g0' h0' := hnorm.2.2.1
    have hdeg_g0 : g0'.natDegree = g0.natDegree := hnorm.2.2.2.1
    have hdeg_h0 : h0'.natDegree = h0.natDegree := hnorm.2.2.2.2.1
    have hprod_norm :
        g0' * h0' = Polynomial.C ((g0 * h0).leadingCoeff)⁻¹ * (g0 * h0) :=
      hnorm.2.2.2.2.2
    -- Proof comment: the remaining blocker is now isolated to lifting the normalized monic
    -- factorization `g0' * h0'` of the normalized residue polynomial and then undoing the unit
    -- rescalings encoded by `hprod_norm`.
    sorry

/-- Helper for Chap10 Lemma 10 153 3: base-changing an `R'`-algebra product decomposition of
`R' ⊗[R] S` back along an `R`-algebra retraction `τ : R' →ₐ[R] R` yields an `R`-algebra product
decomposition of `S`. -/
noncomputable def retractionBaseChangeProductEquiv
    {R' : Type u} {S : Type v} {A : Type v} {B : Type v}
    [CommRing R'] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R R'] [Algebra R S] [Algebra R' R] [Algebra R' A] [Algebra R' B]
    [IsScalarTower R R' R]
    (τ : R' →ₐ[R] R)
    (e : R' ⊗[R] S ≃ₐ[R'] A × B) :
    S ≃ₐ[R] (R ⊗[R'] A) × (R ⊗[R'] B) := by
  -- Proof comment: cancel the base-change tensor `R ⊗[R'] (R' ⊗[R] S)` back to `S`, transport
  -- the upstairs product decomposition across tensoring with `R`, and then use that tensoring
  -- commutes with binary products on the right.
  let eCancel : R ⊗[R'] (R' ⊗[R] S) ≃ₐ[R] S :=
    (Algebra.TensorProduct.cancelBaseChange R R' R R S).trans
      (Algebra.TensorProduct.lid R S)
  exact eCancel.symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans
      (Algebra.TensorProduct.prodRight R' R R A B)

/-- Helper for Chap10 Lemma 10 153 3: after base change along a retraction, the finite family of
finite factors remains finite over the local base. -/
lemma moduleFinite_retractionBaseChangePi
    {R' : Type u} {ι : Type v} {A : ι → Type v}
    [CommRing R'] [Algebra R R'] [Algebra R' R] [Fintype ι]
    [∀ i, CommRing (A i)] [∀ i, Algebra R' (A i)] [∀ i, Module.Finite R' (A i)]
    (τ : R' →ₐ[R] R) :
    Module.Finite R (R ⊗[R'] ((i : ι) → A i)) := by
  -- Proof comment: this is the finite-generation companion to the fixed-`τ` product descent API.
  letI : Module.Finite R' ((i : ι) → A i) := Module.Finite.pi
  -- Proof comment: first package the finite family of finite `R'`-modules into a finite product,
  -- then use the standard tensor-product base-change finiteness instance along `R' → R`.
  exact Module.Finite.base_change R' R ((i : ι) → A i)

/-- Helper for Chap10 Lemma 10 153 3: an `R`-algebra retraction `τ : R' →ₐ[R] R` induces a
bijective residue-field map from any prime `p'` of `R'` whose pullback along `τ` is
`maximalIdeal R`. -/
lemma residueFieldMap_bijective_of_retraction
    {R' : Type u} [CommRing R'] [Algebra R R']
    (τ : R' →ₐ[R] R) (p' : Ideal R') [p'.IsPrime]
    (hp' : p' = Ideal.comap (τ : R' →+* R) (maximalIdeal R)) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ p' (maximalIdeal R) τ hp') := by
  -- Proof comment: `τ` splits `algebraMap R R'`, hence is surjective; residue-field maps along
  -- surjective-on-stalks morphisms are bijective at matching primes.
  have hsurj : Function.Surjective (τ : R' →+* R) := by
    intro r
    refine ⟨algebraMap R R' r, ?_⟩
    simp
  exact
    (RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective
      p' (maximalIdeal R) hp'

/-- Helper for Chap10 Lemma 10 153 3: base change along a retraction identifies the closed fiber
of `R ⊗[R'] B` over `maximalIdeal R` with the closed fiber of `B` over the corresponding prime
`p' ⊂ R'`, provided the tensor product is formed in the `τ`-induced `R'`-algebra structure on
`R`. -/
noncomputable def retractionBaseChangeClosedFiberEquiv
    {R' : Type u} {B : Type v} [CommRing R'] [CommRing B]
    [Algebra R R'] [Algebra R' B]
    (τ : R' →ₐ[R] R) (p' : Ideal R') [p'.IsPrime]
    (hp' : p' = Ideal.comap (τ : R' →+* R) (maximalIdeal R)) :
    letI : Algebra R' R := τ.toRingHom.toAlgebra
    (maximalIdeal R).Fiber (R ⊗[R'] B) ≃+* p'.Fiber B := by
  -- Route correction: the old proof tried to reconstruct the fiber transport by hand. Mathlib's
  -- built-in bijective-residue-field fiber equivalence already gives the right τ-normalized
  -- `cancelBaseChange` comparison once the base map is rewritten to `algebraMap`.
  letI : Algebra R' R := τ.toRingHom.toAlgebra
  have hp'_alg : p' = Ideal.comap (algebraMap R' R) (maximalIdeal R) := by
    -- Proof comment: normalize the retraction equation to the ambient `algebraMap` spelling used
    -- by the residue-field API.
    simpa [RingHom.algebraMap_toAlgebra] using hp'
  letI : (maximalIdeal R).LiesOver p' := ⟨by
    simpa [Ideal.under] using hp'_alg⟩
  have hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ p' (maximalIdeal R) (Algebra.ofId R' R) hp'_alg) := by
    -- Proof comment: the retraction is surjective, so the induced residue-field map at the closed
    -- point is bijective.
    simpa [RingHom.algebraMap_toAlgebra] using
      residueFieldMap_bijective_of_retraction (R := R) τ p' hp'
  let e : (maximalIdeal R).Fiber (R ⊗[R'] B) ≃ₐ[p'.ResidueField] p'.Fiber B :=
    ((Algebra.TensorProduct.cancelBaseChange
        R' R (maximalIdeal R).ResidueField (maximalIdeal R).ResidueField B).restrictScalars _).trans
      (Algebra.TensorProduct.congr
        (.symm <| .ofBijective (Algebra.ofId _ _) hκ)
        (AlgEquiv.refl : B ≃ₐ[R'] B))
  -- Proof comment: forget the scalar structure on the canonical fiber equivalence to obtain the
  -- ring-level closed-fiber identification required by the source descent.
  exact e.toRingEquiv

/-- Helper for Chap10 Lemma 10 153 3: a bijective residue-field map transports subsingleton
fibers of primes across the tensor-product base change. -/
lemma subsingletonPrimesOverBaseChange_ofBijectiveResidueField
    {R₀ : Type u} {R₁ : Type v} {S : Type*}
    [CommRing R₀] [CommRing R₁] [CommRing S]
    [Algebra R₀ R₁] [Algebra R₀ S]
    (p : Ideal R₀) [p.IsPrime] (q : Ideal R₁) [q.IsPrime] [q.LiesOver p]
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ p q (Algebra.ofId R₀ R₁) (q.over_def p)))
    [Subsingleton (p.primesOver S)] :
    Subsingleton (q.primesOver (R₁ ⊗[R₀] S)) := by
  constructor
  intro Q₁ Q₂
  -- Proof comment: `Ideal.fiberIsoOfBijectiveResidueField` already gives the canonical
  -- equivalence of fibers, so equality downstairs pulls back upstairs.
  exact (Ideal.fiberIsoOfBijectiveResidueField hκ).injective (Subsingleton.elim _ _)

/-- Helper for Chap10 Lemma 10 153 3: if a finite factor upstairs has a unique prime over the
closed point `p'`, then its base change along the retraction `τ : R' →ₐ[R] R` is a local
`R`-algebra, again in the `τ`-induced `R'`-algebra structure on `R`. -/
lemma isLocalRing_retractionBaseChange_of_uniquePrime
    {R' : Type u} {A : Type v} [CommRing R'] [CommRing A]
    [Algebra R R'] [Algebra R' A] [Module.Finite R' A]
    (τ : R' →ₐ[R] R) (p' : Ideal R') [p'.IsPrime]
    (hp' : p' = Ideal.comap (τ : R' →+* R) (maximalIdeal R))
    (r : p'.primesOver A) [Subsingleton (p'.primesOver A)] :
    letI : Algebra R' R := τ.toRingHom.toAlgebra
    IsLocalRing (R ⊗[R'] A) := by
  -- Route correction: the old proof tried to reason in an ambient `[Algebra R' R]`. The only
  -- stable local-ring descent route is to normalize the tensor product into the explicit `τ`-world.
  letI : Algebra R' R := τ.toRingHom.toAlgebra
  letI : IsScalarTower R R' R := IsScalarTower.of_algHom τ
  letI : Module.Finite R (R ⊗[R'] A) := Module.Finite.base_change R' R A
  letI : Algebra.IsIntegral R (R ⊗[R'] A) := Algebra.IsIntegral.of_finite R (R ⊗[R'] A)
  have hp'_alg : p' = Ideal.comap (algebraMap R' R) (maximalIdeal R) := by
    -- Proof comment: normalize the closed-point equality to the ambient `algebraMap` spelling
    -- expected by the fiber and lies-over APIs.
    simpa [RingHom.algebraMap_toAlgebra] using hp'
  letI : (maximalIdeal R).LiesOver p' := ⟨by
    simpa [Ideal.under] using hp'_alg⟩
  have hκ :
      Function.Bijective
        (Ideal.ResidueField.mapₐ p' (maximalIdeal R) (Algebra.ofId R' R) hp'_alg) := by
    -- Proof comment: this is the residue-field bridge that transports fiber uniqueness through
    -- the tensor-product base change.
    simpa [RingHom.algebraMap_toAlgebra] using
      residueFieldMap_bijective_of_retraction (R := R) τ p' hp'
  have hSub :
      Subsingleton ((maximalIdeal R).primesOver (R ⊗[R'] A)) := by
    -- Proof comment: uniqueness of the chosen prime upstairs pulls back through the canonical
    -- fiber equivalence induced by the bijective residue-field map.
    exact subsingletonPrimesOverBaseChange_ofBijectiveResidueField
      (R₀ := R') (R₁ := R) (S := A) p' (maximalIdeal R) hκ
  let rTensor : (maximalIdeal R).primesOver (R ⊗[R'] A) :=
    (Ideal.fiberIsoOfBijectiveResidueField (S := A) hκ).symm r
  have hrTensor_max : rTensor.1.IsMaximal := by
    -- Proof comment: the chosen descended prime lies over `maximalIdeal R`, so integrality makes
    -- it maximal.
    letI : Algebra.IsIntegral R (R ⊗[R'] A) := inferInstance
    have hcomap :
        Ideal.comap (algebraMap R (R ⊗[R'] A)) rTensor.1 = maximalIdeal R := by
      simpa [Ideal.under] using (Ideal.over_def rTensor.1 (maximalIdeal R)).symm
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap rTensor.1 <| by
      rw [hcomap]
      exact maximalIdeal.isMaximal R
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨rTensor.1, hrTensor_max, ?_⟩
  intro I hI
  letI : I.IsMaximal := hI
  have hcomap :
      Ideal.comap (algebraMap R (R ⊗[R'] A)) I = maximalIdeal R := by
    -- Proof comment: every maximal ideal of the descended algebra contracts to the maximal ideal
    -- of the local base because the base change is finite, hence integral.
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
  let Iover : (maximalIdeal R).primesOver (R ⊗[R'] A) := ⟨I, inferInstance, ⟨hcomap.symm⟩⟩
  exact congrArg Subtype.val (Subsingleton.elim Iover rTensor)

/-- Helper for Chap10 Lemma 10 153 3: the unique étale-retraction clause descends the finite
local-product decomposition for finite algebras. -/
lemma finiteAlgebraFiniteLocalProduct_of_etaleRetractionUnique :
    @etale_retraction_unique_property.{u, v} R _ _ →
      finite_algebra_finite_local_product_property R := by
  -- TODO: apply Lemma `10.145.3` to the finite algebra, descend the product decomposition with
  -- `retractionBaseChangeProductEquiv`, make each descended factor local using
  -- `isLocalRing_retractionBaseChange_of_uniquePrime`, and then collapse the descended remainder
  -- via `retractionBaseChangeClosedFiberEquiv` plus `subsingleton_of_finite_subsingletonSpecialFiber`.
  -- Route correction: the smaller-universe specialization of clause `(8)` is now handled by
  -- `etaleRetractionUnique_apply`, so the remaining blocker is only the descended product/remainder
  -- algebra, not any outer `ULift` packaging.
  sorry

/-- Helper for Chap10 Lemma 10 153 3: a ring equivalence transports the property that every
minimal prime quotient has dimension at least `1`. -/
lemma positiveDimensionalMinimalPrimes_of_ringEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : ∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
      1 ≤ ringKrullDim (A ⧸ p.asIdeal)) :
    ∀ p : PrimeSpectrum B, p.asIdeal ∈ minimalPrimes B →
      1 ≤ ringKrullDim (B ⧸ p.asIdeal) := by
  intro p hp
  let q : PrimeSpectrum A := (PrimeSpectrum.comapEquiv e).symm p
  have hqmin : q.asIdeal ∈ minimalPrimes A := by
    have hpmin : IsMin p := (PrimeSpectrum.isMin_iff).2 hp
    have hqmin' : IsMin q := by
      -- Proof comment: prime-spectrum order equivalences preserve minimal points.
      simpa [q] using ((PrimeSpectrum.comapEquiv e).symm.isMin_apply (x := p)).2 hpmin
    exact (PrimeSpectrum.isMin_iff).1 hqmin'
  have hqideal : q.asIdeal = Ideal.comap e.toRingHom p.asIdeal := by
    -- Proof comment: unpack the transported prime into the concrete comap normal form used by the
    -- ideal-quotient API.
    simpa [q] using congrArg PrimeSpectrum.asIdeal (PrimeSpectrum.comapEquiv_apply e.symm p)
  have hmap : p.asIdeal = Ideal.map e.toRingHom q.asIdeal := by
    -- Proof comment: a ring equivalence identifies the target prime with the image of the
    -- transported source prime.
    rw [hqideal]
    exact (Ideal.map_comap_eq_self_of_equiv e p.asIdeal).symm
  let eQuot : A ⧸ q.asIdeal ≃+* B ⧸ p.asIdeal :=
    Ideal.quotientEquiv q.asIdeal p.asIdeal e hmap
  have hdim : 1 ≤ ringKrullDim (A ⧸ q.asIdeal) := hA q hqmin
  have hquot :
      ringKrullDim (A ⧸ q.asIdeal) = ringKrullDim (B ⧸ p.asIdeal) :=
    ringKrullDim_eq_of_ringEquiv eQuot
  -- Proof comment: after identifying the two prime quotients, transport the dimension inequality.
  exact hquot ▸ hdim

/-- Helper for Chap10 Lemma 10 153 3: the positive-dimensional minimal-prime condition can be
checked either on the closed fiber `((maximalIdeal R).Fiber B)` or on the special fiber
`κ ⊗[R] B`. -/
lemma closedFiberPositiveDimensional_iff_specialFiberPositiveDimensional
    {B : Type v} [CommRing B] [Algebra R B] :
    (∀ p : PrimeSpectrum ((maximalIdeal R).Fiber B),
        p.asIdeal ∈ minimalPrimes ((maximalIdeal R).Fiber B) →
          1 ≤ ringKrullDim (((maximalIdeal R).Fiber B) ⧸ p.asIdeal)) ↔
      special_fiber_minimal_primes_positive_dimensional R B := by
  let eκRing : (maximalIdeal R).ResidueField ≃+* κ :=
    (RingEquiv.ofBijective
      (algebraMap κ (maximalIdeal R).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm
  let eκ : (maximalIdeal R).ResidueField ≃ₐ[R] κ :=
    { toRingEquiv := eκRing
      commutes' := fun a ↦ by
        -- Proof comment: both residue-field models send `a : R` to its residue class.
        rw [show algebraMap R (maximalIdeal R).ResidueField a =
          algebraMap κ (maximalIdeal R).ResidueField (residue R a) by rfl]
        exact eκRing.apply_symm_apply (residue R a) }
  let e : (maximalIdeal R).Fiber B ≃ₐ[R] (κ ⊗[R] B) :=
    Algebra.TensorProduct.congr eκ (AlgEquiv.refl : B ≃ₐ[R] B)
  let φ : (maximalIdeal R).Fiber B →+* (κ ⊗[R] B) := e.toRingHom
  constructor
  · intro h p hp
    let q : PrimeSpectrum ((maximalIdeal R).Fiber B) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv).symm p
    have hbot : Ideal.comap φ (⊥ : Ideal (κ ⊗[R] B)) = ⊥ := by
      ext x
      change φ x = 0 ↔ x = 0
      constructor
      · intro hx
        exact e.injective hx
      · intro hx
        simpa [hx]
    have hmin :
        minimalPrimes ((maximalIdeal R).Fiber B) =
          Ideal.comap φ ''
            minimalPrimes (κ ⊗[R] B) := by
      have hmin' :
          (Ideal.comap φ (⊥ : Ideal (κ ⊗[R] B))).minimalPrimes =
            Ideal.comap φ '' (⊥ : Ideal (κ ⊗[R] B)).minimalPrimes := by
        exact Ideal.comap_minimalPrimes_eq_of_surjective e.surjective _
      simpa [minimalPrimes, hbot] using hmin'
    have hqmin : q.asIdeal ∈ minimalPrimes ((maximalIdeal R).Fiber B) := by
      rw [hmin]
      exact ⟨p.asIdeal, hp, by simpa [q, φ]⟩
    let eQuot :
        (((maximalIdeal R).Fiber B) ⧸ q.asIdeal) ≃ₐ[R]
          ((κ ⊗[R] B) ⧸ p.asIdeal) :=
      Ideal.quotientEquivAlg q.asIdeal p.asIdeal e <| by
        simpa [q] using
          (Ideal.map_comap_eq_self_of_equiv e.toRingEquiv p.asIdeal).symm
    -- Proof comment: transport the quotient dimension statement across the fiber/special-fiber
    -- equivalence induced by the two residue-field models.
    have hdim :
        ringKrullDim (((maximalIdeal R).Fiber B) ⧸ q.asIdeal) =
          ringKrullDim ((κ ⊗[R] B) ⧸ p.asIdeal) :=
      ringKrullDim_eq_of_ringEquiv eQuot.toRingEquiv
    exact hdim ▸ h q hqmin
  · intro h p hp
    let q : PrimeSpectrum (κ ⊗[R] B) :=
      PrimeSpectrum.comap e.symm.toRingHom p
    have hker :
        RingHom.ker φ = ⊥ := by
      ext x
      change φ x = 0 ↔ x = 0
      constructor
      · intro hx
        exact e.injective hx
      · intro hx
        simpa [hx]
    have hmin :
        minimalPrimes (κ ⊗[R] B) =
          Ideal.map φ ''
            minimalPrimes ((maximalIdeal R).Fiber B) := by
      have hmin' :
          (Ideal.map φ (⊥ : Ideal ((maximalIdeal R).Fiber B))).minimalPrimes =
            Ideal.map φ '' ((⊥ : Ideal ((maximalIdeal R).Fiber B)) ⊔ RingHom.ker φ).minimalPrimes := by
        exact Ideal.minimalPrimes_map_of_surjective e.surjective _
      simpa [minimalPrimes, hker] using hmin'
    have hqmin : q.asIdeal ∈ minimalPrimes (κ ⊗[R] B) := by
      rw [hmin]
      exact ⟨p.asIdeal, hp, by
        change Ideal.map φ p.asIdeal =
          Ideal.comap e.symm.toRingHom p.asIdeal
        have hsymm :
            Ideal.comap e.symm.toRingHom p.asIdeal = Ideal.map e.toRingHom p.asIdeal := by
          show Ideal.comap e.symm.toRingHom p.asIdeal = Ideal.map e.toRingHom p.asIdeal
          exact Ideal.comap_symm e.toRingEquiv
        simpa [φ] using hsymm.symm⟩
    let eQuot :
        (((maximalIdeal R).Fiber B) ⧸ p.asIdeal) ≃ₐ[R]
          ((κ ⊗[R] B) ⧸ q.asIdeal) :=
      Ideal.quotientEquivAlg p.asIdeal q.asIdeal e <| by
        change Ideal.comap e.symm.toRingHom p.asIdeal =
          Ideal.map φ p.asIdeal
        have hsymm :
            Ideal.comap e.symm.toRingHom p.asIdeal = Ideal.map e.toRingHom p.asIdeal := by
          show Ideal.comap e.symm.toRingHom p.asIdeal = Ideal.map e.toRingHom p.asIdeal
          exact Ideal.comap_symm e.toRingEquiv
        simpa [φ] using hsymm
    -- Proof comment: the converse direction is the same transport in the opposite orientation.
    have hdim :
        ringKrullDim (((maximalIdeal R).Fiber B) ⧸ p.asIdeal) =
          ringKrullDim ((κ ⊗[R] B) ⧸ q.asIdeal) :=
      ringKrullDim_eq_of_ringEquiv eQuot.toRingEquiv
    exact hdim.symm ▸ h q hqmin

/-- Helper for Chap10 Lemma 10 153 3: the two finite-type remainder clauses are equivalent after
rewriting non-quasi-finiteness over the closed point in terms of the special fiber. -/
lemma splitNonQuasiFinite_iff_positiveDimensionalFiber :
    @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R _ _ ↔
      @finite_type_algebra_split_finite_positive_dimensional_fiber_property.{u, v} R _ _ := by
  constructor
  · intro h S _ _ _
    obtain ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, hs, hB⟩ := h S
    letI : CommRing A := instAComm
    letI : Algebra R A := instAAlg
    letI : Module.Finite R A := instAFinite
    letI : CommRing B := instBComm
    letI : Algebra R B := instBAlg
    obtain ⟨e⟩ := hs
    letI : Algebra.FiniteType R (A × B) := Algebra.FiniteType.equiv inferInstance e
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.of_surjective (AlgHom.snd R A B) <| by
        intro b
        exact ⟨(0, b), by simp⟩
    refine ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, ⟨e⟩, ?_⟩
    -- Proof comment: first convert the remainder clause to the closed-fiber formulation, then
    -- transport that formulation to the special fiber `κ ⊗[R] B`.
    exact
      (closedFiberPositiveDimensional_iff_specialFiberPositiveDimensional R).1 <|
        (closedFiberNonQuasiFinite_iff_positiveDimensional R).1 hB
  · intro h S _ _ _
    obtain ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, hs, hB⟩ := h S
    letI : CommRing A := instAComm
    letI : Algebra R A := instAAlg
    letI : Module.Finite R A := instAFinite
    letI : CommRing B := instBComm
    letI : Algebra R B := instBAlg
    obtain ⟨e⟩ := hs
    letI : Algebra.FiniteType R (A × B) := Algebra.FiniteType.equiv inferInstance e
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.of_surjective (AlgHom.snd R A B) <| by
        intro b
        exact ⟨(0, b), by simp⟩
    refine ⟨A, instAComm, instAAlg, instAFinite, B, instBComm, instBAlg, ⟨e⟩, ?_⟩
    -- Proof comment: now run the same translation in the opposite direction to recover the
    -- original non-quasi-finite remainder clause.
    exact
      (closedFiberNonQuasiFinite_iff_positiveDimensional R).2 <|
        (closedFiberPositiveDimensional_iff_specialFiberPositiveDimensional R).2 hB

/-- Helper for Chap10 Lemma 10 153 3: the unique étale-retraction clause descends the finite plus
non-quasi-finite decomposition for finite-type algebras. -/
-- TODO: apply Lemma `10.145.3` at `maximalIdeal R`, then base-change the resulting decomposition
-- back along the retraction `R' →ₐ[R] R`; the clause `(8)` specialization itself no longer needs
-- a universe-transport wrapper after `etaleRetractionUnique_apply`.
lemma finiteTypeSplitNonQuasiFinite_of_etaleRetractionUnique :
    @etale_retraction_unique_property.{u, v} R _ _ →
      @finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R _ _ := by
  -- TODO: the new helper `positiveDimensionalMinimalPrimes_of_ringEquiv` isolates the cheap
  -- closed-fiber transport step. The first remaining blocker is an owner-level bridge from the
  -- upstairs `p'`-fiber remainder clause in Lemma `10.145.3` to the downstairs special-fiber
  -- clause over `maximalIdeal R`, for an arbitrary prime `p'` above `maximalIdeal R`.
  sorry

/-- Helper for Chap10 Lemma 10 153 3: if every finite `R`-algebra is a finite product of local
rings, then `R` is henselian. -/
-- TODO: decompose `R[X]/(f)` for a monic polynomial with a simple residue root, isolate the
-- factor with closed fiber `κ`, identify that rank-one finite factor with `R`, and read off the
-- lifted root from the image of `X`.
lemma henselian_of_finiteAlgebraFiniteLocalProduct :
    finite_algebra_finite_local_product_property R →
      HenselianLocalRing R := sorry

/-- Helper for Chap10 Lemma 10 153 3: the quasi-finite zero-special-fiber splitting clause implies
that `R` is henselian. -/
-- Route correction: the old `13 → 2` helper reused the same noncanonical localized quotient route
-- as the discarded `7 → 2` edge. The source instead proves `13 → 1` directly on the finite algebra
-- `R[X] / (f)` by isolating the factor with residue field `κ`.
-- TODO: for a monic polynomial with simple residue root, localize the finite algebra
-- `R[X] / (f)` at a complementary factor so the chosen point becomes quasi-finite, apply the split,
-- show the finite factor with residue field `κ` is isomorphic to `R`, and read off the lifted
-- root from the image of `X`.
lemma henselian_of_quasiFiniteZeroSpecialFiberSplit :
    @quasi_finite_algebra_split_finite_zero_special_fiber_property.{u, v} R _ _ →
      HenselianLocalRing R := sorry

/-- Helper for Chap10 Lemma 10 153 3: the monic coprime-factorization lifting clause implies that
`R` is henselian. -/
-- TODO: follow the source quotient/direct-summand proof on `R[X] ⧸ (f)`, isolate the factor with
-- closed fiber `κ`, prove that finite flat rank-one factor is isomorphic to `R`, and read off the
-- lifted root.
lemma henselian_of_monicCoprimeFactorizationLift :
    monic_coprime_factorization_lift_property R →
      HenselianLocalRing R := by
  -- Proof comment: this is the source `3 → 1` edge and is the remaining algebraic closing route
  -- for the factorization cluster.
  sorry

/-- Helper for Chap10 Lemma 10 153 3: henselian local rings satisfy the strongest coprime
factorization lifting clause with degree control. -/
-- TODO: normalize the chosen nonzero residue factor by its leading coefficient, apply the monic
-- lifting route, and descend the resulting factorization along the retraction `R' →ₐ[R] R`.
lemma coprimeFactorizationLiftWithDegree_of_henselian :
    HenselianLocalRing R →
      coprime_factorization_lift_with_degree_property R := by
  -- Proof comment: this is the source `1 → 6` edge and closes the factorization half of the TFAE
  -- once the normalization-to-monic step is repaired.
  intro hHens
  -- Proof comment: the source route first upgrades henselianity to unique étale retractions and
  -- then invokes the already isolated descent from that clause to degree-controlled factorization
  -- lifting.
  exact
    @coprimeFactorizationLiftWithDegree_of_etaleRetractionUnique.{u, u} R _ _
      (@etaleRetractionUnique_of_henselian.{u, u} R _ _ hHens)

-- Proof sketch: combine the canonical henselian simple-root formulation with the standard
-- coprime-factorization lifting criteria, the étale-neighbourhood retraction characterizations,
-- and the finite / finite-type / quasi-finite decomposition criteria cited in the textbook.
/-- Chap10 Lemma 10 153 3: for a local ring `R`, the following are equivalent: `R` is henselian;
simple roots over the residue field lift; coprime factorizations of residue polynomials lift in
monic and nonmonic forms, with clause `(6)` repaired by the nonzero chosen-factor side condition
implicit in the source proof; étale neighborhoods with
unchanged residue field admit retractions; finite and finite-type `R`-algebras admit the
indicated local-product decompositions; and quasi-finite `R`-algebras split off a finite part
with zero special-fiber remainder. -/
@[stacks 04GG]
theorem henselian_local_ring_tfae :
    List.TFAE
      [ HenselianLocalRing R
      , simple_root_lift_property.{u} R
      , monic_coprime_factorization_lift_property.{u} R
      , monic_coprime_factorization_lift_with_degree_property.{u} R
      , coprime_factorization_lift_property.{u} R
      , coprime_factorization_lift_with_degree_property.{u} R
      , etale_retraction_exists_property.{u, v} R
      , etale_retraction_unique_property.{u, v} R
      , finite_algebra_local_product_property R
      , finite_algebra_finite_local_product_property R
      , finite_type_algebra_split_finite_nonQuasiFinite_property.{u, v} R
      , finite_type_algebra_split_finite_positive_dimensional_fiber_property.{u, v} R
      , quasi_finite_algebra_split_finite_zero_special_fiber_property.{u, v} R
      ] := sorry

end
