import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_24_3
import stacks_proof.stacks_project.Chap15.Definition_15_112_1
import stacks_proof.stacks_project.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial Ideal IsLocalRing Algebra IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-
Domain-style sampling for the radical-extension owners:
- primary domain: simple radical extensions presented by `AdjoinRoot (X ^ n - C π)`;
- sampled owner declarations: `Polynomial.monic_X_pow_sub_C`, `AdjoinRoot`, `AdjoinRoot.root`,
  `AdjoinRoot.map`;
- best owner abstraction: the general `AdjoinRoot` owner over a base commutative ring/domain, with
  DVR hypotheses entering only in the later irreducibility and ramification results;
- primitive-vs-derived split: primitive data are the polynomial `X ^ n - C π`, the quotient
  `AdjoinRoot`, and the distinguished root in the fraction-field presentation. Field structure,
  ramification, tame-ramification, and intermediate-field statements are derived in the DVR
  specialization below.
-/

section UniformizerRootOwners

variable {A : Type u} [CommRing A]

/-- The polynomial `X^n - π` over a commutative ring `A`. -/
abbrev uniformizerRootPolynomial (π : A) (n : ℕ) : A[X] :=
  X ^ n - C π

/-- The `A`-algebra `A[π^(1/n)]`, presented as `A[X] / (X^n - π)`. -/
abbrev uniformizerRootExtensionRing (π : A) (n : ℕ) : Type u :=
  AdjoinRoot (uniformizerRootPolynomial π n)

section FractionField

variable [IsDomain A]

/-- The polynomial `X^n - π` after base change from `A` to `FractionRing A`. -/
abbrev uniformizerRootFractionPolynomial (π : A) (n : ℕ) : (FractionRing A)[X] :=
  (uniformizerRootPolynomial π n).map (algebraMap A (FractionRing A))

/-- The `FractionRing A`-algebra `K[π^(1/n)]`, presented as
`K[X] / (X^n - algebraMap A K π)`. This is the raw `AdjoinRoot` quotient; it only becomes a field
under the later irreducibility hypotheses. -/
abbrev uniformizerRootExtension (π : A) (n : ℕ) : Type u :=
  AdjoinRoot (uniformizerRootFractionPolynomial π n)

/-- The raw quotient `K[π^(1/n)]` carries its canonical `FractionRing A`-algebra structure. -/
instance {π : A} {n : ℕ} : Algebra (FractionRing A) (uniformizerRootExtension π n) := by
  change Algebra (FractionRing A) (AdjoinRoot (uniformizerRootFractionPolynomial π n))
  infer_instance

/-- The raw quotient `K[π^(1/n)]` is canonically an `A`-algebra through the fraction-field tower. -/
instance {π : A} {n : ℕ} : Algebra A (uniformizerRootExtension π n) := by
  change Algebra A (AdjoinRoot (uniformizerRootFractionPolynomial π n))
  infer_instance

/-- The raw quotient `K[π^(1/n)]` sits in the scalar tower `A ⊆ FractionRing A ⊆ K[π^(1/n)]`. -/
instance {π : A} {n : ℕ} :
    IsScalarTower A (FractionRing A) (uniformizerRootExtension π n) := by
  change IsScalarTower A (FractionRing A) (AdjoinRoot (uniformizerRootFractionPolynomial π n))
  infer_instance

/-- The distinguished root `π^(1/n)` in the fraction-field-base-changed quotient
`K[π^(1/n)]`. -/
abbrev uniformizerRoot (π : A) (n : ℕ) : uniformizerRootExtension π n :=
  AdjoinRoot.root (uniformizerRootFractionPolynomial π n)

omit [IsDomain A] in
/-- The distinguished root satisfies `(π^(1/n))^n = π` in the quotient `K[π^(1/n)]`. -/
@[simp] theorem uniformizerRoot_pow {π : A} {n : ℕ} :
    uniformizerRoot π n ^ n = algebraMap A (uniformizerRootExtension π n) π := by
  simpa [uniformizerRoot, uniformizerRootFractionPolynomial, uniformizerRootPolynomial, sub_eq_zero]
    using (AdjoinRoot.eval₂_root (uniformizerRootFractionPolynomial π n))


/-- The radical extension ring acts on the radical extension field through the canonical map. -/
instance {π : A} {n : ℕ} :
    Algebra (uniformizerRootExtensionRing π n) (uniformizerRootExtension π n) :=
  (AdjoinRoot.map (algebraMap A (FractionRing A))
    (uniformizerRootPolynomial π n)
    (uniformizerRootFractionPolynomial π n) dvd_rfl).toAlgebra

/-- The radical extension field is a scalar tower over `A ⊆ A[π^(1/n)]`. -/
instance {π : A} {n : ℕ} :
    IsScalarTower A (uniformizerRootExtensionRing π n) (uniformizerRootExtension π n) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  change
    AdjoinRoot.of (uniformizerRootFractionPolynomial π n) (algebraMap A (FractionRing A) x) =
      AdjoinRoot.map (algebraMap A (FractionRing A))
          (uniformizerRootPolynomial π n) (uniformizerRootFractionPolynomial π n) dvd_rfl
        (algebraMap A (uniformizerRootExtensionRing π n) x)
  simp [AdjoinRoot.algebraMap_eq]

/-- The radical extension field is finite-dimensional over `FractionRing A` as soon as `n ≠ 0`. -/
noncomputable instance
    {π : A} {n : ℕ} [NeZero n] :
    FiniteDimensional (FractionRing A) (uniformizerRootExtension π n) := by
  have hmonic : (uniformizerRootFractionPolynomial π n).Monic := by
    simpa [uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (algebraMap A (FractionRing A) π) (NeZero.ne n))
  exact hmonic.finite_adjoinRoot

end FractionField

end UniformizerRootOwners

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "A[" π "^(1/" n ")]" =>
  uniformizerRootExtensionRing π n

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "K[" π "^(1/" n ")]" =>
  uniformizerRootExtension π n

set_option quotPrecheck false in
scoped[UniformizerRoot] notation3:max "root[" π "^(1/" n ")]" =>
  uniformizerRoot π n

open scoped UniformizerRoot

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

-- Proof sketch: regard `X^n - π` over `FractionRing A` as Eisenstein at the maximal ideal of
-- `A`; the irreducibility hypothesis identifies `π` as a uniformizer, so the constant term has
-- valuation `1`, while all
-- intermediate coefficients vanish.
/-- The polynomial `X^n - π` is irreducible over `FractionRing A` when `π` is irreducible,
equivalently a uniformizer. -/
theorem uniformizerRootFractionPolynomial_irreducible
    {π : A} {n : ℕ}
    (hπ : Irreducible π)
    (hn : n ≠ 0) :
    Irreducible (uniformizerRootFractionPolynomial π n) := by
  let f : Polynomial A := uniformizerRootPolynomial π n
  have hmax : maximalIdeal A = Ideal.span ({π} : Set A) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hmonic : f.Monic := by
    -- The source polynomial `X^n - π` is monic, so Gauss's lemma will later transport
    -- irreducibility to the fraction field.
    simpa [f, uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn
  have hnatDegree : f.natDegree = n := by
    -- The quotient polynomial really has degree `n`, so every lower positive coefficient vanishes.
    simpa [f, uniformizerRootPolynomial] using Polynomial.natDegree_X_pow_sub_C (n := n) (r := π)
  have hcoeff_mem : ∀ {k : ℕ}, k < f.natDegree → f.coeff k ∈ maximalIdeal A := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- The constant coefficient is `-π`, which lies in the maximal ideal generated by `π`.
      have hπmem : π ∈ maximalIdeal A := by
        rw [hmax]
        exact Ideal.mem_span_singleton_self π
      have hneg : -π ∈ maximalIdeal A := (maximalIdeal A).neg_mem hπmem
      have h0n : 0 ≠ n := by
        simpa using hn.symm
      have hcoeff0 : f.coeff 0 = -π := by
        simp [f, uniformizerRootPolynomial, h0n]
      rw [hcoeff0]
      exact hneg
    · -- Every intermediate coefficient vanishes, so it is automatically in the maximal ideal.
      have hk' : k < n := by
        simpa [hnatDegree] using hk
      have hkn : k ≠ n := Nat.ne_of_lt hk'
      have hcoeff_zero : f.coeff k = 0 := by
        have hcoeff_X : (X ^ n : Polynomial A).coeff k = 0 := by
          simp [Polynomial.coeff_X_pow, hkn]
        have hcoeff_C : (C π : Polynomial A).coeff k = 0 := by
          rw [Polynomial.coeff_C]
          simp [Nat.ne_of_gt hkpos]
        calc
          f.coeff k = (X ^ n - C π : Polynomial A).coeff k := by rfl
          _ = (X ^ n : Polynomial A).coeff k - (C π : Polynomial A).coeff k := by simp
          _ = 0 - 0 := by rw [hcoeff_X, hcoeff_C]
          _ = 0 := sub_self 0
      rw [hcoeff_zero]
      exact (maximalIdeal A).zero_mem
  have hπ_not_mem_sq : π ∉ maximalIdeal A ^ 2 := by
    -- Route correction: keep the source Eisenstein argument on `A[X]`; the only nontrivial
    -- coefficient check is that the uniformizer is not divisible by `π^2`.
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    rcases hdiv with ⟨a, ha⟩
    have hπ0 : π ≠ 0 := hπ.ne_zero
    have hone : 1 = π * a := by
      apply mul_left_cancel₀ hπ0
      simpa [pow_two, mul_assoc, mul_one] using ha
    exact hπ.1 <| isUnit_of_dvd_one ⟨a, hone⟩
  have hcoeff0_not_mem_sq : f.coeff 0 ∉ maximalIdeal A ^ 2 := by
    intro hcoeff
    have h0n : 0 ≠ n := by
      simpa using hn.symm
    have hcoeff0 : f.coeff 0 = -π := by
      simp [f, uniformizerRootPolynomial, h0n]
    rw [hcoeff0] at hcoeff
    apply hπ_not_mem_sq
    exact (Submodule.neg_mem_iff _).1 hcoeff
  have hEis : f.IsEisensteinAt (maximalIdeal A) := by
    -- Eisenstein at the maximal ideal is the ring-side source proof controlling irreducibility.
    refine hmonic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal A).ne_top ?_ ?_
    · intro k hk
      exact hcoeff_mem hk
    · simpa [f, uniformizerRootPolynomial] using hcoeff0_not_mem_sq
  have hirrA : Irreducible f := by
    -- Once the Eisenstein data are in place, the standard criterion closes irreducibility over `A`.
    refine hEis.irreducible (maximalIdeal.isMaximal A).isPrime hmonic.isPrimitive ?_
    simpa [f, uniformizerRootPolynomial] using Nat.pos_iff_ne_zero.mpr hn
  -- Gauss's lemma transports the ring-side irreducibility of `X^n - π` to the fraction field.
  simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
    (hmonic.irreducible_iff_irreducible_map_fraction_map (K := FractionRing A)).mp hirrA

/-- The canonical field instance on `K[π^(1/n)]` when irreducibility is available as a fact. -/
noncomputable instance
    {varpi : A} {n : ℕ} [Fact <| Irreducible varpi] [NeZero n] :
    Field (uniformizerRootExtension varpi n) := by
  letI : Fact (Irreducible (uniformizerRootFractionPolynomial varpi n)) :=
    ⟨uniformizerRootFractionPolynomial_irreducible
      Fact.out (NeZero.ne n)⟩
  change Field (AdjoinRoot (uniformizerRootFractionPolynomial varpi n))
  infer_instance
section UniformizerRootExtension

variable {π : A} {n : ℕ}
variable (hπ : Irreducible π) (hn : 0 < n)

local notation "K" => FractionRing A
local notation "R1" => uniformizerRootExtensionRing π n
local notation "K1" => uniformizerRootExtension π n

/- Domain-style sampling for the radical-extension conclusions:
- primary domain: tame ramification of simple radical extensions of fraction fields of discrete
  valuation rings, together with the lattice of intermediate subextensions;
- sampled owner declarations:
  `IsTamelyRamifiedWithRespectTo A L`,
  `ramificationIndex A R1`,
  `IntermediateField K K1`,
  `IntermediateField.adjoin`;
- best owner abstraction: the chapter ramification owner `ramificationIndex A R1` for part `(4)`,
  the global tame-ramification owner `IsTamelyRamifiedWithRespectTo A K1` for part `(7)`, and the
  canonical intermediate-subextension owner `IntermediateField K K1` for part `(8)`;
- primitive-vs-derived split: the branchwise residue-separability and ramification-index
  coprimality data are primitive fields of `IsTamelyRamifiedWithRespectTo`, so part `(7)` should
  expose that owner directly; the single-generator description in part `(8)` is a derived theorem
  about an already bundled intermediate field rather than primitive `Subalgebra` data plus an
  auxiliary field hypothesis.

Source/core/bridge triage:
- part `(7)`: `source-facing` statement with the canonical chapter owner
  `IsTamelyRamifiedWithRespectTo A K1`;
- part `(8)`: `source-facing` classification of canonical `IntermediateField K K1` objects by a
  power of the distinguished radical generator.
-/

section

include hπ hn

local instance : NeZero n := ⟨hn.ne'⟩

local instance : Fact (Irreducible π) := ⟨hπ⟩

section UniformizerRootExtensionDisplay

/-- Helper for Lemma 15.115.2: the explicit quotient ring maps to the fraction-field quotient by
sending the adjoined root to the distinguished fraction-field root. -/
private noncomputable def uniformizerRootExtensionRing_to_fractionField :
    R1 →ₐ[A] K1 := by
  -- Route correction: record the source-faithful quotient map `A[X]/(X^n - π) → K[π^(1/n)]`
  -- before tackling injectivity, so later ring-level arguments can reuse a stable bridge.
  refine
    AdjoinRoot.liftAlgHom
      (uniformizerRootPolynomial π n)
      (Algebra.ofId A K1)
      (root[π^(1/n)])
      ?_
  -- The chosen image of the adjoined root satisfies the same equation `X^n - π = 0`.
  simpa [uniformizerRootPolynomial, sub_eq_zero] using
    (uniformizerRoot_pow (A := A) (π := π) (n := n))

/-- Helper for Lemma 15.115.2: the comparison map agrees with the base algebra map on `A`. -/
@[simp] private theorem uniformizerRootExtensionRing_to_fractionField_of (a : A) :
    uniformizerRootExtensionRing_to_fractionField (π := π) (n := n)
        (algebraMap A R1 a) =
      algebraMap A K1 a := by
  -- This is the defining base-ring compatibility of `AdjoinRoot.liftAlgHom`.
  simpa [uniformizerRootExtensionRing_to_fractionField] using
    (AdjoinRoot.liftAlgHom_of
      (p := uniformizerRootPolynomial π n)
      (i := Algebra.ofId A K1)
      (x := root[π^(1/n)])
      (h := by
        simpa [uniformizerRootPolynomial, sub_eq_zero] using
          (uniformizerRoot_pow (A := A) (π := π) (n := n)))
      a)

/-- Helper for Lemma 15.115.2: the comparison map sends the ring-side distinguished root to the
field-side distinguished root. -/
@[simp] private theorem uniformizerRootExtensionRing_to_fractionField_root :
    uniformizerRootExtensionRing_to_fractionField (π := π) (n := n)
        (AdjoinRoot.root (uniformizerRootPolynomial π n)) =
      root[π^(1/n)] := by
  -- This is the defining generator formula of `AdjoinRoot.liftAlgHom`.
  simp [uniformizerRootExtensionRing_to_fractionField]

/-- Helper for Lemma 15.115.2: the defining polynomial `X^n - π` is already irreducible over the
base discrete valuation ring `A`. -/
private theorem uniformizerRootPolynomial_irreducible :
    Irreducible (uniformizerRootPolynomial π n) := by
  let f : Polynomial A := uniformizerRootPolynomial π n
  have hmax : maximalIdeal A = Ideal.span ({π} : Set A) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hmonic : f.Monic := by
    -- The source polynomial `X^n - π` is monic over the discrete valuation ring itself.
    simpa [f, uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  have hnatDegree : f.natDegree = n := by
    -- Its degree is exactly `n`, so every lower positive coefficient vanishes.
    simpa [f, uniformizerRootPolynomial] using
      Polynomial.natDegree_X_pow_sub_C (n := n) (r := π)
  have hcoeff_mem : ∀ {k : ℕ}, k < f.natDegree → f.coeff k ∈ maximalIdeal A := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- The constant coefficient is `-π`, hence it lies in the maximal ideal generated by `π`.
      have hπmem : π ∈ maximalIdeal A := by
        rw [hmax]
        exact Ideal.mem_span_singleton_self π
      have hneg : -π ∈ maximalIdeal A := (maximalIdeal A).neg_mem hπmem
      have h0n : 0 ≠ n := by
        exact Nat.ne_of_lt hn
      have hcoeff0 : f.coeff 0 = -π := by
        simp [f, uniformizerRootPolynomial, h0n]
      rw [hcoeff0]
      exact hneg
    · -- All intermediate coefficients vanish for `X^n - π`.
      have hk' : k < n := by
        simpa [hnatDegree] using hk
      have hkn : k ≠ n := Nat.ne_of_lt hk'
      have hcoeff_zero : f.coeff k = 0 := by
        have hcoeff_X : (X ^ n : Polynomial A).coeff k = 0 := by
          simp [Polynomial.coeff_X_pow, hkn]
        have hcoeff_C : (C π : Polynomial A).coeff k = 0 := by
          rw [Polynomial.coeff_C]
          simp [Nat.ne_of_gt hkpos]
        calc
          f.coeff k = (X ^ n - C π : Polynomial A).coeff k := by rfl
          _ = (X ^ n : Polynomial A).coeff k - (C π : Polynomial A).coeff k := by simp
          _ = 0 - 0 := by rw [hcoeff_X, hcoeff_C]
          _ = 0 := sub_self 0
      rw [hcoeff_zero]
      exact (maximalIdeal A).zero_mem
  have hπ_not_mem_sq : π ∉ maximalIdeal A ^ 2 := by
    -- The uniformizer cannot be divisible by the square of the maximal ideal generator.
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    rcases hdiv with ⟨a, ha⟩
    have hπ0 : π ≠ 0 := hπ.ne_zero
    have hone : 1 = π * a := by
      apply mul_left_cancel₀ hπ0
      simpa [pow_two, mul_assoc, mul_one] using ha
    exact hπ.1 <| isUnit_of_dvd_one ⟨a, hone⟩
  have hcoeff0_not_mem_sq : f.coeff 0 ∉ maximalIdeal A ^ 2 := by
    -- The constant coefficient is `-π`, so nondivisibility by `π^2` transfers directly.
    intro hcoeff
    have h0n : 0 ≠ n := by
      exact Nat.ne_of_lt hn
    have hcoeff0 : f.coeff 0 = -π := by
      simp [f, uniformizerRootPolynomial, h0n]
    rw [hcoeff0] at hcoeff
    apply hπ_not_mem_sq
    exact (Submodule.neg_mem_iff _).1 hcoeff
  have hEis : f.IsEisensteinAt (maximalIdeal A) := by
    -- Eisenstein at the maximal ideal is the source-proof mechanism for irreducibility.
    refine hmonic.isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal A).ne_top ?_ ?_
    · intro k hk
      exact hcoeff_mem hk
    · simpa [f, uniformizerRootPolynomial] using hcoeff0_not_mem_sq
  -- Once the Eisenstein data are recorded over `A`, irreducibility is immediate.
  refine hEis.irreducible (maximalIdeal.isMaximal A).isPrime hmonic.isPrimitive ?_
  simpa [f, uniformizerRootPolynomial] using hn

/-- The radical extension ring `A[π^(1/n)]` is a domain. -/
instance uniformizerRootExtensionRing_isDomain_of_fact
    [Fact <| Irreducible π] [NeZero n] :
    IsDomain (uniformizerRootExtensionRing π n) := by
  -- Route correction: prove domainness directly from irreducibility in `A[X]`, which is exactly
  -- the source ring-first route and avoids the stalled field-comparison injectivity detour.
  let hirr : Irreducible (uniformizerRootPolynomial π n) :=
    uniformizerRootPolynomial_irreducible
      (A := A) (π := π) (n := n) (hπ := Fact.out) (hn := Nat.pos_of_ne_zero (NeZero.ne n))
  simpa [uniformizerRootExtensionRing] using
    (AdjoinRoot.isDomain_of_prime (f := uniformizerRootPolynomial π n) hirr.prime)

local instance uniformizerRootExtensionRing_isDomain :
    IsDomain (A[π^(1/n)]) := by
  letI : Fact <| Irreducible π := ⟨hπ⟩
  letI : NeZero n := ⟨hn.ne'⟩
  exact uniformizerRootExtensionRing_isDomain_of_fact (A := A) (π := π) (n := n)

-- Proof sketch: once `K1` is realized as `AdjoinRoot (X^n - π)` over the fraction field, its
-- canonical power basis has dimension `n`; equivalently, the quotient by `(X^n - π)` has
-- `FractionRing A`-dimension `n`.
/-- Lemma 15.115.2 (1): adjoining an `n`th root of a uniformizer to `FractionRing A` gives a field
extension of degree `n`. -/
@[stacks 09EV]
theorem uniformizerRootExtensionField_finrank_eq :
    Module.finrank K (K[π^(1/n)]) = n := by
  let f : Polynomial K := uniformizerRootFractionPolynomial π n
  have hf_ne_zero : f ≠ 0 := by
    -- The defining Kummer polynomial `X^n - π` is nonzero for `n > 0`.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (Polynomial.X_pow_sub_C_ne_zero hn (algebraMap A K π))
  have hfinrank : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    -- The quotient presentation carries the canonical power basis coming from `1, X, ..., X^(n-1)`.
    simpa using (AdjoinRoot.powerBasis (f := f) hf_ne_zero).finrank
  have hnatDegree : f.natDegree = n := by
    -- The defining polynomial is exactly `X^n - π`, so its degree is `n`.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (Polynomial.natDegree_X_pow_sub_C (algebraMap A K π) hn.ne')
  calc
    Module.finrank K K1 = Module.finrank K (AdjoinRoot f) := by
      rfl
    _ = f.natDegree := hfinrank
    _ = n := hnatDegree

/-- Helper for Lemma 15.115.2: a single coefficient in `K = FractionRing A` can be rewritten with
one nonzero denominator from `A`. -/
private theorem coeff_fractionRing_clear_denominator (c : K) :
    ∃ num den : A, den ≠ 0 ∧ algebraMap A K num = algebraMap A K den * c := by
  -- Use localization surjectivity in the multiplication-oriented form needed for coefficient
  -- clearing.
  obtain ⟨⟨num, den⟩, hfrac⟩ := IsLocalization.surj (nonZeroDivisors A) c
  refine ⟨num, den, mem_nonZeroDivisors_iff_ne_zero.mp den.2, ?_⟩
  calc
    algebraMap A K num = c * algebraMap A K den := by
      simpa using hfrac.symm
    _ = algebraMap A K den * c := by
      rw [mul_comm]

/-- Helper for Lemma 15.115.2: finitely many coefficients in `K = FractionRing A` admit one common
nonzero denominator from `A`. -/
private theorem finite_common_denominator_for_family (t : Finset ℕ) (c : ℕ → K) :
    ∃ s : A, s ≠ 0 ∧ ∀ m ∈ t, ∃ b : A, algebraMap A K b = algebraMap A K s * c m := by
  induction t using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      intro m hm
      cases hm
  | @insert m t hm ih =>
      rcases ih with ⟨s, hs, hsupport⟩
      rcases coeff_fractionRing_clear_denominator (A := A) (π := π) (n := n) (c m) with
        ⟨bm, dm, hdm, hbm⟩
      refine ⟨s * dm, mul_ne_zero hs hdm, ?_⟩
      intro k hk
      rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · refine ⟨s * bm, ?_⟩
        -- The new coefficient absorbs the old common denominator by one extra multiplication.
        calc
          algebraMap A K (s * bm) = algebraMap A K s * algebraMap A K bm := by
            simp
          _ = algebraMap A K s * (algebraMap A K dm * c m) := by
            rw [hbm]
          _ = (algebraMap A K s * algebraMap A K dm) * c m := by
            ring
          _ = algebraMap A K (s * dm) * c m := by
            simp [mul_assoc]
      · rcases hsupport k hk with ⟨b, hb⟩
        refine ⟨b * dm, ?_⟩
        -- Previously cleared coefficients keep working after multiplying by the fresh
        -- denominator.
        calc
          algebraMap A K (b * dm) = algebraMap A K b * algebraMap A K dm := by
            simp
          _ = (algebraMap A K s * c k) * algebraMap A K dm := by
            rw [hb]
          _ = (algebraMap A K s * algebraMap A K dm) * c k := by
            ring
          _ = algebraMap A K (s * dm) * c k := by
            simp [mul_assoc]

/-- Helper for Lemma 15.115.2: the supported coefficients of a polynomial over
`K = FractionRing A` admit one common denominator from `A`. -/
private theorem polynomial_support_common_denominator (q : Polynomial K) :
    ∃ s : A, s ≠ 0 ∧
      ∀ m ∈ q.support, ∃ b : A, algebraMap A K b = algebraMap A K s * q.coeff m := by
  -- Apply the finite-family clearing lemma to the coefficient function.
  simpa using
    (finite_common_denominator_for_family (A := A) (π := π) (n := n) q.support q.coeff)

/-- Helper for Lemma 15.115.2: after clearing all supported coefficients of `q`, one gets a base
polynomial whose coefficient extension is `C s * q`. -/
private theorem exists_cleared_base_polynomial_map_eq (q : Polynomial K) :
    ∃ s : A, s ≠ 0 ∧ ∃ q₀ : Polynomial A,
      Polynomial.map (algebraMap A K) q₀ = C (algebraMap A K s) * q := by
  classical
  rcases polynomial_support_common_denominator (A := A) (π := π) (n := n) q with
    ⟨s, hs, hsupport⟩
  choose b hb using hsupport
  let coeff₀ : ℕ → A := fun m => if hm : m ∈ q.support then b m hm else 0
  let q₀ : Polynomial A := q.support.sum fun m ↦ Polynomial.monomial m (coeff₀ m)
  refine ⟨s, hs, q₀, ?_⟩
  -- Compare coefficients on and off the finite support of `q`.
  ext m
  rw [Polynomial.coeff_map, Polynomial.coeff_C_mul]
  by_cases hm : m ∈ q.support
  · have hq₀ : q₀.coeff m = coeff₀ m := by
      -- On the support, only the `m`th monomial contributes.
      simp [q₀, Polynomial.coeff_monomial, hm]
    have hqm : q.coeff m ≠ 0 := Polynomial.mem_support_iff.mp hm
    have hcoeff₀ : coeff₀ m = b m hm := by
      simp [coeff₀, hqm]
    rw [hq₀, hcoeff₀, hb m hm]
  · have hq₀ : q₀.coeff m = 0 := by
      -- Off the support, every monomial contributes zero to the `m`th coefficient.
      simp [q₀, Polynomial.coeff_monomial, hm]
    have hqm : q.coeff m = 0 := by
      by_contra hqm
      exact hm (Polynomial.mem_support_iff.mpr hqm)
    rw [hq₀, hqm]
    simp

/-- Helper for Lemma 15.115.2: evaluating the cleared coefficient identity at the distinguished
root in `K[π^(1/n)]` gives the required denominator-cleared equality there. -/
private theorem aeval_map_algebraMap_clear_denominator
    {q : Polynomial K} {s : A} {q₀ : Polynomial A}
    (hmap : Polynomial.map (algebraMap A K) q₀ = C (algebraMap A K s) * q) :
    aeval (root[π^(1/n)]) q₀ =
      algebraMap A K1 s * aeval (root[π^(1/n)]) q := by
  -- Keep coefficient clearing separate from scalar-tower transport through `A ⊆ K ⊆ K1`.
  calc
    aeval (root[π^(1/n)]) q₀ = aeval (root[π^(1/n)]) (Polynomial.map (algebraMap A K) q₀) := by
      symm
      simpa using (Polynomial.aeval_map_algebraMap (R := A) K (root[π^(1/n)]) q₀)
    _ = aeval (root[π^(1/n)]) (C (algebraMap A K s) * q) := by
      rw [hmap]
    _ = algebraMap A K1 s * aeval (root[π^(1/n)]) q := by
      simp [IsScalarTower.algebraMap_eq A K K1]

/-- Helper for Lemma 15.115.2: every element of `K[π^(1/n)]` is represented by a polynomial in the
distinguished root over `K = FractionRing A`. -/
private theorem uniformizerRootExtension_exists_polynomial_representation (z : K1) :
    ∃ q : Polynomial K, aeval (root[π^(1/n)]) q = z := by
  -- Every quotient class in `AdjoinRoot` is already a polynomial in the distinguished root.
  refine AdjoinRoot.induction_on (f := uniformizerRootFractionPolynomial π n) (x := z) ?_
  intro q
  refine ⟨q, ?_⟩
  simpa using (AdjoinRoot.aeval_eq q)

/-- Helper for Lemma 15.115.2: the comparison map `A[π^(1/n)] → K[π^(1/n)]` transports base
polynomial evaluation at the ring-side root to evaluation at the field-side root. -/
private theorem uniformizerRootExtensionRing_to_fractionField_aeval (q₀ : Polynomial A) :
    uniformizerRootExtensionRing_to_fractionField (π := π) (n := n)
        (aeval (AdjoinRoot.root (uniformizerRootPolynomial π n)) q₀) =
      aeval (root[π^(1/n)]) q₀ := by
  -- This is the stable `aeval` transport across the quotient comparison map.
  simpa [uniformizerRootExtensionRing_to_fractionField_root] using
    q₀.map_aeval_eq_aeval_map
      (show algebraMap A K1 =
          (uniformizerRootExtensionRing_to_fractionField (π := π) (n := n)).toRingHom.comp
            (algebraMap A R1) by
        ext a
        simp [uniformizerRootExtensionRing_to_fractionField_of])
      (AdjoinRoot.root (uniformizerRootPolynomial π n))

/-- Helper for Lemma 15.115.2: every element of `K[π^(1/n)]` admits a denominator from
`A[π^(1/n)]`. -/
private theorem uniformizerRootExtensionRing_clear_denominators (z : K1) :
    ∃ r s : R1, s ≠ 0 ∧
      uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) s * z =
        uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) r := by
  rcases uniformizerRootExtension_exists_polynomial_representation
      (A := A) (π := π) (n := n) z with ⟨q, hq⟩
  rcases exists_cleared_base_polynomial_map_eq (A := A) (π := π) (n := n) q with
    ⟨s, hs, q₀, hmap⟩
  let r : R1 := aeval (AdjoinRoot.root (uniformizerRootPolynomial π n)) q₀
  let sR : R1 := algebraMap A R1 s
  have hsR : sR ≠ 0 := by
    -- The explicit quotient ring is already a domain, so nonzero base scalars stay nonzero there.
    exact map_ne_zero (NoZeroSMulDivisors.algebraMap_injective A R1) hs
  have hclear :
      aeval (root[π^(1/n)]) q₀ = algebraMap A K1 s * aeval (root[π^(1/n)]) q :=
    aeval_map_algebraMap_clear_denominator
      (A := A) (π := π) (n := n) (q := q) (s := s) (q₀ := q₀) hmap
  refine ⟨r, sR, hsR, ?_⟩
  -- The numerator is the class of the cleared base polynomial, and the denominator is `s`.
  calc
    uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) sR * z
        = algebraMap A K1 s * z := by
            rw [uniformizerRootExtensionRing_to_fractionField_of (π := π) (n := n) s]
    _ = algebraMap A K1 s * aeval (root[π^(1/n)]) q := by
          rw [← hq]
    _ = aeval (root[π^(1/n)]) q₀ := hclear.symm
    _ = uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) r := by
          rw [uniformizerRootExtensionRing_to_fractionField_aeval (A := A) (π := π) (n := n) q₀]

/-- Helper for Lemma 15.115.2: divisibility by `X^n - π` after coefficient extension to the
fraction field descends to divisibility over the base discrete valuation ring. -/
private theorem uniformizerRootPolynomial_dvd_of_fraction_map_dvd {q : Polynomial A}
    (hq :
      uniformizerRootFractionPolynomial π n ∣ Polynomial.map (algebraMap A K) q) :
    uniformizerRootPolynomial π n ∣ q := by
  let f : Polynomial A := uniformizerRootPolynomial π n
  have hf_monic : f.Monic := by
    -- The source polynomial is monic, so its remainder theory is stable over the base ring.
    simpa [f, uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  have hmap_mod :
      Polynomial.map (algebraMap A K) (q %ₘ f) =
        (Polynomial.map (algebraMap A K) q) %ₘ uniformizerRootFractionPolynomial π n := by
    -- Coefficient extension commutes with division by a monic polynomial.
    simpa [f, uniformizerRootFractionPolynomial] using
      (Polynomial.map_modByMonic (f := q) (g := f) (algebraMap A K) hf_monic)
  have hmap_zero :
      Polynomial.map (algebraMap A K) (q %ₘ f) = 0 := by
    -- A divisible polynomial has zero remainder after division by the monic divisor.
    rw [hmap_mod, Polynomial.modByMonic_eq_zero_iff_dvd]
    · exact hq
    · simpa [uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
        (Polynomial.monic_X_pow_sub_C (algebraMap A K π) hn.ne')
  have hmod_zero : q %ₘ f = 0 := by
    -- Injectivity of `A → K` lets us read the vanishing remainder back on coefficients.
    ext m
    apply IsFractionRing.injective A K
    simpa [Polynomial.coeff_map] using congrArg (fun r : Polynomial K ↦ r.coeff m) hmap_zero
  -- Vanishing remainder is exactly the divisibility statement over the base ring.
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hf_monic]
  simpa [f] using hmod_zero

/-- Helper for Lemma 15.115.2: the explicit quotient map `A[π^(1/n)] → K[π^(1/n)]` is injective.
-/
private theorem uniformizerRootExtensionRing_to_fractionField_injective :
    Function.Injective (uniformizerRootExtensionRing_to_fractionField (π := π) (n := n)) := by
  let f : Polynomial A := uniformizerRootPolynomial π n
  intro x y hxy
  have hzero :
      uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) (x - y) = 0 := by
    -- Injectivity reduces to the kernel, so pass to the difference.
    simpa [map_sub] using sub_eq_zero.mpr hxy
  have hker : x - y = 0 := by
    -- Work with a polynomial representative in the quotient presentation.
    revert hzero
    refine AdjoinRoot.induction_on (f := f) (x := x - y) ?_
    intro q
    intro hq
    have hq_eval :
        aeval (root[π^(1/n)]) (Polynomial.map (algebraMap A K) q) = 0 := by
      -- Transport the zero hypothesis to field-side polynomial evaluation.
      have hq_eval_A : aeval (root[π^(1/n)]) q = 0 := by
        simpa [f, uniformizerRootExtensionRing_to_fractionField_aeval] using hq
      simpa using
        ((Polynomial.aeval_map_algebraMap (R := A) K (root[π^(1/n)]) q).symm.trans hq_eval_A)
    have hq_dvd_map :
        uniformizerRootFractionPolynomial π n ∣ Polynomial.map (algebraMap A K) q := by
      -- Vanishing in the field quotient is equivalent to divisibility by the defining polynomial.
      rw [← AdjoinRoot.mk_eq_zero]
      simpa using hq_eval
    have hq_dvd :
        uniformizerRootPolynomial π n ∣ q :=
      uniformizerRootPolynomial_dvd_of_fraction_map_dvd
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) hq_dvd_map
    -- Returning to the ring quotient, the representative is zero exactly when it is divisible.
    rw [← AdjoinRoot.mk_eq_zero]
    simpa [f] using hq_dvd
  exact sub_eq_zero.mp hker

/-- Helper for Lemma 15.115.2: the canonical `R1`-algebra map to `K1` is the explicit quotient
comparison map. -/
private theorem uniformizerRootExtensionRing_algebraMap_eq_to_fractionField :
    algebraMap R1 K1 =
      uniformizerRootExtensionRing_to_fractionField (π := π) (n := n) := by
  -- Route correction: identify the canonical algebra map with the source-faithful quotient map
  -- before transporting the previously proved injectivity and denominator-clearing owners.
  ext
  -- Two `A`-algebra maps out of the quotient agree once they send the adjoined root to the same
  -- element of `K1`.
  simp [uniformizerRootExtensionRing_to_fractionField_root]

/-- Helper for Lemma 15.115.2: the installed algebra map `R1 → K1` is injective. -/
private theorem uniformizerRootExtensionRing_algebraMap_injective :
    Function.Injective (algebraMap R1 K1) := by
  -- Rewrite the canonical algebra map to the already-controlled explicit comparison map.
  simpa [uniformizerRootExtensionRing_algebraMap_eq_to_fractionField] using
    (uniformizerRootExtensionRing_to_fractionField_injective
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn))

/-- Helper for Lemma 15.115.2: every element of `K1` admits denominator clearing in the canonical
`algebraMap R1 K1` shape. -/
private theorem uniformizerRootExtensionRing_clear_denominators_algebraMap (z : K1) :
    ∃ r s : R1, s ≠ 0 ∧ algebraMap R1 K1 s * z = algebraMap R1 K1 r := by
  -- Transport the existing denominator-clearing statement through the canonical map equality.
  simpa [uniformizerRootExtensionRing_algebraMap_eq_to_fractionField] using
    (uniformizerRootExtensionRing_clear_denominators
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) z)

/-- Helper for Lemma 15.115.2: the distinguished root in `R1 = A[X] / (X^n - π)` satisfies the
same defining equation as in the field-side quotient. -/
@[simp] private theorem uniformizerRootExtensionRing_root_pow :
    AdjoinRoot.root (uniformizerRootPolynomial π n) ^ n = algebraMap A R1 π := by
  -- The quotient generator already annihilates `X^n - π` over the base ring `A`.
  simpa [uniformizerRootPolynomial, sub_eq_zero] using
    (AdjoinRoot.eval₂_root (uniformizerRootPolynomial π n))

/-- Helper for Lemma 15.115.2: any base element in `maximalIdeal A` maps into the principal ideal
generated by the distinguished root of `R1`. -/
private theorem uniformizerRootExtensionRing_image_mem_root_span_of_mem_maximal
    {a : A} (ha : a ∈ maximalIdeal A) :
    algebraMap A R1 a ∈
      Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1) := by
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π n)
  have hπspan : maximalIdeal A = Ideal.span ({π} : Set A) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  rw [hπspan, Ideal.mem_span_singleton] at ha
  rcases ha with ⟨b, rfl⟩
  rw [map_mul, ← uniformizerRootExtensionRing_root_pow (A := A) (π := π) (n := n)]
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, hm⟩
  rw [hm, pow_succ]
  -- Once `π` is rewritten as `y^n`, the result is visibly a multiple of `y`.
  exact Ideal.mul_mem_right _ _
    (Ideal.subset_span (by simp [y]))

/-- Helper for Lemma 15.115.2: quotienting `R1 = A[X] / (X^n - π)` by the distinguished root
recovers the residue field of `A`. -/
private theorem uniformizerRootExtensionRing_quotient_by_root_equiv_residueField :
    (R1 ⧸ Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1)) ≃+*
      ResidueField A := by
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π n)
  have hπzero : residue A π = 0 := by
    -- The chosen uniformizer dies in the residue field.
    apply (IsLocalRing.residue_eq_zero_iff (R := A) (a := π)).2
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact Ideal.mem_span_singleton_self π
  have hφ_root :
      aeval (0 : ResidueField A) (uniformizerRootPolynomial π n) = 0 := by
    -- Evaluating `X^n - π` at the killed root `0` leaves only the residue of `π`.
    simp [uniformizerRootPolynomial, hπzero, hn.ne']
  let φ : R1 →ₐ[A] ResidueField A :=
    AdjoinRoot.liftAlgHom (uniformizerRootPolynomial π n) (residue A) 0 hφ_root
  have hφ_of (a : A) :
      φ (algebraMap A R1 a) = residue A a := by
    -- The lifted quotient map agrees with the base residue map on coefficients.
    simpa [φ] using
      (AdjoinRoot.liftAlgHom_of
        (p := uniformizerRootPolynomial π n)
        (i := residue A)
        (x := (0 : ResidueField A))
        (h := hφ_root)
        a)
  have hφ_root_apply : φ y = 0 := by
    -- The lift was defined to kill the distinguished root.
    simpa [φ, y]
  have hφ_surj : Function.Surjective φ := by
    -- Every residue-field element is represented by a coefficient from `A`.
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap A R1 a, hφ_of a⟩
  have hspan_le_ker :
      Ideal.span ({y} : Set R1) ≤ RingHom.ker φ.toRingHom := by
    -- The kernel contains `(y)` because `φ y = 0`.
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    rw [RingHom.mem_ker]
    exact hφ_root_apply
  have hker_le_span :
      RingHom.ker φ.toRingHom ≤ Ideal.span ({y} : Set R1) := by
    intro z hz
    revert hz
    refine AdjoinRoot.induction_on (f := uniformizerRootPolynomial π n) (x := z) ?_
    intro q
    intro hq
    rw [RingHom.mem_ker] at hq
    have hconst_zero : residue A (q.coeff 0) = 0 := by
      -- Evaluating at the killed root `0` leaves only the constant coefficient.
      have hq_eval : aeval (0 : ResidueField A) q = 0 := by
        simpa [φ, y] using hq
      simpa using hq_eval
    have hconst_mem : q.coeff 0 ∈ maximalIdeal A := by
      exact (IsLocalRing.residue_eq_zero_iff (R := A) (a := q.coeff 0)).1 hconst_zero
    have hconst_span :
        algebraMap A R1 (q.coeff 0) ∈ Ideal.span ({y} : Set R1) := by
      exact uniformizerRootExtensionRing_image_mem_root_span_of_mem_maximal
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) hconst_mem
    have hmul_span :
        y * aeval y q.divX ∈ Ideal.span ({y} : Set R1) := by
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp [y]))
    have hsplit : q = C (q.coeff 0) + X * q.divX := by
      -- Split off the constant term so the remaining summand is visibly divisible by `X`.
      ext k
      cases k with
      | zero =>
          simp
      | succ k =>
          simp [Polynomial.coeff_divX]
    have hrepr :
        (AdjoinRoot.mk (uniformizerRootPolynomial π n) q : R1) =
          algebraMap A R1 (q.coeff 0) + y * aeval y q.divX := by
      -- Re-express the quotient class as constant term plus a visible multiple of `y`.
      calc
        (AdjoinRoot.mk (uniformizerRootPolynomial π n) q : R1) = aeval y q := by
          simpa [y] using (AdjoinRoot.aeval_eq q)
        _ = aeval y (C (q.coeff 0) + X * q.divX) := by
          rw [hsplit]
        _ = algebraMap A R1 (q.coeff 0) + y * aeval y q.divX := by
          simp [y, mul_comm, mul_left_comm, mul_assoc]
    rw [hrepr]
    exact Ideal.add_mem _ hconst_span hmul_span
  have hker_eq :
      RingHom.ker φ.toRingHom =
        Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1) := by
    -- The explicit residue-evaluation kernel is exactly the principal ideal `(y)`.
    simpa [y] using le_antisymm hker_le_span hspan_le_ker
  let eker : (R1 ⧸ RingHom.ker φ.toRingHom) ≃+* ResidueField A :=
    RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ_surj
  -- Transport the quotient-by-kernel equivalence through the computed kernel equality.
  exact (Ideal.quotientEquivAlgOfEq A hker_eq.symm).toRingEquiv.trans eker

/-- Helper for Lemma 15.115.2: the principal ideal generated by the distinguished root of `R1`
is maximal. -/
private theorem uniformizerRootExtensionRing_root_span_isMaximal :
    Ideal.IsMaximal
      (Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1)) := by
  let e :=
    uniformizerRootExtensionRing_quotient_by_root_equiv_residueField
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)
  -- The quotient is a field because it is canonically identified with `ResidueField A`.
  exact Ideal.Quotient.maximal_of_isField _ <|
    e.toRingEquiv.toMulEquiv.isField (Field.toIsField _)

/-- Helper for Lemma 15.115.2: `R1 = A[X] / (X^n - π)` is local, and its maximal ideal is exactly
the principal ideal generated by the distinguished root. -/
private theorem uniformizerRootExtensionRing_isLocalRing_and_maximalIdeal_eq :
    ∃ hlocal : IsLocalRing R1,
      @maximalIdeal R1 inferInstance hlocal =
        Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1) := by
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π n)
  have hmonic : (uniformizerRootPolynomial π n).Monic := by
    -- The owner polynomial is monic, so the quotient is finite, hence integral, over `A`.
    simpa [uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  letI : Module.Finite A R1 := hmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A R1 := Algebra.IsIntegral.of_finite A R1
  have hspan_max :
      Ideal.IsMaximal
        (Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1)) :=
    uniformizerRootExtensionRing_root_span_isMaximal
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)
  have hlocal : IsLocalRing R1 := by
    -- Every maximal ideal upstairs contains `y`, hence equals `(y)`.
    refine IsLocalRing.of_unique_max_ideal ?_
    refine ⟨Ideal.span ({y} : Set R1), hspan_max, ?_⟩
    intro I hI
    letI : I.IsMaximal := hI
    have hcomap : Ideal.comap (algebraMap A R1) I = maximalIdeal A := by
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
    have hpi_mem : algebraMap A R1 π ∈ I := by
      change π ∈ Ideal.comap (algebraMap A R1) I
      rw [hcomap, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
      exact Ideal.mem_span_singleton_self π
    have hy_pow_mem : y ^ n ∈ I := by
      simpa [y] using hpi_mem
    have hy_mem : y ∈ I := by
      exact hI.isPrime.mem_of_pow_mem n hy_pow_mem
    have hle : Ideal.span ({y} : Set R1) ≤ I := by
      refine Ideal.span_le.2 ?_
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hy_mem
    exact (Ideal.IsMaximal.eq_of_le hspan_max hI.ne_top hle).symm
  -- In a local ring, the distinguished maximal ideal is the unique maximal ideal.
  exact ⟨hlocal, (IsLocalRing.eq_maximalIdeal hspan_max).symm⟩

/-- Helper for Lemma 15.115.2: `R1 = A[X] / (X^n - π)` is Noetherian because the monic owner
quotient is finite over the Noetherian DVR `A`. -/
private theorem uniformizerRootExtensionRing_isNoetherianRing :
    IsNoetherianRing R1 := by
  have hmonic : (uniformizerRootPolynomial π n).Monic := by
    -- The source-faithful quotient by a monic polynomial is finite over `A`.
    simpa [uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  letI : Module.Finite A R1 := hmonic.finite_adjoinRoot
  exact IsNoetherianRing.of_finite A R1

/-- Helper for Lemma 15.115.2: clause `(4)` of `discreteValuationRing_tfae` holds for
`R1 = A[X] / (X^n - π)`. -/
private theorem uniformizerRootExtensionRing_tfae_clause_four :
    ∃ (_ : IsLocalRing R1) (_ : IsNoetherianRing R1) (_ : IsDomain R1),
      maximalIdeal R1 ≠ ⊥ ∧ (maximalIdeal R1).IsPrincipal := by
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π n)
  letI : IsNoetherianRing R1 :=
    uniformizerRootExtensionRing_isNoetherianRing (A := A) (π := π) (n := n) (hn := hn)
  rcases uniformizerRootExtensionRing_isLocalRing_and_maximalIdeal_eq
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) with
    ⟨hlocal, hmax⟩
  letI : IsLocalRing R1 := hlocal
  have hy_ne_zero : y ≠ 0 := by
    -- If the quotient root vanished, then the nonzero uniformizer `π` would vanish in the domain.
    intro hy0
    have hpi0 : algebraMap A R1 π = 0 := by
      simpa [y, hy0] using
        (uniformizerRootExtensionRing_root_pow (A := A) (π := π) (n := n))
    exact hπ.ne_zero ((NoZeroSMulDivisors.algebraMap_injective A R1) hpi0)
  have hmax_ne_bot : maximalIdeal R1 ≠ ⊥ := by
    rw [hmax]
    intro hbot
    have hy_mem : y ∈ (⊥ : Ideal R1) := by
      simpa [hbot, y] using
        (Ideal.mem_span_singleton_self (AdjoinRoot.root (uniformizerRootPolynomial π n)) :
          AdjoinRoot.root (uniformizerRootPolynomial π n) ∈
            Ideal.span ({AdjoinRoot.root (uniformizerRootPolynomial π n)} : Set R1))
    exact hy_ne_zero (by simpa using hy_mem)
  have hprincipal : (maximalIdeal R1).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, hmax_ne_bot, hprincipal⟩

/-- Helper for Lemma 15.115.2: the explicit quotient ring `R1 = A[X] / (X^n - π)` is a discrete
valuation ring. -/
private theorem uniformizerRootExtensionRing_isDiscreteValuationRing_aux :
    @IsDiscreteValuationRing R1 inferInstance uniformizerRootExtensionRing_isDomain := by
  have htfae :=
    (show List.TFAE
        [ (∃ (_ : IsDomain R1), IsDiscreteValuationRing R1),
          ∃ (_ : IsDomain R1) (_ : IsNoetherianRing R1), ValuationRing R1 ∧ ¬ IsField R1,
          IsRegularLocalRing R1 ∧ ringKrullDim R1 = 1,
          ∃ (_ : IsLocalRing R1) (_ : IsNoetherianRing R1) (_ : IsDomain R1),
            maximalIdeal R1 ≠ ⊥ ∧ (maximalIdeal R1).IsPrincipal,
          ∃ (_ : IsLocalRing R1) (_ : IsNoetherianRing R1) (_ : IsDomain R1)
            (_ : IsIntegrallyClosed R1), ringKrullDim R1 = 1 ] from
      discreteValuationRing_tfae (A := R1))
  -- Clause `(4) → (1)` packages the local/principal-maximal-ideal route into the DVR owner.
  have hdvr : ∃ (_ : IsDomain R1), IsDiscreteValuationRing R1 := by
    exact (htfae.out 3 0).mp <|
      uniformizerRootExtensionRing_tfae_clause_four
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)
  exact hdvr.choose_spec

/-- Helper for Lemma 15.115.2: the canonical map `R1 → K1` exhibits `K1` as the fraction field of
`R1`. -/
private theorem uniformizerRootExtensionRing_fractionField_bridge :
    IsFractionRing R1 K1 := by
  -- Route correction: package the already-proved injective comparison map and denominator
  -- clearing into the standard `IsFractionRing.of_field` owner before the integral-closure proof.
  letI : FaithfulSMul R1 K1 :=
    FaithfulSMul.of_injective
      (algebraMap R1 K1)
      (uniformizerRootExtensionRing_algebraMap_injective
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn))
  refine IsFractionRing.of_field R1 K1 ?_
  intro z
  rcases uniformizerRootExtensionRing_clear_denominators_algebraMap
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) z with
    ⟨r, s, hs, hclear⟩
  refine ⟨r, s, ?_⟩
  -- The multiplicative denominator-clearing identity is equivalent to the expected fraction
  -- representation because `algebraMap R1 K1 s` is nonzero in the field `K1`.
  apply (eq_div_iff ?_).2
  exact fun hs0 ↦ hs <|
    (uniformizerRootExtensionRing_algebraMap_injective
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)) hs0
  simpa [mul_comm] using hclear

-- Proof sketch: compare the explicit quotient ring `A[X] / (X^n - π)` with the integral closure
-- inside `K1`; the explicit ring is finite over `A`, integrally closed, and contains the chosen
-- root, so it realizes the integral closure.
/-- Lemma 15.115.2 (2): the explicit quotient ring `A[π^(1/n)] = A[X] / (X^n - π)` is the
integral closure of `A` in `K[π^(1/n)]`. -/
@[stacks 09EV]
theorem uniformizerRootExtensionRing_isIntegralClosure :
    IsIntegralClosure (A[π^(1/n)]) A (K[π^(1/n)]) := by
  have hmonic : (uniformizerRootPolynomial π n).Monic := by
    -- The owner polynomial is monic, so the explicit quotient is finite, hence integral, over `A`.
    simpa [uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  letI : Module.Finite A R1 := hmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A R1 := Algebra.IsIntegral.of_finite A R1
  letI : IsDiscreteValuationRing R1 :=
    uniformizerRootExtensionRing_isDiscreteValuationRing_aux
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)
  letI : IsFractionRing R1 K1 :=
    uniformizerRootExtensionRing_fractionField_bridge
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)
  letI : IsIntegrallyClosed R1 := by
    infer_instance
  -- A DVR is integrally closed in its fraction field, so the canonical owner theorem applies.
  exact IsIntegralClosure.of_isIntegrallyClosed R1 A K1

/-- The radical extension field `K[π^(1/n)]` is the fraction field of `A[π^(1/n)]`. -/
instance uniformizerRootExtensionRing_isFractionRing :
    IsFractionRing R1 K1 :=
  uniformizerRootExtensionRing_fractionField_bridge
    (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)

/-- Lemma 15.115.2 (3): the integral-closure ring `A[π^(1/n)]` is a discrete valuation ring. -/
@[stacks 09EV]
instance uniformizerRootExtensionRing_isDiscreteValuationRing
    [Fact <| Irreducible π] [NeZero n] :
    IsDiscreteValuationRing (uniformizerRootExtensionRing π n) :=
  uniformizerRootExtensionRing_isDiscreteValuationRing_aux
    (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)

/-- The canonical map `A → A[π^(1/n)]` is an extension of discrete valuation rings. -/
instance uniformizerRootExtensionRing_isExtensionOfDiscreteValuationRings
    [Fact <| Irreducible π] [NeZero n] :
    IsExtensionOfDiscreteValuationRings A R1 := by
  have hmonic : (uniformizerRootPolynomial π n).Monic := by
    -- The explicit quotient is finite over `A`, so the structure map is integral.
    simpa [uniformizerRootPolynomial] using Polynomial.monic_X_pow_sub_C π hn.ne'
  letI : Module.Finite A R1 := hmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A R1 := Algebra.IsIntegral.of_finite A R1
  -- The source map is integral and injective, so it is an extension of DVRs once `R1` is known
  -- to be a DVR.
  refine
    { toIsLocalHom := ?_
      algebraMap_injective := ?_ }
  · exact
      (algebraMap_isIntegral_iff.mpr (show Algebra.IsIntegral A R1 by infer_instance)).isLocalHom
        (uniformizerRootExtensionRing_algebraMap_injective
          (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn))
  · exact
      uniformizerRootExtensionRing_algebraMap_injective
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)

/-- Helper for Lemma 15.115.2: the image of `maximalIdeal A` in `R1` is the `n`th power of the
maximal ideal generated by the distinguished root. -/
private theorem uniformizerRootExtensionRing_map_maximalIdeal_eq_pow_root :
    Ideal.map (algebraMap A R1) (maximalIdeal A) = maximalIdeal R1 ^ n := by
  let y : R1 := AdjoinRoot.root (uniformizerRootPolynomial π n)
  rcases uniformizerRootExtensionRing_isLocalRing_and_maximalIdeal_eq
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) with
    ⟨hlocal, hmax⟩
  letI : IsLocalRing R1 := hlocal
  -- Rewrite both maximal ideals through the chosen generators `π` and `y`.
  calc
    Ideal.map (algebraMap A R1) (maximalIdeal A)
        = Ideal.map (algebraMap A R1) (Ideal.span ({π} : Set A)) := by
            rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    _ = Ideal.span ({algebraMap A R1 π} : Set R1) := by
          rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.span ({y ^ n} : Set R1) := by
          rw [← uniformizerRootExtensionRing_root_pow (A := A) (π := π) (n := n)]
    _ = Ideal.span ({y} : Set R1) ^ n := by
          simpa using (Ideal.span_singleton_pow y n).symm
    _ = maximalIdeal R1 ^ n := by
          rw [← hmax]

-- Proof sketch: in the discrete valuation ring `R1 = A[π^(1/n)]`, the adjoined root generates the
-- maximal ideal, and its `n`th power is the image of the uniformizer `π`; comparing generators of
-- the two maximal ideals gives ramification index `n`.
/-- Lemma 15.115.2 (4): the ramification index of `A[π^(1/n)]` over `A` is `n`. -/
@[stacks 09EV]
theorem ramificationIndex_uniformizerRootExtensionRing
    [Fact <| Irreducible π] [NeZero n] :
    ramificationIndex A (uniformizerRootExtensionRing π n) = n := by
  -- The ramification index is exactly the exponent appearing in the mapped-maximal-ideal
  -- equality just proved.
  exact ramificationIndex_eq_of_map_maximalIdeal_eq_pow (A := A) (B := R1) <|
    uniformizerRootExtensionRing_map_maximalIdeal_eq_pow_root
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)

end UniformizerRootExtensionDisplay

-- Proof sketch: `R1` is itself a discrete valuation ring, so it has a unique maximal ideal;
-- any maximal ideal lying over `maximalIdeal A` must therefore be that maximal ideal.
/-- Lemma 15.115.2 (5): the quotient ring `A[π^(1/n)]` has a unique maximal ideal lying over the
maximal ideal of `A`. -/
@[stacks 09EV]
theorem uniformizerRootExtensionRing_unique_maximalIdeal_liesOver
    [Fact <| Irreducible π] [NeZero n]
    (P : Ideal R1) (hP : P.IsMaximal) (hPOver : Ideal.LiesOver P (maximalIdeal A)) :
    P = maximalIdeal R1 := by
  letI : P.IsMaximal := hP
  letI : Ideal.LiesOver P (maximalIdeal A) := hPOver
  -- The target ring is a DVR, hence local, so every maximal branch equals the unique maximal
  -- ideal.
  exact IsLocalRing.eq_maximalIdeal inferInstance

/-- Helper for Lemma 15.115.2: in a local ring, the residue field at the maximal ideal identifies
with the canonical local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv
    (R : Type*) [CommRing R] [IsLocalRing R] :
    (maximalIdeal R).ResidueField ≃+* ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.115.2: the maximal-ideal residue-field identification sends residue
classes of elements to the canonical local residue classes. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (R : Type*) [CommRing R] [IsLocalRing R] (a : R) :
    maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a) =
      IsLocalRing.residue R a := by
  -- Compare both sides through the inverse equivalence coming from the quotient/residue-field map.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap (ResidueField R) (maximalIdeal R).ResidueField (IsLocalRing.residue R a) by rfl]
  change
    maximalIdeal_residueField_equiv R
        ((maximalIdeal_residueField_equiv R).symm (IsLocalRing.residue R a)) =
      IsLocalRing.residue R a
  exact (maximalIdeal_residueField_equiv R).apply_symm_apply (IsLocalRing.residue R a)

/-- Helper for Lemma 15.115.2: after identifying ideal residue fields with local residue fields,
the ideal-level residue-field map becomes the canonical local residue-field map. -/
private theorem maximalIdeal_residueField_equiv_comp_residueFieldMap
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (maximalIdeal_residueField_equiv S).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdeal_residueField_equiv R).toRingHom := by
  -- It suffices to check the comparison on residue classes of elements of `R`.
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdeal_residueField_equiv S
        (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) f
          (IsLocalRing.maximalIdeal_comap f).symm
          (algebraMap R (maximalIdeal R).ResidueField a)) =
      ResidueField.map f
        (maximalIdeal_residueField_equiv R (algebraMap R (maximalIdeal R).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdeal_residueField_equiv_apply_algebraMap,
    maximalIdeal_residueField_equiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

/-- Helper for Lemma 15.115.2: at the unique maximal ideal of `R1`, the residue-field map is
bijective. -/
private theorem uniformizerRootExtensionRing_residueFieldMap_bijective_maximalIdeal :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
        ((Ideal.liesOver_iff _ _).2 rfl)) := by
  rcases uniformizerRootExtensionRing_isLocalRing_and_maximalIdeal_eq
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) with
    ⟨hlocal, hmax⟩
  letI : IsLocalRing R1 := hlocal
  let e : ResidueField A ≃+* ResidueField R1 :=
    (uniformizerRootExtensionRing_quotient_by_root_equiv_residueField
        (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)).symm.trans
      (Ideal.quotientEquivAlgOfEq A hmax.symm).toRingEquiv
  have hmap :
      ResidueField.map (algebraMap A R1) = e.toRingHom := by
    -- The explicit quotient equivalence should agree with the canonical local residue-field map
    -- on residue classes coming from `A`.
    apply Ideal.Quotient.ringHom_ext
    intro a
    change IsLocalRing.residue R1 ((algebraMap A R1) a) = e (IsLocalRing.residue A a)
    simp [e, IsLocalRing.ResidueField.map_residue]
  have hres : Function.Bijective (ResidueField.map (algebraMap A R1)) := by
    simpa [hmap] using e.bijective
  have hcomp :
      (maximalIdeal_residueField_equiv R1).toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
            ((Ideal.liesOver_iff _ _).2 rfl)) =
        (ResidueField.map (algebraMap A R1)).comp
          (maximalIdeal_residueField_equiv A).toRingHom := by
    simpa using
      maximalIdeal_residueField_equiv_comp_residueFieldMap
        (f := algebraMap A R1)
  constructor
  · intro x y hxy
    -- Compare the two classes after moving both residue fields to the local quotient residue
    -- fields.
    have hx :
        (maximalIdeal_residueField_equiv R1)
            (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
              ((Ideal.liesOver_iff _ _).2 rfl) x) =
          (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A) x) := by
      simpa [RingHom.comp_apply] using
        congrArg (fun g : (maximalIdeal A).ResidueField →+* ResidueField R1 ↦ g x) hcomp
    have hy :
        (maximalIdeal_residueField_equiv R1)
            (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
              ((Ideal.liesOver_iff _ _).2 rfl) y) =
          (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A) y) := by
      simpa [RingHom.comp_apply] using
        congrArg (fun g : (maximalIdeal A).ResidueField →+* ResidueField R1 ↦ g y) hcomp
    have hxy' :
        (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A) x) =
          (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A) y) := by
      calc
        (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A) x) =
            (maximalIdeal_residueField_equiv R1)
              (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
                ((Ideal.liesOver_iff _ _).2 rfl) x) := hx.symm
        _ =
            (maximalIdeal_residueField_equiv R1)
              (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
                ((Ideal.liesOver_iff _ _).2 rfl) y) := by simpa [hxy]
        _ =
            (ResidueField.map (algebraMap A R1))
              ((maximalIdeal_residueField_equiv A) y) := hy
    exact (maximalIdeal_residueField_equiv A).injective (hres.1 hxy')
  · intro z
    -- Pull the target class back through the quotient equivalences and the bijective local
    -- residue-field map.
    obtain ⟨w, hw⟩ := hres.2 ((maximalIdeal_residueField_equiv R1) z)
    refine ⟨(maximalIdeal_residueField_equiv A).symm w, ?_⟩
    apply (maximalIdeal_residueField_equiv R1).injective
    calc
      (maximalIdeal_residueField_equiv R1)
          (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal R1) (algebraMap A R1)
            ((Ideal.liesOver_iff _ _).2 rfl)
            ((maximalIdeal_residueField_equiv A).symm w)) =
          (ResidueField.map (algebraMap A R1))
            ((maximalIdeal_residueField_equiv A)
              ((maximalIdeal_residueField_equiv A).symm w)) := by
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun g : (maximalIdeal A).ResidueField →+* ResidueField R1 ↦
                    g ((maximalIdeal_residueField_equiv A).symm w))
                  hcomp
      _ = (ResidueField.map (algebraMap A R1)) w := by simp
      _ = (maximalIdeal_residueField_equiv R1) z := hw

/-- Lemma 15.115.2 (6): for every maximal ideal of `A[π^(1/n)]` above `maximalIdeal A`, the
induced map on residue fields is bijective. -/
@[stacks 09EV]
theorem uniformizerRootExtensionRing_residueFieldMap_bijective
    (P : Ideal R1) (hP : P.IsMaximal) (hPOver : Ideal.LiesOver P (maximalIdeal A)) :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) P (algebraMap A R1) (P.over_def (maximalIdeal A))) := by
  have hP' :
      P = maximalIdeal R1 :=
    uniformizerRootExtensionRing_unique_maximalIdeal_liesOver
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn) P hP hPOver
  subst hP'
  -- Route correction: first normalize to the unique maximal branch of the local target ring, and
  -- only then compare the canonical residue-field map with the explicit quotient computation.
  simpa using
    uniformizerRootExtensionRing_residueFieldMap_bijective_maximalIdeal
      (A := A) (π := π) (n := n) (hπ := hπ) (hn := hn)

end

end UniformizerRootExtension

section UniformizerRootExtensionIrreducibleContext

variable {π : A} {n : ℕ}
variable [Fact <| Irreducible π] [NeZero n]

section

-- Reuse the canonical owner instances from `uniformizerRootExtension π n`; only the faithful
-- `A`-action is derived here from the fraction-field presentation.

/-- Helper for Lemma 15.115.2: adjoining a root of a monic polynomial of nonzero degree over a
nontrivial ring gives an injective base algebra map. -/
private lemma algebraMap_adjoinRoot_injective_of_monic_degree_ne_zero
    {R : Type*} [CommRing R] [Nontrivial R] {f : R[X]}
    (hf : f.Monic) (hdeg : f.degree ≠ 0) :
    Function.Injective (algebraMap R (AdjoinRoot f)) := by
  have hne : f ≠ 1 := by
    -- A monic polynomial equal to `1` would have degree `0`, contradicting the hypothesis.
    intro h1
    apply hdeg
    simpa [h1]
  intro r s hrs
  -- Compare the two base elements inside the quotient presentation by constant polynomials.
  change AdjoinRoot.mk f (Polynomial.C r) = AdjoinRoot.mk f (Polynomial.C s) at hrs
  rw [AdjoinRoot.mk_eq_mk] at hrs
  have hmod : (Polynomial.C (r - s)) %ₘ f = 0 := by
    -- Equality in the quotient means the constant difference is divisible by the defining
    -- polynomial.
    rw [Polynomial.modByMonic_eq_zero_iff_dvd hf]
    simpa using hrs
  have hdeg_pos : (0 : WithBot ℕ) < f.degree := by
    -- A nonconstant monic polynomial has positive degree.
    have hnat : 0 < f.natDegree := hf.natDegree_pos.mpr hne
    simpa [Polynomial.degree_eq_natDegree hf.ne_zero] using hnat
  have hself : (Polynomial.C (r - s)) %ₘ f = Polynomial.C (r - s) := by
    -- Since the divisor has positive degree, the constant polynomial is already its own
    -- remainder.
    rw [Polynomial.modByMonic_eq_self_iff hf]
    exact lt_of_le_of_lt Polynomial.degree_C_le hdeg_pos
  have hzero : Polynomial.C (r - s) = 0 := by
    -- The zero remainder forces the constant difference polynomial to vanish.
    rw [← hself, hmod]
  simpa [Polynomial.C_eq_zero, sub_eq_zero] using hzero

local instance uniformizerRootExtensionAlgebra :
    Algebra (FractionRing A) (uniformizerRootExtension π n) :=
  AdjoinRoot.instAlgebra (uniformizerRootFractionPolynomial π n)

local instance uniformizerRootExtensionBaseAlgebra :
    Algebra A (uniformizerRootExtension π n) :=
  AdjoinRoot.instAlgebra (uniformizerRootFractionPolynomial π n)

local instance uniformizerRootExtensionIsScalarTower :
    IsScalarTower A (FractionRing A) (uniformizerRootExtension π n) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  rfl

local instance : FaithfulSMul A (uniformizerRootExtension π n) := by
  letI : Fact (Irreducible (uniformizerRootFractionPolynomial π n)) :=
    ⟨uniformizerRootFractionPolynomial_irreducible Fact.out (NeZero.ne n)⟩
  have hmonic : (uniformizerRootFractionPolynomial π n).Monic := by
    simpa [uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (algebraMap A (FractionRing A) π) (NeZero.ne n))
  have hdeg : (uniformizerRootFractionPolynomial π n).degree ≠ 0 := by
    exact (degree_pos_of_irreducible (Fact.out :
      Irreducible (uniformizerRootFractionPolynomial π n))).ne'
  have hK :
      Function.Injective
        (algebraMap (FractionRing A) (uniformizerRootExtension π n)) := by
    have hK' :
        Function.Injective
          (algebraMap (FractionRing A)
            (AdjoinRoot (uniformizerRootFractionPolynomial π n))) :=
      algebraMap_adjoinRoot_injective_of_monic_degree_ne_zero hmonic hdeg
    simpa [uniformizerRootExtension] using hK'
  refine (faithfulSMul_iff_algebraMap_injective A (uniformizerRootExtension π n)).mpr ?_
  intro x y hxy
  change
    algebraMap (FractionRing A) (uniformizerRootExtension π n) (algebraMap A (FractionRing A) x) =
      algebraMap (FractionRing A) (uniformizerRootExtension π n) (algebraMap A (FractionRing A) y)
    at hxy
  apply IsFractionRing.injective A (FractionRing A)
  exact hK hxy

-- Proof sketch: identify the explicit quotient ring `R1` with the canonical integral closure of
-- `A` in `K1` via part `(2)`, then transport the unique-branch and residue-field-bijectivity
-- statements from parts `(5)` and `(6)` across this canonical equivalence.
/-- The radical extension `K[π^(1/n)] / FractionRing A` is totally ramified with respect to `A`. -/
theorem uniformizerRootExtensionField_isTotallyRamifiedWithRespectTo :
    IsTotallyRamifiedWithRespectTo A (uniformizerRootExtension π n) := by
  sorry

-- Proof sketch: the residue-field map is trivial by part (6), the ramification index is `n` by
-- part (4), and the hypothesis that `n` is prime to the residue characteristic gives the
-- coprimality condition for the ramification index at every maximal ideal over `maximalIdeal A`.
/-- Lemma 15.115.2 (7): if `n` is prime to the residue characteristic of `A`, then
`K[π^(1/n)] / FractionRing A` is tamely ramified with respect to `A`. -/
@[stacks 09EV]
theorem uniformizerRootExtensionField_isTamelyRamifiedWithRespectTo
    (hprime : PrimeToResidueCharacteristic A n) :
    IsTamelyRamifiedWithRespectTo A (uniformizerRootExtension π n) := by
  sorry

-- Proof sketch: apply Lemma `9.24.3` to the simple extension generated by the distinguished root
-- `π^(1/n)`. The equality `(π^(1/n))^n = π` places its `n`th power in the base field, and the
-- tame hypothesis forces every `n`th root of unity in `K[π^(1/n)]` to come from the base field.
/-- Lemma 15.115.2 (8): if `n` is prime to the residue characteristic of `A`, then every
intermediate field of `K[π^(1/n)] / FractionRing A` is generated by `π^(1/d)` for some divisor
`d` of `n`, realized as the power `root[π^(1/n)] ^ (n / d)` of the distinguished root. -/
@[stacks 09EV]
theorem exists_intermediateField_eq_adjoin_uniformizerRoot_pow
    (hprime : PrimeToResidueCharacteristic A n)
    (S : IntermediateField (FractionRing A) (uniformizerRootExtension π n)) :
    ∃ d : ℕ, d ∣ n ∧ S = (FractionRing A)⟮root[π^(1/n)] ^ (n / d)⟯ := by
  sorry

end

end UniformizerRootExtensionIrreducibleContext
