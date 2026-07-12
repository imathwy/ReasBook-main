import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.CommonKernelQuotient
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.FrobeniusProductNormalization
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.MatrixCornerActions
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_2_6.ProductIdempotentDecomposition
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section

universe v w

open scoped TensorProduct

namespace Representation

section EquivalenceCriterion

variable {k : Type} [Field k]
variable {G : Type v} [Monoid G]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A]
variable {V W : Type w}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Exercise 18-18.2-6: scalar extension of a monoid representation is obtained by
base-changing each action endomorphism. -/
noncomputable def scalarExtensionMonoid
    {K : Type*} [Field K] [Algebra k K]
    {X : Type*} [AddCommGroup X] [Module k X]
    (ρ : Representation k G X) :
    Representation K G (K ⊗[k] X) :=
  MonoidHom.comp (Module.End.baseChangeHom k K X).toMonoidHom ρ

/-- Helper for Exercise 18-18.2-6: the algebra homomorphism of a scalar-extended monoid
representation is the base change of the original algebra homomorphism after mapping
coefficients in the monoid algebra. -/
lemma scalarExtensionMonoid_asAlgebraHom_mapRange
    {K : Type*} [Field K] [Algebra k K]
    {X : Type*} [AddCommGroup X] [Module k X]
    (ρ : Representation k G X) (t : MonoidAlgebra k G) :
    (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom
        ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) t) =
      LinearMap.baseChange K (ρ.asAlgebraHom t) := by
  -- Check the identity on monoid generators and extend it across the monoid algebra.
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra k G ↦
      (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom
          ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) t) =
        LinearMap.baseChange K (ρ.asAlgebraHom t))
    t ?_ ?_ ?_
  · intro g
    -- On generators both sides are the base-changed action endomorphism.
    simp [scalarExtensionMonoid, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]
  · intro a b ha hb
    -- Additivity is inherited from both algebra homomorphisms.
    simp [ha, hb]
  · intro r a ha
    -- Scalar multiplication is compatible with coefficient mapping and base change.
    calc
      (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom
          ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) (r • a)) =
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom
          (r • ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) a)) := by
          rw [map_smul]
      _ = r • (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom
          ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) a) := by
          exact AlgHom.map_smul_of_tower
            (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom r _
      _ = r • LinearMap.baseChange K (ρ.asAlgebraHom a) := by
          rw [ha]
      _ = LinearMap.baseChange K (ρ.asAlgebraHom (r • a)) := by
          rw [map_smul, LinearMap.baseChange_smul]

/-- Helper for Exercise 18-18.2-6: scalar extension sends the reversed characteristic
polynomial of the negated action endomorphism to the coefficientwise image of the original
polynomial. -/
lemma negCharpolyReverse_scalarExtensionMonoid_eq_map
    {K : Type*} [Field K] [Algebra k K]
    {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (ρ : Representation k G X) (g : G) :
    ((-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse :
        Polynomial K) =
      Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) := by
  -- Rewrite the scalar-extended action as the base change of the source action, then commute
  -- characteristic polynomials and polynomial reversal with coefficient mapping.
  have hneg :
      -(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g) =
        LinearMap.baseChange K (-ρ g) := by
    simp [scalarExtensionMonoid, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]
  rw [hneg, LinearMap.charpoly_baseChange]
  symm
  exact
    polynomial_reverse_map (f := algebraMap k K)
      (hf := FaithfulSMul.algebraMap_injective k K) ((-ρ g).charpoly)

/-- Helper for Exercise 18-18.2-6: generator determinant-polynomial equality survives scalar
extension of monoid representations. -/
lemma detOneAddPolynomialEq_scalarExtensionMonoid
    {K : Type*} [Field K] [Algebra k K]
    {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    ∀ g : G,
      (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse =
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse := by
  intro g
  -- Apply the base-change computation on both sides and map the source determinant equality.
  calc
    (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse =
        Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) := by
          exact negCharpolyReverse_scalarExtensionMonoid_eq_map (k := k) (G := G) (K := K) ρ g
    _ = Polynomial.map (algebraMap k K) (((-ρ' g).charpoly.reverse : Polynomial k)) := by
          rw [hdet g]
    _ = (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse := by
          exact
            (negCharpolyReverse_scalarExtensionMonoid_eq_map
              (k := k) (G := G) (K := K) ρ' g).symm

/-- Helper for Exercise 18-18.2-6: an equivariant linear equivalence remains equivariant after
scalar extension along a field extension. -/
lemma scalarExtensionMonoid_equiv_of_equiv
    {K : Type*} [Field K] [Algebra k K]
    {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (e : Representation.Equiv ρ ρ') :
    Nonempty ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).Equiv
      (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ')) := by
  let eK : K ⊗[k] X ≃ₗ[K] K ⊗[k] Y :=
    e.toLinearEquiv.baseChange k K X Y
  refine ⟨Representation.Equiv.mk eK ?_⟩
  intro g
  -- Check the intertwining identity on pure tensors, where scalar extension is explicit.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  have hgx := LinearMap.congr_fun (e.isIntertwining' g) x
  simpa [scalarExtensionMonoid] using congrArg (fun y ↦ a ⊗ₜ[k] y) hgx

/-- Helper for Exercise 18-18.2-6: an equivalence after scalar extension reflects equality of
the original generator determinant polynomials. -/
lemma detOneAddPolynomialEq_of_scalarExtensionMonoid_equiv
    {K : Type*} [Field K] [Algebra k K]
    {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hK :
      Nonempty ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).Equiv
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ'))) :
    ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse := by
  rcases hK with ⟨eK⟩
  intro g
  -- Conjugacy by the upstairs equivalence preserves the characteristic polynomial over `K`.
  have hcharK :
      (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly =
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly := by
    have hconj_pos :
        eK.toLinearEquiv.conj
            (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g) =
          scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g := by
      exact
        Representation.Equiv.conj_apply_self
          (ρ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
          (σ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ') g eK
    have hconj :
        eK.toLinearEquiv.conj
            (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)) =
          -(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g) := by
      -- Move negation through conjugation, then apply the positive intertwining identity.
      calc
        eK.toLinearEquiv.conj
            (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)) =
          -(eK.toLinearEquiv.conj
              (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)) := by
            exact
              map_neg (eK.toLinearEquiv.conj)
                (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)
        _ = -(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g) := by
              rw [hconj_pos]
    simpa [hconj] using
      (LinearEquiv.charpoly_conj eK.toLinearEquiv
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g))).symm
  have hmap :
      Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) =
        Polynomial.map (algebraMap k K) (((-ρ' g).charpoly.reverse : Polynomial k)) := by
    -- Rewrite the upstairs equality as equality of coefficientwise images of the downstairs
    -- determinant polynomials.
    calc
      Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) =
          (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse := by
            symm
            exact negCharpolyReverse_scalarExtensionMonoid_eq_map
              (k := k) (G := G) (K := K) ρ g
      _ = (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse := by
            exact congrArg Polynomial.reverse hcharK
      _ = Polynomial.map (algebraMap k K) (((-ρ' g).charpoly.reverse : Polynomial k)) := by
            exact negCharpolyReverse_scalarExtensionMonoid_eq_map
              (k := k) (G := G) (K := K) ρ' g
  -- The field extension coefficient map is injective, so the downstairs polynomials agree.
  exact
    (Polynomial.map_injective (algebraMap k K)
      (FaithfulSMul.algebraMap_injective k K)) hmap

/-- Helper for Exercise 18-18.2-6: generator determinant-polynomial equality is unchanged by
passing to any field extension. -/
lemma detOneAddPolynomialEq_scalarExtensionMonoid_iff
    {K : Type*} [Field K] [Algebra k K]
    {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y} :
    (∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) ↔
      ∀ g : G,
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse =
          (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse := by
  constructor
  · intro hdet
    -- Push the source determinant character through the coefficient-field map.
    exact
      detOneAddPolynomialEq_scalarExtensionMonoid
        (k := k) (G := G) (K := K) (ρ := ρ) (ρ' := ρ') hdet
  · intro hdetK g
    -- Pull the upstairs equality back through the injective coefficient map.
    have hmap :
        Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) =
          Polynomial.map (algebraMap k K) (((-ρ' g).charpoly.reverse : Polynomial k)) := by
      calc
        Polynomial.map (algebraMap k K) (((-ρ g).charpoly.reverse : Polynomial k)) =
            (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse := by
              symm
              exact
                negCharpolyReverse_scalarExtensionMonoid_eq_map
                  (k := k) (G := G) (K := K) ρ g
        _ = (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse := by
              exact hdetK g
        _ = Polynomial.map (algebraMap k K) (((-ρ' g).charpoly.reverse : Polynomial k)) := by
              exact
                negCharpolyReverse_scalarExtensionMonoid_eq_map
                  (k := k) (G := G) (K := K) ρ' g
    exact
      (Polynomial.map_injective (algebraMap k K)
        (FaithfulSMul.algebraMap_injective k K)) hmap

/-- Helper for Exercise 18-18.2-6: scalar extension transports the ordinary character by applying
the coefficient-field map pointwise. -/
lemma scalarExtensionMonoid_character_eq_map
    {K : Type*} [Field K] [Algebra k K]
    {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (ρ : Representation k G X) :
    (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).character =
      fun g ↦ algebraMap k K (ρ.character g) := by
  ext g
  -- Base change preserves traces, so the scalar-extended character is just the mapped source
  -- character.
  exact LinearMap.trace_baseChange (ρ g) K

/-- Helper for Exercise 18-18.2-6: equality of ordinary characters survives scalar extension to
any field extension. -/
lemma scalarExtensionMonoid_character_eq_of_character_eq
    {K : Type*} [Field K] [Algebra k K]
    {X Y : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hchar : ρ.character = ρ'.character) :
    (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).character =
      (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ').character := by
  -- Transport both characters to the extension field and then rewrite by the source equality.
  ext g
  rw [scalarExtensionMonoid_character_eq_map (k := k) (G := G) (K := K) ρ]
  rw [scalarExtensionMonoid_character_eq_map (k := k) (G := G) (K := K) ρ']
  exact congrArg (algebraMap k K) (congrFun hchar g)

/-- Helper for Exercise 18-18.2-6: a field is not of characteristic zero exactly when its
`ringChar` is nonzero. -/
lemma not_charZero_iff_ringChar_ne_zero :
    (¬ CharZero k) ↔ ringChar k ≠ 0 := by
  constructor
  · intro hnonCharZero hzero
    -- Convert a zero `ringChar` back to a `CharZero` instance, contradicting the hypothesis.
    exact hnonCharZero ((CharP.ringChar_zero_iff_CharZero (R := k)).mp hzero)
  · intro hringChar_ne_zero hcharZero
    -- In characteristic zero Mathlib computes the ring characteristic as `0`.
    exact hringChar_ne_zero (ringChar.eq_zero (R := k))

/-- Helper for Exercise 18-18.2-6: the positive characteristic forced by `¬ CharZero k` is
prime. -/
lemma ringChar_prime_of_not_charZero (hnonCharZero : ¬ CharZero k) :
    Nat.Prime (ringChar k) := by
  -- The previous helper supplies the nonzero characteristic required by Mathlib's prime
  -- characteristic theorem for nontrivial rings.
  exact
    CharP.char_prime_of_ne_zero (R := k) (p := ringChar k)
      ((not_charZero_iff_ringChar_ne_zero (k := k)).mp hnonCharZero)

/-- Helper for Exercise 18-18.2-6: powers of a polynomial with constant coefficient `1` still
have constant coefficient `1`. -/
lemma polynomial_coeff_zero_pow_eq_one_of_coeff_zero_eq_one
    (p : Polynomial k) (n : ℕ) (h0 : p.coeff 0 = 1) :
    (p ^ n).coeff 0 = 1 := by
  -- Induct on the exponent and multiply constant coefficients at the successor step.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, Polynomial.mul_coeff_zero, ih, h0]
      simp

/-- Helper for Exercise 18-18.2-6: the coefficient of `T` in a power of a
constant-term-one polynomial is the exponent times the original coefficient of `T`. -/
lemma polynomial_coeff_one_pow_eq_natCast_mul_coeff_one_of_coeff_zero_eq_one
    (p : Polynomial k) (n : ℕ) (h0 : p.coeff 0 = 1) :
    (p ^ n).coeff 1 = (n : k) * p.coeff 1 := by
  -- The successor step uses the two-term formula for the coefficient of `T` in a product.
  induction n with
  | zero =>
      simp [Polynomial.coeff_one]
  | succ n ih =>
      have hpow0 : (p ^ n).coeff 0 = 1 :=
        polynomial_coeff_zero_pow_eq_one_of_coeff_zero_eq_one (p := p) (n := n) h0
      rw [pow_succ, Polynomial.mul_coeff_one, ih]
      simp [h0, hpow0, Nat.cast_succ, add_mul]
      ring

/-- Helper for Exercise 18-18.2-6: a finite product of constant-term-one polynomials has
constant coefficient `1`. -/
lemma polynomial_coeff_zero_prod_eq_one_of_coeff_zero_eq_one
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    ((∏ i ∈ s, f i) : Polynomial k).coeff 0 = 1 := by
  classical
  -- Insert one factor at a time and keep only the constant coefficient of the product.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s has ih =>
      have h0a : (f a).coeff 0 = 1 := h0 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, (f i).coeff 0 = 1 :=
        fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      simp [Finset.prod_insert, has, Polynomial.mul_coeff_zero, h0a, ih h0s]

/-- Helper for Exercise 18-18.2-6: for a finite product of constant-term-one polynomials, the
coefficient of `T` is the sum of the individual coefficients of `T`. -/
lemma polynomial_coeff_one_prod_eq_sum_coeff_one_of_coeff_zero_eq_one
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    ((∏ i ∈ s, f i) : Polynomial k).coeff 1 =
      ∑ i ∈ s, (f i).coeff 1 := by
  classical
  -- The successor step uses `coeff (p*q) 1 = p₀*q₁ + p₁*q₀` and the product constant term.
  induction s using Finset.induction_on with
  | empty =>
      simp [Polynomial.coeff_one]
  | insert a s has ih =>
      have h0a : (f a).coeff 0 = 1 := h0 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, (f i).coeff 0 = 1 :=
        fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      have hprod0 : ((∏ i ∈ s, f i) : Polynomial k).coeff 0 = 1 :=
        polynomial_coeff_zero_prod_eq_one_of_coeff_zero_eq_one (s := s) (f := f) h0s
      rw [Finset.prod_insert has, Finset.sum_insert has, Polynomial.mul_coeff_one, ih h0s]
      simp [h0a, hprod0, add_comm]

/-- Helper for Exercise 18-18.2-6: for a finite product of powers of constant-term-one
polynomials, the coefficient of `T` is the weighted sum of the individual coefficients of `T`. -/
lemma polynomial_coeff_one_prod_pow_eq_sum_natCast_mul_coeff_one_of_coeff_zero_eq_one
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k) (m : ι → ℕ)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1) :
    ((∏ i ∈ s, f i ^ m i) : Polynomial k).coeff 1 =
      ∑ i ∈ s, (m i : k) * (f i).coeff 1 := by
  classical
  -- First reduce the product coefficient to a sum over factors, then apply the power formula
  -- factorwise.
  have h0pow : ∀ i ∈ s, ((f i) ^ m i : Polynomial k).coeff 0 = 1 := by
    intro i hi
    exact
      polynomial_coeff_zero_pow_eq_one_of_coeff_zero_eq_one
        (p := f i) (n := m i) (h0 i hi)
  have hprod :
      ((∏ i ∈ s, f i ^ m i) : Polynomial k).coeff 1 =
        ∑ i ∈ s, ((f i) ^ m i : Polynomial k).coeff 1 := by
    exact
      polynomial_coeff_one_prod_eq_sum_coeff_one_of_coeff_zero_eq_one
        (s := s) (f := fun i ↦ f i ^ m i) h0pow
  calc
    ((∏ i ∈ s, f i ^ m i) : Polynomial k).coeff 1 =
        ∑ i ∈ s, ((f i) ^ m i : Polynomial k).coeff 1 := hprod
    _ = ∑ i ∈ s, (m i : k) * (f i).coeff 1 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact
            polynomial_coeff_one_pow_eq_natCast_mul_coeff_one_of_coeff_zero_eq_one
              (p := f i) (n := m i) (h0 i hi)

/-- Helper for Exercise 18-18.2-6: equality of two products of powers of
constant-term-one polynomials gives the corresponding weighted relation among their
coefficients of `T`. -/
lemma polynomial_weighted_coeff_one_sum_eq_zero_of_prod_pow_eq
    {ι : Type*} (s : Finset ι) (f : ι → Polynomial k) (m n : ι → ℕ)
    (h0 : ∀ i ∈ s, (f i).coeff 0 = 1)
    (hprod : ((∏ i ∈ s, f i ^ m i) : Polynomial k) =
      ((∏ i ∈ s, f i ^ n i) : Polynomial k)) :
    ∑ i ∈ s, ((m i : k) - (n i : k)) * (f i).coeff 1 = 0 := by
  -- Read the first coefficient of the two equal products using the previously isolated
  -- product-of-powers formula.
  have hm :
      ((∏ i ∈ s, f i ^ m i) : Polynomial k).coeff 1 =
        ∑ i ∈ s, (m i : k) * (f i).coeff 1 :=
    polynomial_coeff_one_prod_pow_eq_sum_natCast_mul_coeff_one_of_coeff_zero_eq_one
      (s := s) (f := f) (m := m) h0
  have hn :
      ((∏ i ∈ s, f i ^ n i) : Polynomial k).coeff 1 =
        ∑ i ∈ s, (n i : k) * (f i).coeff 1 :=
    polynomial_coeff_one_prod_pow_eq_sum_natCast_mul_coeff_one_of_coeff_zero_eq_one
      (s := s) (f := f) (m := n) h0
  have hcoeff :
      ∑ i ∈ s, (m i : k) * (f i).coeff 1 =
        ∑ i ∈ s, (n i : k) * (f i).coeff 1 := by
    calc
      ∑ i ∈ s, (m i : k) * (f i).coeff 1 =
          ((∏ i ∈ s, f i ^ m i) : Polynomial k).coeff 1 := hm.symm
      _ = ((∏ i ∈ s, f i ^ n i) : Polynomial k).coeff 1 := by
            rw [hprod]
      _ = ∑ i ∈ s, (n i : k) * (f i).coeff 1 := hn
  -- Distribute the subtraction termwise and cancel the two equal coefficient sums.
  calc
    ∑ i ∈ s, ((m i : k) - (n i : k)) * (f i).coeff 1 =
        ∑ i ∈ s, ((m i : k) * (f i).coeff 1 -
          (n i : k) * (f i).coeff 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (∑ i ∈ s, (m i : k) * (f i).coeff 1) -
          ∑ i ∈ s, (n i : k) * (f i).coeff 1 := by
          simp [Finset.sum_sub_distrib]
    _ = 0 := by
          rw [hcoeff, sub_self]

/-- Helper for Exercise 18-18.2-6: equality of determinant-power products gives the exact
weighted trace relation on monoid generators. -/
lemma generatorTraceRelation_of_detProductEq
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k)) :
    ∀ g : G, ∑ i ∈ s, ((m i : k) - (n i : k)) * (ρ i).character g = 0 := by
  intro g
  -- Apply the coefficient-one product formula to the determinant factors at this generator.
  have h0 : ∀ i ∈ s,
      (((-(ρ i g)).charpoly.reverse : Polynomial k).coeff 0) = 1 := by
    intro i hi
    simp [Polynomial.coeff_zero_reverse, LinearMap.charpoly_monic]
  have hcoeff :=
    polynomial_weighted_coeff_one_sum_eq_zero_of_prod_pow_eq
      (s := s)
      (f := fun i ↦ (((-(ρ i g)).charpoly.reverse : Polynomial k)))
      (m := m) (n := n) h0 (hprod g)
  have hcoeff_one :
      ∀ i ∈ s,
        (((-(ρ i g)).charpoly.reverse : Polynomial k).coeff 1) =
          (ρ i).character g := by
    intro i hi
    -- The coefficient of `T` in `det(1 + ρ(g)T)` is the ordinary trace character.
    calc
      (((-(ρ i g)).charpoly.reverse : Polynomial k).coeff 1) =
          LinearMap.trace k (⋀[k]^1 (E i)) (exteriorPower.map 1 (ρ i g)) := by
            exact (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ i g) 1).symm
      _ = (ρ i).character g := by
            simp [Representation.character, trace_exteriorPower_map_one]
  -- Rewrite the coefficient relation through the trace-character bridge.
  calc
    ∑ i ∈ s, ((m i : k) - (n i : k)) * (ρ i).character g =
        ∑ i ∈ s, ((m i : k) - (n i : k)) *
          (((-(ρ i g)).charpoly.reverse : Polynomial k).coeff 1) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hcoeff_one i hi]
    _ = 0 := hcoeff

/-- Helper for Exercise 18-18.2-6: after Frobenius normalization has made one
multiplicity difference nonzero in `k`, equality of determinant products gives a nonzero
linear relation among the generator characters. -/
lemma exists_nonzero_generatorTraceRelation_of_detProductEq_of_nonzero_weight
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hnonzero : ∃ i ∈ s, ((m i : k) - (n i : k)) ≠ 0) :
    ∃ c : ι → k, (∃ i ∈ s, c i ≠ 0) ∧
      ∀ g : G, ∑ i ∈ s, c i * (ρ i).character g = 0 := by
  refine ⟨fun i ↦ (m i : k) - (n i : k), hnonzero, ?_⟩
  -- The exact weighted relation above supplies the required nonzero generator relation.
  exact generatorTraceRelation_of_detProductEq (s := s) (ρ := ρ) (m := m) (n := n) hprod

/-- Helper for Exercise 18-18.2-6: a finite trace relation verified on monoid generators extends
linearly to the whole monoid algebra. -/
lemma traceRelation_eq_zero_asAlgebraHom_of_generator_eq_zero
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (c : ι → k)
    (hgen : ∀ g : G, ∑ i ∈ s, c i * (ρ i).character g = 0) :
    ∀ t : MonoidAlgebra k G,
      ∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 0 := by
  intro t
  -- The monoid algebra is generated by the monoid basis; additivity and scalar linearity carry
  -- the generator relation to every element.
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra k G ↦
      ∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 0)
    t ?_ ?_ ?_
  · intro g
    simpa [Representation.character, Representation.asAlgebraHom_of] using hgen g
  · intro a b ha hb
    calc
      ∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom (a + b)) =
          ∑ i ∈ s, (c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom a) +
            c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom b)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_add]
      _ = (∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom a)) +
            ∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom b) := by
          rw [Finset.sum_add_distrib]
      _ = 0 := by
          rw [ha, hb, add_zero]
  · intro r a ha
    calc
      ∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom (r • a)) =
          r * (∑ i ∈ s, c i * LinearMap.trace k (E i) ((ρ i).asAlgebraHom a)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [mul_left_comm]
      _ = 0 := by
          rw [ha, mul_zero]

/-- Helper for Exercise 18-18.2-6: equality of determinant-power products gives the exact
weighted trace relation on the whole monoid algebra. -/
lemma traceRelation_asAlgebraHom_of_detProductEq
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k)) :
    ∀ t : MonoidAlgebra k G,
      ∑ i ∈ s, ((m i : k) - (n i : k)) *
        LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 0 := by
  -- First prove the generator relation, then extend it linearly across `k[G]`.
  exact
    traceRelation_eq_zero_asAlgebraHom_of_generator_eq_zero
      (s := s) (ρ := ρ) (c := fun i ↦ (m i : k) - (n i : k))
      (generatorTraceRelation_of_detProductEq (s := s) (ρ := ρ) (m := m) (n := n) hprod)

/-- Helper for Exercise 18-18.2-6: a nonzero coefficient in a trace relation contradicts a
separator whose trace is `1` on that constituent and `0` on the rest of the finite support. -/
lemma traceRelation_contradicts_separator
    {ι : Type*} (s : Finset ι) (c : ι → k)
    (trace : ι → MonoidAlgebra k G → k)
    (hrel : ∀ t : MonoidAlgebra k G, ∑ i ∈ s, c i * trace i t = 0)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hc₀ : c i₀ ≠ 0)
    (t : MonoidAlgebra k G)
    (hself : trace i₀ t = 1)
    (hother : ∀ j ∈ s, j ≠ i₀ → trace j t = 0) :
    False := by
  classical
  -- Evaluate the relation at the separator; all terms but the selected coefficient vanish.
  have hsum : ∑ i ∈ s, c i * trace i t = c i₀ := by
    rw [Finset.sum_eq_single_of_mem i₀ hi₀]
    · simp [hself]
    · intro j hj hji
      simp [hother j hj hji]
  have hzero := hrel t
  -- The relation says the selected coefficient is zero, contradicting its normalization.
  exact hc₀ (by rw [← hsum, hzero])

/-- Helper for Exercise 18-18.2-6: a nonzero generator-level trace relation is incompatible
with a monoid-algebra separator for the selected constituent. -/
lemma generatorTraceRelation_contradicts_separator
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (c : ι → k)
    (hgen : ∀ g : G, ∑ i ∈ s, c i * (ρ i).character g = 0)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hc₀ : c i₀ ≠ 0)
    (t : MonoidAlgebra k G)
    (hself : LinearMap.trace k (E i₀) ((ρ i₀).asAlgebraHom t) = 1)
    (hother : ∀ j ∈ s, j ≠ i₀ →
      LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    False := by
  -- First extend the relation from monoid generators to every element of the monoid algebra.
  have hrel :=
    traceRelation_eq_zero_asAlgebraHom_of_generator_eq_zero
      (s := s) (ρ := ρ) (c := c) hgen
  -- The separator then collapses the extended relation to the selected nonzero coefficient.
  exact
    traceRelation_contradicts_separator
      (s := s) (c := c)
      (trace := fun i t ↦ LinearMap.trace k (E i) ((ρ i).asAlgebraHom t))
      hrel hi₀ hc₀ t hself hother

/-- Helper for Exercise 18-18.2-6: a nonzero finite generator trace relation is impossible once
every supported constituent has a monoid-algebra trace separator. -/
lemma nonzeroGeneratorTraceRelation_contradicts_separator_exists
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i))
    (hrel : ∃ c : ι → k, (∃ i ∈ s, c i ≠ 0) ∧
      ∀ g : G, ∑ i ∈ s, c i * (ρ i).character g = 0)
    (hsep : ∀ i, i ∈ s → ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j ∈ s, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    False := by
  rcases hrel with ⟨c, ⟨i₀, hi₀, hc₀⟩, hgen⟩
  rcases hsep i₀ hi₀ with ⟨t, hself, hother⟩
  -- Choose a nonzero coefficient in the relation, then evaluate the extended relation at the
  -- separator for that same constituent.
  exact
    generatorTraceRelation_contradicts_separator
      (s := s) (ρ := ρ) (c := c) hgen hi₀ hc₀ t hself hother

/-- Helper for Exercise 18-18.2-6: a determinant-product relation with a selected nonzero
weight is impossible once a monoid-algebra separator exists for that selected constituent. -/
lemma detProductEq_contradicts_trace_separator_of_nonzero_weight
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hweight₀ : ((m i₀ : k) - (n i₀ : k)) ≠ 0)
    (t : MonoidAlgebra k G)
    (hself :
      LinearMap.trace k (E i₀) ((ρ i₀).asAlgebraHom t) = 1)
    (hother : ∀ j ∈ s, j ≠ i₀ →
      LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    False := by
  -- The product identity first supplies the generator-level relation needed by the separator
  -- contradiction helper.
  have hgen :=
    generatorTraceRelation_of_detProductEq (s := s) (ρ := ρ) (m := m) (n := n) hprod
  exact
    generatorTraceRelation_contradicts_separator
      (s := s) (c := fun i ↦ (m i : k) - (n i : k))
      (ρ := ρ) hgen hi₀ hweight₀ t hself hother

/-- Helper for Exercise 18-18.2-6: a determinant-product equality with some nonzero normalized
weight is incompatible with separators for all supported constituents. -/
lemma detProductEq_contradicts_separator_exists_of_nonzero_weight
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hnonzero : ∃ i ∈ s, ((m i : k) - (n i : k)) ≠ 0)
    (hsep : ∀ i, i ∈ s → ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j ∈ s, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    False := by
  have hrel :
      ∃ c : ι → k, (∃ i ∈ s, c i ≠ 0) ∧
        ∀ g : G, ∑ i ∈ s, c i * (ρ i).character g = 0 :=
    exists_nonzero_generatorTraceRelation_of_detProductEq_of_nonzero_weight
      (s := s) (ρ := ρ) (m := m) (n := n) hprod hnonzero
  -- The determinant identity supplies a nonzero generator relation; the separator package
  -- collapses that relation to a contradiction.
  exact
    nonzeroGeneratorTraceRelation_contradicts_separator_exists
      (s := s) (ρ := ρ) hrel hsep

/-- Helper for Exercise 18-18.2-6: the determinant factor for a negated representation action has
constant coefficient one after reversing the characteristic polynomial. -/
lemma negCharpolyReverse_coeff_zero_eq_one
    {E : Type*} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (ρ : Representation k G E) (g : G) :
    (((-(ρ g)).charpoly.reverse : Polynomial k).coeff 0) = 1 := by
  -- This is the constant coefficient of `det (1 + ρ(g)T)`, equivalently the leading
  -- coefficient of the monic characteristic polynomial.
  simp [Polynomial.coeff_zero_reverse, LinearMap.charpoly_monic]

/-- Helper for Exercise 18-18.2-6: in prime characteristic, determinant-product equality plus
trace separators forces equality of all supported multiplicities. -/
lemma detProductEq_multiplicity_eq_of_separator_primeChar
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hsep : ∀ i, i ∈ s → ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j ∈ s, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    ∀ i, i ∈ s → m i = n i := by
  intro i hi
  by_contra hneq
  have hdiff : ∃ i ∈ s, m i ≠ n i := ⟨i, hi, hneq⟩
  have h0 : ∀ i ∈ s, ∀ g : G,
      (((-(ρ i g)).charpoly.reverse : Polynomial k).coeff 0) = 1 := by
    intro i hi g
    exact negCharpolyReverse_coeff_zero_eq_one (ρ i) g
  obtain ⟨m', n', hprod', _hdiff', hnonzero⟩ :=
    exists_normalized_nonzeroWeight_of_prodPowEq_primeChar
      (s := s)
      (f := fun i g ↦ (((-(ρ i g)).charpoly.reverse : Polynomial k)))
      (m := m) (n := n) h0 hprod hdiff
  -- The normalized equality has a nonzero field-valued weight, which the separator package
  -- forbids by the determinant-product contradiction lemma.
  exact
    (detProductEq_contradicts_separator_exists_of_nonzero_weight
      (s := s) (ρ := ρ) (m := m') (n := n') hprod' hnonzero hsep).elim

/-- Helper for Exercise 18-18.2-6: the prime-characteristic determinant-product separator
criterion in the common finite-family normal form with support `Finset.univ`. -/
lemma detProductEq_multiplicity_eq_of_separator_primeChar_univ
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) : Polynomial k) =
        ((∏ i, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hsep : ∀ i, ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    ∀ i, m i = n i := by
  classical
  have hprod_univ : ∀ g : G,
      ((∏ i ∈ (Finset.univ : Finset ι),
          (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) : Polynomial k) =
        ((∏ i ∈ (Finset.univ : Finset ι),
          (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) : Polynomial k) := by
    intro g
    -- Repackage the product over all finite-family constituents as a supported product.
    simpa using hprod g
  have hsep_univ : ∀ i, i ∈ (Finset.univ : Finset ι) →
      ∃ t : MonoidAlgebra k G,
        LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
          ∀ j ∈ (Finset.univ : Finset ι), j ≠ i →
            LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0 := by
    intro i _hi
    rcases hsep i with ⟨t, hself, hother⟩
    -- The separator hypotheses already hold for every constituent, so membership in `univ`
    -- carries no additional information.
    exact ⟨t, hself, fun j _hj hji ↦ hother j hji⟩
  intro i
  exact
    detProductEq_multiplicity_eq_of_separator_primeChar
      (k := k) (G := G) (p := p) (s := Finset.univ) (ρ := ρ)
      (m := m) (n := n) hprod_univ hsep_univ i (Finset.mem_univ i)

/-- Helper for Exercise 18-18.2-6: a determinant-product equality remains valid after enlarging
the support by constituents whose two multiplicities are both zero. -/
lemma detProductEq_extend_support_of_zero_multiplicity
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s t : Finset ι) (hst : s ⊆ t)
    (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hm : ∀ i, i ∈ t → i ∉ s → m i = 0)
    (hn : ∀ i, i ∈ t → i ∉ s → n i = 0)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k)) :
    ∀ g : G,
      ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k) := by
  intro g
  have hmprod :
      ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) := by
    -- Drop the newly-added factors on the left product; their exponents are zero.
    symm
    exact Finset.prod_subset hst fun i hit his ↦ by
      rw [hm i hit his]
      simp
  have hnprod :
      ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k) := by
    -- The same support normalization applies to the right product.
    symm
    exact Finset.prod_subset hst fun i hit his ↦ by
      rw [hn i hit his]
      simp
  -- Normalize both enlarged products back to the original support and apply the hypothesis.
  calc
    ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
        Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) := hmprod
    _ = ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k) := hprod g
    _ = ((∏ i ∈ t, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k) := hnprod.symm

/-- Helper for Exercise 18-18.2-6: the finite-family multiplicity separator criterion can be
used directly from a `¬ CharZero k` hypothesis by choosing `ringChar k` as the prime
characteristic. -/
lemma detProductEq_multiplicity_eq_of_separator_not_charZero
    (hnonCharZero : ¬ CharZero k)
    {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (s : Finset ι) (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) :
          Polynomial k) =
        ((∏ i ∈ s, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hsep : ∀ i, i ∈ s → ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j ∈ s, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    ∀ i, i ∈ s → m i = n i := by
  -- Put the positive-characteristic branch in the normal form expected by the Frobenius
  -- normalization helper.
  let p := ringChar k
  letI : CharP k p := ringChar.charP (R := k)
  letI : Fact p.Prime := ⟨by
    simpa [p] using ringChar_prime_of_not_charZero (k := k) hnonCharZero⟩
  -- With the characteristic instances available, the proved prime-characteristic separator
  -- theorem applies without further transport.
  exact
    detProductEq_multiplicity_eq_of_separator_primeChar
      (k := k) (G := G) (p := p) (s := s) (ρ := ρ) (m := m) (n := n) hprod hsep

/-- Helper for Exercise 18-18.2-6: the non-characteristic-zero determinant-product separator
criterion in the common finite-family normal form with support `Finset.univ`. -/
lemma detProductEq_multiplicity_eq_of_separator_not_charZero_univ
    (hnonCharZero : ¬ CharZero k)
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, FiniteDimensional k (E i)]
    (ρ : ∀ i, Representation k G (E i)) (m n : ι → ℕ)
    (hprod : ∀ g : G,
      ((∏ i, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) : Polynomial k) =
        ((∏ i, (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) :
          Polynomial k))
    (hsep : ∀ i, ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
        ∀ j, j ≠ i →
          LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0) :
    ∀ i, m i = n i := by
  classical
  have hprod_univ : ∀ g : G,
      ((∏ i ∈ (Finset.univ : Finset ι),
          (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ m i) : Polynomial k) =
        ((∏ i ∈ (Finset.univ : Finset ι),
          (((-(ρ i g)).charpoly.reverse : Polynomial k)) ^ n i) : Polynomial k) := by
    intro g
    -- Repackage the all-constituent determinant product with the supported-product API.
    simpa using hprod g
  have hsep_univ : ∀ i, i ∈ (Finset.univ : Finset ι) →
      ∃ t : MonoidAlgebra k G,
        LinearMap.trace k (E i) ((ρ i).asAlgebraHom t) = 1 ∧
          ∀ j ∈ (Finset.univ : Finset ι), j ≠ i →
            LinearMap.trace k (E j) ((ρ j).asAlgebraHom t) = 0 := by
    intro i _hi
    rcases hsep i with ⟨t, hself, hother⟩
    -- The separator is global on the finite family, so restricting it to `univ` is immediate.
    exact ⟨t, hself, fun j _hj hji ↦ hother j hji⟩
  intro i
  exact
    detProductEq_multiplicity_eq_of_separator_not_charZero
      (k := k) (G := G) hnonCharZero (s := Finset.univ) (ρ := ρ)
      (m := m) (n := n) hprod_univ hsep_univ i (Finset.mem_univ i)

/-- Helper for Exercise 18-18.2-6: the exterior-trace invariant on `k[G]` already yields ordinary
trace equality on the lifted common image algebra. -/
lemma trace_eq_of_hexteriorTrace_one_on_lift
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ a : MonoidAlgebra k G, LinearMap.trace k V (φV (liftι a)) =
      LinearMap.trace k W (φW (liftι a)) := by
  intro a
  -- The source proof uses only the `n = 1` exterior trace, which recovers the ordinary trace.
  have hchar : ρ.character = ρ'.character := by
    ext g
    have h1 := hexteriorTrace 1 (MonoidAlgebra.of k G g)
    simpa [Representation.character, Representation.nthExteriorPower,
      Representation.asAlgebraHom_of, trace_exteriorPower_map_one] using h1
  have htrace :=
    trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar a
  -- Re-express the descended action through the compatibility with the quotient lift.
  have hVa : φV (liftι a) = ρ.asAlgebraHom a := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f a) hφV
  have hWa : φW (liftι a) = ρ'.asAlgebraHom a := by
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f a) hφW
  simpa [hVa, hWa] using htrace

/-- Helper for Exercise 18-18.2-6: equality of the ambient `k`-dimensions of finite-dimensional
`D`-modules forces equality of their `D`-dimensions. -/
lemma finrank_over_divisionRing_eq_of_baseField_finrank_eq
    {D : Type*} [DivisionRing D] [Algebra k D] [Module.Finite k D]
    {X Y : Type*} [AddCommGroup X] [Module D X] [FiniteDimensional D X]
    [Module k X] [IsScalarTower k D X]
    [AddCommGroup Y] [Module D Y] [FiniteDimensional D Y]
    [Module k Y] [IsScalarTower k D Y]
    (h : Module.finrank k X = Module.finrank k Y) :
    Module.finrank D X = Module.finrank D Y := by
  have hX := Module.finrank_mul_finrank k D X
  have hY := Module.finrank_mul_finrank k D Y
  rw [h, ← hY] at hX
  -- Cancel the positive scalar-extension factor `finrank k D`.
  have hDpos : 0 < Module.finrank k D := by
    simpa using (Module.finrank_pos (R := k) (M := D))
  exact Nat.eq_of_mul_eq_mul_left hDpos hX

/-- Helper for Exercise 18-18.2-6: on the `i`-th coordinate summand of a split Wedderburn
product, the negative primitive corner projector has reverse characteristic polynomial
`(X + 1)^m`, where `m` is the base-field dimension of the corresponding Morita corner. -/
lemma splitProduct_coordinateProjector_reverseCharpoly_eq_pow_one_add
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    (i : Fin n) :
    let Xi :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (D i) Xi :=
      Module.compHom Xi
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
    let _ : IsScalarTower k (D i) Xi :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := Xi)
    let _ : Module.Finite k Xi := Module.Finite.of_injective
      (Xi.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k Xi := FiniteDimensional.of_injective
      (Xi.subtype.restrictScalars k) Subtype.val_injective
    let X0 := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
    (-DistribSMul.toLinearMap k Xi
      (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse =
      (Polynomial.X + 1) ^ Module.finrank k (Submodule.restrictScalars k X0) := by
  intro Xi _ _ _ MM _ _ _ _ X0
  -- Reduce the product algebra to the chosen matrix factor, where the primitive-corner
  -- characteristic-polynomial computation is already available.
  simpa [Xi, MM, X0] using
    neg_charpoly_reverse_matrix_corner_action_eq_pow_one_add
      (k := k) (D := D i) (m := d i) (M := Xi) (j := (0 : Fin (d i)))

/-- Helper for Exercise 18-18.2-6: the polynomial `(X + 1)^m` remembers its exponent. -/
lemma exponent_eq_of_pow_X_add_one_eq
    {m n : ℕ}
    (h : ((Polynomial.X + 1 : Polynomial k) ^ m) = (Polynomial.X + 1) ^ n) :
    m = n := by
  -- Compare nat-degrees; the monic linear factor `X + 1` has nat-degree `1`.
  have hdeg := congrArg Polynomial.natDegree h
  simpa [show (Polynomial.X + (1 : Polynomial k)) = Polynomial.X + Polynomial.C (1 : k) by simp]
    using hdeg

/-- Helper for Exercise 18-18.2-6: the reverse characteristic polynomial of the negative of an
idempotent linear projector records the dimension of its range as `(X + 1)^rank`. -/
lemma neg_charpoly_reverse_idempotent_eq_pow_one_add_range
    {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (f : M →ₗ[k] M) (hf : f.comp f = f) :
    (-f).charpoly.reverse = (Polynomial.X + 1) ^ Module.finrank k f.range := by
  let R : Submodule k M := f.range
  have hstable : R ≤ R.comap (-f) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (-f) (f y) ∈ R
    refine ⟨-f y, ?_⟩
    simp
  have hrestrict : (-f).restrict hstable = -LinearMap.id := by
    -- On the range of an idempotent projector, `f` is the identity, so `-f` is `-id`.
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.neg_apply, LinearMap.id_coe, id_eq]
    rcases x.property with ⟨y, hy⟩
    have hx : f (x : M) = x := by
      rw [← hy]
      exact congrArg (fun g : M →ₗ[k] M ↦ g y) hf
    simp [hx]
  have hmapQ : R.mapQ R (-f) hstable = 0 := by
    -- The quotient by the range kills `-f`, because every value of `-f` still lies in the range.
    apply R.quot_hom_ext
    intro y
    rw [Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero (p := R) (x := (-f) y)).2 ⟨-y, by simp⟩
  have hchar :
      (-f).charpoly =
        ((Polynomial.X + 1) ^ Module.finrank k R) * Polynomial.X ^ Module.finrank k (M ⧸ R) := by
    -- Split along the invariant range and the zero induced map on the quotient.
    rw [charpoly_eq_charpoly_restrict_mul_charpoly_mapQ (f := -f) (W := R) (hW := hstable),
      hrestrict, hmapQ,
      LinearMap.charpoly_zero]
    have hone := LinearMap.charpoly_sub_smul (0 : R →ₗ[k] R) (1 : k)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hone
  have hreverse_pow :
      (((Polynomial.X : Polynomial k) + 1) ^ Module.finrank k R).reverse =
        (Polynomial.X + 1) ^ Module.finrank k R := by
    -- The linear factor `X + 1` is fixed by reversal, hence so are all of its powers.
    have hX1 : Polynomial.reverse ((Polynomial.X : Polynomial k) + 1) = Polynomial.X + 1 := by
      rw [show ((Polynomial.X : Polynomial k) + 1) = Polynomial.C (1 : k) + Polynomial.X by
        simp [add_comm]]
      rw [Polynomial.reverse_C_add]
      simp [Polynomial.reverse, add_comm]
    induction Module.finrank k R with
    | zero =>
        simp [Polynomial.reverse]
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, hX1]
  have hreverse_X_pow :
      (Polynomial.X ^ Module.finrank k (M ⧸ R) : Polynomial k).reverse = 1 := by
    -- Reversal removes the pure trailing `X`-power from the quotient-zero part.
    induction Module.finrank k (M ⧸ R) with
    | zero =>
        simp [Polynomial.reverse]
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_X, ih]
  -- Reverse the split characteristic polynomial; the quotient factor contributes only `1`.
  rw [hchar, Polynomial.reverse_mul_of_domain, hreverse_pow, hreverse_X_pow]
  simpa [R]

/-- Helper for Exercise 18-18.2-6: equality of the primitive projector reverse characteristic
polynomials on two coordinate factors gives equality of their base-field Morita-corner
dimensions. -/
lemma cornerBaseFieldFinrank_eq_of_projector_reverseCharpoly_eq
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (i : Fin n)
    (hprojector :
      let XiM :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let XiN :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (D i) XiM :=
        Module.compHom XiM
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : Module (D i) XiN :=
        Module.compHom XiN
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
      let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
      let _ : IsScalarTower k (D i) XiM :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
      let _ : IsScalarTower k (D i) XiN :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
      let _ : Module.Finite k XiM := Module.Finite.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : Module.Finite k XiN := Module.Finite.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let X0M := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
      let X0N := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
      (-DistribSMul.toLinearMap k XiM
        (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse =
        (-DistribSMul.toLinearMap k XiN
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse) :
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
    let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
    let _ : IsScalarTower k (D i) XiM :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
    let _ : IsScalarTower k (D i) XiN :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
    let _ : Module.Finite k XiM := Module.Finite.of_injective
      (XiM.subtype.restrictScalars k) Subtype.val_injective
    let _ : Module.Finite k XiN := Module.Finite.of_injective
      (XiN.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
      (XiM.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
      (XiN.subtype.restrictScalars k) Subtype.val_injective
    let X0M := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
    let X0N := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
    Module.finrank k (Submodule.restrictScalars k X0M) =
      Module.finrank k (Submodule.restrictScalars k X0N) := by
  intro XiM XiN _ _ _ _ _ _ MM NN _ _ _ _ _ _ _ _ X0M X0N
  have hpolyM :=
    splitProduct_coordinateProjector_reverseCharpoly_eq_pow_one_add
      (k := k) (D := D) (d := d) (M := M) i
  have hpolyN :=
    splitProduct_coordinateProjector_reverseCharpoly_eq_pow_one_add
      (k := k) (D := D) (d := d) (M := N) i
  -- Rewrite both projector characteristic polynomials as powers of `X + 1`, then compare
  -- exponents to recover the base-field corner dimensions.
  have hpow :
      (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k (Submodule.restrictScalars k X0M) =
        (Polynomial.X + 1) ^ Module.finrank k (Submodule.restrictScalars k X0N) := by
    calc
      (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k (Submodule.restrictScalars k X0M)
          =
        (-DistribSMul.toLinearMap k XiM
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse := by
            symm
            simpa [XiM, MM, X0M] using hpolyM
      _ =
        (-DistribSMul.toLinearMap k XiN
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse := by
            simpa [XiM, XiN, MM, NN, X0M, X0N] using hprojector
      _ = (Polynomial.X + 1 : Polynomial k) ^
          Module.finrank k (Submodule.restrictScalars k X0N) := by
            simpa [XiN, NN, X0N] using hpolyN
  exact exponent_eq_of_pow_X_add_one_eq (k := k) hpow

/-- Helper for Exercise 18-18.2-6: base-field equality of the primitive Morita-corner
dimensions in a split Wedderburn factor cancels the common finite division-ring dimension and
therefore gives equality of the actual `D i`-multiplicities. -/
lemma cornerFinrank_eq_of_cornerBaseFieldFinrank_eq
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (i : Fin n)
    (hbase :
      let XiM :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let XiN :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (D i) XiM :=
        Module.compHom XiM
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : Module (D i) XiN :=
        Module.compHom XiN
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
      let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
      let _ : IsScalarTower k (D i) XiM :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
      let _ : IsScalarTower k (D i) XiN :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
      let _ : Module.Finite k XiM := Module.Finite.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : Module.Finite k XiN := Module.Finite.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let X0M := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
      let X0N := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
      Module.finrank k (Submodule.restrictScalars k X0M) =
        Module.finrank k (Submodule.restrictScalars k X0N)) :
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
      Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
  intro XiM XiN _ _ _ _ _ _ _ _
  let _ : IsScalarTower k (D i) XiM :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
  let _ : IsScalarTower k (D i) XiN :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
  let _ : Module.Finite k XiM := Module.Finite.of_injective
    (XiM.subtype.restrictScalars k) Subtype.val_injective
  let _ : Module.Finite k XiN := Module.Finite.of_injective
    (XiN.subtype.restrictScalars k) Subtype.val_injective
  let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
    (XiM.subtype.restrictScalars k) Subtype.val_injective
  let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
    (XiN.subtype.restrictScalars k) Subtype.val_injective
  let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
    finiteDimensional_toModuleCatObj_of_matrix_module
      (k := k) (D := D i) (m := d i) (M := XiM) (j := 0)
  let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
    finiteDimensional_toModuleCatObj_of_matrix_module
      (k := k) (D := D i) (m := d i) (M := XiN) (j := 0)
  -- Convert the base-field equality into a division-ring finrank equality by canceling the
  -- finite nonzero scalar-extension factor `Module.finrank k (D i)`.
  exact
    finrank_over_divisionRing_eq_of_baseField_finrank_eq
      (k := k) (D := D i)
      (X := MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
      (Y := MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
      (by simpa [XiM, XiN] using hbase)

/-- Helper for Exercise 18-18.2-6: evaluating the ambient trace equality on the primitive
projector in the `i`-th Wedderburn factor identifies the corresponding Morita corner dimensions
after coercion to the base field `k`. -/
lemma corner_baseField_finrank_eq_of_wedderburn_primitive_projector
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (htrace : ∀ b : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i),
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
        LinearMap.trace k N (DistribSMul.toLinearMap k N b))
    (i : Fin n) :
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : IsScalarTower k (D i) XiM :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
    let _ : IsScalarTower k (D i) XiN :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
    (Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) : k) =
      Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
  let XiM :=
    pi_coordinate_submodule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let XiN :=
    pi_coordinate_submodule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    pi_coordinate_submodule_factorModule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    pi_coordinate_submodule_factorModule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : Module (D i) XiM :=
    Module.compHom XiM
      (Matrix.scalarAlgHom (Fin (d i)) k :
        D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
  let _ : Module (D i) XiN :=
    Module.compHom XiN
      (Matrix.scalarAlgHom (Fin (d i)) k :
        D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
  let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
      (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
  let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
      (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
  let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
    pi_coordinate_submodule_factor_isScalarTower
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
  let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
    pi_coordinate_submodule_factor_isScalarTower
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
  let _ : IsScalarTower k (D i) XiM :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
  let _ : IsScalarTower k (D i) XiN :=
    isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
  let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
    ((pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i).subtype
      |>.restrictScalars k)
    Subtype.val_injective
  let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
    ((pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i).subtype
      |>.restrictScalars k)
    Subtype.val_injective
  let b : Π j, Matrix (Fin (d j)) (Fin (d j)) (D j) :=
    Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
  have hM :
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
        Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) := by
    -- First isolate the `i`-th product factor, then read the primitive corner trace as the
    -- dimension of the corresponding Morita coefficient module.
    calc
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
          LinearMap.trace k XiM
            (DistribSMul.toLinearMap k XiM
              (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))) := by
            simpa [XiM, b] using
              trace_pi_single_action_eq_trace_coordinate_action
                (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
                (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
      _ = Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) := by
            simpa [XiM] using
              trace_matrix_corner_action_eq_finrank_toModuleCatObj
                (k := k) (D := D i) (m := d i) (M := XiM) (j := (0 : Fin (d i)))
  have hN :
      LinearMap.trace k N (DistribSMul.toLinearMap k N b) =
        Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
    -- The same primitive projector computation holds on the second module.
    calc
      LinearMap.trace k N (DistribSMul.toLinearMap k N b) =
          LinearMap.trace k XiN
            (DistribSMul.toLinearMap k XiN
              (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))) := by
            simpa [XiN, b] using
              trace_pi_single_action_eq_trace_coordinate_action
                (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
                (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))
      _ = Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
            simpa [XiN] using
              trace_matrix_corner_action_eq_finrank_toModuleCatObj
                (k := k) (D := D i) (m := d i) (M := XiN) (j := (0 : Fin (d i)))
  -- Specializing the ambient trace equality at the primitive projector gives the corner
  -- multiplicity equality over the base field.
  simpa [XiM, XiN] using hM.symm.trans ((htrace b).trans hN)

/-- Helper for Exercise 18-18.2-6: the ambient primitive product projector has reverse
characteristic polynomial `(X + 1)^m`, where `m` is the base-field dimension of the corresponding
Morita corner. -/
lemma splitProduct_ambientCoordinateProjector_reverseCharpoly_eq_pow_one_add
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    (i : Fin n) :
    let Xi :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (D i) Xi :=
      Module.compHom Xi
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) Xi :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
    let _ : IsScalarTower k (D i) Xi :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := Xi)
    let _ : Module.Finite k Xi := Module.Finite.of_injective
      (Xi.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k Xi := FiniteDimensional.of_injective
      (Xi.subtype.restrictScalars k) Subtype.val_injective
    let X0 := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
    (-DistribSMul.toLinearMap k M
      (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
        Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
      (Polynomial.X + 1) ^ Module.finrank k (Submodule.restrictScalars k X0) := by
  intro Xi _ _ _ MM _ _ _ _ X0
  let e : Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)
  let b : Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j) := Pi.single i e
  let fK : M →ₗ[k] M := DistribSMul.toLinearMap k M b
  have hidem : fK.comp fK = fK := by
    -- The primitive matrix unit is idempotent, so the associated product action is a projector.
    ext x
    change b • (b • x) = b • x
    rw [← mul_smul]
    congr 1
    ext j
    by_cases hji : j = i
    · subst hji
      simp [b, e]
    · simp [b, Pi.single_eq_of_ne hji]
  have hrange :
      LinearMap.range fK =
        (Submodule.restrictScalars k X0).map (Xi.subtype.restrictScalars k) := by
    -- The range of the ambient product projector is exactly the image in `M` of the Morita
    -- corner inside the `i`-th coordinate summand.
    ext x
    constructor
    · rintro ⟨y, hy⟩
      let yXi : Xi := ⟨
        (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j)) • y,
        pi_coordinate_projection_mem
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i y⟩
      let zXi : Xi := e • yXi
      have hzX0 : zXi ∈ X0 := by
        exact ⟨yXi, rfl⟩
      refine ⟨zXi, hzX0, ?_⟩
      rw [← hy]
      change (zXi : M) = b • y
      calc
        (zXi : M) = (Pi.single i e : Π j, Matrix (Fin (d j)) (Fin (d j)) (D j)) •
            ((Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) • y) := by
              rfl
        _ = (((Pi.single i e : Π j, Matrix (Fin (d j)) (Fin (d j)) (D j)) *
              Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) • y : M) := by
              rw [← mul_smul]
        _ = b • y := by
              congr 1
              ext j
              by_cases hji : j = i
              · subst hji
                simp [b, e]
              · simp [b, Pi.single_eq_of_ne hji]
    · rintro ⟨zXi, hzX0, hz⟩
      rcases hzX0 with ⟨yXi, hyXi⟩
      refine ⟨(yXi : M), ?_⟩
      rw [← hz, ← hyXi]
      rfl
  have hpoly :=
    neg_charpoly_reverse_idempotent_eq_pow_one_add_range (k := k) fK hidem
  -- Replace the projector range by the Morita corner, whose dimension is the desired exponent.
  rw [hpoly, hrange]
  let q : Submodule k Xi := Submodule.restrictScalars k X0
  let l : q →ₗ[k] M := (Xi.subtype.restrictScalars k).comp q.subtype
  have hl_range : LinearMap.range l = q.map (Xi.subtype.restrictScalars k) := by
    -- The image submodule is literally the range of the subtype map restricted to the corner.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hl_inj : Function.Injective l := by
    intro x y hxy
    -- The ambient subtype map is injective, hence so is its restriction to the corner.
    exact Subtype.ext (Subtype.ext hxy)
  have hfin : Module.finrank k (q.map (Xi.subtype.restrictScalars k)) = Module.finrank k q := by
    have hfin_range := LinearMap.finrank_range_of_inj (f := l) hl_inj
    rw [hl_range] at hfin_range
    exact hfin_range
  exact congrArg (fun m ↦ (Polynomial.X + 1 : Polynomial k) ^ m) (by simpa [q] using hfin)

/-- Helper for Exercise 18-18.2-6: equality of ambient primitive product-projector reverse
characteristic polynomials gives equality of the corresponding base-field Morita-corner
dimensions. -/
lemma cornerBaseFieldFinrank_eq_of_ambient_projector_reverseCharpoly_eq
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (i : Fin n)
    (hprojector :
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse) :
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
    let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
    let _ : IsScalarTower k (D i) XiM :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
    let _ : IsScalarTower k (D i) XiN :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
    let _ : Module.Finite k XiM := Module.Finite.of_injective
      (XiM.subtype.restrictScalars k) Subtype.val_injective
    let _ : Module.Finite k XiN := Module.Finite.of_injective
      (XiN.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
      (XiM.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
      (XiN.subtype.restrictScalars k) Subtype.val_injective
    let X0M := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
    let X0N := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
    Module.finrank k (Submodule.restrictScalars k X0M) =
      Module.finrank k (Submodule.restrictScalars k X0N) := by
  intro XiM XiN _ _ _ _ _ _ MM NN _ _ _ _ _ _ _ _ X0M X0N
  have hpolyM :=
    splitProduct_ambientCoordinateProjector_reverseCharpoly_eq_pow_one_add
      (k := k) (D := D) (d := d) (M := M) i
  have hpolyN :=
    splitProduct_ambientCoordinateProjector_reverseCharpoly_eq_pow_one_add
      (k := k) (D := D) (d := d) (M := N) i
  -- Normalize the two ambient projector polynomials to powers of `X + 1` and compare exponents.
  have hpow :
      (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k (Submodule.restrictScalars k X0M) =
        (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k
          (Submodule.restrictScalars k X0N) := by
    calc
      (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k
          (Submodule.restrictScalars k X0M) =
        (-DistribSMul.toLinearMap k M
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := by
            symm
            simpa [XiM, MM, X0M] using hpolyM
      _ =
        (-DistribSMul.toLinearMap k N
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := hprojector
      _ = (Polynomial.X + 1 : Polynomial k) ^ Module.finrank k
          (Submodule.restrictScalars k X0N) := by
            simpa [XiN, NN, X0N] using hpolyN
  exact exponent_eq_of_pow_X_add_one_eq (k := k) hpow

/-- Helper for Exercise 18-18.2-6: once a chosen lift exists for every point of the semisimple
image algebra, the `n = 1` exterior-trace specialization descends to ordinary trace equality on
that target algebra. -/
lemma trace_eq_on_target_of_surjective_lift
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  -- Choose a lift and apply the already-proved `n = 1` specialization on `k[G]`.
  intro a
  rcases hlift a with ⟨t, rfl⟩
  exact
    trace_eq_of_hexteriorTrace_one_on_lift
      (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hexteriorTrace t

/-- Helper for Exercise 18-18.2-6: generator-level determinant equality gives ordinary trace
equality after descending along a surjective lift to the finite image algebra. -/
lemma trace_eq_on_target_of_generator_det_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  intro a
  rcases hlift a with ⟨t, rfl⟩
  -- The coefficient-one part of the determinant identity is character equality on generators.
  have hchar : ρ.character = ρ'.character :=
    character_eq_of_det_one_add_polynomial_eq (ρ := ρ) (ρ' := ρ') hdetG
  have htrace :
      LinearMap.trace k V (ρ.asAlgebraHom t) =
        LinearMap.trace k W (ρ'.asAlgebraHom t) :=
    trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar t
  have hVa : φV (liftι t) = ρ.asAlgebraHom t := by
    -- Re-express the descended left action through the chosen lift.
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f t) hφV
  have hWa : φW (liftι t) = ρ'.asAlgebraHom t := by
    -- Re-express the descended right action through the chosen lift.
    simpa [AlgHom.comp_apply] using
      congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f t) hφW
  simpa [hVa, hWa] using htrace

/-- Helper for Exercise 18-18.2-6: generator determinant-polynomial equality identifies the
characters of all exterior-power representations. -/
lemma nthExteriorPower_character_eq_of_generator_det_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (n : ℕ) :
    (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character := by
  ext g
  -- Read the `n`th coefficient of each generator determinant polynomial through the
  -- exterior-power trace formula, then rewrite by the source determinant hypothesis.
  calc
    (ρ.nthExteriorPower n).character g =
        LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (ρ g)) := by
          simp [Representation.character, Representation.nthExteriorPower]
    _ = (((-ρ g).charpoly.reverse : Polynomial k).coeff n) := by
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ g) n
    _ = (((-ρ' g).charpoly.reverse : Polynomial k).coeff n) := by
          rw [hdetG g]
    _ = LinearMap.trace k (⋀[k]^n W) (exteriorPower.map n (ρ' g)) := by
          symm
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' g) n
    _ = (ρ'.nthExteriorPower n).character g := by
          simp [Representation.character, Representation.nthExteriorPower]

/-- Helper for Exercise 18-18.2-6: generator determinant-polynomial equality gives trace equality
on the whole monoid algebra for every exterior-power representation. -/
lemma exteriorTrace_eq_asAlgebraHom_of_generator_det_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (n : ℕ) (t : MonoidAlgebra k G) :
    LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
      LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t) := by
  -- Once characters agree on generators, the trace functional extends linearly across `k[G]`.
  have hchar :
      (ρ.nthExteriorPower n).character = (ρ'.nthExteriorPower n).character :=
    nthExteriorPower_character_eq_of_generator_det_eq (ρ := ρ) (ρ' := ρ') hdetG n
  exact
    trace_eq_asAlgebraHom_of_character_eq
      (ρ := ρ.nthExteriorPower n) (ρ' := ρ'.nthExteriorPower n) hchar t

/-- Helper for Exercise 18-18.2-6: specializing the exterior-trace identities to monoid
generators recovers equality of the determinant polynomials `det (1 + ρ(g)T)`. -/
lemma detOneAddPolynomialEq_on_generators_of_exteriorTrace
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse := by
  intro g
  ext n
  -- Read each coefficient through the Chapter 9 exterior-power trace formula at the generator `g`.
  calc
    (((-ρ g).charpoly.reverse : Polynomial k).coeff n) =
        LinearMap.trace k (⋀[k]^n V)
          ((ρ.nthExteriorPower n).asAlgebraHom (MonoidAlgebra.of k G g)) := by
            simpa [Representation.nthExteriorPower, Representation.asAlgebraHom_of] using
              (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ g) n).symm
    _ =
        LinearMap.trace k (⋀[k]^n W)
          ((ρ'.nthExteriorPower n).asAlgebraHom (MonoidAlgebra.of k G g)) :=
        hexteriorTrace n (MonoidAlgebra.of k G g)
    _ = (((-ρ' g).charpoly.reverse : Polynomial k).coeff n) := by
          simpa [Representation.nthExteriorPower, Representation.asAlgebraHom_of] using
            trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' g) n

/-- Helper for Exercise 18-18.2-6: equality of all exterior-power traces of two endomorphisms
identifies their determinant polynomials `det (1 + fT)`. -/
lemma negCharpolyReverse_eq_of_exteriorPower_trace_eq
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (f : X →ₗ[k] X) (g : Y →ₗ[k] Y)
    (htrace : ∀ n : ℕ,
      LinearMap.trace k (⋀[k]^n X) (exteriorPower.map n f) =
        LinearMap.trace k (⋀[k]^n Y) (exteriorPower.map n g)) :
    (-f).charpoly.reverse = (-g).charpoly.reverse := by
  ext n
  -- Compare the `n`th coefficient of each determinant polynomial through the Chapter 9
  -- exterior-power trace formula.
  calc
    (((-f).charpoly.reverse : Polynomial k).coeff n) =
        LinearMap.trace k (⋀[k]^n X) (exteriorPower.map n f) := by
          exact (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := f) n).symm
    _ = LinearMap.trace k (⋀[k]^n Y) (exteriorPower.map n g) := htrace n
    _ = (((-g).charpoly.reverse : Polynomial k).coeff n) := by
          exact trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := g) n

/-- Helper for Exercise 18-18.2-6: target-level exterior-power trace equality on monoid-algebra
lifts is exactly the coefficientwise determinant equality needed on those lifts. -/
lemma det_eq_on_lift_of_target_exterior_trace
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (htargetExteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) (exteriorPower.map n (φV (liftι t))) =
        LinearMap.trace k (⋀[k]^n W) (exteriorPower.map n (φW (liftι t)))) :
    ∀ t : MonoidAlgebra k G,
      (-φV (liftι t)).charpoly.reverse = (-φW (liftι t)).charpoly.reverse := by
  intro t
  -- The previous coefficient bridge converts the target exterior traces at this lift into
  -- equality of the whole determinant polynomial.
  exact
    negCharpolyReverse_eq_of_exteriorPower_trace_eq
      (φV (liftι t)) (φW (liftι t)) (fun n ↦ htargetExteriorTrace n t)

/-- Helper for Exercise 18-18.2-6: once the common image algebra `A` is split by a Wedderburn
equivalence `eA : A ≃ₐ[k] B`, the already-descended ordinary trace identity transports directly to
the product algebra `B`. -/
lemma trace_eq_on_split_product_of_trace_eq
    {B : Type*} [Ring B] [Algebra k B]
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module A X] [Module A Y]
    [IsScalarTower k A X] [IsScalarTower k A Y]
    (eA : A ≃ₐ[k] B)
    (htraceA : ∀ a : A,
      LinearMap.trace k X (DistribSMul.toLinearMap k X a) =
        LinearMap.trace k Y (DistribSMul.toLinearMap k Y a)) :
    let _ : Module B X := Module.compHom X eA.symm.toRingHom
    let _ : Module B Y := Module.compHom Y eA.symm.toRingHom
    let _ : IsScalarTower k B X :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := X) fun r x ↦ by
        change (eA.symm ((algebraMap k B) r)) • x = r • x
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
    let _ : IsScalarTower k B Y :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := Y) fun r y ↦ by
        change (eA.symm ((algebraMap k B) r)) • y = r • y
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r y
    ∀ b : B,
      LinearMap.trace k X (DistribSMul.toLinearMap k X b) =
        LinearMap.trace k Y (DistribSMul.toLinearMap k Y b) := by
  -- The transported `B`-action is defined through `eA.symm`, so the trace identity on `A`
  -- immediately rewrites to the corresponding one on the split product.
  simpa using fun b : B ↦ htraceA (eA.symm b)

/-- Helper for Exercise 18-18.2-6: generator-level determinant equality gives ordinary trace
equality after transporting the finite image algebra across a Wedderburn split. -/
lemma trace_eq_on_split_product_of_generator_det_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    {B : Type*} [Ring B] [Algebra k B]
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (eA : A ≃ₐ[k] B)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    let _ : IsScalarTower k A V :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
        change (φV (algebraMap k A r)) x = r • x
        simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
    let _ : IsScalarTower k A W :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
        change (φW (algebraMap k A r)) x = r • x
        simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
    let _ : Module B V := Module.compHom V eA.symm.toRingHom
    let _ : Module B W := Module.compHom W eA.symm.toRingHom
    let _ : IsScalarTower k B V :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
        change (eA.symm ((algebraMap k B) r)) • x = r • x
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
    let _ : IsScalarTower k B W :=
      IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r y ↦ by
        change (eA.symm ((algebraMap k B) r)) • y = r • y
        rw [eA.symm.commutes]
        exact IsScalarTower.algebraMap_smul (R := k) (A := A) r y
    ∀ b : B,
      LinearMap.trace k V (DistribSMul.toLinearMap k V b) =
        LinearMap.trace k W (DistribSMul.toLinearMap k W b) := by
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r y ↦ by
      change (φW (algebraMap k A r)) y = r • y
      simpa using congrArg (fun f : Module.End k W ↦ f y) (φW.commutes r)
  let _ : Module B V := Module.compHom V eA.symm.toRingHom
  let _ : Module B W := Module.compHom W eA.symm.toRingHom
  let _ : IsScalarTower k B V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let _ : IsScalarTower k B W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r y ↦ by
      change (eA.symm ((algebraMap k B) r)) • y = r • y
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r y
  have htraceA_asHom :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) :=
    trace_eq_on_target_of_generator_det_eq
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hdetG
  have htraceA :
      ∀ a : A,
        LinearMap.trace k V (DistribSMul.toLinearMap k V a) =
          LinearMap.trace k W (DistribSMul.toLinearMap k W a) := by
    intro a
    -- The `A`-module structures are exactly the actions induced by `φV` and `φW`.
    simpa [DistribSMul.toLinearMap] using htraceA_asHom a
  -- Transport the descended trace identity through the fixed split algebra equivalence.
  exact trace_eq_on_split_product_of_trace_eq (A := A) (eA := eA) htraceA

/-- Helper for Exercise 18-18.2-6: once the Morita corner modules in each Wedderburn factor have
the same division-ring dimension, the ambient modules over the product of matrix algebras are
already linearly equivalent. -/
theorem nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (hcorner : ∀ i : Fin n,
      let XiM :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let XiN :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (D i) XiM :=
        Module.compHom XiM
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : Module (D i) XiN :=
        Module.compHom XiN
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
          (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
          (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  let eM :=
    pi_idempotent_linearEquiv
      (k := k) (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)) (M := M)
  let eN :=
    pi_idempotent_linearEquiv
      (k := k) (R := fun i ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)) (M := N)
  let ecoord :
      ∀ i : Fin n,
        pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i ≃ₗ[Π j,
              Matrix (Fin (d j)) (Fin (d j)) (D j)]
            pi_coordinate_submodule
              (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i := by
    intro i
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
    let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) MM
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) NN
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
      ((pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i).subtype
        |>.restrictScalars k)
      Subtype.val_injective
    let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
      ((pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i).subtype
        |>.restrictScalars k)
      Subtype.val_injective
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiM) (j := 0)
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiN) (j := 0)
    let _ : Module.Free (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
      Module.Free.of_divisionRing
        (K := D i) (V := MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
    let _ : Module.Free (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      Module.Free.of_divisionRing
        (K := D i) (V := MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
    let ecorner :
        MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)) ≃ₗ[D i]
          MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)) :=
      LinearEquiv.ofFinrankEq
        (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
        (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
        (by simpa [XiM, XiN] using hcorner i)
    let eXi :
        XiM ≃ₗ[Matrix (Fin (d i)) (Fin (d i)) (D i)] XiN :=
      (toModuleCatFromModuleCatLinearEquiv (R := D i) (M := MM) 0).trans
        ((matrix_module_linearEquiv_of_linearEquiv (n := Fin (d i)) ecorner).trans
          (toModuleCatFromModuleCatLinearEquiv (R := D i) (M := NN) 0).symm)
    -- Each product coordinate becomes product-linear because the ambient action factors through
    -- that single coordinate.
    simpa [XiM, XiN] using
      (coordinate_linearEquiv_is_product_linear
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) (N := N) i eXi)
  -- Decompose both modules into coordinate summands, apply the factorwise matrix equivalences,
  -- and reassemble.
  exact
    ⟨eM.trans ((LinearEquiv.piCongrRight ecoord).trans eN.symm)⟩

/-- Helper for Exercise 18-18.2-6: equality of the primitive projector reverse characteristic
polynomials in every Wedderburn factor is enough to identify the two split-product modules. -/
theorem nonempty_linearEquiv_of_projector_reverseCharpoly_eq_on_pi_matrix_divisionRing
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (hprojector : ∀ i : Fin n,
      let XiM :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let XiN :=
        pi_coordinate_submodule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factorModule
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
      let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        pi_coordinate_submodule_factor_isScalarTower
          (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
      let _ : Module (D i) XiM :=
        Module.compHom XiM
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let _ : Module (D i) XiN :=
        Module.compHom XiN
          (Matrix.scalarAlgHom (Fin (d i)) k :
            D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
      let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
      let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
        ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
      let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
        MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
      let _ : IsScalarTower k (D i) XiM :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
      let _ : IsScalarTower k (D i) XiN :=
        isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
      let _ : Module.Finite k XiM := Module.Finite.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : Module.Finite k XiN := Module.Finite.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiM := FiniteDimensional.of_injective
        (XiM.subtype.restrictScalars k) Subtype.val_injective
      let _ : FiniteDimensional k XiN := FiniteDimensional.of_injective
        (XiN.subtype.restrictScalars k) Subtype.val_injective
      let X0M := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
      let X0N := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
      (-DistribSMul.toLinearMap k XiM
        (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse =
        (-DistribSMul.toLinearMap k XiN
          (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i))).charpoly.reverse) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  -- First turn the projector characteristic-polynomial identities into Morita corner dimension
  -- equalities in each Wedderburn coordinate.
  have hcorner :
      ∀ i : Fin n,
        let XiM :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let XiN :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (D i) XiM :=
          Module.compHom XiM
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiN :=
          Module.compHom XiN
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
          Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
    intro i
    have hbase :=
      cornerBaseFieldFinrank_eq_of_projector_reverseCharpoly_eq
        (k := k) (D := D) (d := d) (M := M) (N := N) i (hprojector i)
    exact
      cornerFinrank_eq_of_cornerBaseFieldFinrank_eq
        (k := k) (D := D) (d := d) (M := M) (N := N) i hbase
  -- The existing Morita reconstruction theorem then assembles the coordinate equivalences.
  exact
    nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
      (k := k) (D := D) (d := d) (M := M) (N := N) hcorner

/-- Helper for Exercise 18-18.2-6: equality of the ambient primitive product-projector
characteristic polynomials is enough to identify the two split-product modules. -/
theorem nonempty_linearEquiv_of_ambient_projector_reverseCharpoly_eq_on_pi_matrix_divisionRing
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (hprojector : ∀ i : Fin n,
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  -- Convert each ambient projector identity into Morita corner-rank equality.
  have hcorner :
      ∀ i : Fin n,
        let XiM :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let XiN :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (D i) XiM :=
          Module.compHom XiM
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiN :=
          Module.compHom XiN
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
          Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
    intro i
    have hbase :=
      cornerBaseFieldFinrank_eq_of_ambient_projector_reverseCharpoly_eq
        (k := k) (D := D) (d := d) (M := M) (N := N) i (hprojector i)
    exact
      cornerFinrank_eq_of_cornerBaseFieldFinrank_eq
        (k := k) (D := D) (d := d) (M := M) (N := N) i hbase
  -- Matching Morita corner ranks reconstruct the full product-algebra linear equivalence.
  exact
    nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
      (k := k) (D := D) (d := d) (M := M) (N := N) hcorner

/-- Helper for Exercise 18-18.2-6: determinant-polynomial equality on the finite semisimple
image algebra is enough to identify the two descended semisimple modules. -/
theorem nonempty_linearEquiv_of_det_eq_on_finite_semisimple_image
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (hdetA : ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  -- Route correction: avoid positive-characteristic cancellation from traces.  We split the
  -- semisimple image algebra and compare actual primitive-projector characteristic polynomials.
  classical
  obtain ⟨n, D, d, _, _, _, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) (D i)
  let _ : Module B V := Module.compHom V eA.symm.toRingHom
  let _ : Module B W := Module.compHom W eA.symm.toRingHom
  let _ : IsScalarTower k B V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let _ : IsScalarTower k B W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  have hcorner :
      ∀ i : Fin n,
        let XiV :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let XiW :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (D i) XiV :=
          Module.compHom XiV
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiW :=
          Module.compHom XiW
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV)
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW)
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiV (0 : Fin (d i))) =
          Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiW (0 : Fin (d i))) := by
    intro i
    let XiV :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let XiW :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : Module (D i) XiV :=
      Module.compHom XiV
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiW :=
      Module.compHom XiW
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV)
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
        (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW)
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
    let _ : IsScalarTower k (D i) XiV :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiV)
    let _ : IsScalarTower k (D i) XiW :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiW)
    let e00 : Matrix (Fin (d i)) (Fin (d i)) (D i) :=
      Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)
    let b : B := Pi.single i e00
    have hprojector_ambient :
        (-DistribSMul.toLinearMap k V b).charpoly.reverse =
          (-DistribSMul.toLinearMap k W b).charpoly.reverse := by
      -- Transport determinant equality to the split product and evaluate at `Pi.single i E₀₀`.
      simpa [B, b] using hdetA (eA.symm b)
    have hcorner_base :
        let XiV :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let XiW :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := V) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := W) i
        let _ : Module (D i) XiV :=
          Module.compHom XiV
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiW :=
          Module.compHom XiW
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
          ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV
        let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
          ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiV :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) MM
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiW :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) NN
        let _ : IsScalarTower k (D i) XiV :=
          isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiV)
        let _ : IsScalarTower k (D i) XiW :=
          isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiW)
        let _ : Module.Finite k XiV := Module.Finite.of_injective
          (XiV.subtype.restrictScalars k) Subtype.val_injective
        let _ : Module.Finite k XiW := Module.Finite.of_injective
          (XiW.subtype.restrictScalars k) Subtype.val_injective
        let _ : FiniteDimensional k XiV := FiniteDimensional.of_injective
          (XiV.subtype.restrictScalars k) Subtype.val_injective
        let _ : FiniteDimensional k XiW := FiniteDimensional.of_injective
          (XiW.subtype.restrictScalars k) Subtype.val_injective
        let X0V := MatrixModCat.toModuleCatObj (D i) MM (0 : Fin (d i))
        let X0W := MatrixModCat.toModuleCatObj (D i) NN (0 : Fin (d i))
        Module.finrank k (Submodule.restrictScalars k X0V) =
          Module.finrank k (Submodule.restrictScalars k X0W) := by
      -- Comparing powers of `X + 1` recovers honest base-field corner dimensions.
      exact
        cornerBaseFieldFinrank_eq_of_ambient_projector_reverseCharpoly_eq
          (k := k) (D := D) (d := d) (M := V) (N := W) i hprojector_ambient
    -- Cancel the common finite `k`-dimension of `D i` to get the Morita multiplicity equality.
    exact
      cornerFinrank_eq_of_cornerBaseFieldFinrank_eq
        (k := k) (D := D) (d := d) (M := V) (N := W) i hcorner_base
  have hBlinear : Nonempty (V ≃ₗ[B] W) := by
    simpa [B] using
      nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
        (k := k) (D := D) (d := d) (M := V) (N := W) hcorner
  rcases hBlinear with ⟨eB⟩
  have hmap_smul : ∀ (a : A) (x : V), eB (a • x) = a • eB x := by
    intro a x
    have hVsmul : (eA a : B) • x = a • x := by
      change (eA.symm (eA a)) • x = a • x
      simp
    have hWsmul : (eA a : B) • eB x = a • eB x := by
      change (eA.symm (eA a)) • eB x = a • eB x
      simp
    calc
      eB (a • x) = eB ((eA a : B) • x) := by rw [hVsmul]
      _ = (eA a : B) • eB x := eB.map_smul (eA a) x
      _ = a • eB x := hWsmul
  let eAlinear : V ≃ₗ[A] W :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := hmap_smul }
  exact ⟨eAlinear⟩

/-- Helper for Exercise 18-18.2-6: determinant-polynomial equality on every chosen lift from
`k[G]` descends to the finite image algebra. -/
lemma det_eq_on_target_of_det_eq_on_lift
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hlift : Function.Surjective liftι)
    (hdetLift : ∀ t : MonoidAlgebra k G,
      (-φV (liftι t)).charpoly.reverse = (-φW (liftι t)).charpoly.reverse) :
    ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse := by
  intro a
  -- Choose a monoid-algebra lift of the target element, then apply the lifted determinant
  -- identity at that representative.
  rcases hlift a with ⟨t, rfl⟩
  exact hdetLift t

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: semisimplicity over a finite image algebra makes the lifted
monoid representation semisimple after restricting along the surjective lift. -/
lemma isSemisimpleRepresentation_of_surjective_lift
    {ρ : Representation k G V}
    (φV : A →ₐ[k] Module.End k V)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V) :
    IsSemisimpleRepresentation ρ := by
  -- Move the target from representation language to the owner `k[G]`-module.
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  let _ : Module A V := Module.compHom V φV.toRingHom
  have hkg : (let _ : Module (MonoidAlgebra k G) V := Module.compHom V liftι.toRingHom
      IsSemisimpleModule (MonoidAlgebra k G) V) := by
    -- Restrict semisimplicity along the surjective monoid-algebra map.
    exact (isSemisimpleModule_iff_of_ringHom_surjective liftι.toRingHom hlift).2 hV
  change @IsSemisimpleModule (MonoidAlgebra k G) MonoidAlgebra.ring V _
    (Module.compHom V ρ.asAlgebraHom.toRingHom)
  have hring : (φV.comp liftι).toRingHom = ρ.asAlgebraHom.toRingHom :=
    congrArg AlgHom.toRingHom hφV
  -- The compatibility hypothesis identifies the restricted action with the representation action.
  rw [← hring]
  exact hkg

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: the determinant polynomial of a product representation factors
as the product of the determinant polynomials of the two factors. -/
lemma negCharpolyReverse_prod
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (ρ : Representation k G X) (σ : Representation k G Y) (g : G) :
    (-(ρ.prod σ g)).charpoly.reverse =
      (((-(ρ g)).charpoly.reverse : Polynomial k) *
        ((-(σ g)).charpoly.reverse : Polynomial k)) := by
  have hneg : -(ρ.prod σ g) = (-ρ g).prodMap (-(σ g)) := by
    apply LinearMap.ext
    intro x
    cases x with
    | mk x y =>
        -- The product action is coordinatewise, and negation is coordinatewise as well.
        ext <;> simp [Representation.prod_apply_apply, LinearMap.prodMap_apply]
  -- Characteristic polynomials multiply on product maps; reversal preserves products over a field.
  rw [hneg, LinearMap.charpoly_prodMap, Polynomial.reverse_mul_of_domain]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: equivalent representations have the same reversed
characteristic polynomial on every generator. -/
lemma negCharpolyReverse_eq_of_representationEquiv
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {σ : Representation k G Y}
    (e : ρ.Equiv σ) (g : G) :
    (-ρ g).charpoly.reverse = (-σ g).charpoly.reverse := by
  -- Conjugate the generator action through the equivalence, then pass to characteristic
  -- polynomials and reverse them.
  have hconj_pos : e.toLinearEquiv.conj (ρ g) = σ g := by
    exact Representation.Equiv.conj_apply_self (ρ := ρ) (σ := σ) g e
  have hconj_neg : e.toLinearEquiv.conj (-(ρ g)) = -(σ g) := by
    calc
      e.toLinearEquiv.conj (-(ρ g)) = -(e.toLinearEquiv.conj (ρ g)) := by
        exact map_neg e.toLinearEquiv.conj (ρ g)
      _ = -(σ g) := by rw [hconj_pos]
  have hchar : (-σ g).charpoly = (-ρ g).charpoly := by
    calc
      (-σ g).charpoly = (e.toLinearEquiv.conj (-(ρ g))).charpoly := by rw [hconj_neg]
      _ = (-ρ g).charpoly := LinearEquiv.charpoly_conj e.toLinearEquiv (-(ρ g))
  exact congrArg Polynomial.reverse hchar.symm

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: if a representation is equivalent to a product, its reversed
characteristic polynomial factors over the two product constituents. -/
lemma negCharpolyReverse_eq_mul_of_equiv_prod
    {X Y Z : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [AddCommGroup Z] [Module k Z] [FiniteDimensional k Z]
    {ρ : Representation k G X} (σ : Representation k G Y) (τ : Representation k G Z)
    (e : ρ.Equiv (σ.prod τ)) (g : G) :
    (-ρ g).charpoly.reverse =
      (((-(σ g)).charpoly.reverse : Polynomial k) *
        ((-(τ g)).charpoly.reverse : Polynomial k)) := by
  -- First replace the source action by the equivalent product action, then use the product
  -- characteristic-polynomial computation.
  calc
    (-ρ g).charpoly.reverse = (-(σ.prod τ g)).charpoly.reverse := by
      exact negCharpolyReverse_eq_of_representationEquiv (ρ := ρ) (σ := σ.prod τ) e g
    _ = (((-(σ g)).charpoly.reverse : Polynomial k) *
        ((-(τ g)).charpoly.reverse : Polynomial k)) := by
      exact negCharpolyReverse_prod (ρ := σ) (σ := τ) g

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: an equivalence of representations intertwines the induced
actions of every element of the monoid algebra, not only the monoid generators. -/
lemma representationEquiv_asAlgebraHom_comm
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : ρ.Equiv ρ') (t : MonoidAlgebra k G) :
    e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom t) =
      (ρ'.asAlgebraHom t).comp e.toLinearEquiv.toLinearMap := by
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra k G ↦
      e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom t) =
        (ρ'.asAlgebraHom t).comp e.toLinearEquiv.toLinearMap)
    t ?_ ?_ ?_
  · intro g
    ext x
    -- On generators this is exactly the intertwining relation stored in the representation
    -- equivalence.
    simpa [Representation.asAlgebraHom_of, LinearMap.comp_apply] using
      congrArg (fun f : V →ₗ[k] W ↦ f x) (e.toIntertwiningMap.2 g)
  · intro x y hx hy
    -- The commutation relation is additive in the monoid-algebra input.
    simp [hx, hy, LinearMap.add_comp, LinearMap.comp_add]
  · intro r x hx
    -- Scalar multiples commute because both sides are `k`-linear maps.
    simp [hx, LinearMap.smul_comp, LinearMap.comp_smul]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: a representation equivalence becomes an `A`-linear equivalence
when both `A`-actions are generated by a common surjective monoid-algebra lift. -/
lemma nonempty_linearEquiv_of_surjective_lift_of_representationEquiv
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (e : ρ.Equiv ρ') :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  have hmap_smul : ∀ (a : A) (x : V), e.toLinearEquiv (a • x) = a • e.toLinearEquiv x := by
    intro a x
    rcases hlift a with ⟨t, ht⟩
    have hVt : φV (liftι t) = ρ.asAlgebraHom t := by
      -- Rewrite the descended left action through the chosen monoid-algebra representative.
      simpa [AlgHom.comp_apply] using
        congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f t) hφV
    have hWt : φW (liftι t) = ρ'.asAlgebraHom t := by
      -- Rewrite the descended right action through the same representative.
      simpa [AlgHom.comp_apply] using
        congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f t) hφW
    have hcomm :=
      congrArg (fun f : V →ₗ[k] W ↦ f x) (representationEquiv_asAlgebraHom_comm e t)
    -- After replacing `a` by its lift, `A`-linearity is precisely the monoid-algebra
    -- intertwining relation above.
    change e.toLinearEquiv ((φV a) x) = (φW a) (e.toLinearEquiv x)
    rw [← ht, hVt, hWt]
    exact hcomm
  let eA : V ≃ₗ[A] W :=
    { toFun := e.toLinearEquiv
      invFun := e.toLinearEquiv.symm
      left_inv := e.toLinearEquiv.left_inv
      right_inv := e.toLinearEquiv.right_inv
      map_add' := e.toLinearEquiv.map_add
      map_smul' := hmap_smul }
  exact ⟨eA⟩

/-- Helper for Exercise 18-18.2-6: in characteristic zero, trace equality on every element of a
split Wedderburn product already identifies the Morita corner multiplicities and hence the
modules. This records the exact boundary of the trace-only route. -/
theorem nonempty_linearEquiv_of_trace_eq_on_pi_matrix_divisionRing_charZero
    [CharZero k]
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (htrace : ∀ b : Π i, Matrix (Fin (d i)) (Fin (d i)) (D i),
      LinearMap.trace k M (DistribSMul.toLinearMap k M b) =
        LinearMap.trace k N (DistribSMul.toLinearMap k N b)) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  -- Convert the trace of each primitive product projector into an equality of natural
  -- base-field corner dimensions; `CharZero k` is exactly the cancellation used here.
  have hcorner :
      ∀ i : Fin n,
        let XiM :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let XiN :=
          pi_coordinate_submodule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factorModule
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        let _ : Module (D i) XiM :=
          Module.compHom XiM
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : Module (D i) XiN :=
          Module.compHom XiN
            (Matrix.scalarAlgHom (Fin (d i)) k :
              D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM)
        let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i))
            (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN)
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
        let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
          pi_coordinate_submodule_factor_isScalarTower
            (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
        Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
          Module.finrank (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
    intro i
    let XiM :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let XiN :=
      pi_coordinate_submodule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : Module (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factorModule
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : Module (D i) XiM :=
      Module.compHom XiM
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let _ : Module (D i) XiN :=
      Module.compHom XiN
        (Matrix.scalarAlgHom (Fin (d i)) k :
          D i →ₐ[k] Matrix (Fin (d i)) (Fin (d i)) (D i)).toRingHom
    let MM : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM
    let NN : ModuleCat (Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
      ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) MM
    let _ : IsScalarTower (D i) (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      MatrixModCat.isScalarTower_toModuleCat (R := D i) (ι := Fin (d i)) NN
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiM :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := M) i
    let _ : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) (D i)) XiN :=
      pi_coordinate_submodule_factor_isScalarTower
        (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) (M := N) i
    let _ : IsScalarTower k (D i) XiM :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiM)
    let _ : IsScalarTower k (D i) XiN :=
      isScalarTower_of_matrix_scalar_action (k := k) (D := D i) (n := Fin (d i)) (M := XiN)
    let _ : FiniteDimensional k XiM :=
      FiniteDimensional.of_injective (XiM.subtype.restrictScalars k) Subtype.val_injective
    let _ : FiniteDimensional k XiN :=
      FiniteDimensional.of_injective (XiN.subtype.restrictScalars k) Subtype.val_injective
    have hbaseCast :
        (Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) : k) =
          Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) := by
      exact
        corner_baseField_finrank_eq_of_wedderburn_primitive_projector
          (k := k) (D := D) (d := d) (M := M) (N := N) htrace i
    have hbase :
        Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) =
          Module.finrank k (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      Nat.cast_injective (R := k) hbaseCast
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiM) (j := 0)
    let _ : FiniteDimensional (D i) (MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i))) :=
      finiteDimensional_toModuleCatObj_of_matrix_module
        (k := k) (D := D i) (m := d i) (M := XiN) (j := 0)
    -- Cancel the finite nonzero base-field dimension of the division algebra in each factor.
    exact
      finrank_over_divisionRing_eq_of_baseField_finrank_eq
        (k := k) (D := D i)
        (X := MatrixModCat.toModuleCatObj (D i) XiM (0 : Fin (d i)))
        (Y := MatrixModCat.toModuleCatObj (D i) XiN (0 : Fin (d i)))
        hbase
  -- With matching Morita multiplicities in every factor, the existing reconstruction theorem
  -- gives the product-algebra linear equivalence.
  exact
    nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
      (k := k) (D := D) (d := d) (M := M) (N := N) hcorner

/-- Helper for Exercise 18-18.2-6: in characteristic zero, the generator determinant-polynomial
hypothesis identifies the two descended modules over the finite semisimple image algebra by the
ordinary trace route. -/
theorem nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_charZero
    [CharZero k]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  classical
  obtain ⟨n, D, d, _, _, _, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) (D i)
  let _ : Module B V := Module.compHom V eA.symm.toRingHom
  let _ : Module B W := Module.compHom W eA.symm.toRingHom
  let _ : IsScalarTower k B V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let _ : IsScalarTower k B W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  have htraceB :
      ∀ b : B, LinearMap.trace k V (DistribSMul.toLinearMap k V b) =
        LinearMap.trace k W (DistribSMul.toLinearMap k W b) := by
    -- In characteristic zero the determinant hypothesis is only used through its ordinary
    -- trace shadow; transport that trace identity to the fixed Wedderburn product.
    simpa [B] using
      trace_eq_on_split_product_of_generator_det_eq
        (A := A) (B := B) (ρ := ρ) (ρ' := ρ')
        φV φW liftι hφV hφW hlift eA hdetG
  have hBlinear : Nonempty (V ≃ₗ[B] W) := by
    -- The split-product characteristic-zero theorem cancels natural dimensions from traces and
    -- reconstructs the module from its Morita corner multiplicities.
    simpa [B] using
      nonempty_linearEquiv_of_trace_eq_on_pi_matrix_divisionRing_charZero
        (k := k) (D := D) (d := d) (M := V) (N := W) htraceB
  rcases hBlinear with ⟨eB⟩
  have hmap_smul : ∀ (a : A) (x : V), eB (a • x) = a • eB x := by
    intro a x
    -- Transport `B`-linearity back across the Wedderburn equivalence `eA`.
    have hVsmul : (eA a : B) • x = a • x := by
      change (eA.symm (eA a)) • x = a • x
      simp
    have hWsmul : (eA a : B) • eB x = a • eB x := by
      change (eA.symm (eA a)) • eB x = a • eB x
      simp
    calc
      eB (a • x) = eB ((eA a : B) • x) := by rw [hVsmul]
      _ = (eA a : B) • eB x := eB.map_smul (eA a) x
      _ = a • eB x := hWsmul
  let eAlinear : V ≃ₗ[A] W :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := hmap_smul }
  exact ⟨eAlinear⟩

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: composing a surjective finite-image generator map with an
algebra equivalence keeps it surjective. -/
lemma algEquiv_toAlgHom_comp_surjective
    {B C : Type*} [Ring B] [Algebra k B] [Ring C] [Algebra k C]
    (e : A ≃ₐ[k] B) (f : C →ₐ[k] A) (hf : Function.Surjective f) :
    Function.Surjective (e.toAlgHom.comp f) := by
  intro b
  rcases hf (e.symm b) with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  -- Choose a preimage after transporting the target element back through the equivalence.
  change e (f c) = b
  rw [hc]
  simp

omit [Module.Finite k A] [IsSemisimpleRing A] in
/-- Helper for Exercise 18-18.2-6: after the finite image algebra is split, generator action
identities transport the original determinant-polynomial hypothesis to the split product. -/
lemma splitProduct_generator_det_eq_of_action_eq
    {B : Type*} [Ring B] [Algebra k B]
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module B X] [IsScalarTower k B X]
    [Module B Y] [IsScalarTower k B Y]
    {ρX : Representation k G X} {ρY : Representation k G Y}
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβX : ∀ g : G, DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g)) = ρX g)
    (hβY : ∀ g : G, DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g)) = ρY g)
    (hdetG : ∀ g : G, (-ρX g).charpoly.reverse = (-ρY g).charpoly.reverse) :
    ∀ g : G,
      (-DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g))).charpoly.reverse := by
  intro g
  -- Rewrite both split-product generator actions back to the source representations, where the
  -- determinant-polynomial identity is exactly the hypothesis.
  calc
    (-DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-ρX g).charpoly.reverse := by
          rw [hβX g]
    _ = (-ρY g).charpoly.reverse := hdetG g
    _ = (-DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g))).charpoly.reverse := by
          rw [hβY g]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: after transporting a finite image algebra through a
Wedderburn equivalence, the split-product action of a lifted monoid-algebra element is the
original target-algebra action. -/
lemma splitProduct_lift_action_eq_target_action
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module A X] [Module B X]
    [IsScalarTower k B X]
    (eA : A ≃ₐ[k] B) (φX : A →ₐ[k] Module.End k X)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ : β = eA.toAlgHom.comp liftι)
    (hAsmul : ∀ (a : A) (x : X), a • x = φX a x)
    (hBsmul : ∀ (b : B) (x : X), b • x = (eA.symm b : A) • x)
    (t : MonoidAlgebra k G) :
    DistribSMul.toLinearMap k X (β t) = φX (liftι t) := by
  ext x
  -- First unfold the transported `B`-action, then use the defining `A`-action through `φX`.
  calc
    DistribSMul.toLinearMap k X (β t) x = (β t) • x := rfl
    _ = (eA.symm (β t) : A) • x := hBsmul (β t) x
    _ = φX (eA.symm (β t)) x := hAsmul (eA.symm (β t)) x
    _ = φX (liftι t) x := by
          have hβt : eA.symm (β t) = liftι t := by
            subst β
            simp
          rw [hβt]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: transporting a split-product action through the Wedderburn
equivalence gives the same reversed characteristic polynomial as the original target-algebra
action. -/
lemma splitProduct_lift_negCharpolyReverse_eq_target
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X] [Module A X] [Module B X]
    [IsScalarTower k B X]
    (eA : A ≃ₐ[k] B) (φX : A →ₐ[k] Module.End k X)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ : β = eA.toAlgHom.comp liftι)
    (hAsmul : ∀ (a : A) (x : X), a • x = φX a x)
    (hBsmul : ∀ (b : B) (x : X), b • x = (eA.symm b : A) • x)
    (t : MonoidAlgebra k G) :
    (-DistribSMul.toLinearMap k X (β t)).charpoly.reverse =
      (-φX (liftι t)).charpoly.reverse := by
  -- First identify the transported action as a linear map, then pass that equality through
  -- negation, characteristic polynomial, and reversal.
  rw [splitProduct_lift_action_eq_target_action
    (A := A) (eA := eA) (φX := φX) (liftι := liftι) (β := β)
    hβ hAsmul hBsmul t]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: determinant equality for lifted target-algebra actions
transports across a Wedderburn equivalence to determinant equality for the split-product
generator actions. -/
lemma splitProduct_generator_det_eq_of_lifted_target_det_eq
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X] [Module A X] [Module B X]
    [IsScalarTower k B X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] [Module A Y] [Module B Y]
    [IsScalarTower k B Y]
    (eA : A ≃ₐ[k] B) (φX : A →ₐ[k] Module.End k X)
    (φY : A →ₐ[k] Module.End k Y)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ : β = eA.toAlgHom.comp liftι)
    (hAsmulX : ∀ (a : A) (x : X), a • x = φX a x)
    (hAsmulY : ∀ (a : A) (y : Y), a • y = φY a y)
    (hBsmulX : ∀ (b : B) (x : X), b • x = (eA.symm b : A) • x)
    (hBsmulY : ∀ (b : B) (y : Y), b • y = (eA.symm b : A) • y)
    (hdetLifted : ∀ g : G,
      (-φX (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φY (liftι (MonoidAlgebra.of k G g))).charpoly.reverse) :
    ∀ g : G,
      (-DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g))).charpoly.reverse := by
  intro g
  -- Normalize both transported split-product generator actions back to the target algebra,
  -- where the lifted determinant hypothesis is stated.
  calc
    (-DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φX (liftι (MonoidAlgebra.of k G g))).charpoly.reverse := by
          exact
            splitProduct_lift_negCharpolyReverse_eq_target
              (A := A) (B := B) (X := X) (eA := eA) (φX := φX)
              (liftι := liftι) (β := β) hβ hAsmulX hBsmulX
              (MonoidAlgebra.of k G g)
    _ = (-φY (liftι (MonoidAlgebra.of k G g))).charpoly.reverse := hdetLifted g
    _ = (-DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g))).charpoly.reverse := by
          exact
            (splitProduct_lift_negCharpolyReverse_eq_target
              (A := A) (B := B) (X := Y) (eA := eA) (φX := φY)
              (liftι := liftι) (β := β) hβ hAsmulY hBsmulY
              (MonoidAlgebra.of k G g)).symm

/-- Helper for Exercise 18-18.2-6: a map from `k[G]` to a split Wedderburn product gives the
standard representation on each matrix factor by evaluating the image of every generator. -/
noncomputable def wedderburnFactorRepresentation
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (i : Fin n) :
    Representation k G (Fin (d i) → D i) :=
  (DistribMulAction.toModuleEnd k (Fin (d i) → D i)).comp
    ((Pi.evalMonoidHom (fun i : Fin n ↦ Matrix (Fin (d i)) (Fin (d i)) (D i)) i).comp
      (β.toMonoidHom.comp (MonoidAlgebra.of k G)))

/-- Helper for Exercise 18-18.2-6: the Wedderburn factor representation acts by the evaluated
matrix obtained from the monoid-algebra generator. -/
lemma wedderburnFactorRepresentation_apply
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (i : Fin n) (g : G) :
    wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i g =
      DistribSMul.toLinearMap k (Fin (d i) → D i)
        ((β (MonoidAlgebra.of k G g)) i) := by
  -- Unfold the composed monoid homomorphisms; this pins the standard-factor normal form.
  rfl

/-- Helper for Exercise 18-18.2-6: on monoid generators, the algebra hom attached to a
Wedderburn factor representation is the same evaluated matrix action. -/
lemma wedderburnFactorRepresentation_asAlgebraHom_of
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (i : Fin n) (g : G) :
    (wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).asAlgebraHom
        (MonoidAlgebra.of k G g) =
      DistribSMul.toLinearMap k (Fin (d i) → D i)
        ((β (MonoidAlgebra.of k G g)) i) := by
  -- Move from the representation-level generator formula to the monoid-algebra generator API.
  rw [Representation.asAlgebraHom_of]
  exact wedderburnFactorRepresentation_apply (k := k) (G := G) (D := D) (d := d) β i g

/-- Helper for Exercise 18-18.2-6: the algebra homomorphism attached to a Wedderburn factor
representation acts by the evaluated split-product image on every monoid-algebra element. -/
lemma wedderburnFactorRepresentation_asAlgebraHom_apply
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (i : Fin n) (t : MonoidAlgebra k G) :
    (wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).asAlgebraHom t =
      DistribSMul.toLinearMap k (Fin (d i) → D i) ((β t) i) := by
  -- Extend the generator computation linearly across the monoid algebra.
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra k G ↦
      (wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).asAlgebraHom t =
        DistribSMul.toLinearMap k (Fin (d i) → D i) ((β t) i))
    t ?_ ?_ ?_
  · intro g
    exact wedderburnFactorRepresentation_asAlgebraHom_of
      (k := k) (G := G) (D := D) (d := d) β i g
  · intro a b ha hb
    apply LinearMap.ext
    intro x
    simp [ha, hb, add_smul]
  · intro r a ha
    apply LinearMap.ext
    intro x
    simp [ha]

/-- Helper for Exercise 18-18.2-6: a surjective map to the split Wedderburn product has
monoid-algebra preimages of the primitive product projectors. -/
lemma splitProduct_primitiveProjector_lifts_of_surjective
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, NeZero (d i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β) :
    ∀ i : Fin n, ∃ t : MonoidAlgebra k G,
      β t =
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j)) := by
  intro i
  -- Surjectivity supplies a lift of the selected primitive product idempotent.
  exact
    hβ_surj
      (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
        Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))

/-- Helper for Exercise 18-18.2-6: evaluating a surjective split-product action on one
Wedderburn factor gives a simple restricted `k[G]`-module. -/
lemma splitProduct_standardFactor_isSimpleModule_of_surjective
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, NeZero (d i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β) (i : Fin n) :
    let q : MonoidAlgebra k G →+* Matrix (Fin (d i)) (Fin (d i)) (D i) :=
      (Pi.evalRingHom (fun j : Fin n ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) i).comp
        β.toRingHom
    let _ : Module (MonoidAlgebra k G) (Fin (d i) → D i) :=
      Module.compHom (Fin (d i) → D i) q
    IsSimpleModule (MonoidAlgebra k G) (Fin (d i) → D i) := by
  classical
  intro q _
  have hq_surj : Function.Surjective q := by
    intro a
    let b : Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j) := Pi.single i a
    rcases hβ_surj b with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    -- Evaluate the chosen product lift at the selected factor.
    change (β t) i = a
    rw [ht]
    simp [b]
  exact
    (isSimpleModule_iff_of_ringHom_surjective q hq_surj).2
      (matrixStandardModule_isSimpleModule (D := D i) (ι := Fin (d i)))

/-- Helper for Exercise 18-18.2-6: the standard Wedderburn factor representations are
irreducible after restriction along a surjective split-product map. -/
lemma wedderburnFactorRepresentation_isIrreducible
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, NeZero (d i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β) (i : Fin n) :
    (wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).IsIrreducible := by
  classical
  let ρi := wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i
  change ρi.IsIrreducible
  let q : MonoidAlgebra k G →+* Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    (Pi.evalRingHom (fun j : Fin n ↦ Matrix (Fin (d j)) (Fin (d j)) (D j)) i).comp
      β.toRingHom
  letI : Module (MonoidAlgebra k G) (Fin (d i) → D i) :=
    Module.compHom (Fin (d i) → D i) q
  have hsimpStd : IsSimpleModule (MonoidAlgebra k G) (Fin (d i) → D i) := by
    -- The evaluated action is simple because the evaluated algebra map is surjective.
    simpa [q] using
      splitProduct_standardFactor_isSimpleModule_of_surjective
        (k := k) (G := G) (D := D) (d := d) β hβ_surj i
  letI : AddCommGroup ρi.asModule := ρi.instAddCommGroupAsModule
  letI : Module (MonoidAlgebra k G) ρi.asModule := ρi.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule (MonoidAlgebra k G) (Fin (d i) → D i) := hsimpStd
  let eOwner : ρi.asModule ≃ₗ[MonoidAlgebra k G] (Fin (d i) → D i) :=
    { toFun := fun x ↦ ρi.asModuleEquiv x
      invFun := fun x ↦ ρi.asModuleEquiv.symm x
      left_inv := fun x ↦ ρi.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρi.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρi.asModuleEquiv.map_add x y
      map_smul' := by
        intro r x
        -- Move the owner `k[G]`-action through `asModuleEquiv`, then rewrite the attached
        -- algebra homomorphism to the evaluated split-product scalar action.
        calc
          ρi.asModuleEquiv (r • x) = ρi.asAlgebraHom r (ρi.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρi) r x
          _ = DistribSMul.toLinearMap k (Fin (d i) → D i) ((β r) i)
              (ρi.asModuleEquiv x) := by
                rw [wedderburnFactorRepresentation_asAlgebraHom_apply
                  (k := k) (G := G) (D := D) (d := d) β i r]
          _ = r • ρi.asModuleEquiv x := by
                rfl }
  have hsimpleOwner :
      @IsSimpleModule (MonoidAlgebra k G) _ ρi.asModule
        ρi.instAddCommGroupAsModule ρi.instModuleMonoidAlgebraAsModule := by
    -- Transport simplicity back from the concrete restricted standard factor to the owner module.
    exact
      @IsSimpleModule.congr (MonoidAlgebra k G) _ ρi.asModule
        ρi.instAddCommGroupAsModule ρi.instModuleMonoidAlgebraAsModule
        (Fin (d i) → D i) inferInstance inferInstance eOwner hsimpStd
  -- Irreducibility is the representation-facing form of the simple owner-module statement.
  exact (Representation.irreducible_iff_isSimpleModule_asModule ρi).mpr hsimpleOwner

/-- Helper for Exercise 18-18.2-6: a surjective map onto the split Wedderburn product supplies
monoid-algebra lifts of primitive factor projectors, with zero trace on all other standard
factors and self-trace equal to the base-field dimension of the factor division algebra. -/
lemma wedderburnFactor_traceProjectorLifts_of_surjective
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β) :
    ∀ i : Fin n, ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (Fin (d i) → D i)
          ((wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).asAlgebraHom t) =
        Module.finrank k (D i) ∧
      ∀ j : Fin n, j ≠ i →
        LinearMap.trace k (Fin (d j) → D j)
            ((wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β j).asAlgebraHom t) =
          0 := by
  intro i
  let e00 : Matrix (Fin (d i)) (Fin (d i)) (D i) :=
    Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)
  let b : Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j) := Pi.single i e00
  rcases hβ_surj b with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · -- On the selected factor the lifted primitive projector has trace `finrank k (D i)`.
    calc
      LinearMap.trace k (Fin (d i) → D i)
          ((wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β i).asAlgebraHom t) =
          LinearMap.trace k (Fin (d i) → D i)
            (DistribSMul.toLinearMap k (Fin (d i) → D i) e00) := by
            rw [wedderburnFactorRepresentation_asAlgebraHom_apply
              (k := k) (G := G) (D := D) (d := d) β i t, ht]
            simp [b, e00]
      _ = Module.finrank k (D i) := by
            simpa [e00] using
              trace_matrix_corner_idempotent_eq_finrank
                (k := k) (D := D i) (n := Fin (d i)) (X := D i) (0 : Fin (d i))
  · intro j hji
    -- Away from the selected factor the same lift evaluates to the zero matrix.
    calc
      LinearMap.trace k (Fin (d j) → D j)
          ((wedderburnFactorRepresentation (k := k) (G := G) (D := D) (d := d) β j).asAlgebraHom t) =
          LinearMap.trace k (Fin (d j) → D j)
            (DistribSMul.toLinearMap k (Fin (d j) → D j) (0 : Matrix (Fin (d j)) (Fin (d j)) (D j))) := by
            rw [wedderburnFactorRepresentation_asAlgebraHom_apply
              (k := k) (G := G) (D := D) (d := d) β j t, ht]
            simp [b, Pi.single_eq_of_ne hji]
      _ = 0 := by
            have hzero :
                DistribSMul.toLinearMap k (Fin (d j) → D j)
                    (0 : Matrix (Fin (d j)) (Fin (d j)) (D j)) = 0 := by
              ext x
              simp
            rw [hzero]
            exact map_zero (LinearMap.trace k (Fin (d j) → D j))

/-- Helper for Exercise 18-18.2-6: in the split matrix-product case, the primitive-projector
trace separator has self-trace exactly `1`. -/
lemma splitMatrixProduct_traceSeparator_one
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
    (hβ_surj : Function.Surjective β) :
    ∀ i : Fin n, ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (Fin (d i) → k)
          ((wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i).asAlgebraHom t) =
        1 ∧
      ∀ j : Fin n, j ≠ i →
        LinearMap.trace k (Fin (d j) → k)
            ((wedderburnFactorRepresentation
              (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β j).asAlgebraHom t) =
          0 := by
  intro i
  rcases
    wedderburnFactor_traceProjectorLifts_of_surjective
      (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β hβ_surj i with
    ⟨t, hself, hother⟩
  refine ⟨t, ?_, ?_⟩
  · -- In split factors the division-ring factor is the base field, so its `k`-dimension is one.
    simpa using hself
  · intro j hji
    -- The off-diagonal vanishing part is inherited unchanged from the primitive-projector lift.
    exact hother j hji

/-- Helper for Exercise 18-18.2-6: in the split matrix-product case and nonzero characteristic,
the determinant-product separator identifies the multiplicities of the standard factor
representations once the product normal form has been established. -/
lemma splitMatrixProduct_multiplicity_eq_of_detProductEq_notCharZero
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (hnonCharZero : ¬ CharZero k)
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
    (hβ_surj : Function.Surjective β)
    (m r : Fin n → ℕ)
    (hprod : ∀ g : G,
      ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ m i) : Polynomial k) =
        ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ r i) : Polynomial k)) :
    ∀ i : Fin n, m i = r i := by
  -- Feed the split primitive-projector separators into the existing determinant-product
  -- criterion; the only remaining work for the main branch is the product-normalization lemma.
  exact
    detProductEq_multiplicity_eq_of_separator_not_charZero_univ
      (k := k) (G := G) hnonCharZero
      (ρ := fun i ↦
        wedderburnFactorRepresentation
          (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i)
      (m := m) (n := r) hprod
      (splitMatrixProduct_traceSeparator_one
        (k := k) (G := G) (d := d) β hβ_surj)

/-- Helper for Exercise 18-18.2-6: the Morita multiplicity of a module over a split product of
matrix algebras, read from the `0`th corner of each coordinate factor. -/
noncomputable def splitMatrixProductCornerMultiplicity
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (M : Type*) [AddCommGroup M]
    [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    (i : Fin n) : ℕ :=
  let Xi :=
    pi_coordinate_submodule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i
  let _ : Module (Matrix (Fin (d i)) (Fin (d i)) k) Xi :=
    pi_coordinate_submodule_factorModule
      (k := k) (R := fun j ↦ Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i
  letI : Module k Xi :=
    Module.compHom Xi (Matrix.scalar (α := k) (Fin (d i)))
  letI :=
    MatrixModCat.isScalarTower_toModuleCat (R := k) (ι := Fin (d i))
      (ModuleCat.of (Matrix (Fin (d i)) (Fin (d i)) k) Xi)
  Module.finrank k (MatrixModCat.toModuleCatObj k Xi (0 : Fin (d i)))

/-- Helper for Exercise 18-18.2-6: in the split matrix-product case, the determinant-product
normal form identifies the Morita corner multiplicities. -/
lemma splitMatrixProduct_cornerMultiplicity_eq_of_detProductEq_notCharZero
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    (hnonCharZero : ¬ CharZero k)
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
    (hβ_surj : Function.Surjective β)
    (hprod : ∀ g : G,
      ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ splitMatrixProductCornerMultiplicity (k := k) (d := d) M i) :
            Polynomial k) =
        ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ splitMatrixProductCornerMultiplicity (k := k) (d := d) N i) :
            Polynomial k)) :
    ∀ i : Fin n,
      splitMatrixProductCornerMultiplicity (k := k) (d := d) M i =
        splitMatrixProductCornerMultiplicity (k := k) (d := d) N i := by
  -- The split primitive-projector separators have trace one, so the determinant-product
  -- separator theorem can compare the corner exponents directly.
  exact
    splitMatrixProduct_multiplicity_eq_of_detProductEq_notCharZero
      (k := k) (G := G) (d := d) hnonCharZero β hβ_surj
      (fun i ↦ splitMatrixProductCornerMultiplicity (k := k) (d := d) M i)
      (fun i ↦ splitMatrixProductCornerMultiplicity (k := k) (d := d) N i)
      hprod

/-- Helper for Exercise 18-18.2-6: equal split Morita corner multiplicities reconstruct a
linear equivalence over the whole split product of matrix algebras. -/
theorem nonempty_linearEquiv_of_splitMatrixProduct_cornerMultiplicity_eq
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    (hmult : ∀ i : Fin n,
      splitMatrixProductCornerMultiplicity (k := k) (d := d) M i =
        splitMatrixProductCornerMultiplicity (k := k) (d := d) N i) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) k] N) := by
  -- Route correction: instead of rebuilding the coordinate equivalences by hand, rewrite the
  -- split multiplicity invariant into the corner-finrank hypothesis of the existing Morita API.
  refine
    nonempty_linearEquiv_of_corner_finrank_eq_on_pi_matrix_divisionRing
      (k := k) (D := fun _ : Fin n ↦ k) (d := d) (M := M) (N := N) ?_
  intro i
  -- The split multiplicity definition is exactly the `D := k` corner finrank normal form.
  simpa [splitMatrixProductCornerMultiplicity] using hmult i

/-- Helper for Exercise 18-18.2-6: in the split matrix-product case, the determinant-product
normal form and the trace-one separators identify the Morita corner multiplicities, hence the
two modules are linearly equivalent over the split product algebra. -/
theorem nonempty_linearEquiv_of_splitMatrixProduct_detProduct_eq_notCharZero
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) N]
    (hnonCharZero : ¬ CharZero k)
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) k)
    (hβ_surj : Function.Surjective β)
    (hprod : ∀ g : G,
      ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ splitMatrixProductCornerMultiplicity (k := k) (d := d) M i) :
            Polynomial k) =
        ((∏ i,
          (((-(wedderburnFactorRepresentation
            (k := k) (G := G) (D := fun _ : Fin n ↦ k) (d := d) β i g)).charpoly.reverse :
              Polynomial k)) ^ splitMatrixProductCornerMultiplicity (k := k) (d := d) N i) :
            Polynomial k)) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) k] N) := by
  have hmult : ∀ i : Fin n,
      splitMatrixProductCornerMultiplicity (k := k) (d := d) M i =
        splitMatrixProductCornerMultiplicity (k := k) (d := d) N i :=
    splitMatrixProduct_cornerMultiplicity_eq_of_detProductEq_notCharZero
      (k := k) (G := G) (d := d) hnonCharZero β hβ_surj hprod
  -- The determinant-product comparison supplies exactly the split Morita multiplicities needed
  -- by the product reconstruction theorem.
  exact
    nonempty_linearEquiv_of_splitMatrixProduct_cornerMultiplicity_eq
      (k := k) (d := d) (M := M) (N := N) hmult

/-- Helper for Exercise 18-18.2-6: determinant equality on all monoid-algebra lifts to a split
Wedderburn product gives equality of the primitive projector determinant polynomials, hence a
linear equivalence of the two product-algebra modules. -/
theorem nonempty_linearEquiv_of_splitProduct_det_eq_on_monoidAlgebra
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β)
    (hdetβ_all : ∀ t : MonoidAlgebra k G,
      (-DistribSMul.toLinearMap k M (β t)).charpoly.reverse =
      (-DistribSMul.toLinearMap k N (β t)).charpoly.reverse) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  have hprojectorLifts :=
    splitProduct_primitiveProjector_lifts_of_surjective
      (k := k) (G := G) (D := D) (d := d) β hβ_surj
  have hprojector : ∀ i : Fin n,
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := by
    intro i
    rcases hprojectorLifts i with ⟨t, ht⟩
    -- A chosen lift of the primitive product projector lets the all-lifts determinant identity
    -- specialize to the exact ambient-projector comparison needed by the Morita criterion.
    calc
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k M (β t)).charpoly.reverse := by
          rw [ht]
      _ = (-DistribSMul.toLinearMap k N (β t)).charpoly.reverse := hdetβ_all t
      _ = (-DistribSMul.toLinearMap k N
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := by
          rw [ht]
  -- Matching primitive projector determinant polynomials reconstruct the split-product module.
  exact
    nonempty_linearEquiv_of_ambient_projector_reverseCharpoly_eq_on_pi_matrix_divisionRing
      (k := k) (D := D) (d := d) (M := M) (N := N) hprojector

/-- Helper for Exercise 18-18.2-6: determinant equality on chosen monoid-algebra lifts of the
primitive product projectors is the exact split-product input needed for Morita reconstruction. -/
theorem nonempty_linearEquiv_of_splitProduct_projector_lift_det_eq
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type*}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hprojectorLiftDet : ∀ i : Fin n, ∃ t : MonoidAlgebra k G,
      β t =
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j)) ∧
      (-DistribSMul.toLinearMap k M (β t)).charpoly.reverse =
        (-DistribSMul.toLinearMap k N (β t)).charpoly.reverse) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  have hprojector : ∀ i : Fin n,
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N
          (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
            Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := by
    intro i
    rcases hprojectorLiftDet i with ⟨t, ht, hdet⟩
    -- Rewrite the chosen lift to the primitive projector on both sides of the determinant
    -- comparison.
    calc
      (-DistribSMul.toLinearMap k M
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse =
        (-DistribSMul.toLinearMap k M (β t)).charpoly.reverse := by
          rw [ht]
      _ = (-DistribSMul.toLinearMap k N (β t)).charpoly.reverse := hdet
      _ = (-DistribSMul.toLinearMap k N
        (Pi.single i (Matrix.single (0 : Fin (d i)) (0 : Fin (d i)) (1 : D i)) :
          Π j : Fin n, Matrix (Fin (d j)) (Fin (d j)) (D j))).charpoly.reverse := by
          rw [ht]
  -- The ambient primitive-projector criterion now supplies the product-algebra equivalence.
  exact
    nonempty_linearEquiv_of_ambient_projector_reverseCharpoly_eq_on_pi_matrix_divisionRing
      (k := k) (D := D) (d := d) (M := M) (N := N) hprojector

/-- Helper for Exercise 18-18.2-6: a `k`-linear equivalence that intertwines the images of all
monoid generators under a surjective algebra map is automatically linear over the target
algebra. -/
lemma nonempty_linearEquiv_of_surjective_generator_intertwining
    {B : Type*} [Ring B] [Algebra k B]
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    [AddCommGroup Y] [Module k Y] [Module B Y] [IsScalarTower k B Y]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ_surj : Function.Surjective β)
    (e : X ≃ₗ[k] Y)
    (hgen : ∀ g : G, ∀ x : X,
      e ((β (MonoidAlgebra.of k G g)) • x) =
        (β (MonoidAlgebra.of k G g)) • e x) :
    Nonempty (X ≃ₗ[B] Y) := by
  have hall : ∀ t : MonoidAlgebra k G, ∀ x : X, e ((β t) • x) = (β t) • e x := by
    intro t
    -- Extend the generator intertwining relation linearly across the monoid algebra.
    refine MonoidAlgebra.induction_on
      (p := fun t : MonoidAlgebra k G ↦ ∀ x : X, e ((β t) • x) = (β t) • e x)
      t ?_ ?_ ?_
    · intro g x
      exact hgen g x
    · intro a b ha hb x
      simp [add_smul, ha, hb]
    · intro r a ha x
      simp [ha]
  have hmap_smul : ∀ (b : B) (x : X), e (b • x) = b • e x := by
    intro b x
    rcases hβ_surj b with ⟨t, ht⟩
    -- Surjectivity lets the monoid-algebra intertwining relation cover every scalar in `B`.
    rw [← ht]
    exact hall t x
  let eB : X ≃ₗ[B] Y :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := hmap_smul }
  exact ⟨eB⟩

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: an algebra map from `k[G]` to an acting algebra gives the
restricted monoid representation whose generator action is scalar multiplication by the image of
the generator. -/
noncomputable def representationOfAlgHomAction
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    (β : MonoidAlgebra k G →ₐ[k] B) :
    Representation k G X :=
  (DistribMulAction.toModuleEnd k X).comp
    (β.toMonoidHom.comp (MonoidAlgebra.of k G))

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: the restricted representation acts on a generator by the
original scalar action through the algebra map. -/
lemma representationOfAlgHomAction_apply
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    (β : MonoidAlgebra k G →ₐ[k] B) (g : G) :
    representationOfAlgHomAction (k := k) (G := G) β g =
      DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g)) := by
  -- The definition is chosen so that generator evaluation is already in scalar-action normal form.
  rfl

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: determinant equality for the scalar actions supplied by an
algebra map is exactly determinant equality for the two restricted monoid representations. -/
lemma representationOfAlgHomAction_det_eq_of_generator_det_eq
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module B X] [IsScalarTower k B X]
    [Module B Y] [IsScalarTower k B Y]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hdetβ : ∀ g : G,
      (-DistribSMul.toLinearMap k X (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k Y (β (MonoidAlgebra.of k G g))).charpoly.reverse) :
    ∀ g : G,
      (-(representationOfAlgHomAction (k := k) (G := G) (X := X) β g)).charpoly.reverse =
        (-(representationOfAlgHomAction (k := k) (G := G) (X := Y) β g)).charpoly.reverse := by
  intro g
  -- Put both restricted representation actions into the scalar-action normal form consumed by
  -- the determinant hypothesis.
  simpa [representationOfAlgHomAction_apply] using hdetβ g

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: determinant equality for actions supplied by algebra
homomorphisms is determinant equality for the corresponding restricted monoid actions. -/
lemma representationOfAlgHomAction_det_eq_of_lifted_algHom_det_eq
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    [Module B X] [IsScalarTower k B X]
    [Module B Y] [IsScalarTower k B Y]
    (φX : B →ₐ[k] Module.End k X) (φY : B →ₐ[k] Module.End k Y)
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hsmulX : ∀ a : B, ∀ x : X, a • x = (φX a) x)
    (hsmulY : ∀ a : B, ∀ y : Y, a • y = (φY a) y)
    (hdetβ : ∀ g : G,
      (-φX (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φY (β (MonoidAlgebra.of k G g))).charpoly.reverse) :
    ∀ g : G,
      (-(representationOfAlgHomAction (k := k) (G := G) (X := X) β g)).charpoly.reverse =
        (-(representationOfAlgHomAction (k := k) (G := G) (X := Y) β g)).charpoly.reverse := by
  intro g
  have hX :
      representationOfAlgHomAction (k := k) (G := G) (X := X) β g =
        φX (β (MonoidAlgebra.of k G g)) := by
    ext x
    -- The restricted action is scalar multiplication by `β g`, which is the supplied action map.
    simpa [representationOfAlgHomAction_apply] using
      hsmulX (β (MonoidAlgebra.of k G g)) x
  have hY :
      representationOfAlgHomAction (k := k) (G := G) (X := Y) β g =
        φY (β (MonoidAlgebra.of k G g)) := by
    ext y
    -- The same scalar-action normalization applies to the second module.
    simpa [representationOfAlgHomAction_apply] using
      hsmulY (β (MonoidAlgebra.of k G g)) y
  -- Rewrite the restricted representations to the algebra-hom actions and use the hypothesis.
  simpa [hX, hY] using hdetβ g

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: an equivalence linear over a lifted image algebra already
intertwines the original monoid representations after restriction along the lift. -/
lemma nonempty_equiv_of_lifted_linearEquiv
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    [AddCommGroup Y] [Module k Y] [Module B Y] [IsScalarTower k B Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (φX : B →ₐ[k] Module.End k X) (φY : B →ₐ[k] Module.End k Y)
    (liftι : MonoidAlgebra k G →ₐ[k] B)
    (hφX : φX.comp liftι = ρ.asAlgebraHom)
    (hφY : φY.comp liftι = ρ'.asAlgebraHom)
    (hsmulX : ∀ a : B, ∀ x : X, a • x = (φX a) x)
    (hsmulY : ∀ a : B, ∀ y : Y, a • y = (φY a) y)
    (e : X ≃ₗ[B] Y) :
    Nonempty (ρ.Equiv ρ') := by
  -- Restrict the lifted-algebra equivalence to `k`, then check the intertwining identity on
  -- monoid generators by rewriting both actions through the same lift.
  refine ⟨Representation.Equiv.mk (e.restrictScalars k) ?_⟩
  intro g
  ext x
  have hρg : ρ g = φX (liftι (MonoidAlgebra.of k G g)) := by
    -- Evaluate the compatibility of the left lifted action on the generator `g`.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k X ↦ f (MonoidAlgebra.of k G g))
        hφX.symm
  have hρ'g : ρ' g = φY (liftι (MonoidAlgebra.of k G g)) := by
    -- The right lifted action has the same generator-level compatibility.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k Y ↦ f (MonoidAlgebra.of k G g))
        hφY.symm
  -- `B`-linearity for the lifted generator is exactly the representation intertwining relation.
  calc
    e (ρ g x) = e (liftι (MonoidAlgebra.of k G g) • x) := by rw [hρg, ← hsmulX]
    _ = liftι (MonoidAlgebra.of k G g) • e x := e.map_smul _ x
    _ = (φY (liftι (MonoidAlgebra.of k G g))) (e x) := by rw [hsmulY]
    _ = ρ' g (e x) := by rw [← hρ'g]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: the algebra homomorphism attached to the restricted
representation is scalar multiplication by the image of the monoid-algebra element. -/
lemma representationOfAlgHomAction_asAlgebraHom_apply
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    (β : MonoidAlgebra k G →ₐ[k] B) (t : MonoidAlgebra k G) :
    (representationOfAlgHomAction (k := k) (G := G) β).asAlgebraHom t =
      DistribSMul.toLinearMap k X (β t) := by
  -- Extend the generator computation linearly across `k[G]`.
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra k G ↦
      (representationOfAlgHomAction (k := k) (G := G) β).asAlgebraHom t =
        DistribSMul.toLinearMap k X (β t))
    t ?_ ?_ ?_
  · intro g
    rw [Representation.asAlgebraHom_of]
    exact representationOfAlgHomAction_apply (k := k) (G := G) β g
  · intro a b ha hb
    ext x
    simp [ha, hb, add_smul]
  · intro r a ha
    ext x
    simp [ha]

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: semisimplicity of a module over the target algebra descends to
the restricted monoid representation along a surjective algebra map. -/
lemma isSemisimpleRepresentation_of_surjective_algHomAction
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ_surj : Function.Surjective β)
    (hX : IsSemisimpleModule B X) :
    IsSemisimpleRepresentation
      (representationOfAlgHomAction (k := k) (G := G) β : Representation k G X) := by
  let φX : B →ₐ[k] Module.End k X := Algebra.lsmul k k X
  have hφX :
      φX.comp β =
        (representationOfAlgHomAction (k := k) (G := G) β :
          Representation k G X).asAlgebraHom := by
    apply AlgHom.ext
    intro t
    apply LinearMap.ext
    intro x
    -- The descended algebra action and the restricted representation both act by `β t`.
    change (β t) • x =
      ((representationOfAlgHomAction (k := k) (G := G) β :
          Representation k G X).asAlgebraHom t) x
    rw [representationOfAlgHomAction_asAlgebraHom_apply (k := k) (G := G) β t]
    rfl
  have hX' : (let _ : Module B X := Module.compHom X φX.toRingHom
      IsSemisimpleModule B X) := by
    -- The action induced by `Algebra.lsmul` is the original `B`-module action.
    simpa [φX, Algebra.lsmul] using hX
  exact
    isSemisimpleRepresentation_of_surjective_lift
      (A := B)
      (ρ := (representationOfAlgHomAction (k := k) (G := G) β : Representation k G X))
      φX β hφX hβ_surj hX'

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: an equivalence of the two restricted representations upgrades
to a linear equivalence over the target algebra when the restricting algebra map is surjective. -/
lemma nonempty_linearEquiv_of_algHomAction_equiv
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [Module B X] [IsScalarTower k B X]
    [AddCommGroup Y] [Module k Y] [Module B Y] [IsScalarTower k B Y]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ_surj : Function.Surjective β)
    (hrep :
      Nonempty
        ((representationOfAlgHomAction (k := k) (G := G) (X := X) β).Equiv
          (representationOfAlgHomAction (k := k) (G := G) (X := Y) β))) :
    Nonempty (X ≃ₗ[B] Y) := by
  rcases hrep with ⟨eρ⟩
  have hgen : ∀ g : G, ∀ x : X,
      eρ.toLinearEquiv ((β (MonoidAlgebra.of k G g)) • x) =
        (β (MonoidAlgebra.of k G g)) • eρ.toLinearEquiv x := by
    intro g x
    -- The representation equivalence gives generator intertwining after both actions are put in
    -- scalar-action normal form.
    have hcomm :=
      congrArg (fun f : X →ₗ[k] Y ↦ f x) (eρ.toIntertwiningMap.2 g)
    simpa [representationOfAlgHomAction_apply, LinearMap.comp_apply] using hcomm
  -- Surjectivity extends generator intertwining from `β(k[G])` to every target-algebra element.
  exact
    nonempty_linearEquiv_of_surjective_generator_intertwining
      (k := k) (G := G) β hβ_surj eρ.toLinearEquiv hgen

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: a surjective algebra map to a semisimple target makes the
restricted monoid actions semisimple and transports the generator determinant hypothesis to those
restricted representations. -/
lemma semisimpleAlgHomAction_detEq_of_surjective
    {B M N : Type*} [Ring B] [Algebra k B] [IsSemisimpleRing B]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module B M] [IsScalarTower k B M]
    [AddCommGroup N] [Module k N] [FiniteDimensional k N]
    [Module B N] [IsScalarTower k B N]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ_surj : Function.Surjective β)
    (hdetβ : ∀ g : G,
      (-DistribSMul.toLinearMap k M (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N (β (MonoidAlgebra.of k G g))).charpoly.reverse) :
    IsSemisimpleRepresentation
        (representationOfAlgHomAction (k := k) (G := G) (X := M) β) ∧
      IsSemisimpleRepresentation
        (representationOfAlgHomAction (k := k) (G := G) (X := N) β) ∧
      ∀ g : G,
        (-(representationOfAlgHomAction (k := k) (G := G) (X := M) β g)).charpoly.reverse =
          (-(representationOfAlgHomAction (k := k) (G := G) (X := N) β g)).charpoly.reverse := by
  -- Over the semisimple image algebra every target module is semisimple; surjectivity carries
  -- that semisimplicity back to the restricted `k[G]`-representations.
  have hM : IsSemisimpleModule B M := by
    infer_instance
  have hN : IsSemisimpleModule B N := by
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · exact
      isSemisimpleRepresentation_of_surjective_algHomAction
        (k := k) (G := G) (X := M) β hβ_surj hM
  · exact
      isSemisimpleRepresentation_of_surjective_algHomAction
        (k := k) (G := G) (X := N) β hβ_surj hN
  · -- The restricted representation has precisely the scalar action used in the determinant
    -- hypothesis, so the determinant-polynomial identity transfers without extra transport.
    exact
      representationOfAlgHomAction_det_eq_of_generator_det_eq
        (k := k) (G := G) (X := M) (Y := N) β hdetβ

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: determinant equality on the original representations transfers
to determinant equality on generator lifts through any factored algebra action. -/
lemma det_eq_on_lifted_generators_of_comp_eq_support
    {B X Y : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (φX : B →ₐ[k] Module.End k X) (φY : B →ₐ[k] Module.End k Y)
    (liftι : MonoidAlgebra k G →ₐ[k] B)
    (hφX : φX.comp liftι = ρ.asAlgebraHom)
    (hφY : φY.comp liftι = ρ'.asAlgebraHom)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    ∀ g : G,
      (-φX (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φY (liftι (MonoidAlgebra.of k G g))).charpoly.reverse := by
  intro g
  have hXg : φX (liftι (MonoidAlgebra.of k G g)) = ρ g := by
    -- Evaluate the left factorization identity at the generator `g`.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k X ↦ f (MonoidAlgebra.of k G g))
        hφX
  have hYg : φY (liftι (MonoidAlgebra.of k G g)) = ρ' g := by
    -- The same generator-level computation holds for the right factored action.
    simpa [AlgHom.comp_apply, Representation.asAlgebraHom_of] using
      congrArg
        (fun f : MonoidAlgebra k G →ₐ[k] Module.End k Y ↦ f (MonoidAlgebra.of k G g))
        hφY
  -- Rewrite both lifted generator actions back to the original representation actions.
  calc
    (-φX (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-ρ g).charpoly.reverse := by
          exact congrArg (fun f : Module.End k X ↦ (-f).charpoly.reverse) hXg
    _ = (-ρ' g).charpoly.reverse := hdetG g
    _ = (-φY (liftι (MonoidAlgebra.of k G g))).charpoly.reverse := by
          exact (congrArg (fun f : Module.End k Y ↦ (-f).charpoly.reverse) hYg).symm

/-- Helper for Exercise 18-18.2-6: in characteristic zero, a finite-image linear equivalence
criterion restricts back to an equivalence of the original monoid representations. -/
theorem nonempty_equiv_of_generator_det_eq_on_finite_semisimple_image_charZero_support
    [CharZero k]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r y ↦ by
      change (φW (algebraMap k A r)) y = r • y
      simpa using congrArg (fun f : Module.End k W ↦ f y) (φW.commutes r)
  obtain ⟨eQ⟩ :=
    nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_charZero
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hV hW hdetG
  -- Restrict the finite-image linear equivalence along the surjective lift to recover an
  -- equivalence of the original monoid representations.
  exact
    nonempty_equiv_of_lifted_linearEquiv
      (B := A) (X := V) (Y := W) (ρ := ρ) (ρ' := ρ')
      φV φW liftι hφV hφW (fun a x ↦ rfl) (fun a y ↦ rfl) eQ

/-- Helper for Exercise 18-18.2-6: the determinant-polynomial hypothesis transports to the
common-kernel quotient actions on every lifted monoid generator. -/
lemma commonKernelQuotient_det_eq_on_lifted_generators_support
    {X Y : Type w}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (g : G) :
    (-(commonKernelLeftAction (k := k) (G := G) ρ ρ'
        ((commonKernelProjection (k := k) (G := G) ρ ρ') (MonoidAlgebra.of k G g)))).charpoly.reverse =
      (-(commonKernelRightAction (k := k) (G := G) ρ ρ'
        ((commonKernelProjection (k := k) (G := G) ρ ρ') (MonoidAlgebra.of k G g)))).charpoly.reverse := by
  -- Specialize the generic lifted-generator bridge to the canonical common-kernel quotient
  -- factorization on the two sides.
  exact
    det_eq_on_lifted_generators_of_comp_eq_support
      (k := k) (G := G) (X := X) (Y := Y) (ρ := ρ) (ρ' := ρ')
      (commonKernelLeftAction (k := k) (G := G) ρ ρ')
      (commonKernelRightAction (k := k) (G := G) ρ ρ')
      (commonKernelProjection (k := k) (G := G) ρ ρ')
      (commonKernelLeftAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ'))
      (commonKernelRightAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ'))
      hdet g

/-- Helper for Exercise 18-18.2-6: in the same-universe case, equality of semisimple
Grothendieck classes gives the source-facing representation equivalence. -/
theorem nonempty_equiv_of_sameUniverse_grothendieckClass_eq
    {K : Type w} [Field K]
    {H : Type w} [Monoid H]
    {X Y : Type w}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    {ρ : Representation K H X} {ρ' : Representation K H Y}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hclass : [FDRep.of ρ]₀ = [FDRep.of ρ']₀) :
    Nonempty (ρ.Equiv ρ') := by
  -- The Chapter `14` semisimple criterion turns class equality into a bundled `FDRep`
  -- isomorphism.
  rcases
    (finiteRepGrothendieckClass_eq_iff_nonempty_iso_of_isSemisimple
      (E := FDRep.of ρ) (E' := FDRep.of ρ') hρ hρ').mp hclass with
    ⟨e⟩
  -- Convert the bundled `FDRep` isomorphism back to the source-facing representation equivalence.
  exact
    ⟨Representation.equivOfIso
      ((CategoryTheory.forget₂ (FDRep K H) (Rep K H)).mapIso e)⟩

/-- Helper for Exercise 18-18.2-6: in characteristic zero, the determinant-polynomial criterion
follows by passing to the finite common image algebra and using the trace separator there. -/
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_charZero
    [CharZero k]
    {X Y : Type w}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  let A := commonKernelQuotient (k := k) (G := G) ρ ρ'
  let φX : A →ₐ[k] Module.End k X :=
    commonKernelLeftAction (k := k) (G := G) ρ ρ'
  let φY : A →ₐ[k] Module.End k Y :=
    commonKernelRightAction (k := k) (G := G) ρ ρ'
  let liftι : MonoidAlgebra k G →ₐ[k] A :=
    commonKernelProjection (k := k) (G := G) ρ ρ'
  let _ : Module.Finite k A :=
    commonKernelQuotient_finite (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing A :=
    commonKernelQuotient_isSemisimpleRing
      (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  have hφX : φX.comp liftι = ρ.asAlgebraHom := by
    -- The left common-kernel action composes with the quotient projection to the original action.
    simpa [A, φX, liftι] using
      commonKernelLeftAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  have hφY : φY.comp liftι = ρ'.asAlgebraHom := by
    -- The same quotient factorization holds for the second representation.
    simpa [A, φY, liftι] using
      commonKernelRightAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  have hlift : Function.Surjective liftι := by
    -- The quotient projection onto the common image algebra is surjective.
    simpa [A, liftι, commonKernelProjection, commonKernelQuotient, commonKernelIdeal] using
      (Ideal.Quotient.mkₐ_surjective k
        (commonKernelIdeal (k := k) (G := G) ρ ρ'))
  have hX : let _ : Module A X := Module.compHom X φX.toRingHom
      IsSemisimpleModule A X := by
    -- Semisimplicity descends from the original representation to the left quotient module.
    simpa [A, φX] using
      commonKernelQuotient_left_isSemisimpleModule
        (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  have hY : let _ : Module A Y := Module.compHom Y φY.toRingHom
      IsSemisimpleModule A Y := by
    -- The right quotient module has the same semisimplicity descent.
    simpa [A, φY] using
      commonKernelQuotient_right_isSemisimpleModule
        (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  -- The characteristic-zero finite-image theorem now applies to the common quotient action.
  exact
    nonempty_equiv_of_generator_det_eq_on_finite_semisimple_image_charZero_support
      (A := A) (ρ := ρ) (ρ' := ρ') φX φY liftι hφX hφY hlift hX hY hdet

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: the module structure induced by an algebra homomorphism into
endomorphisms is automatically compatible with the ambient `k`-module structure. -/
lemma isScalarTower_compHom_toModuleEnd
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X]
    (φ : B →ₐ[k] Module.End k X) :
    let _ : Module B X := Module.compHom X φ.toRingHom
    IsScalarTower k B X := by
  let _ : Module B X := Module.compHom X φ.toRingHom
  -- The scalar-tower condition is exactly the algebra-hom commutation relation evaluated on
  -- vectors.
  exact
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := X) fun r x ↦ by
      change (φ (algebraMap k B r)) x = r • x
      exact congrArg (fun f : Module.End k X ↦ f x) (φ.commutes r)

omit [Module.Finite k A] [IsSemisimpleRing A] [FiniteDimensional k V]
  [FiniteDimensional k W] in
/-- Helper for Exercise 18-18.2-6: under the `Module.compHom` action, scalar multiplication by
an element of the acting algebra is evaluation of the corresponding endomorphism. -/
lemma compHom_toModuleEnd_smul
    {B X : Type*} [Ring B] [Algebra k B]
    [AddCommGroup X] [Module k X]
    (φ : B →ₐ[k] Module.End k X) :
    let _ : Module B X := Module.compHom X φ.toRingHom
    ∀ a : B, ∀ x : X, a • x = (φ a) x := by
  -- This is the definitional action used by `Module.compHom`.
  dsimp
  intro a x
  rfl

omit [Module.Finite k A] [IsSemisimpleRing A] in
/-- Helper for Exercise 18-18.2-6: reversed characteristic polynomials commute with arbitrary
field scalar extension. -/
lemma negCharpolyReverse_baseChange_eq_map
    {K : Type*} [Field K] [Algebra k K]
    {X : Type*} [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    (f : Module.End k X) :
    ((-(LinearMap.baseChange K f)).charpoly.reverse : Polynomial K) =
      Polynomial.map (algebraMap k K) (((-f).charpoly.reverse : Polynomial k)) := by
  -- Normalize the negated upstairs endomorphism to the base change of the downstairs negation,
  -- then use the standard characteristic-polynomial base-change formula.
  rw [show -(LinearMap.baseChange K f) = LinearMap.baseChange K (-f) by simp]
  rw [LinearMap.charpoly_baseChange]
  symm
  exact
    polynomial_reverse_map (f := algebraMap k K)
      (hf := FaithfulSMul.algebraMap_injective k K) ((-f).charpoly)

omit [Module.Finite k A] [IsSemisimpleRing A] in
/-- Helper for Exercise 18-18.2-6: an equivalence of representations gives equality of the
reversed characteristic polynomials for every monoid-algebra element. -/
lemma negCharpolyReverse_asAlgebraHom_eq_of_representationEquiv
    {X Y : Type*}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {σ : Representation k G Y}
    (e : ρ.Equiv σ) (t : MonoidAlgebra k G) :
    (-(ρ.asAlgebraHom t)).charpoly.reverse =
      (-(σ.asAlgebraHom t)).charpoly.reverse := by
  have hcomm :
      e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom t) =
        (σ.asAlgebraHom t).comp e.toLinearEquiv.toLinearMap := by
    -- Prove the monoid-algebra intertwining relation here so the bridge is universe-polymorphic
    -- enough for tensor-product scalar extensions.
    refine MonoidAlgebra.induction_on
      (p := fun t : MonoidAlgebra k G ↦
        e.toLinearEquiv.toLinearMap.comp (ρ.asAlgebraHom t) =
          (σ.asAlgebraHom t).comp e.toLinearEquiv.toLinearMap)
      t ?_ ?_ ?_
    · intro g
      ext x
      simpa [Representation.asAlgebraHom_of, LinearMap.comp_apply] using
        congrArg (fun f : X →ₗ[k] Y ↦ f x) (e.toIntertwiningMap.2 g)
    · intro x y hx hy
      simp [hx, hy, LinearMap.add_comp, LinearMap.comp_add]
    · intro r x hx
      simp [hx, LinearMap.smul_comp, LinearMap.comp_smul]
  have hconj_pos : e.toLinearEquiv.conj (ρ.asAlgebraHom t) = σ.asAlgebraHom t := by
    apply LinearMap.ext
    intro y
    -- The representation equivalence intertwines the whole monoid-algebra action by linearity.
    have hy := LinearMap.congr_fun hcomm (e.toLinearEquiv.symm y)
    calc
      (e.toLinearEquiv.conj (ρ.asAlgebraHom t)) y =
          e.toLinearEquiv ((ρ.asAlgebraHom t) (e.toLinearEquiv.symm y)) := by
            simp [LinearEquiv.conj_apply_apply]
      _ = (σ.asAlgebraHom t) (e.toLinearEquiv (e.toLinearEquiv.symm y)) := by
            simpa [LinearMap.comp_apply] using hy
      _ = (σ.asAlgebraHom t) y := by
            rw [e.toLinearEquiv.apply_symm_apply y]
  have hconj_neg : e.toLinearEquiv.conj (-(ρ.asAlgebraHom t)) = -(σ.asAlgebraHom t) := by
    -- Move negation through conjugation before applying characteristic-polynomial invariance.
    calc
      e.toLinearEquiv.conj (-(ρ.asAlgebraHom t)) =
          -(e.toLinearEquiv.conj (ρ.asAlgebraHom t)) := by
            exact map_neg e.toLinearEquiv.conj (ρ.asAlgebraHom t)
      _ = -(σ.asAlgebraHom t) := by rw [hconj_pos]
  have hchar : (-(σ.asAlgebraHom t)).charpoly = (-(ρ.asAlgebraHom t)).charpoly := by
    calc
      (-(σ.asAlgebraHom t)).charpoly =
          (e.toLinearEquiv.conj (-(ρ.asAlgebraHom t))).charpoly := by rw [hconj_neg]
      _ = (-(ρ.asAlgebraHom t)).charpoly := by
            exact LinearEquiv.charpoly_conj e.toLinearEquiv (-(ρ.asAlgebraHom t))
  exact congrArg Polynomial.reverse hchar.symm

omit [Module.Finite k A] [IsSemisimpleRing A] in
/-- Helper for Exercise 18-18.2-6: after scalar extension, generator determinant equality
still controls every exterior-power trace on the extended monoid algebra. -/
lemma exteriorTrace_eq_asAlgebraHom_scalarExtensionMonoid_of_det_eq
    {K : Type} [Field K] [Algebra k K]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    ∀ n (t : MonoidAlgebra K G),
      LinearMap.trace K (⋀[K]^n (K ⊗[k] V))
          (Representation.asAlgebraHom
            ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).nthExteriorPower n)
            t) =
        LinearMap.trace K (⋀[K]^n (K ⊗[k] W))
          (Representation.asAlgebraHom
            ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ').nthExteriorPower n)
            t) := by
  intro n t
  -- First transport the determinant-polynomial identity to the extension field.
  have hdetK :
      ∀ g : G,
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse =
          (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse :=
    detOneAddPolynomialEq_scalarExtensionMonoid
      (k := k) (G := G) (K := K) (ρ := ρ) (ρ' := ρ') hdet
  -- The existing exterior-power character bridge then extends this equality linearly over
  -- `K[G]`.
  exact
    exteriorTrace_eq_asAlgebraHom_of_generator_det_eq
      (k := K) (G := G) (V := K ⊗[k] V) (W := K ⊗[k] W)
      (ρ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
      (ρ' := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ')
      hdetK n t

/-- Helper for Exercise 18-18.2-6: after scalar extension, the generator determinant identity
also gives ordinary trace equality on every element of the extended monoid algebra. -/
lemma trace_eq_asAlgebraHom_scalarExtensionMonoid_of_det_eq
    {K : Type} [Field K] [Algebra k K]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (t : MonoidAlgebra K G) :
    LinearMap.trace K (K ⊗[k] V)
        ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom t) =
      LinearMap.trace K (K ⊗[k] W)
        ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ').asAlgebraHom t) := by
  -- First push the determinant identity to the extension field.
  have hdetK :
      ∀ g : G,
        (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ g)).charpoly.reverse =
          (-(scalarExtensionMonoid (k := k) (G := G) (K := K) ρ' g)).charpoly.reverse :=
    detOneAddPolynomialEq_scalarExtensionMonoid
      (k := k) (G := G) (K := K) (ρ := ρ) (ρ' := ρ') hdet
  -- Then read off the coefficient-one character relation and extend it linearly over `K[G]`.
  have hchar :
      (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).character =
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ').character :=
    character_eq_of_det_one_add_polynomial_eq
      (ρ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
      (ρ' := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ')
      hdetK
  exact
    trace_eq_asAlgebraHom_of_character_eq
      (ρ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
      (ρ' := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ')
      hchar t

omit [Module.Finite k A] [IsSemisimpleRing A] in
/-- Helper for Exercise 18-18.2-6: a scalar-extended equivalence of the restricted
representations reflects determinant equality to every element of the finite image algebra. -/
lemma target_det_eq_of_scalarExtended_restricted_equiv
    {K : Type} [Field K] [Algebra k K]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hK :
      Nonempty ((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).Equiv
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ'))) :
    ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse := by
  rcases hK with ⟨eK⟩
  intro a
  rcases hlift a with ⟨t, rfl⟩
  have hVt : ρ.asAlgebraHom t = φV (liftι t) := by
    simpa [AlgHom.comp_apply] using
      (congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f t) hφV).symm
  have hWt : ρ'.asAlgebraHom t = φW (liftι t) := by
    simpa [AlgHom.comp_apply] using
      (congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f t) hφW).symm
  have hKpoly :
      (-(LinearMap.baseChange K (φV (liftι t)))).charpoly.reverse =
        (-(LinearMap.baseChange K (φW (liftι t)))).charpoly.reverse := by
    -- Transport the upstairs equivalence from monoid generators to the chosen monoid-algebra
    -- lift, then normalize both scalar-extended actions to base changes of the target actions.
    have hpoly :=
      negCharpolyReverse_asAlgebraHom_eq_of_representationEquiv
        (k := K) (G := G)
        (ρ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
        (σ := scalarExtensionMonoid (k := k) (G := G) (K := K) ρ') eK
        ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) t)
    simpa [scalarExtensionMonoid_asAlgebraHom_mapRange (k := k) (G := G) (K := K) ρ t,
      scalarExtensionMonoid_asAlgebraHom_mapRange (k := k) (G := G) (K := K) ρ' t,
      hVt, hWt] using hpoly
  have hmap :
      Polynomial.map (algebraMap k K) (((-φV (liftι t)).charpoly.reverse : Polynomial k)) =
        Polynomial.map (algebraMap k K)
          (((-φW (liftι t)).charpoly.reverse : Polynomial k)) := by
    -- Rewrite the upstairs equality as equality of coefficientwise images of downstairs
    -- determinant polynomials.
    calc
      Polynomial.map (algebraMap k K) (((-φV (liftι t)).charpoly.reverse : Polynomial k)) =
          (-(LinearMap.baseChange K (φV (liftι t)))).charpoly.reverse := by
            symm
            exact negCharpolyReverse_baseChange_eq_map (k := k) (K := K) (φV (liftι t))
      _ = (-(LinearMap.baseChange K (φW (liftι t)))).charpoly.reverse := hKpoly
      _ = Polynomial.map (algebraMap k K)
          (((-φW (liftι t)).charpoly.reverse : Polynomial k)) := by
            exact negCharpolyReverse_baseChange_eq_map (k := k) (K := K) (φW (liftι t))
  -- Injectivity of the coefficient field map reflects the determinant equality back to `k`.
  exact
    (Polynomial.map_injective (algebraMap k K)
      (FaithfulSMul.algebraMap_injective k K)) hmap


section SemisimplificationAndBrauerNesbitt

open scoped Matrix.Module

-- ===== Lemma A: semisimplification preserving det-on-all =====

/-- The algebra hom of the restricted representation `subrepresentation σ W le_comap`, applied to
`t`, is the restriction of `σ.asAlgebraHom t` to `W`. -/
private lemma subrepresentation_asAlgebraHom_coe
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X]
    (σ : Representation K G X) (W : Submodule K X)
    (le_comap : ∀ g, W ≤ W.comap (σ g))
    (t : MonoidAlgebra K G) (v : W) :
    ((Representation.subrepresentation σ W le_comap).asAlgebraHom t v : X)
      = σ.asAlgebraHom t (v : X) := by
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra K G ↦
      ((Representation.subrepresentation σ W le_comap).asAlgebraHom t v : X)
        = σ.asAlgebraHom t (v : X)) t ?_ ?_ ?_
  · intro g
    simp [Representation.subrepresentation_apply, LinearMap.restrict_coe_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  · intro r a ha
    simp only [map_smul, LinearMap.smul_apply, SetLike.val_smul, ha]

/-- If `m` is a `K[G]`-submodule of `X` (with the action coming from `σ`), the restricted
representation on `W := m.restrictScalars K` has its `asModule` `K[G]`-linearly isomorphic to `m`. -/
private def subrepresentation_asModule_equiv
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X]
    (σ : Representation K G X)
    [inst : Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    (hsmul : ∀ (r : MonoidAlgebra K G) (x : X), r • x = σ.asAlgebraHom r x)
    (m : Submodule (MonoidAlgebra K G) X)
    (le_comap : ∀ g, (m.restrictScalars K) ≤ (m.restrictScalars K).comap (σ g)) :
    (Representation.subrepresentation σ (m.restrictScalars K) le_comap).asModule
      ≃ₗ[MonoidAlgebra K G] m :=
  { toFun := fun v =>
      ⟨((show (↥(m.restrictScalars K)) from v) : X),
        (Submodule.restrictScalars_mem K m _).1 (show (↥(m.restrictScalars K)) from v).2⟩
    invFun := fun u =>
      (show (↥(m.restrictScalars K)) from
        ⟨(u : X), (Submodule.restrictScalars_mem K m _).2 u.2⟩)
    left_inv := fun v => Subtype.ext rfl
    right_inv := fun u => Subtype.ext rfl
    map_add' := fun a b => Subtype.ext rfl
    map_smul' := fun r v => by
      apply Subtype.ext
      show ((Representation.subrepresentation σ (m.restrictScalars K) le_comap).asAlgebraHom r
          (show (↥(m.restrictScalars K)) from v) : X)
          = (r • ((show (↥(m.restrictScalars K)) from v) : X) : X)
      rw [hsmul]
      exact subrepresentation_asAlgebraHom_coe σ (m.restrictScalars K) le_comap r
        (show (↥(m.restrictScalars K)) from v) }

set_option backward.isDefEq.respectTransparency false in
/-- If `m` is a simple `K[G]`-submodule of `X` (with the action coming from `σ`), then the
restricted representation on `m.restrictScalars K` is semisimple. -/
private lemma subrepresentation_isSemisimpleRepresentation_of_isSimpleModule
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X]
    (σ : Representation K G X)
    [inst : Module (MonoidAlgebra K G) X] [IsScalarTower K (MonoidAlgebra K G) X]
    (hsmul : ∀ (r : MonoidAlgebra K G) (x : X), r • x = σ.asAlgebraHom r x)
    (m : Submodule (MonoidAlgebra K G) X) [IsSimpleModule (MonoidAlgebra K G) m]
    (le_comap : ∀ g, (m.restrictScalars K) ≤ (m.restrictScalars K).comap (σ g)) :
    IsSemisimpleRepresentation
      (Representation.subrepresentation σ (m.restrictScalars K) le_comap) := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI : IsSimpleModule (MonoidAlgebra K G)
      (Representation.subrepresentation σ (m.restrictScalars K) le_comap).asModule :=
    IsSimpleModule.congr (subrepresentation_asModule_equiv σ hsmul m le_comap)
  infer_instance

/-- The algebra hom of a product representation is the `prodMap` of the two algebra homs. -/
private lemma prod_asAlgebraHom
    {K : Type} [Field K] {X Y : Type w}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (ρ : Representation K G X) (τ : Representation K G Y) (t : MonoidAlgebra K G) :
    (ρ.prod τ).asAlgebraHom t = (ρ.asAlgebraHom t).prodMap (τ.asAlgebraHom t) := by
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra K G ↦
      (ρ.prod τ).asAlgebraHom t = (ρ.asAlgebraHom t).prodMap (τ.asAlgebraHom t)) t ?_ ?_ ?_
  · intro g
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of,
      Representation.asAlgebraHom_of]
    rfl
  · intro a b ha hb
    rw [map_add, map_add, map_add, ha, hb]
    ext x <;> simp [LinearMap.prodMap_apply]
  · intro r a ha
    rw [map_smul, map_smul, map_smul, ha]
    ext x <;> simp [LinearMap.prodMap_apply]

/-- A product of two semisimple modules over a ring is semisimple. -/
private lemma isSemisimpleModule_prod
    {R : Type*} [Ring R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSemisimpleModule R M] [IsSemisimpleModule R N] :
    IsSemisimpleModule R (M × N) := by
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun b : Bool => if b then LinearMap.range (LinearMap.inr R M N)
      else LinearMap.range (LinearMap.inl R M N)) ?_ ?_
  · intro b
    cases b with
    | false => exact IsSemisimpleModule.range (LinearMap.inl R M N)
    | true => exact IsSemisimpleModule.range (LinearMap.inr R M N)
  · rw [iSup_bool_eq]
    simp only [if_true]
    rw [sup_comm]
    exact LinearMap.sup_range_inl_inr

/-- The `asModule` of a product representation is `K[G]`-linearly isomorphic to the product of the
two `asModule`s. -/
private def prod_asModule_equiv
    {K : Type} [Field K] {X Y : Type w}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (ρ : Representation K G X) (τ : Representation K G Y) :
    (ρ.prod τ).asModule ≃ₗ[MonoidAlgebra K G] ρ.asModule × τ.asModule :=
  { toFun := fun v => (show X × Y from v)
    invFun := fun v => (show (ρ.prod τ).asModule from v)
    left_inv := fun v => rfl
    right_inv := fun v => rfl
    map_add' := fun a b => rfl
    map_smul' := fun r v => by
      show ((ρ.prod τ).asAlgebraHom r (show X × Y from v) : X × Y)
          = (ρ.asAlgebraHom r (show X from v.1), τ.asAlgebraHom r (show Y from v.2))
      rw [prod_asAlgebraHom]
      rfl }

set_option backward.isDefEq.respectTransparency false in
/-- A product of two semisimple representations is semisimple. -/
private lemma prod_isSemisimpleRepresentation
    {K : Type} [Field K] {X Y : Type w}
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (ρ : Representation K G X) (τ : Representation K G Y)
    (hρ : IsSemisimpleRepresentation ρ) (hτ : IsSemisimpleRepresentation τ) :
    IsSemisimpleRepresentation (ρ.prod τ) := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hρ hτ ⊢
  haveI : IsSemisimpleModule (MonoidAlgebra K G) (ρ.asModule × τ.asModule) :=
    isSemisimpleModule_prod
  exact IsSemisimpleModule.congr (prod_asModule_equiv ρ τ)

/-- The reversed characteristic polynomial of the negated `asAlgebraHom` of a product
representation factors as the product over the two constituents, for every `t : K[G]`. -/
private lemma negCharpolyReverse_prod_asAlgebraHom
    {K : Type} [Field K] {X Y : Type w}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (ρ : Representation K G X) (τ : Representation K G Y) (t : MonoidAlgebra K G) :
    (-(ρ.prod τ).asAlgebraHom t).charpoly.reverse
      = (-(ρ.asAlgebraHom t)).charpoly.reverse * (-(τ.asAlgebraHom t)).charpoly.reverse := by
  have hneg : -(ρ.prod τ).asAlgebraHom t
      = (-(ρ.asAlgebraHom t)).prodMap (-(τ.asAlgebraHom t)) := by
    rw [prod_asAlgebraHom]
    apply LinearMap.ext
    intro x
    cases x with
    | mk x y => ext <;> simp [LinearMap.prodMap_apply]
  rw [hneg, LinearMap.charpoly_prodMap, Polynomial.reverse_mul_of_domain]

/-- A `G`-invariant subspace is invariant under `σ.asAlgebraHom t` for every `t : K[G]`. -/
private lemma le_comap_asAlgebraHom
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X]
    (σ : Representation K G X) (W : Submodule K X)
    (le_comap : ∀ g, W ≤ W.comap (σ g)) (t : MonoidAlgebra K G) :
    W ≤ W.comap (σ.asAlgebraHom t) := by
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra K G ↦ W ≤ W.comap (σ.asAlgebraHom t)) t ?_ ?_ ?_
  · intro g
    rw [Representation.asAlgebraHom_of]
    exact le_comap g
  · intro a b ha hb x hx
    rw [Submodule.mem_comap, map_add, LinearMap.add_apply]
    exact W.add_mem (ha hx) (hb hx)
  · intro r a ha x hx
    rw [Submodule.mem_comap, map_smul, LinearMap.smul_apply]
    exact W.smul_mem r (ha hx)

/-- The `asAlgebraHom` of the quotient representation commutes with the canonical projection. -/
private lemma quotient_asAlgebraHom_mkQ
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X]
    (σ : Representation K G X) (W : Submodule K X)
    (le_comap : ∀ g, W ≤ W.comap (σ g)) (t : MonoidAlgebra K G) (x : X) :
    (Representation.quotient σ W le_comap).asAlgebraHom t (W.mkQ x)
      = W.mkQ (σ.asAlgebraHom t x) := by
  refine MonoidAlgebra.induction_on
    (p := fun t : MonoidAlgebra K G ↦
      (Representation.quotient σ W le_comap).asAlgebraHom t (W.mkQ x)
        = W.mkQ (σ.asAlgebraHom t x)) t ?_ ?_ ?_
  · intro g
    simp only [Representation.asAlgebraHom_of, Representation.quotient_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply]
  · intro a b ha hb
    rw [map_add, LinearMap.add_apply, ha, hb, map_add, LinearMap.add_apply, map_add]
  · intro r a ha
    rw [map_smul, LinearMap.smul_apply, ha, map_smul, LinearMap.smul_apply, map_smul]

/-- The reversed characteristic polynomial of `-(σ.asAlgebraHom t)` factors through a `G`-invariant
subspace `W` as the product over the restricted and quotient representations. -/
private lemma negCharpolyReverse_restrict_quotient_factor
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (σ : Representation K G X) (W : Submodule K X)
    (le_comap : ∀ g, W ≤ W.comap (σ g)) (t : MonoidAlgebra K G) :
    (-(σ.asAlgebraHom t)).charpoly.reverse
      = (-((Representation.subrepresentation σ W le_comap).asAlgebraHom t)).charpoly.reverse
        * (-((Representation.quotient σ W le_comap).asAlgebraHom t)).charpoly.reverse := by
  set f : X →ₗ[K] X := -(σ.asAlgebraHom t) with hf
  have hWf : W ≤ W.comap f := by
    intro x hx
    rw [Submodule.mem_comap, hf, LinearMap.neg_apply]
    exact W.neg_mem (Submodule.mem_comap.1 (le_comap_asAlgebraHom σ W le_comap t hx))
  -- Factor the charpoly through `W`.
  rw [Representation.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ f W hWf]
  -- Identify the restricted endomorphism with the negated restricted action.
  have hrestrict : f.restrict hWf
      = -((Representation.subrepresentation σ W le_comap).asAlgebraHom t) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, hf, LinearMap.neg_apply, LinearMap.neg_apply,
      Submodule.coe_neg, ← subrepresentation_asAlgebraHom_coe σ W le_comap t v]
  -- Identify the induced quotient endomorphism with the negated quotient action.
  have hquot : W.mapQ W f hWf
      = -((Representation.quotient σ W le_comap).asAlgebraHom t) := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.neg_apply]
    show (W.mapQ W f hWf) (W.mkQ x)
        = -((Representation.quotient σ W le_comap).asAlgebraHom t (W.mkQ x))
    rw [quotient_asAlgebraHom_mkQ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      hf, LinearMap.neg_apply, ← Submodule.Quotient.mk_neg]
  rw [hrestrict, hquot, Polynomial.reverse_mul_of_domain]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary form of Lemma A, set up for strong induction on `Module.finrank K X`. -/
private lemma exists_semisimple_aux
    {K : Type} [Field K] :
    ∀ (n : ℕ) (X : Type w) [AddCommGroup X] [Module K X] [FiniteDimensional K X]
      (σ : Representation K G X), Module.finrank K X = n →
      ∃ (Y : Type w) (_ : AddCommGroup Y) (_ : Module K Y) (_ : FiniteDimensional K Y)
        (τ : Representation K G Y), IsSemisimpleRepresentation τ ∧
        ∀ t : MonoidAlgebra K G,
          (-(σ.asAlgebraHom t)).charpoly.reverse = (-(τ.asAlgebraHom t)).charpoly.reverse := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro X _ _ _ σ hX
    by_cases hnt : Nontrivial X
    · -- Nontrivial case: split off a simple subrepresentation and recurse on the quotient.
      letI : Module (MonoidAlgebra K G) X := Module.compHom X σ.asAlgebraHom.toRingHom
      letI : IsScalarTower K (MonoidAlgebra K G) X :=
        IsScalarTower.of_algebraMap_smul (R := K) (A := MonoidAlgebra K G) (M := X) fun r x => by
          change (σ.asAlgebraHom (algebraMap K (MonoidAlgebra K G) r)) x = r • x
          rw [σ.asAlgebraHom.commutes r, Module.algebraMap_end_apply]
      haveI : IsArtinian (MonoidAlgebra K G) X :=
        isArtinian_of_tower K isArtinian_of_fg_of_artinian'
      have hsmul : ∀ (r : MonoidAlgebra K G) (x : X), r • x = σ.asAlgebraHom r x := fun r x => rfl
      -- Get a simple `K[G]`-submodule.
      obtain ⟨m, hm⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra K G) X)
      haveI hsimple : IsSimpleModule (MonoidAlgebra K G) m := (isSimpleModule_iff_isAtom).2 hm
      -- `W := m.restrictScalars K` is the underlying `K`-subspace; it is `G`-invariant.
      have le_comap_W : ∀ g, (m.restrictScalars K) ≤ (m.restrictScalars K).comap (σ g) := by
        intro g x hx
        rw [Submodule.restrictScalars_mem] at hx
        rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
        have hmem : (MonoidAlgebra.of K G g) • x ∈ m := m.smul_mem _ hx
        rwa [hsmul, Representation.asAlgebraHom_of] at hmem
      -- The restricted and quotient representations.
      let τW : Representation K G (m.restrictScalars K) :=
        Representation.subrepresentation σ (m.restrictScalars K) le_comap_W
      let τQ : Representation K G (X ⧸ m.restrictScalars K) :=
        Representation.quotient σ (m.restrictScalars K) le_comap_W
      -- `τW` is semisimple.
      have hτW_ss : IsSemisimpleRepresentation τW :=
        subrepresentation_isSemisimpleRepresentation_of_isSimpleModule σ hsmul m le_comap_W
      -- `W` is nonzero, so the quotient has strictly smaller dimension.
      have hWne : (m.restrictScalars K) ≠ ⊥ := by
        intro hcontra
        exact hm.1 ((Submodule.restrictScalars_eq_bot_iff (S := K) (R := MonoidAlgebra K G)
          (M := X) (p := m)).1 hcontra)
      haveI : Nontrivial (m.restrictScalars K) := Submodule.nontrivial_iff_ne_bot.mpr hWne
      have hdim : Module.finrank K (X ⧸ m.restrictScalars K) < n := by
        have hsum := Submodule.finrank_quotient_add_finrank (m.restrictScalars K)
        have hpos : 0 < Module.finrank K (m.restrictScalars K) := Module.finrank_pos
        omega
      -- Recurse on the quotient.
      obtain ⟨YQ, _, _, _, τQ', hτQ'_ss, hdetQ⟩ :=
        IH (Module.finrank K (X ⧸ m.restrictScalars K)) hdim (X ⧸ m.restrictScalars K) τQ rfl
      -- Assemble the answer as a product.
      refine ⟨(m.restrictScalars K) × YQ, inferInstance, inferInstance, inferInstance,
        τW.prod τQ', ?_, ?_⟩
      · -- Semisimplicity of the product.
        exact prod_isSemisimpleRepresentation τW τQ' hτW_ss hτQ'_ss
      · -- The det-on-all identity.
        intro t
        rw [negCharpolyReverse_restrict_quotient_factor σ (m.restrictScalars K) le_comap_W t,
          negCharpolyReverse_prod_asAlgebraHom τW τQ' t, hdetQ t]
    · -- Trivial case: `σ` is already semisimple (the carrier is subsingleton).
      rw [not_nontrivial_iff_subsingleton] at hnt
      refine ⟨X, inferInstance, inferInstance, inferInstance, σ, ?_, fun t => rfl⟩
      rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
      haveI : Subsingleton σ.asModule := hnt
      rw [isSemisimpleModule_iff]
      exact Subsingleton.instComplementedLattice

lemma exists_semisimple_negCharpolyReverse_asAlgebraHom_eq
    {K : Type} [Field K] {X : Type w}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    (σ : Representation K G X) :
    ∃ (Y : Type w) (_ : AddCommGroup Y) (_ : Module K Y) (_ : FiniteDimensional K Y)
      (τ : Representation K G Y), IsSemisimpleRepresentation τ ∧
      ∀ t : MonoidAlgebra K G,
        (-(σ.asAlgebraHom t)).charpoly.reverse = (-(τ.asAlgebraHom t)).charpoly.reverse :=
  exists_semisimple_aux (Module.finrank K X) X σ rfl


-- ===== Lemma B: semisimple Brauer-Nesbitt over algebraically closed field =====
-- reindex conjugation: piCongrLeft' transports piMap to the reindexed piMap
lemma conj_piCongrLeft'_piMap {k : Type} [Field k]
    {ι ι' : Type*}
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    (e : ι ≃ ι')
    (f : ∀ i, E i →ₗ[k] E i) :
    (LinearEquiv.piCongrLeft' k E e).conj (LinearMap.piMap f)
      = LinearMap.piMap (fun i' : ι' => f (e.symm i')) := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply_apply]
  funext i'
  show (LinearEquiv.piCongrLeft' k E e) (LinearMap.piMap f
      ((LinearEquiv.piCongrLeft' k E e).symm x)) i' = (f (e.symm i')) (x i')
  rw [LinearEquiv.piCongrLeft'_apply]
  rw [LinearMap.coe_piMap, Pi.map_apply]
  congr 1
  show ((LinearEquiv.piCongrLeft' k E e).symm x) (e.symm i') = x i'
  exact Equiv.piCongrLeft'_symm_apply_apply E e x i'

-- conjugation under piOptionEquivProd
lemma conj_piOptionEquivProd_piMap {k : Type} [Field k]
    {ι : Type*}
    {E : Option ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    (f : ∀ i, E i →ₗ[k] E i) :
    (LinearEquiv.piOptionEquivProd k (M := E)).conj (LinearMap.piMap f)
      = (f none).prodMap (LinearMap.piMap (fun i : ι => f (some i))) := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply_apply]
  rcases x with ⟨x0, xr⟩
  apply Prod.ext
  · simp [LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd, LinearMap.piMap,
      LinearMap.prodMap_apply]
  · funext i
    simp [LinearEquiv.piOptionEquivProd, Equiv.piOptionEquivProd, LinearMap.piMap,
      LinearMap.prodMap_apply]

/-- charpoly of a finite block-diagonal endomorphism is the product of the block charpolys. -/
lemma charpoly_piMap {k : Type} [Field k]
    {ι : Type} [Fintype ι]
    {E : ι → Type w} [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
    [∀ i, Module.Free k (E i)] [∀ i, Module.Finite k (E i)]
    (f : ∀ i, E i →ₗ[k] E i) :
    (LinearMap.piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  -- Induct over the finite index type, quantifying over the family and its block maps.
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (E : α → Type w) [∀ i, AddCommGroup (E i)] [∀ i, Module k (E i)]
      [∀ i, Module.Free k (E i)] [∀ i, Module.Finite k (E i)]
      (f : ∀ i, E i →ₗ[k] E i),
      (LinearMap.piMap f).charpoly = ∏ i, (f i).charpoly
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · -- reindexing along an equivalence of index types
      intro α β _ e hα E _ _ _ _ f
      letI : Fintype α := Fintype.ofEquiv β e.symm
      -- transport the β-product to the α-product along `e.symm : β ≃ α`
      have hconj := conj_piCongrLeft'_piMap (k := k) (E := E) e.symm f
      calc
        (LinearMap.piMap f).charpoly
            = ((LinearEquiv.piCongrLeft' k E e.symm).conj (LinearMap.piMap f)).charpoly := by
              rw [LinearEquiv.charpoly_conj]
        _ = (LinearMap.piMap (fun i : α => f (e.symm.symm i))).charpoly := by rw [hconj]
        _ = ∏ i : α, (f (e.symm.symm i)).charpoly :=
              hα (fun i : α => E (e.symm.symm i)) (fun i : α => f (e.symm.symm i))
        _ = ∏ i : β, (f i).charpoly := by
              rw [Equiv.symm_symm]
              exact Fintype.prod_equiv e _ _ (fun _ => rfl)
    · -- empty index: the product is the trivial module, every endo has charpoly 1
      intro E _ _ _ _ f
      rw [Finset.prod_of_isEmpty]
      have hsub : Subsingleton (∀ i : PEmpty, E i) := ⟨fun a b => funext fun i => i.elim⟩
      have hf0 : LinearMap.piMap f = 0 := by
        apply LinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      rw [hf0, LinearMap.charpoly_zero]
      have hfin : Module.finrank k (∀ i : PEmpty, E i) = 0 :=
        Module.finrank_zero_of_subsingleton
      rw [hfin, pow_zero]
    · -- option index: split off the `none` block
      intro α _ hα E _ _ _ _ f
      have hconj := conj_piOptionEquivProd_piMap (k := k) (E := E) f
      calc
        (LinearMap.piMap f).charpoly
            = ((LinearEquiv.piOptionEquivProd k (M := E)).conj
                (LinearMap.piMap f)).charpoly := by
              rw [LinearEquiv.charpoly_conj]
        _ = ((f none).prodMap (LinearMap.piMap (fun i : α => f (some i)))).charpoly := by
              rw [hconj]
        _ = (f none).charpoly * (LinearMap.piMap (fun i : α => f (some i))).charpoly :=
              LinearMap.charpoly_prodMap _ _
        _ = (f none).charpoly * ∏ i : α, (f (some i)).charpoly := by
              rw [hα (fun i : α => E (some i)) (fun i : α => f (some i))]
        _ = ∏ i : Option α, (f i).charpoly := by
              rw [Fintype.prod_option]
  exact hP E f

/-- A `Matrix n n k`-linear equivalence preserves the charpoly of the `k`-linear endomorphism
given by the scalar action of a matrix `a`. -/
lemma charpoly_matrix_action_congr {k : Type} [Field k]
    {n : Type} [Fintype n] [DecidableEq n]
    {Y Z : Type w}
    [AddCommGroup Y] [Module (Matrix n n k) Y] [Module k Y] [FiniteDimensional k Y]
    [IsScalarTower k (Matrix n n k) Y]
    [AddCommGroup Z] [Module (Matrix n n k) Z] [Module k Z] [FiniteDimensional k Z]
    [IsScalarTower k (Matrix n n k) Z]
    (e : Y ≃ₗ[Matrix n n k] Z) (a : Matrix n n k) :
    (DistribSMul.toLinearMap k Y a).charpoly = (DistribSMul.toLinearMap k Z a).charpoly := by
  have hconj :
      (e.restrictScalars k).conj (DistribSMul.toLinearMap k Y a)
        = DistribSMul.toLinearMap k Z a := by
    apply LinearMap.ext
    intro z
    rw [LinearEquiv.conj_apply_apply]
    show e (a • (e.symm z)) = a • z
    rw [e.map_smul]
    rw [e.apply_symm_apply]
  rw [← hconj, LinearEquiv.charpoly_conj]

/-- Swap conjugation: the matrix `a` acting on `Fin m → (Fin μ → k)` corresponds, after swapping
the two product coordinates, to `μ` independent copies of `a` acting on `Fin m → k`. -/
lemma conj_piComm_matrix_action {k : Type} [Field k] {m μ : ℕ}
    (a : Matrix (Fin m) (Fin m) k) :
    let sw : (Fin m → (Fin μ → k)) ≃ₗ[k] (Fin μ → (Fin m → k)) :=
      { Equiv.piComm (fun (_ : Fin m) (_ : Fin μ) => k) with
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    sw.conj (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a)
      = LinearMap.piMap (fun _ : Fin μ => DistribSMul.toLinearMap k (Fin m → k) a) := by
  intro sw
  apply LinearMap.ext
  intro w
  rw [LinearEquiv.conj_apply_apply]
  funext p
  rw [LinearMap.coe_piMap, Pi.map_apply]
  -- Both sides: evaluate the matrix action coordinatewise.
  show (sw (a • (sw.symm w))) p = DistribSMul.toLinearMap k (Fin m → k) a (w p)
  funext i
  show (a • (sw.symm w)) i p = (a • (w p)) i
  rw [Matrix.Module.smul_apply, Matrix.Module.smul_apply]
  -- ∑ j a i j • (sw.symm w j) p  =  ∑ j a i j • (w p j)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

/-- The charpoly of the matrix action of `a` on the "thick" standard module `Fin m → (Fin μ → k)`
is the charpoly of `a` on the standard module `Fin m → k` raised to the power `μ`. -/
lemma charpoly_matrix_action_thick {k : Type} [Field k] {m μ : ℕ}
    (a : Matrix (Fin m) (Fin m) k) :
    (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a).charpoly =
      (DistribSMul.toLinearMap k (Fin m → k) a).charpoly ^ μ := by
  classical
  let sw : (Fin m → (Fin μ → k)) ≃ₗ[k] (Fin μ → (Fin m → k)) :=
    { Equiv.piComm (fun (_ : Fin m) (_ : Fin μ) => k) with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hconj := conj_piComm_matrix_action (k := k) (m := m) (μ := μ) a
  calc
    (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a).charpoly
        = (sw.conj (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a)).charpoly := by
          rw [LinearEquiv.charpoly_conj]
    _ = (LinearMap.piMap
          (fun _ : Fin μ => DistribSMul.toLinearMap k (Fin m → k) a)).charpoly := by
          rw [hconj]
    _ = ∏ _i : Fin μ, (DistribSMul.toLinearMap k (Fin m → k) a).charpoly :=
          charpoly_piMap (fun _ : Fin μ => DistribSMul.toLinearMap k (Fin m → k) a)
    _ = (DistribSMul.toLinearMap k (Fin m → k) a).charpoly ^ μ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Universe-polymorphic variant of `charpoly_matrix_action_congr`: a `Matrix n n k`-linear
equivalence between modules in possibly different universes preserves the charpoly of the
`k`-linear endomorphism given by the scalar action of a matrix `a`.  (The proof is identical to
`charpoly_matrix_action_congr`; only the universe constraint `Y Z : Type w` is relaxed, which is
needed to bridge the corner module `↥C : Type w` with the `Type 0` standard module.) -/
private lemma charpoly_matrix_action_congr' {k : Type} [Field k]
    {n : Type} [Fintype n] [DecidableEq n]
    {Y : Type w} {Z : Type v}
    [AddCommGroup Y] [Module (Matrix n n k) Y] [Module k Y] [FiniteDimensional k Y]
    [IsScalarTower k (Matrix n n k) Y]
    [AddCommGroup Z] [Module (Matrix n n k) Z] [Module k Z] [FiniteDimensional k Z]
    [IsScalarTower k (Matrix n n k) Z]
    (e : Y ≃ₗ[Matrix n n k] Z) (a : Matrix n n k) :
    (DistribSMul.toLinearMap k Y a).charpoly = (DistribSMul.toLinearMap k Z a).charpoly := by
  have hconj :
      (e.restrictScalars k).conj (DistribSMul.toLinearMap k Y a)
        = DistribSMul.toLinearMap k Z a := by
    apply LinearMap.ext
    intro z
    rw [LinearEquiv.conj_apply_apply]
    show e (a • (e.symm z)) = a • z
    rw [e.map_smul]
    rw [e.apply_symm_apply]
  rw [← hconj, LinearEquiv.charpoly_conj]

open Matrix MatrixModCat in
/-- The Morita isomorphism `Y ≃ₗ[Mₘ(k)] (Fin m → (Eₒₒ • Y))`, built with the *ambient*
`k`-module structure on `Y` (rather than the `Module.compHom` one used in the Mathlib statement
of `toModuleCatFromModuleCatLinearEquiv`).  Keeping the ambient `Module k Y` makes the corner
submodule `MatrixModCat.toModuleCatObj k (ModuleCat.of _ Y) 0` literally the one appearing in
`charpoly_matrix_action_eq_pow_standard`.  The construction copies Mathlib's
`toModuleCatFromModuleCatLinearEquiv` (only `Matrix`-linearity and the `single` matrices are
used; the `k`-module structure enters merely in naming the codomain submodule). -/
private def moritaIsoAmbient
    {k : Type} [Field k] {m : ℕ} [NeZero m]
    {Y : Type w} [AddCommGroup Y] [Module (Matrix (Fin m) (Fin m) k) Y]
    [Module k Y] [IsScalarTower k (Matrix (Fin m) (Fin m) k) Y] :
    (ModuleCat.of (Matrix (Fin m) (Fin m) k) Y) ≃ₗ[Matrix (Fin m) (Fin m) k]
      (Fin m → MatrixModCat.toModuleCatObj k
        (ModuleCat.of (Matrix (Fin m) (Fin m) k) Y) (0 : Fin m)) := by
  classical
  exact
    { toFun := fun mm i =>
        ⟨single (0 : Fin m) i (1 : k) • mm, single (0 : Fin m) i (1 : k) • mm, by
          simp [← SemigroupAction.mul_smul]⟩
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun x mm => funext fun i => Subtype.ext <| by
        simp only [← SemigroupAction.mul_smul, RingHom.id_apply, Module.smul_apply,
          AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, ← smul_assoc, ← Finset.sum_smul]
        congr
        ext i1 j1
        simp only [mul_apply, smul_single, smul_eq_mul, mul_one, sum_apply]
        rw [Finset.sum_eq_single_of_mem (a := i) (by simp)
          (fun b _ hb ↦ by simp [single, Ne.symm hb])]
        simp only [single_apply, and_true, ite_mul, one_mul, zero_mul]
        split_ifs with h <;> simp [h]
      invFun := fun v =>
        ∑ i, single i (0 : Fin m) (1 : k) •
          (v i : (ModuleCat.of (Matrix (Fin m) (Fin m) k) Y))
      left_inv := fun mm => by
        simp [← SemigroupAction.mul_smul, ← Finset.sum_smul, sum_single_one]
      right_inv := fun v => by
        dsimp
        ext i
        simp only [Finset.smul_sum]
        rw [Finset.sum_eq_single i (fun b _ hb ↦ by
          simp [← SemigroupAction.mul_smul, Matrix.single_mul_single_of_ne _ _ _ _ hb.symm])
          (by simp)]
        obtain ⟨y, hy⟩ := by simpa [-SetLike.coe_mem] using (v i).2
        simp [← SemigroupAction.mul_smul, ← hy] }

/-- DEEPEST SUB-LEMMA.
For a finite-dimensional `k`-module `Y` carrying a `Matrix (Fin m) (Fin m) k`-action compatible
with the `k`-action, the charpoly of the matrix `a` acting on `Y` is the charpoly of `a` acting
on the standard module `Fin m → k`, raised to the Morita corner dimension. -/
lemma charpoly_matrix_action_eq_pow_standard
    {k : Type} [Field k] {m : ℕ} [NeZero m]
    {Y : Type w} [AddCommGroup Y] [Module (Matrix (Fin m) (Fin m) k) Y]
    [Module k Y] [FiniteDimensional k Y]
    [IsScalarTower k (Matrix (Fin m) (Fin m) k) Y]
    (a : Matrix (Fin m) (Fin m) k) :
    (DistribSMul.toLinearMap k Y a).charpoly =
      (DistribSMul.toLinearMap k (Fin m → k) a).charpoly ^
        Module.finrank k (MatrixModCat.toModuleCatObj k
          (ModuleCat.of (Matrix (Fin m) (Fin m) k) Y) (0 : Fin m)) := by
  classical
  -- The Morita corner, with the *ambient* `k`-module structure (exactly the goal's corner).
  set C : Submodule k Y :=
    MatrixModCat.toModuleCatObj k (ModuleCat.of (Matrix (Fin m) (Fin m) k) Y) (0 : Fin m) with hC
  set μ : ℕ := Module.finrank k C with hμ
  haveI : FiniteDimensional k C := inferInstance
  -- A `k`-basis of the corner gives `C ≃ₗ[k] (Fin μ → k)`.
  let eC : C ≃ₗ[k] (Fin μ → k) := (Module.finBasis k C).equivFun
  -- Lift it coefficientwise to a matrix-linear equivalence on the standard module.
  let eThick : (Fin m → C) ≃ₗ[Matrix (Fin m) (Fin m) k] (Fin m → (Fin μ → k)) :=
    matrix_module_linearEquiv_of_linearEquiv (D := k) (n := Fin m) eC
  -- The Morita iso `Y ≃ₗ[Mₘ(k)] (Fin m → C)`.
  let eMorita : Y ≃ₗ[Matrix (Fin m) (Fin m) k] (Fin m → C) := moritaIsoAmbient (Y := Y)
  -- Step 1: transport the charpoly of the matrix action along the Morita iso.
  have h1 : (DistribSMul.toLinearMap k Y a).charpoly =
      (DistribSMul.toLinearMap k (Fin m → C) a).charpoly :=
    charpoly_matrix_action_congr' (n := Fin m) eMorita a
  -- Step 2: transport along the coefficientwise basis equivalence.
  have h2 : (DistribSMul.toLinearMap k (Fin m → C) a).charpoly =
      (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a).charpoly :=
    charpoly_matrix_action_congr' (n := Fin m) eThick a
  -- Step 3: the thick standard module gives the `μ`-th power.
  have h3 : (DistribSMul.toLinearMap k (Fin m → (Fin μ → k)) a).charpoly =
      (DistribSMul.toLinearMap k (Fin m → k) a).charpoly ^ μ :=
    charpoly_matrix_action_thick (m := m) (μ := μ) a
  rw [h1, h2, h3]

/-- Conjugating the full product-algebra action `b` through the central-idempotent decomposition
yields the block-diagonal endomorphism whose `i`-th block is the action of `b i` on the `i`-th
coordinate summand. -/
lemma conj_pi_idempotent_action {k : Type} [Field k]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, Ring (R i)] [∀ i, Algebra k (R i)]
    {M : Type w} [AddCommGroup M] [Module (Π i, R i) M] [Module k M]
    [FiniteDimensional k M] [IsScalarTower k (Π i, R i) M]
    (b : Π i, R i) :
    let ek := (pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).restrictScalars k
    ek.conj (DistribSMul.toLinearMap k M b) =
      LinearMap.piMap (fun i =>
        letI : Module (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
          pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
        letI : IsScalarTower k (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
          pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) i
        DistribSMul.toLinearMap k
          (pi_coordinate_submodule (k := k) (R := R) (M := M) i) (b i)) := by
  intro ek
  -- `ek.symm` is the reassembly map (two-sided inverse of the decomposition).
  have hsymm : ∀ x : (∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i),
      ((pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).symm x : M)
        = ∑ i : ι, (x i : M) := by
    intro x
    have hinv := pi_coordinate_decompose_reassemble_apply (k := k) (R := R) (M := M) x
    have heq : (pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).symm x
        = pi_coordinate_reassemble (k := k) (R := R) (M := M) x := by
      apply (pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact hinv.symm
    rw [heq]
    simp [pi_coordinate_reassemble]
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply_apply]
  funext j
  letI : Module (R j) (pi_coordinate_submodule (k := k) (R := R) (M := M) j) :=
    pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) j
  letI : IsScalarTower k (R j) (pi_coordinate_submodule (k := k) (R := R) (M := M) j) :=
    pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) j
  rw [LinearMap.coe_piMap, Pi.map_apply]
  apply Subtype.ext
  -- LHS j-th coordinate: `Pi.single j 1 • (b • ek.symm x)`.
  show ((pi_idempotent_linearEquiv (k := k) (R := R) (M := M))
        (b • (((pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).restrictScalars k).symm x)) j : M)
      = ((b j) • (x j) : pi_coordinate_submodule (k := k) (R := R) (M := M) j)
  have hek_symm :
      (((pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).restrictScalars k).symm x : M)
        = ∑ i : ι, (x i : M) := hsymm x
  have hcoord : ((pi_idempotent_linearEquiv (k := k) (R := R) (M := M))
        (b • (((pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).restrictScalars k).symm x)) j : M)
      = (Pi.single j (1 : R j)) •
          (b • (((pi_idempotent_linearEquiv (k := k) (R := R) (M := M)).restrictScalars k).symm x)) := by
    rfl
  rw [hcoord, hek_symm]
  -- RHS: factor action `(b j) • (x j)` is `Pi.single j (b j) • (x j : M)`.
  show (Pi.single j (1 : R j)) • (b • (∑ i : ι, (x i : M)))
      = (Pi.single j (b j)) • ((x j : M))
  rw [← mul_smul, Finset.smul_sum]
  rw [Finset.sum_eq_single j]
  · -- the `j`-th term: `(Pi.single j 1 * b) • x j = Pi.single j (b j) • x j`
    congr 1
    ext l
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  · -- off-diagonal terms vanish: `(Pi.single j 1 * b) • x i = 0` for `i ≠ j`
    intro i _ hij
    have hbi := pi_coordinate_submodule_action_factors_through_eval
      (k := k) (R := R) (M := M) i ((Pi.single j (1 : R j) : Π l, R l) * b) (x i)
    rw [hbi]
    have hzero : (((Pi.single j (1 : R j) : Π l, R l) * b) i) = 0 := by
      rw [Pi.mul_apply, Pi.single_eq_of_ne hij, zero_mul]
    rw [hzero]
    have : (Pi.single i (0 : R i) : Π l, R l) = 0 := by
      ext l; by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [this, zero_smul]
  · intro hi
    exact (hi (Finset.mem_univ j)).elim

/-- `reverse` commutes with a power of a polynomial over an integral domain. -/
lemma reverse_pow_of_domain {k : Type} [Field k] (p : Polynomial k) (n : ℕ) :
    (p ^ n).reverse = (p.reverse) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [← Polynomial.C_1, Polynomial.reverse_C]
  | succ m ih => rw [pow_succ, pow_succ, Polynomial.reverse_mul_of_domain, ih]

/-- `reverse` commutes with a finite product over a finset, over an integral domain. -/
lemma reverse_finset_prod {k : Type} [Field k] {ι : Type}
    (s : Finset ι) (p : ι → Polynomial k) :
    (∏ i ∈ s, p i).reverse = ∏ i ∈ s, (p i).reverse := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty]
      rw [← Polynomial.C_1, Polynomial.reverse_C]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Polynomial.reverse_mul_of_domain, ih]

/-- `reverse` commutes with a finite product of polynomial powers over an integral domain. -/
lemma reverse_prod_pow {k : Type} [Field k] {ι : Type} [Fintype ι]
    (p : ι → Polynomial k) (μ : ι → ℕ) :
    (∏ i, (p i) ^ (μ i)).reverse = ∏ i, ((p i).reverse) ^ (μ i) := by
  rw [reverse_finset_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact reverse_pow_of_domain (p i) (μ i)

/-- On the `i`-th coordinate summand of a module over a finite product of *matrix algebras*, the
*ambient* `k`-module structure (restriction of scalars from the product algebra) agrees with the
`Module.compHom` structure obtained by pulling the factor matrix action back along
`Matrix.scalar k`.  This is the `Module`-instance equality that lets the two Morita-corner
finranks (the one produced by `charpoly_matrix_action_eq_pow_standard` and the one fixed inside
`splitMatrixProductCornerMultiplicity`) match. -/
private lemma pi_coordinate_submodule_ambient_module_eq_compHom
    {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ι → ℕ}
    {M : Type w} [AddCommGroup M]
    [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M] [Module k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M] (i : ι) :
    letI _factor : Module (Matrix (Fin (d i)) (Fin (d i)) k)
        (pi_coordinate_submodule (k := k)
          (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i) :=
      pi_coordinate_submodule_factorModule (k := k)
        (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i
    (inferInstance : Module k (pi_coordinate_submodule (k := k)
        (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i)) =
      Module.compHom (pi_coordinate_submodule (k := k)
        (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i)
        (Matrix.scalar (α := k) (Fin (d i))) := by
  letI _factor : Module (Matrix (Fin (d i)) (Fin (d i)) k)
      (pi_coordinate_submodule (k := k)
        (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i) :=
    pi_coordinate_submodule_factorModule (k := k)
      (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i
  letI : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) k)
      (pi_coordinate_submodule (k := k)
        (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i) :=
    pi_coordinate_submodule_factor_isScalarTower (k := k)
      (R := fun j => Matrix (Fin (d j)) (Fin (d j)) k) (M := M) i
  apply Module.ext'
  intro r x
  -- The `compHom` action sends `r` to `Matrix.scalar r = algebraMap k (Mₘ k) r`, then acts;
  -- the scalar tower identifies that with the ambient `k`-action.
  show r • x = Matrix.scalar (Fin (d i)) r • x
  have hscalar : (Matrix.scalar (Fin (d i)) r : Matrix (Fin (d i)) (Fin (d i)) k)
      = algebraMap k (Matrix (Fin (d i)) (Fin (d i)) k) r := rfl
  rw [hscalar, algebraMap_smul]

/-- DET-PRODUCT-BRIDGE (no-reverse form).  For a finite-dimensional module `M` over a split
product of matrix algebras over `k`, the charpoly of the matrix action of a tuple `b` is the
product over the factors of the standard-factor charpoly raised to the Morita corner
multiplicity of `M`. -/
lemma charpoly_action_eq_prod_pow_corner {k : Type} [Field k]
    {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    {M : Type w} [AddCommGroup M]
    [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) k) M]
    (b : Π i, Matrix (Fin (d i)) (Fin (d i)) k) :
    (DistribSMul.toLinearMap k M b).charpoly =
      ∏ i, (DistribSMul.toLinearMap k (Fin (d i) → k) (b i)).charpoly ^
        splitMatrixProductCornerMultiplicity (k := k) (d := d) M i := by
  classical
  set R : Fin n → Type := fun i => Matrix (Fin (d i)) (Fin (d i)) k with hR
  -- Each coordinate summand is a finite-dimensional `k`-vector space.
  haveI hfd : ∀ i, FiniteDimensional k (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    fun i => FiniteDimensional.of_injective
      ((pi_coordinate_submodule (k := k) (R := R) (M := M) i).subtype.restrictScalars k)
      Subtype.val_injective
  haveI hfree : ∀ i, Module.Free k (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    fun i => inferInstance
  haveI hfin : ∀ i, Module.Finite k (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    fun i => inferInstance
  haveI hfinPi : FiniteDimensional k (∀ i, pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    inferInstance
  -- Step 1: conjugate through the central-idempotent decomposition.
  have hconj := conj_pi_idempotent_action (k := k) (R := R) (M := M) b
  have h1 : (DistribSMul.toLinearMap k M b).charpoly =
      (LinearMap.piMap (fun i =>
        letI : Module (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
          pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
        letI : IsScalarTower k (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
          pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) i
        DistribSMul.toLinearMap k
          (pi_coordinate_submodule (k := k) (R := R) (M := M) i) (b i))).charpoly := by
    rw [← hconj, LinearEquiv.charpoly_conj]
  rw [h1]
  -- Step 2: charpoly of the block-diagonal endomorphism is the product over the blocks.
  rw [charpoly_piMap]
  -- Step 3: each block charpoly is the standard charpoly raised to the corner multiplicity.
  apply Finset.prod_congr rfl
  intro i _
  letI : Module (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    pi_coordinate_submodule_factorModule (k := k) (R := R) (M := M) i
  letI : IsScalarTower k (R i) (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    pi_coordinate_submodule_factor_isScalarTower (k := k) (R := R) (M := M) i
  letI : FiniteDimensional k (pi_coordinate_submodule (k := k) (R := R) (M := M) i) :=
    FiniteDimensional.of_injective
      ((pi_coordinate_submodule (k := k) (R := R) (M := M) i).subtype.restrictScalars k)
      Subtype.val_injective
  -- The per-block charpoly equals the standard-factor charpoly raised to the Morita corner rank.
  rw [charpoly_matrix_action_eq_pow_standard
    (k := k) (m := d i) (Y := pi_coordinate_submodule (k := k) (R := R) (M := M) i) (b i)]
  -- It remains to match the corner finrank with `splitMatrixProductCornerMultiplicity`.
  congr 1
  rw [splitMatrixProductCornerMultiplicity]
  -- The two corners differ only in the chosen `Module k`-structure on the `i`-th summand:
  -- `charpoly_matrix_action_eq_pow_standard` uses the *ambient* restriction-of-scalars structure,
  -- while `splitMatrixProductCornerMultiplicity` uses the `Module.compHom` structure.  These
  -- structures agree, so the corner finranks coincide.
  convert rfl using 4 <;>
    first
      | exact pi_coordinate_submodule_ambient_module_eq_compHom (k := k) (d := d) (M := M) i
      | exact (pi_coordinate_submodule_ambient_module_eq_compHom (k := k) (d := d) (M := M) i).symm


variable {G : Type v} [Monoid G]

/-- DET-PRODUCT-BRIDGE (reverse form).  For a module `M` over a split product of matrix algebras
that restricts to a representation `ρ` with generator action `β (of g)`, the reversed determinant
polynomial of `-ρ g` is the product over the matrix factors of the reversed standard-factor
determinant polynomial, raised to the Morita corner multiplicity of `M`. -/
lemma negCharpolyReverse_action_eq_prod_wedderburnFactor_pow
    {K : Type} [Field K] {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    {M : Type w} [AddCommGroup M]
    [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) K) M]
    [Module K M] [FiniteDimensional K M]
    [IsScalarTower K (Π i, Matrix (Fin (d i)) (Fin (d i)) K) M]
    (β : MonoidAlgebra K G →ₐ[K] Π i, Matrix (Fin (d i)) (Fin (d i)) K)
    {ρ : Representation K G M}
    (g : G)
    (hβM : DistribSMul.toLinearMap K M (β (MonoidAlgebra.of K G g)) = ρ g) :
    (∏ i, ((-(wedderburnFactorRepresentation
      (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g)).charpoly.reverse) ^
        splitMatrixProductCornerMultiplicity (k := K) (d := d) M i) =
      (-ρ g).charpoly.reverse := by
  -- The negated action of `β (of g)` is the action of `-(β (of g))`.
  have hneg : (-DistribSMul.toLinearMap K M (β (MonoidAlgebra.of K G g))) =
      DistribSMul.toLinearMap K M (-(β (MonoidAlgebra.of K G g))) := by
    apply LinearMap.ext
    intro x
    show -(β (MonoidAlgebra.of K G g) • x) = (-(β (MonoidAlgebra.of K G g))) • x
    rw [neg_smul]
  have hcorner := charpoly_action_eq_prod_pow_corner (k := K) (d := d) (M := M)
    (-(β (MonoidAlgebra.of K G g)))
  -- Identify each standard-factor block with the (negated) Wedderburn factor representation.
  have hfactor : ∀ i : Fin n,
      (DistribSMul.toLinearMap K (Fin (d i) → K) ((-(β (MonoidAlgebra.of K G g))) i)) =
        -(wedderburnFactorRepresentation
          (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g) := by
    intro i
    rw [wedderburnFactorRepresentation_apply
      (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g]
    apply LinearMap.ext
    intro v
    show ((-(β (MonoidAlgebra.of K G g))) i) • v
        = -((β (MonoidAlgebra.of K G g) i) • v)
    rw [Pi.neg_apply, neg_smul]
  calc
    (∏ i, ((-(wedderburnFactorRepresentation
      (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g)).charpoly.reverse) ^
        splitMatrixProductCornerMultiplicity (k := K) (d := d) M i)
        = (∏ i, ((DistribSMul.toLinearMap K (Fin (d i) → K)
            ((-(β (MonoidAlgebra.of K G g))) i)).charpoly.reverse) ^
            splitMatrixProductCornerMultiplicity (k := K) (d := d) M i) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [hfactor i]
    _ = (∏ i, ((DistribSMul.toLinearMap K (Fin (d i) → K)
            ((-(β (MonoidAlgebra.of K G g))) i)).charpoly) ^
            splitMatrixProductCornerMultiplicity (k := K) (d := d) M i).reverse := by
          rw [reverse_prod_pow]
    _ = (DistribSMul.toLinearMap K M (-(β (MonoidAlgebra.of K G g)))).charpoly.reverse := by
          rw [← hcorner]
    _ = (-DistribSMul.toLinearMap K M (β (MonoidAlgebra.of K G g))).charpoly.reverse := by
          rw [hneg]
    _ = (-ρ g).charpoly.reverse := by rw [hβM]

-- LEMMA B: semisimple Brauer-Nesbitt over an ALGEBRAICALLY CLOSED field K of nonzero char.
-- Two semisimple representations with equal reversed charpoly of negated action on GROUP elements
-- are equivalent.
lemma nonempty_equiv_of_isSemisimple_det_eq_on_generators_isAlgClosed_notCharZero
    {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Type w}
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    {τ : Representation K G X} {τ' : Representation K G Y}
    (hτ : IsSemisimpleRepresentation τ) (hτ' : IsSemisimpleRepresentation τ')
    (hdet : ∀ g : G, (-τ g).charpoly.reverse = (-τ' g).charpoly.reverse)
    (hnc : ¬ CharZero K) :
    Nonempty (τ.Equiv τ') := by
  classical
  -- Common image algebra through which both representations factor.
  let A := commonKernelQuotient (k := K) (G := G) τ τ'
  let liftι : MonoidAlgebra K G →ₐ[K] A := commonKernelProjection (k := K) (G := G) τ τ'
  let φX : A →ₐ[K] Module.End K X := commonKernelLeftAction (k := K) (G := G) τ τ'
  let φY : A →ₐ[K] Module.End K Y := commonKernelRightAction (k := K) (G := G) τ τ'
  have hφX : φX.comp liftι = τ.asAlgebraHom :=
    commonKernelLeftAction_comp_projection (k := K) (G := G) (ρ := τ) (ρ' := τ')
  have hφY : φY.comp liftι = τ'.asAlgebraHom :=
    commonKernelRightAction_comp_projection (k := K) (G := G) (ρ := τ) (ρ' := τ')
  have hlift : Function.Surjective liftι :=
    Ideal.Quotient.mkₐ_surjective K _
  letI : Module.Finite K A := commonKernelQuotient_finite (ρ := τ) (ρ' := τ')
  letI : IsSemisimpleRing A := commonKernelQuotient_isSemisimpleRing (ρ := τ) (ρ' := τ') hτ hτ'
  letI : Module A X := Module.compHom X φX.toRingHom
  letI : Module A Y := Module.compHom Y φY.toRingHom
  have hsmulX : ∀ a : A, ∀ x : X, a • x = (φX a) x := fun a x => rfl
  have hsmulY : ∀ a : A, ∀ y : Y, a • y = (φY a) y := fun a y => rfl
  letI : IsScalarTower K A X :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := A) (M := X) fun r x => by
      change (φX (algebraMap K A r)) x = r • x
      rw [φX.commutes]; rfl
  letI : IsScalarTower K A Y :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := A) (M := Y) fun r y => by
      change (φY (algebraMap K A r)) y = r • y
      rw [φY.commutes]; rfl
  letI : FiniteDimensional K A := inferInstance
  -- Split the semisimple image algebra over the algebraically closed field.
  obtain ⟨n, d, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed (F := K) (R := A)
  letI : ∀ i, NeZero (d i) := hd
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) K
  letI : Module B X := Module.compHom X eA.symm.toRingHom
  letI : Module B Y := Module.compHom Y eA.symm.toRingHom
  letI : IsScalarTower K B X :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := B) (M := X) fun r x => by
      change (eA.symm ((algebraMap K B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := K) (A := A) r x
  letI : IsScalarTower K B Y :=
    IsScalarTower.of_algebraMap_smul (R := K) (A := B) (M := Y) fun r y => by
      change (eA.symm ((algebraMap K B) r)) • y = r • y
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := K) (A := A) r y
  let β : MonoidAlgebra K G →ₐ[K] B := eA.toAlgHom.comp liftι
  have hβ_surj : Function.Surjective β :=
    algEquiv_toAlgHom_comp_surjective (e := eA) (f := liftι) hlift
  -- On generators, the transported split action recovers the original representations.
  have hβX : ∀ g : G, DistribSMul.toLinearMap K X (β (MonoidAlgebra.of K G g)) = τ g := by
    intro g
    apply LinearMap.ext
    intro x
    have hliftX : φX (liftι (MonoidAlgebra.of K G g)) =
        τ.asAlgebraHom (MonoidAlgebra.of K G g) := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun f : MonoidAlgebra K G →ₐ[K] Module.End K X => f (MonoidAlgebra.of K G g)) hφX
    have hβt : eA.symm (β (MonoidAlgebra.of K G g)) = liftι (MonoidAlgebra.of K G g) := by
      simp [β]
    change (φX (eA.symm (β (MonoidAlgebra.of K G g)))) x = τ g x
    rw [hβt, hliftX]
    simp
  have hβY : ∀ g : G, DistribSMul.toLinearMap K Y (β (MonoidAlgebra.of K G g)) = τ' g := by
    intro g
    apply LinearMap.ext
    intro y
    have hliftY : φY (liftι (MonoidAlgebra.of K G g)) =
        τ'.asAlgebraHom (MonoidAlgebra.of K G g) := by
      simpa [AlgHom.comp_apply] using
        congrArg (fun f : MonoidAlgebra K G →ₐ[K] Module.End K Y => f (MonoidAlgebra.of K G g)) hφY
    have hβt : eA.symm (β (MonoidAlgebra.of K G g)) = liftι (MonoidAlgebra.of K G g) := by
      simp [β]
    change (φY (eA.symm (β (MonoidAlgebra.of K G g)))) y = τ' g y
    rw [hβt, hliftY]
    simp
  -- The determinant-product bridge: the corner multiplicities of `X` and `Y` carry the same
  -- product of standard-factor reversed determinants.
  have hprod : ∀ g : G,
      (∏ i, ((-(wedderburnFactorRepresentation
        (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g)).charpoly.reverse) ^
          splitMatrixProductCornerMultiplicity (k := K) (d := d) X i) =
      (∏ i, ((-(wedderburnFactorRepresentation
        (k := K) (G := G) (D := fun _ : Fin n => K) (d := d) β i g)).charpoly.reverse) ^
          splitMatrixProductCornerMultiplicity (k := K) (d := d) Y i) := by
    intro g
    rw [negCharpolyReverse_action_eq_prod_wedderburnFactor_pow (M := X) β g (hβX g),
      negCharpolyReverse_action_eq_prod_wedderburnFactor_pow (M := Y) β g (hβY g)]
    exact hdet g
  -- Equal corner multiplicities, hence a `B`-linear equivalence.
  have hmult : ∀ i : Fin n,
      splitMatrixProductCornerMultiplicity (k := K) (d := d) X i =
        splitMatrixProductCornerMultiplicity (k := K) (d := d) Y i :=
    splitMatrixProduct_cornerMultiplicity_eq_of_detProductEq_notCharZero
      (k := K) (G := G) (d := d) hnc β hβ_surj hprod
  obtain ⟨eB⟩ :=
    nonempty_linearEquiv_of_splitMatrixProduct_cornerMultiplicity_eq
      (k := K) (d := d) (M := X) (N := Y) hmult
  -- Transport the `B`-linear equivalence back to an `A`-linear one.
  have hmap_smul : ∀ (a : A) (x : X), eB (a • x) = a • eB x := by
    intro a x
    have hVsmul : (eA a : B) • x = a • x := by
      change (eA.symm (eA a)) • x = a • x
      simp
    have hWsmul : (eA a : B) • eB x = a • eB x := by
      change (eA.symm (eA a)) • eB x = a • eB x
      simp
    calc
      eB (a • x) = eB ((eA a : B) • x) := by rw [hVsmul]
      _ = (eA a : B) • eB x := eB.map_smul (eA a) x
      _ = a • eB x := hWsmul
  let eAlinear : X ≃ₗ[A] Y :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := hmap_smul }
  -- Restrict the lifted-algebra equivalence to a representation equivalence.
  exact
    nonempty_equiv_of_lifted_linearEquiv (B := A) (ρ := τ) (ρ' := τ')
      φX φY liftι hφX hφY hsmulX hsmulY eAlinear


end SemisimplificationAndBrauerNesbitt

/-- Helper for Exercise 18-18.2-6: the source-facing scalar-extension frontier.  After extending
the two restricted representations to the algebraic closure, the established trace, exterior-trace,
and generator-determinant identities should identify their simple multiplicities. -/
theorem nonempty_scalarExtensionMonoid_equiv_of_restricted_exterior_trace_notCharZero
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a))
    (hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t))
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    Nonempty
      ((scalarExtensionMonoid (k := k) (G := G) (K := AlgebraicClosure k) ρ).Equiv
        (scalarExtensionMonoid (k := k) (G := G) (K := AlgebraicClosure k) ρ')) := by
  -- Route correction: keep the reflection bridge out of this proof.  This helper is only the
  -- algebraic-closure Brauer-Nesbitt step: split the scalar-extended finite image algebra, use the
  -- finite-support trace separators to recover simple multiplicities from `htraceA`,
  -- `hexteriorTrace`, and `hdetG`, then assemble a representation equivalence upstairs.
  have hdetK :
      ∀ g : G,
        (-(scalarExtensionMonoid
          (k := k) (G := G) (K := AlgebraicClosure k) ρ g)).charpoly.reverse =
          (-(scalarExtensionMonoid
            (k := k) (G := G) (K := AlgebraicClosure k) ρ' g)).charpoly.reverse :=
    detOneAddPolynomialEq_scalarExtensionMonoid
      (k := k) (G := G) (K := AlgebraicClosure k) (ρ := ρ) (ρ' := ρ') hdetG
  have hexteriorTraceK :
      ∀ n (t : MonoidAlgebra (AlgebraicClosure k) G),
        LinearMap.trace (AlgebraicClosure k) (⋀[AlgebraicClosure k]^n
            (AlgebraicClosure k ⊗[k] V))
            (Representation.asAlgebraHom
              ((scalarExtensionMonoid
                (k := k) (G := G) (K := AlgebraicClosure k) ρ).nthExteriorPower n)
              t) =
          LinearMap.trace (AlgebraicClosure k) (⋀[AlgebraicClosure k]^n
            (AlgebraicClosure k ⊗[k] W))
            (Representation.asAlgebraHom
              ((scalarExtensionMonoid
                (k := k) (G := G) (K := AlgebraicClosure k) ρ').nthExteriorPower n)
              t) :=
    exteriorTrace_eq_asAlgebraHom_scalarExtensionMonoid_of_det_eq
      (k := k) (G := G) (K := AlgebraicClosure k) (ρ := ρ) (ρ' := ρ') hdetG
  have htraceK :
      ∀ t : MonoidAlgebra (AlgebraicClosure k) G,
        LinearMap.trace (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] V)
            ((scalarExtensionMonoid
              (k := k) (G := G) (K := AlgebraicClosure k) ρ).asAlgebraHom t) =
          LinearMap.trace (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] W)
            ((scalarExtensionMonoid
              (k := k) (G := G) (K := AlgebraicClosure k) ρ').asAlgebraHom t) := by
    -- The scalar-extended determinant identity also supplies the ordinary trace invariant needed
    -- by the finite simple-family separator.
    exact
      trace_eq_asAlgebraHom_scalarExtensionMonoid_of_det_eq
        (k := k) (G := G) (K := AlgebraicClosure k) (ρ := ρ) (ρ' := ρ') hdetG
  -- The proved prefix supplies the scalar-extended generator determinant identity `hdetK`.
  -- `AlgebraicClosure k` is algebraically closed and inherits the nonzero characteristic, so the
  -- semisimplification (which preserves every `det (1 + t T)`) plus the semisimple Brauer–Nesbitt
  -- separator over the split Wedderburn family extend `hdetK` to ALL of `K[G]`.  Descending that
  -- identity to `A` gives `hdetA`, which the characteristic-free finite-image criterion turns into
  -- a representation equivalence; scalar extension then yields the target equivalence.
  set K := AlgebraicClosure k with hKdef
  have hncK : ¬ CharZero K := by
    rw [not_charZero_iff_ringChar_ne_zero]
    have hk : ringChar k ≠ 0 := (not_charZero_iff_ringChar_ne_zero (k := k)).mp hnonCharZero
    letI : CharP k (ringChar k) := ringChar.charP (R := k)
    letI : CharP K (ringChar k) := inferInstanceAs (CharP (AlgebraicClosure k) (ringChar k))
    rwa [ringChar.eq K (ringChar k)]
  -- `master`: the generator determinant identity over `K` extends to every element of `K[G]`.
  have hdetKall :
      ∀ t : MonoidAlgebra K G,
        (-((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom t)).charpoly.reverse =
          (-((scalarExtensionMonoid
            (k := k) (G := G) (K := K) ρ').asAlgebraHom t)).charpoly.reverse := by
    obtain ⟨Y₁, _, _, _, τ, hτss, hτdet⟩ :=
      exists_semisimple_negCharpolyReverse_asAlgebraHom_eq (K := K) (G := G)
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ)
    obtain ⟨Y₂, _, _, _, τ', hτ'ss, hτ'det⟩ :=
      exists_semisimple_negCharpolyReverse_asAlgebraHom_eq (K := K) (G := G)
        (scalarExtensionMonoid (k := k) (G := G) (K := K) ρ')
    have hdetτ : ∀ g : G, (-τ g).charpoly.reverse = (-τ' g).charpoly.reverse := by
      intro g
      have h1 := hτdet (MonoidAlgebra.of K G g)
      have h2 := hτ'det (MonoidAlgebra.of K G g)
      simp only [Representation.asAlgebraHom_of] at h1 h2
      rw [← h1, ← h2]
      exact hdetK g
    obtain ⟨e⟩ :=
      nonempty_equiv_of_isSemisimple_det_eq_on_generators_isAlgClosed_notCharZero
        (K := K) (G := G) hτss hτ'ss hdetτ hncK
    intro t
    calc
      (-((scalarExtensionMonoid (k := k) (G := G) (K := K) ρ).asAlgebraHom t)).charpoly.reverse
          = (-(τ.asAlgebraHom t)).charpoly.reverse := hτdet t
      _ = (-(τ'.asAlgebraHom t)).charpoly.reverse :=
          negCharpolyReverse_asAlgebraHom_eq_of_representationEquiv (k := K) (G := G) e t
      _ = (-((scalarExtensionMonoid
            (k := k) (G := G) (K := K) ρ').asAlgebraHom t)).charpoly.reverse := (hτ'det t).symm
  -- Descend the all-of-`K[G]` determinant identity to every element of the image algebra `A`.
  have hdetA : ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse := by
    intro a
    rcases hlift a with ⟨t, rfl⟩
    have hVt : ρ.asAlgebraHom t = φV (liftι t) := by
      simpa [AlgHom.comp_apply] using
        (congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f t) hφV).symm
    have hWt : ρ'.asAlgebraHom t = φW (liftι t) := by
      simpa [AlgHom.comp_apply] using
        (congrArg (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f t) hφW).symm
    have hKpoly :
        (-(LinearMap.baseChange K (φV (liftι t)))).charpoly.reverse =
          (-(LinearMap.baseChange K (φW (liftι t)))).charpoly.reverse := by
      have hpoly := hdetKall ((MonoidAlgebra.mapAlgHom G (Algebra.ofId k K)) t)
      simpa [scalarExtensionMonoid_asAlgebraHom_mapRange (k := k) (G := G) (K := K) ρ t,
        scalarExtensionMonoid_asAlgebraHom_mapRange (k := k) (G := G) (K := K) ρ' t,
        hVt, hWt] using hpoly
    have hmap :
        Polynomial.map (algebraMap k K) (((-φV (liftι t)).charpoly.reverse : Polynomial k)) =
          Polynomial.map (algebraMap k K)
            (((-φW (liftι t)).charpoly.reverse : Polynomial k)) := by
      calc
        Polynomial.map (algebraMap k K) (((-φV (liftι t)).charpoly.reverse : Polynomial k)) =
            (-(LinearMap.baseChange K (φV (liftι t)))).charpoly.reverse := by
              symm
              exact negCharpolyReverse_baseChange_eq_map (k := k) (K := K) (φV (liftι t))
        _ = (-(LinearMap.baseChange K (φW (liftι t)))).charpoly.reverse := hKpoly
        _ = Polynomial.map (algebraMap k K)
            (((-φW (liftι t)).charpoly.reverse : Polynomial k)) := by
              exact negCharpolyReverse_baseChange_eq_map (k := k) (K := K) (φW (liftι t))
    exact
      (Polynomial.map_injective (algebraMap k K)
        (FaithfulSMul.algebraMap_injective k K)) hmap
  -- The characteristic-free finite-image criterion turns `hdetA` into a `k[G]`-equivalence.
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r y ↦ by
      change (φW (algebraMap k A r)) y = r • y
      simpa using congrArg (fun f : Module.End k W ↦ f y) (φW.commutes r)
  obtain ⟨eA⟩ :=
    nonempty_linearEquiv_of_det_eq_on_finite_semisimple_image
      (A := A) φV φW hdetA hV hW
  obtain ⟨eρ⟩ :=
    nonempty_equiv_of_lifted_linearEquiv
      (B := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW
      (fun a x ↦ rfl) (fun a y ↦ rfl) eA
  -- Scalar extension carries the equivalence to the algebraic closure.
  exact scalarExtensionMonoid_equiv_of_equiv (k := k) (G := G) (K := K) eρ

/-- Helper for Exercise 18-18.2-6: the remaining nonzero-characteristic determinant bridge from
the restricted generator determinant data, after the trace and exterior-trace prefixes have already
been descended to the finite semisimple image algebra. -/
theorem det_eq_on_target_of_restricted_exterior_trace_notCharZero
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a))
    (hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t))
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse := by
  -- Route correction: the old endpoint tried to produce an equivalence of the restricted
  -- `k[G]`-representations, which re-enters the theorem being proved.  The intended frontier is
  -- weaker: use the nonzero-characteristic determinant-product/Frobenius separator argument to
  -- turn the established trace and exterior-trace data into determinant equality for each target
  -- algebra element.
  have hK :
      Nonempty
        ((scalarExtensionMonoid (k := k) (G := G) (K := AlgebraicClosure k) ρ).Equiv
          (scalarExtensionMonoid (k := k) (G := G) (K := AlgebraicClosure k) ρ')) := by
    -- The remaining representation-equivalence step is isolated in the source-facing helper
    -- above; the present declaration only reflects that equivalence back to determinant equality.
    exact
      nonempty_scalarExtensionMonoid_equiv_of_restricted_exterior_trace_notCharZero
        (A := A) (ρ := ρ) (ρ' := ρ')
        φV φW liftι hφV hφW hlift hV hW htraceA hexteriorTrace hdetG hnonCharZero
  -- The scalar-extension reflection bridge turns that upstairs equivalence into the target
  -- determinant equality required by the finite-image endgame.
  exact
    target_det_eq_of_scalarExtended_restricted_equiv
      (A := A) (K := AlgebraicClosure k) (ρ := ρ) (ρ' := ρ')
      φV φW liftι hφV hφW hlift hK

/-- Helper for Exercise 18-18.2-6: the non-circular finite-image frontier in nonzero
characteristic.  This is the remaining determinant-product/multiplicity statement over an
arbitrary finite semisimple image algebra; it must not call the representation-level criterion
proved below. -/
theorem nonempty_linearEquiv_of_surjective_semisimpleAlgebra_lifted_generator_det_eq_nonCharZero_nonCircular
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetLifted : ∀ g : G,
      (-φV (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φW (liftι (MonoidAlgebra.of k G g))).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    isScalarTower_compHom_toModuleEnd (k := k) φV
  let _ : IsScalarTower k A W :=
    isScalarTower_compHom_toModuleEnd (k := k) φW
  have hVsemi :
      IsSemisimpleRepresentation
        (representationOfAlgHomAction (k := k) (G := G) (X := V) liftι) :=
    isSemisimpleRepresentation_of_surjective_algHomAction
      (k := k) (G := G) (X := V) liftι hlift hV
  have hWsemi :
      IsSemisimpleRepresentation
        (representationOfAlgHomAction (k := k) (G := G) (X := W) liftι) :=
    isSemisimpleRepresentation_of_surjective_algHomAction
      (k := k) (G := G) (X := W) liftι hlift hW
  have hdetRep :
      ∀ g : G,
        (-(representationOfAlgHomAction (k := k) (G := G) (X := V) liftι g)).charpoly.reverse =
          (-(representationOfAlgHomAction (k := k) (G := G) (X := W) liftι g)).charpoly.reverse :=
    representationOfAlgHomAction_det_eq_of_lifted_algHom_det_eq
      (k := k) (G := G) (X := V) (Y := W) φV φW liftι
      (compHom_toModuleEnd_smul (k := k) φV)
      (compHom_toModuleEnd_smul (k := k) φW)
      hdetLifted
  have hφVcomp :
      φV.comp liftι =
        (representationOfAlgHomAction (k := k) (G := G) (X := V) liftι).asAlgebraHom := by
    -- The restricted monoid-algebra action is exactly the supplied target action on `V`.
    apply AlgHom.ext
    intro t
    apply LinearMap.ext
    intro x
    rw [representationOfAlgHomAction_asAlgebraHom_apply]
    simpa [AlgHom.comp_apply] using
      (compHom_toModuleEnd_smul (k := k) φV (liftι t) x).symm
  have hφWcomp :
      φW.comp liftι =
        (representationOfAlgHomAction (k := k) (G := G) (X := W) liftι).asAlgebraHom := by
    -- The same compatibility holds for the target action on `W`.
    apply AlgHom.ext
    intro t
    apply LinearMap.ext
    intro x
    rw [representationOfAlgHomAction_asAlgebraHom_apply]
    simpa [AlgHom.comp_apply] using
      (compHom_toModuleEnd_smul (k := k) φW (liftι t) x).symm
  have htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) :=
    trace_eq_on_target_of_generator_det_eq
      (A := A)
      (ρ := representationOfAlgHomAction (k := k) (G := G) (X := V) liftι)
      (ρ' := representationOfAlgHomAction (k := k) (G := G) (X := W) liftι)
      φV φW liftι hφVcomp hφWcomp hlift hdetRep
  have hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V)
          (Representation.asAlgebraHom
            ((representationOfAlgHomAction (k := k) (G := G) (X := V) liftι).nthExteriorPower n)
            t) =
        LinearMap.trace k (⋀[k]^n W)
          (Representation.asAlgebraHom
            ((representationOfAlgHomAction (k := k) (G := G) (X := W) liftι).nthExteriorPower n)
            t) := by
    intro n t
    -- Generator determinant equality controls all exterior-power characters on the source
    -- monoid algebra; the remaining gap is transporting that control to arbitrary target
    -- algebra elements in positive characteristic.
    exact
      exteriorTrace_eq_asAlgebraHom_of_generator_det_eq
        (ρ := representationOfAlgHomAction (k := k) (G := G) (X := V) liftι)
        (ρ' := representationOfAlgHomAction (k := k) (G := G) (X := W) liftι)
        hdetRep n t
  have hdetA :
      ∀ a : A, (-φV a).charpoly.reverse = (-φW a).charpoly.reverse := by
    -- The main proof has now reduced the problem to the isolated determinant-on-target bridge.
    exact
      det_eq_on_target_of_restricted_exterior_trace_notCharZero
        (A := A)
        (ρ := representationOfAlgHomAction (k := k) (G := G) (X := V) liftι)
        (ρ' := representationOfAlgHomAction (k := k) (G := G) (X := W) liftι)
        φV φW liftι hφVcomp hφWcomp hlift hV hW htraceA hexteriorTrace hdetRep
        hnonCharZero
  -- Once every target-algebra element has matching determinant polynomial, the earlier
  -- all-target finite-image theorem supplies the `A`-linear equivalence.
  exact
    nonempty_linearEquiv_of_det_eq_on_finite_semisimple_image
      (A := A) φV φW hdetA hV hW

/-- Helper for Exercise 18-18.2-6: the isolated non-characteristic-zero finite-image
criterion, stated directly in terms of determinant equality on lifted monoid generators. -/
theorem nonempty_linearEquiv_of_surjective_semisimpleAlgebra_lifted_generator_det_eq_nonCharZero_support
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetLifted : ∀ g : G,
      (-φV (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φW (liftι (MonoidAlgebra.of k G g))).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  -- Route correction: the previous proof called the representation-level determinant criterion
  -- that this finite-image layer is supposed to support.  Delegate instead to the explicitly
  -- non-circular finite-image frontier.
  exact
    nonempty_linearEquiv_of_surjective_semisimpleAlgebra_lifted_generator_det_eq_nonCharZero_nonCircular
      (A := A) φV φW liftι hlift hV hW hdetLifted hnonCharZero

/-- Helper for Exercise 18-18.2-6: the isolated non-characteristic-zero finite-image frontier
for the common-kernel quotient. -/
theorem nonempty_linearEquiv_of_commonKernelQuotient_nonCharZero_support
    {X Y : Type w}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    let A := commonKernelQuotient (k := k) (G := G) ρ ρ'
    let φX : A →ₐ[k] Module.End k X :=
      commonKernelLeftAction (k := k) (G := G) ρ ρ'
    let φY : A →ₐ[k] Module.End k Y :=
      commonKernelRightAction (k := k) (G := G) ρ ρ'
    let _ : Module A X := Module.compHom X φX.toRingHom
    let _ : Module A Y := Module.compHom Y φY.toRingHom
    Nonempty (X ≃ₗ[A] Y) := by
  let A := commonKernelQuotient (k := k) (G := G) ρ ρ'
  let φX : A →ₐ[k] Module.End k X :=
    commonKernelLeftAction (k := k) (G := G) ρ ρ'
  let φY : A →ₐ[k] Module.End k Y :=
    commonKernelRightAction (k := k) (G := G) ρ ρ'
  let liftι : MonoidAlgebra k G →ₐ[k] A :=
    commonKernelProjection (k := k) (G := G) ρ ρ'
  let _ : Module.Finite k A :=
    commonKernelQuotient_finite (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing A :=
    commonKernelQuotient_isSemisimpleRing
      (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  have hφX : φX.comp liftι = ρ.asAlgebraHom := by
    -- The left quotient action composes with the projection to the original action.
    simpa [A, φX, liftι] using
      commonKernelLeftAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  have hφY : φY.comp liftι = ρ'.asAlgebraHom := by
    -- The right quotient action has the same factorization property.
    simpa [A, φY, liftι] using
      commonKernelRightAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  have hlift : Function.Surjective liftι := by
    -- The common-kernel quotient projection is surjective.
    simpa [A, liftι, commonKernelProjection, commonKernelQuotient, commonKernelIdeal] using
      (Ideal.Quotient.mkₐ_surjective k
        (commonKernelIdeal (k := k) (G := G) ρ ρ'))
  have hX : let _ : Module A X := Module.compHom X φX.toRingHom
      IsSemisimpleModule A X := by
    -- Semisimplicity descends to the left module over the finite common image algebra.
    simpa [A, φX] using
      commonKernelQuotient_left_isSemisimpleModule
        (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  have hY : let _ : Module A Y := Module.compHom Y φY.toRingHom
      IsSemisimpleModule A Y := by
    -- The same descent supplies semisimplicity for the right module.
    simpa [A, φY] using
      commonKernelQuotient_right_isSemisimpleModule
        (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ'
  let _ := hX
  let _ := hY
  let _ : Module A X := Module.compHom X φX.toRingHom
  let _ : Module A Y := Module.compHom Y φY.toRingHom
  have hdetLifted : ∀ g : G,
      (-φX (liftι (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-φY (liftι (MonoidAlgebra.of k G g))).charpoly.reverse := by
    intro g
    -- The generator determinant hypothesis is now recorded at the common-image algebra level.
    simpa [A, φX, φY, liftι] using
      commonKernelQuotient_det_eq_on_lifted_generators_support
        (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hdet g
  -- The quotient construction is now fully discharged; the only remaining frontier is the
  -- generic finite-image non-characteristic-zero criterion above.
  exact
    nonempty_linearEquiv_of_surjective_semisimpleAlgebra_lifted_generator_det_eq_nonCharZero_support
      (A := A) φX φY liftι hlift hX hY hdetLifted hnonCharZero

/-- Helper for Exercise 18-18.2-6: the representation-level Brauer-Nesbitt criterion is reduced
to characteristic zero or to the isolated non-circular finite-image frontier. -/
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_grothendieck
    {X Y : Type w}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  by_cases hcharZero : CharZero k
  · let _ : CharZero k := hcharZero
    -- In characteristic zero the already-proved trace separator route closes the criterion.
    exact
      nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_charZero
        hρ hρ' hdet
  let A := commonKernelQuotient (k := k) (G := G) ρ ρ'
  let φX : A →ₐ[k] Module.End k X :=
    commonKernelLeftAction (k := k) (G := G) ρ ρ'
  let φY : A →ₐ[k] Module.End k Y :=
    commonKernelRightAction (k := k) (G := G) ρ ρ'
  let liftι : MonoidAlgebra k G →ₐ[k] A :=
    commonKernelProjection (k := k) (G := G) ρ ρ'
  have hφX : φX.comp liftι = ρ.asAlgebraHom := by
    -- The left common-kernel action is the original action after composing with the projection.
    simpa [A, φX, liftι] using
      commonKernelLeftAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  have hφY : φY.comp liftι = ρ'.asAlgebraHom := by
    -- The same factorization records the right common-kernel action.
    simpa [A, φY, liftι] using
      commonKernelRightAction_comp_projection (k := k) (G := G) (ρ := ρ) (ρ' := ρ')
  let _ : Module A X := Module.compHom X φX.toRingHom
  let _ : Module A Y := Module.compHom Y φY.toRingHom
  let _ : IsScalarTower k A X :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := X) fun r x ↦ by
      change (φX (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k X ↦ f x) (φX.commutes r)
  let _ : IsScalarTower k A Y :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := Y) fun r y ↦ by
      change (φY (algebraMap k A r)) y = r • y
      simpa using congrArg (fun f : Module.End k Y ↦ f y) (φY.commutes r)
  obtain ⟨eA⟩ :=
    nonempty_linearEquiv_of_commonKernelQuotient_nonCharZero_support
      (k := k) (G := G) (ρ := ρ) (ρ' := ρ') hρ hρ' hdet hcharZero
  -- The finite-image equivalence is linear over the common quotient, hence intertwines the
  -- original representations after restriction along the quotient projection.
  exact
    nonempty_equiv_of_lifted_linearEquiv
      (B := A) (X := X) (Y := Y) (ρ := ρ) (ρ' := ρ')
      φX φY liftι hφX hφY (fun a x ↦ rfl) (fun a y ↦ rfl) eA

/-- Helper for Exercise 18-18.2-6: the representation-level Brauer-Nesbitt criterion needed by
the finite-image support layer. This is the acyclic source-facing frontier: it should be proved
from the complete-simple-family Grothendieck/separator argument, not from the finite-image
theorems below. -/
theorem nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_support
    {X Y : Type w}
    [AddCommGroup X] [Module k X] [FiniteDimensional k X]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    {ρ : Representation k G X} {ρ' : Representation k G Y}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ')
    (hdet : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  -- Route correction: this support theorem is now just an alias for the acyclic
  -- Grothendieck/simple-family criterion, avoiding the old common-kernel recursion.
  exact
    nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_grothendieck
      hρ hρ' hdet

/-- Helper for Exercise 18-18.2-6: in prime characteristic, generator determinant equality for a
surjective finite semisimple image algebra determines the two semisimple modules. -/
theorem nonempty_linearEquiv_of_surjective_semisimpleAlgebra_generator_det_eq_primeChar
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {B : Type*} [Ring B] [Algebra k B] [Module.Finite k B] [IsSemisimpleRing B]
    {M N : Type w}
    [AddCommGroup M] [Module B M] [Module k M] [FiniteDimensional k M]
    [IsScalarTower k B M]
    [AddCommGroup N] [Module B N] [Module k N] [FiniteDimensional k N]
    [IsScalarTower k B N]
    (β : MonoidAlgebra k G →ₐ[k] B)
    (hβ_surj : Function.Surjective β)
    (hdetβ : ∀ g : G,
      (-DistribSMul.toLinearMap k M (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N (β (MonoidAlgebra.of k G g))).charpoly.reverse) :
    Nonempty (M ≃ₗ[B] N) := by
  -- Route correction: the older split-product proof tried to isolate simple factors with
  -- primitive matrix projectors; their self-traces can vanish in characteristic `p`.  The
  -- next bridge reduces the remaining work to the representation-level Brauer-Nesbitt statement
  -- for the restricted `k[G]`-actions; surjectivity then upgrades that equivalence back to
  -- `B`-linearity.
  rcases
    semisimpleAlgHomAction_detEq_of_surjective
      (k := k) (G := G) (B := B) (M := M) (N := N) β hβ_surj hdetβ with
    ⟨hMsemi, hNsemi, hdetRep⟩
  have hrep :
      Nonempty
        ((representationOfAlgHomAction (k := k) (G := G) (X := M) β).Equiv
          (representationOfAlgHomAction (k := k) (G := G) (X := N) β)) := by
    -- The finite-image algebra problem has been reduced to the acyclic representation-level
    -- Brauer-Nesbitt criterion for the two restricted `k[G]`-representations.
    exact
      nonempty_equiv_of_isSemisimple_of_det_one_add_polynomial_eq_support
        hMsemi hNsemi hdetRep
  -- Any equivalence of the restricted representations is automatically `B`-linear because
  -- `β : k[G] → B` is surjective.
  exact
    nonempty_linearEquiv_of_algHomAction_equiv
      (k := k) (G := G) (X := M) (Y := N) β hβ_surj hrep

/-- Helper for Exercise 18-18.2-6: in prime characteristic, generator determinant equality for a
surjective map to a split Wedderburn product is the split-product specialization of the finite
semisimple-image Brauer-Nesbitt helper. -/
theorem nonempty_linearEquiv_of_splitProduct_generator_det_eq_primeChar
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {n : ℕ} {D : Fin n → Type*} {d : Fin n → ℕ}
    [∀ i, DivisionRing (D i)] [∀ i, Algebra k (D i)] [∀ i, Module.Finite k (D i)]
    [∀ i, NeZero (d i)]
    {M N : Type w}
    [AddCommGroup M] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [Module k M] [FiniteDimensional k M]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) M]
    [AddCommGroup N] [Module (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    [Module k N] [FiniteDimensional k N]
    [IsScalarTower k (Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) N]
    (β : MonoidAlgebra k G →ₐ[k] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
    (hβ_surj : Function.Surjective β)
    (hdetβ : ∀ g : G,
      (-DistribSMul.toLinearMap k M (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k N (β (MonoidAlgebra.of k G g))).charpoly.reverse) :
    Nonempty (M ≃ₗ[Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)] N) := by
  -- Specialize the source-facing finite-image theorem to the split Wedderburn product; all
  -- product, matrix, finite-dimensional, and semisimple-ring instances are canonical here.
  exact
    nonempty_linearEquiv_of_surjective_semisimpleAlgebra_generator_det_eq_primeChar
      (k := k) (G := G) (p := p)
      (B := Π i, Matrix (Fin (d i)) (Fin (d i)) (D i))
      (M := M) (N := N) β hβ_surj hdetβ

/-- Helper for Exercise 18-18.2-6: the positive-prime-characteristic core of the
source-faithful Brauer-Nesbitt argument over a finite semisimple image algebra. -/
theorem nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_primeCharCore
    {p : ℕ} [CharP k p] [Fact p.Prime]
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a))
    (hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t))
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  classical
  -- Route correction: the exterior-trace-on-target route is invalid for arbitrary additive lifts,
  -- and the previous arbitrary-simple-constituent route bundled decomposition and reconstruction
  -- into one missing step.  Split the finite image algebra first and keep the remaining blocker
  -- at the split product/Morita multiplicity layer.
  obtain ⟨n, D, d, _, _, _, hd, ⟨eA⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  let B := Π i : Fin n, Matrix (Fin (d i)) (Fin (d i)) (D i)
  let _ : Module B V := Module.compHom V eA.symm.toRingHom
  let _ : Module B W := Module.compHom W eA.symm.toRingHom
  let _ : IsScalarTower k B V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := V) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let _ : IsScalarTower k B W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := B) (M := W) fun r x ↦ by
      change (eA.symm ((algebraMap k B) r)) • x = r • x
      rw [eA.symm.commutes]
      exact IsScalarTower.algebraMap_smul (R := k) (A := A) r x
  let β : MonoidAlgebra k G →ₐ[k] B := eA.toAlgHom.comp liftι
  have hβ_surj : Function.Surjective β :=
    algEquiv_toAlgHom_comp_surjective (e := eA) (f := liftι) hlift
  have hβV :
      ∀ g : G, DistribSMul.toLinearMap k V (β (MonoidAlgebra.of k G g)) = ρ g := by
    intro g
    apply LinearMap.ext
    intro x
    have hliftV : φV (liftι (MonoidAlgebra.of k G g)) =
        ρ.asAlgebraHom (MonoidAlgebra.of k G g) := by
      simpa [AlgHom.comp_apply] using
        congrArg
          (fun f : MonoidAlgebra k G →ₐ[k] Module.End k V ↦ f (MonoidAlgebra.of k G g))
          hφV
    have hβt : eA.symm (β (MonoidAlgebra.of k G g)) =
        liftι (MonoidAlgebra.of k G g) := by
      simp [β]
    -- The transported split-product action on a generator is the original representation action.
    change (φV (eA.symm (β (MonoidAlgebra.of k G g)))) x = ρ g x
    rw [hβt, hliftV]
    simp
  have hβW :
      ∀ g : G, DistribSMul.toLinearMap k W (β (MonoidAlgebra.of k G g)) = ρ' g := by
    intro g
    apply LinearMap.ext
    intro x
    have hliftW : φW (liftι (MonoidAlgebra.of k G g)) =
        ρ'.asAlgebraHom (MonoidAlgebra.of k G g) := by
      simpa [AlgHom.comp_apply] using
        congrArg
          (fun f : MonoidAlgebra k G →ₐ[k] Module.End k W ↦ f (MonoidAlgebra.of k G g))
          hφW
    have hβt : eA.symm (β (MonoidAlgebra.of k G g)) =
        liftι (MonoidAlgebra.of k G g) := by
      simp [β]
    -- The same generator normalization holds for the second descended action.
    change (φW (eA.symm (β (MonoidAlgebra.of k G g)))) x = ρ' g x
    rw [hβt, hliftW]
    simp
  have hdetβ : ∀ g : G,
      (-DistribSMul.toLinearMap k V (β (MonoidAlgebra.of k G g))).charpoly.reverse =
        (-DistribSMul.toLinearMap k W (β (MonoidAlgebra.of k G g))).charpoly.reverse :=
    splitProduct_generator_det_eq_of_action_eq
      (β := β) (ρX := ρ) (ρY := ρ') hβV hβW hdetG
  have hBlinear : Nonempty (V ≃ₗ[B] W) := by
    -- Route correction: do not try to compare determinant polynomials on arbitrary additive
    -- lifts of primitive projectors.  Instead, pass the honest generator determinant data to the
    -- split-product multiplicity theorem, whose frontier is the determinant-product separator.
    simpa [B] using
      nonempty_linearEquiv_of_splitProduct_generator_det_eq_primeChar
        (k := k) (G := G) (p := p) (D := D) (d := d) (M := V) (N := W)
        β hβ_surj hdetβ
  rcases hBlinear with ⟨eB⟩
  have hmap_smul : ∀ (a : A) (x : V), eB (a • x) = a • eB x := by
    intro a x
    -- A `B`-linear equivalence transports back to `A`-linearity through the Wedderburn split.
    have hVsmul : (eA a : B) • x = a • x := by
      change (eA.symm (eA a)) • x = a • x
      simp
    have hWsmul : (eA a : B) • eB x = a • eB x := by
      change (eA.symm (eA a)) • eB x = a • eB x
      simp
    calc
      eB (a • x) = eB ((eA a : B) • x) := by rw [hVsmul]
      _ = (eA a : B) • eB x := eB.map_smul (eA a) x
      _ = a • eB x := hWsmul
  let eAlinear : V ≃ₗ[A] W :=
    { toFun := eB
      invFun := eB.symm
      left_inv := eB.left_inv
      right_inv := eB.right_inv
      map_add' := eB.map_add
      map_smul' := hmap_smul }
  exact ⟨eAlinear⟩

/-- Helper for Exercise 18-18.2-6: the remaining non-characteristic-zero branch of the
source-faithful Brauer-Nesbitt argument.  The already-established trace and exterior-trace
prefixes are included explicitly so the missing step is just the positive-characteristic
determinant-character separator, not the finite-image setup. -/
theorem nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_nonCharZero
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a))
    (hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t))
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse)
    (hnonCharZero : ¬ CharZero k) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  -- Route correction: the characteristic-zero trace route cannot recover natural multiplicities
  -- after casting to `k`; the next proof step must use determinant-product normalization plus
  -- Jacobson density on finite simple constituents.
  let p := ringChar k
  letI : CharP k p := ringChar.charP (R := k)
  letI : Fact p.Prime := ⟨by
    simpa [p] using ringChar_prime_of_not_charZero (k := k) hnonCharZero⟩
  -- Once `ringChar k` is registered as the positive prime characteristic, the isolated core is
  -- exactly the remaining finite-image constituent/separator argument.
  exact
    nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_primeCharCore
      (A := A) (ρ := ρ) (ρ' := ρ') (p := p)
      φV φW liftι hφV hφW hlift hV hW htraceA hexteriorTrace hdetG

/-- Helper for Exercise 18-18.2-6: generator-level determinant equality is the source-faithful
Brauer-Nesbitt input needed to identify the two descended modules over the finite semisimple image
algebra. -/
theorem nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  have htraceA :
      ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) :=
    trace_eq_on_target_of_generator_det_eq
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hdetG
  have hexteriorTrace : ∀ n (t : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom t) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom t) := by
    intro n t
    -- The full exterior-trace invariant on `k[G]` is now available from the generator
    -- determinant hypothesis; the remaining blocker is that this is not the characteristic
    -- polynomial of an arbitrary additive lift in `A`.
    exact
      exteriorTrace_eq_asAlgebraHom_of_generator_det_eq
        (ρ := ρ) (ρ' := ρ') hdetG n t
  by_cases hcharZero : CharZero k
  · let _ : CharZero k := hcharZero
    -- The trace route is valid exactly in characteristic zero, where natural corner dimensions
    -- can be recovered from their casts to `k`.
    exact
      nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_charZero
        (A := A) (ρ := ρ) (ρ' := ρ')
        φV φW liftι hφV hφW hlift hV hW hdetG
  -- In the complementary branch the established trace prefixes are passed to the isolated
  -- positive-characteristic Brauer-Nesbitt frontier.
  exact
    nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image_nonCharZero
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hV hW
      htraceA hexteriorTrace hdetG hcharZero

/-- Helper for Exercise 18-18.2-6: a linear equivalence over a finite semisimple image algebra
obtained from generator determinant equality restricts back to an equivalence of the original
representations. -/
theorem nonempty_equiv_of_generator_det_eq_on_finite_semisimple_image
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hdetG : ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse) :
    Nonempty (ρ.Equiv ρ') := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r y ↦ by
      change (φW (algebraMap k A r)) y = r • y
      simpa using congrArg (fun f : Module.End k W ↦ f y) (φW.commutes r)
  obtain ⟨eA⟩ :=
    nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hV hW hdetG
  -- The finite-image equivalence is linear for the lifted algebra, so restriction along the
  -- generator lift gives the desired representation equivalence.
  exact
    nonempty_equiv_of_lifted_linearEquiv
      (B := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW
      (fun a x ↦ rfl) (fun a y ↦ rfl) eA

/-- Helper for Exercise 18-18.2-6: once the exterior-trace data is available on lifts from the
common finite-dimensional semisimple image algebra, the remaining source-faithful step is to
split `A`, isolate primitive matrix projectors, and recover the simple multiplicities factorwise. -/
theorem nonempty_linearEquiv_of_exterior_trace_eq_on_finite_semisimple_image
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (φV : A →ₐ[k] Module.End k V) (φW : A →ₐ[k] Module.End k W)
    (liftι : MonoidAlgebra k G →ₐ[k] A)
    (hφV : φV.comp liftι = ρ.asAlgebraHom)
    (hφW : φW.comp liftι = ρ'.asAlgebraHom)
    (hlift : Function.Surjective liftι)
    (hV : let _ : Module A V := Module.compHom V φV.toRingHom
      IsSemisimpleModule A V)
    (hW : let _ : Module A W := Module.compHom W φW.toRingHom
      IsSemisimpleModule A W)
    (hexteriorTrace : ∀ n (a : MonoidAlgebra k G),
      LinearMap.trace k (⋀[k]^n V) ((ρ.nthExteriorPower n).asAlgebraHom a) =
        LinearMap.trace k (⋀[k]^n W) ((ρ'.nthExteriorPower n).asAlgebraHom a)) :
    let _ : Module A V := Module.compHom V φV.toRingHom
    let _ : Module A W := Module.compHom W φW.toRingHom
    Nonempty (V ≃ₗ[A] W) := by
  let _ := hV
  let _ := hW
  let _ : Module A V := Module.compHom V φV.toRingHom
  let _ : Module A W := Module.compHom W φW.toRingHom
  let _ : IsScalarTower k A V :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := V) fun r x ↦ by
      change (φV (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k V ↦ f x) (φV.commutes r)
  let _ : IsScalarTower k A W :=
    IsScalarTower.of_algebraMap_smul (R := k) (A := A) (M := W) fun r x ↦ by
      change (φW (algebraMap k A r)) x = r • x
      simpa using congrArg (fun f : Module.End k W ↦ f x) (φW.commutes r)
  have hdetG :
      ∀ g : G, (-ρ g).charpoly.reverse = (-ρ' g).charpoly.reverse :=
    detOneAddPolynomialEq_on_generators_of_exteriorTrace
      (ρ := ρ) (ρ' := ρ') hexteriorTrace
  -- Route correction: exterior powers give determinant data on monoid generators, not on
  -- arbitrary additive lifts in `A`; pass the honest generator determinant character to the
  -- characteristic-free separator theorem.
  exact
    nonempty_linearEquiv_of_generator_det_eq_on_finite_semisimple_image
      (A := A) (ρ := ρ) (ρ' := ρ') φV φW liftι hφV hφW hlift hV hW hdetG

end EquivalenceCriterion

end Representation
