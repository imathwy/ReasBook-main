import Mathlib
import stacks_project.Chap10.Lemma_10_36_5
import stacks_project.Chap10.Lemma_10_115_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [Algebra.FiniteType R S]

local notation "K" => FractionRing R
local instance : Algebra ℤ K := Ring.toIntAlgebra K

/-
Source/core/bridge triage:
* primary domain: Noether normalization over a domain together with localization-away descent;
* sampled owner API:
  `exists_finite_inj_algHom_of_fg` from mathlib's Noether-normalization file,
  `exists_noether_normalization_polynomials_quotient_mvPolynomial` from Lemma `10.115.4`,
  `Localization.awayMapₐ` for the canonical localization-away algebra map,
  `Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ` for the localization-away owner
  interface used later in the chapter;
* source-facing: an intermediate `R`-algebra `S'` sitting between `R[y₁, …, y_d]` and `S`, with
  both structure maps injective, `S'` finite over the polynomial algebra, and `S'_f ≃ S_f` for
  some nonzero `f ∈ R`;
* core/canonical: injective `AlgHom`s, `AlgHom.Finite`, and the localization-away algebra
  `Localization.Away`;
* bridge/view: describing the polynomial algebra by a chosen family `y : Fin d → T` inside a
  subalgebra `T ⊆ S`, together with algebraic-independence or module-finiteness consequences.

Primitive data here are the intermediate algebra, the two injective maps, the finite polynomial
map, the nonzero localization element, and bijectivity of the canonical localized map. The earlier
subalgebra-and-generators presentation is derived API from this factorization and should not remain
the main public owner.
-/

/-- The image subalgebra of `S` cut out by a polynomial factorization, together with the finite
injective polynomial map and the away-localization comparison being an isomorphism-on-underlying
sets. -/
structure IsInjectivePolynomialFactorizationAway
    (d : ℕ) (S' : Subalgebra R S)
    (polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] S') (f : R) : Prop where
  polynomialToIntermediate_injective : Function.Injective polynomialToIntermediate
  polynomialToIntermediate_finite : AlgHom.Finite polynomialToIntermediate
  localizationElement_ne_zero : f ≠ 0
  awayMap_bijective :
    Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' f))

omit [IsDomain R] in
/-- Helper for Lemma 10.115.7: a finite type algebra admits a fixed surjective presentation by a
polynomial ring in finitely many variables. -/
private lemma exists_surjective_mvPolynomial_presentation :
    ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] S, Function.Surjective π := by
  -- Use the canonical finite-type owner interface to choose one quotient presentation once.
  simpa using
    (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType R S))

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: the images of the coordinate variables in a fixed polynomial
presentation generate the whole target algebra. -/
private lemma adjoin_range_presentation_variables_eq_top
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπsurj : Function.Surjective π) :
    Algebra.adjoin R (Set.range fun i : Fin n ↦ π (MvPolynomial.X i)) = ⊤ := by
  -- Rewrite the adjoin as the range of the evaluation map determined by the same variables.
  calc
    Algebra.adjoin R (Set.range fun i : Fin n ↦ π (MvPolynomial.X i))
        = (MvPolynomial.aeval fun i : Fin n ↦ π (MvPolynomial.X i)).range := by
          exact Algebra.adjoin_range_eq_range_aeval (R := R)
            (f := fun i : Fin n ↦ π (MvPolynomial.X i))
    _ = π.range := by
          -- An algebra homomorphism out of a polynomial ring is determined by the variable images.
          congr 1
          ext i
          simp
    _ = ⊤ := (AlgHom.range_eq_top (f := π)).2 hπsurj

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: the away map induced by a subalgebra inclusion is injective. -/
private lemma awayMap_injective_subalgebra_val
    (S' : Subalgebra R S) (f : R) :
    Function.Injective (Localization.awayMapₐ S'.val (algebraMap R S' f)) := by
  -- Reduce to the owner criterion for injectivity of the underlying away map.
  change Function.Injective (Localization.awayMap S'.val.toRingHom (algebraMap R S' f))
  rw [Localization.awayMap_injective_iff]
  intro a ha
  have hzero : a = 0 := by
    apply Subtype.ext
    simpa using ha
  refine ⟨0, ?_⟩
  simpa [hzero]

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: injectivity of the ambient algebra map descends to any intermediate
subalgebra. -/
private lemma algebraMap_injective_subalgebra
    (S' : Subalgebra R S) (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap R S') := by
  -- Compare in the ambient algebra and use the given injectivity there.
  intro x y hxy
  apply hinj
  simpa using congrArg Subtype.val hxy

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: once the polynomial map is injective and finite and the localized
subalgebra inclusion is surjective, the remaining factorization data are automatic. -/
private lemma factorizationAway_of_surjective_awayMap
    {d : ℕ} (S' : Subalgebra R S)
    (polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] S') (f : R)
    (hpoly_inj : Function.Injective polynomialToIntermediate)
    (hpoly_finite : AlgHom.Finite polynomialToIntermediate)
    (hf : f ≠ 0)
    (hsurj : Function.Surjective (Localization.awayMapₐ S'.val (algebraMap R S' f))) :
    IsInjectivePolynomialFactorizationAway d S' polynomialToIntermediate f := by
  -- The injective half of the away map is the standard localization fact for subalgebra
  -- inclusions, so surjectivity is the only extra input needed here.
  refine ⟨hpoly_inj, hpoly_finite, hf, ?_⟩
  exact ⟨awayMap_injective_subalgebra_val (R := R) (S := S) S' f, hsurj⟩

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: if each chosen generator of `S` becomes a multiple of `f` by an
element of an intermediate subalgebra, then every element of the adjoin of those generators admits
the same kind of multiple lying in the intermediate subalgebra. -/
private lemma exists_scaled_multiple_of_mem_adjoin
    {n : ℕ} (S' : Subalgebra R S) (f : R)
    (x : Fin n → S) (x' : Fin n → S')
    (hx' : ∀ i, (x' i : S) = algebraMap R S f * x i) :
    ∀ z ∈ Algebra.adjoin R (Set.range x),
      ∃ z' : S', ∃ m : ℕ, (z' : S) = algebraMap R S f ^ m * z := by
  intro z hz
  -- Induct over the `R`-subalgebra generated by the chosen tuple `x`.
  let P :
      (a : S) → a ∈ Algebra.adjoin R (Set.range x) → Prop :=
    fun a _ ↦ ∃ a' : S', ∃ m : ℕ, (a' : S) = algebraMap R S f ^ m * a
  change P z hz
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · intro a ha
    rcases ha with ⟨i, rfl⟩
    -- The hypothesis gives the required multiple for each distinguished generator.
    refine ⟨x' i, 1, ?_⟩
    simpa [hx' i]
  · intro r
    -- Scalars already lie in the intermediate subalgebra without adding any factor of `f`.
    refine ⟨algebraMap R S' r, 0, ?_⟩
    simp
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨a', m, hm⟩
    rcases hPb with ⟨b', n, hn⟩
    -- Clear the two denominators to the common exponent `m + n`.
    refine ⟨(algebraMap R S' f) ^ n * a' + (algebraMap R S' f) ^ m * b', m + n, ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
    calc
      algebraMap R S f ^ n * (a' : S) + algebraMap R S f ^ m * (b' : S)
          = algebraMap R S f ^ n * (algebraMap R S f ^ m * a) +
              algebraMap R S f ^ m * (algebraMap R S f ^ n * b) := by
                rw [hm, hn]
      _ = algebraMap R S f ^ (m + n) * (a + b) := by
            simp [pow_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨a', m, hm⟩
    rcases hPb with ⟨b', n, hn⟩
    -- Multiplication multiplies the chosen multiples and adds the exponents.
    refine ⟨a' * b', m + n, ?_⟩
    simp only [Subalgebra.coe_mul]
    calc
      (a' : S) * (b' : S)
          = (algebraMap R S f ^ m * a) * (algebraMap R S f ^ n * b) := by
              rw [hm, hn]
      _ = algebraMap R S f ^ (m + n) * (a * b) := by
            simp [pow_add, mul_assoc, mul_left_comm, mul_comm]

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: once the original generators become `f`-divisible inside an
intermediate subalgebra, the induced away map from that intermediate subalgebra to `S` is
surjective. -/
private lemma awayMap_surjective_of_scaled_generators
    {n : ℕ} (S' : Subalgebra R S) (f : R)
    (x : Fin n → S) (x' : Fin n → S')
    (hx_top : Algebra.adjoin R (Set.range x) = ⊤)
    (hx' : ∀ i, (x' i : S) = algebraMap R S f * x i) :
    Function.Surjective (Localization.awayMapₐ S'.val (algebraMap R S' f)) := by
  -- Reinterpret surjectivity through the standard away-map criterion.
  change Function.Surjective
    (Localization.awayMap S'.val.toRingHom (algebraMap R S' f))
  rw [Localization.awayMap_surjective_iff]
  intro z
  have hz_mem : z ∈ Algebra.adjoin R (Set.range x) := by
    rw [hx_top]
    trivial
  -- Every element of `S` lies in the adjoin of the generators, so the previous induction
  -- supplies an `f`-multiple already inside `S'`.
  obtain ⟨z', m, hz'⟩ :=
    exists_scaled_multiple_of_mem_adjoin (R := R) (S := S) S' f x x' hx' z hz_mem
  refine ⟨z', m, ?_⟩
  simpa using hz'

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: adjoining finitely many elements integral over the polynomial
subalgebra generated by `y` yields an intermediate algebra finite over that polynomial
subalgebra. -/
private lemma exists_finite_polynomial_map_to_intermediate_of_integral_generators
    {d n : ℕ} (y : Fin d → S) (x' : Fin n → S)
    (hx'int : ∀ i, IsIntegral (Algebra.adjoin R (Set.range y)) (x' i)) :
    ∃ polynomialToIntermediate :
        MvPolynomial (Fin d) R →ₐ[R] Algebra.adjoin R (Set.range y ∪ Set.range x'),
      AlgHom.Finite polynomialToIntermediate := by
  let A : Subalgebra R S := Algebra.adjoin R (Set.range y)
  let B : Subalgebra R S := Algebra.adjoin R (Set.range y ∪ Set.range x')
  let ψS : MvPolynomial (Fin d) R →ₐ[R] S := MvPolynomial.aeval y
  have hψS_range : ψS.range = A := by
    -- The range of evaluation at `y` is exactly the polynomial subalgebra `R[y]`.
    simpa [A, ψS] using
      (Algebra.adjoin_range_eq_range_aeval (R := R) (f := y)).symm
  let eA : ψS.range ≃ₐ[R] A := Subalgebra.equivOfEq _ _ hψS_range
  let polynomialToA : MvPolynomial (Fin d) R →ₐ[R] A :=
    eA.toAlgHom.comp ψS.rangeRestrict
  have hpolynomialToA_surj : Function.Surjective polynomialToA := by
    intro a
    let a' : ψS.range := eA.symm a
    rcases ψS.rangeRestrict_surjective a' with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    -- Passing through the range-restriction identifies the polynomial algebra with `A`.
    change eA (ψS.rangeRestrict p) = a
    rw [hp]
    exact eA.apply_symm_apply a
  have hpolynomialToA_finite : AlgHom.Finite polynomialToA := by
    -- Surjective algebra maps are finite.
    exact AlgHom.Finite.of_surjective polynomialToA hpolynomialToA_surj
  let _ : Algebra A S := A.val.toAlgebra
  let B0 : Subalgebra A S := Algebra.adjoin A (Set.range x')
  have hB0_finite :
      RingHom.Finite (algebraMap A B0) := by
    -- The larger algebra is obtained by adjoining finitely many elements integral over `A`.
    change RingHom.Finite (algebraMap A (Algebra.adjoin A (Set.range x')))
    rw [RingHom.finite_algebraMap]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x')
      (fun z hz ↦ by
        rcases hz with ⟨i, rfl⟩
        exact hx'int i)
  have hA_le_B0 : A ≤ B0.restrictScalars R := by
    intro a ha
    change (a : S) ∈ B0
    exact Subalgebra.algebraMap_mem B0 ⟨a, ha⟩
  let inclusionToB0 : A →ₐ[R] B0.restrictScalars R := Subalgebra.inclusion hA_le_B0
  have hInclusionToB0_finite : AlgHom.Finite inclusionToB0 := by
    -- This inclusion is the algebra map into the finite `A`-adjoin of the integral generators.
    simpa [AlgHom.Finite, RingHom.Finite, inclusionToB0] using hB0_finite
  have hB0_eq_B : B0.restrictScalars R = B := by
    -- Reassociate adjoining `x'` over `A = R[y]` with adjoining `y` and `x'` over `R`.
    simpa [A, B, B0] using
      (Algebra.adjoin_union_eq_adjoin_adjoin
        (R := R) (s := Set.range y) (t := Set.range x')).symm
  let eB : B0.restrictScalars R ≃ₐ[R] B := Subalgebra.equivOfEq _ _ hB0_eq_B
  let polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] B :=
    eB.toAlgHom.comp (inclusionToB0.comp polynomialToA)
  refine ⟨polynomialToIntermediate, ?_⟩
  have heB_finite : AlgHom.Finite eB.toAlgHom := by
    -- Algebra equivalences are finite because they are surjective.
    exact AlgHom.Finite.of_surjective eB.toAlgHom eB.surjective
  exact AlgHom.Finite.comp heB_finite
    (AlgHom.Finite.comp hInclusionToB0_finite hpolynomialToA_finite)

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: the fixed polynomial presentation of `S` base-changes to a
surjective generic-fiber presentation over the fraction field, and this generic-fiber map has
proper kernel once `R → S` is injective. -/
  private lemma generic_fiber_presentation_from_fixed_generators
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπsurj : Function.Surjective π) :
    ∃ piK : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S,
      Function.Surjective piK ∧
        (∀ i, piK (MvPolynomial.X i) =
          (1 : FractionRing R) ⊗ₜ[R] π (MvPolynomial.X i)) := by
  let K' := FractionRing R
  let x : Fin n → S := fun i ↦ π (MvPolynomial.X i)
  let tensorPresentation :
      TensorProduct R K' (MvPolynomial (Fin n) R) →ₐ[K'] TensorProduct R K' S :=
    Algebra.TensorProduct.map (AlgHom.id K' K') π
  let piK : MvPolynomial (Fin n) K' →ₐ[K'] TensorProduct R K' S :=
    MvPolynomial.aeval fun i ↦ (1 : K') ⊗ₜ[R] x i
  have htensor_surj : Function.Surjective tensorPresentation := by
    -- Tensoring the fixed surjective presentation with `K` keeps it surjective.
    exact Algebra.TensorProduct.map_surjective
      (f := AlgHom.id K' K') (g := π) Function.surjective_id hπsurj
  have hcomp :
      tensorPresentation.comp (MvPolynomial.algebraTensorAlgEquiv R K').symm.toAlgHom = piK := by
    -- Both descriptions of the generic-fiber map agree on the coordinate variables.
    ext i
    simp [tensorPresentation, piK, x]
  have hpiK_surj : Function.Surjective piK := by
    -- The tensor presentation is surjective, and the tensor/polynomial equivalence is bijective.
    rw [← hcomp]
    exact htensor_surj.comp (MvPolynomial.algebraTensorAlgEquiv R K').symm.surjective
  refine ⟨piK, hpiK_surj, ?_⟩
  intro i
  -- This is the fixed-coordinate formula used later when descending the normalization generators.
  simp [piK, x]

omit [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: tensoring the injective map `R → S` with the fraction field keeps
the generic fiber nontrivial, so the kernel of the generic-fiber presentation is proper. -/
private lemma generic_fiber_kernel_proper_from_injective_base_change
    {n : ℕ}
    (piK : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hinj : Function.Injective (algebraMap R S)) :
    RingHom.ker piK ≠ ⊤ := by
  -- Install the source-faithful nontriviality bridge on the generic fiber before taking kernels.
  letI : Nontrivial (TensorProduct R (FractionRing R) S) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := R) (A := FractionRing R) (B := S) hinj
  -- A map into a nontrivial ring cannot have kernel equal to the whole source.
  exact RingHom.ker_ne_top piK

omit [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: applying Lemma `10.115.4` to the proper kernel of the
generic-fiber presentation produces normalization polynomials with integer coordinates and a
finite injective polynomial map into the generic fiber. -/
private lemma generic_fiber_normalization_data_from_kernel
    {n : ℕ}
    (piK : MvPolynomial (Fin n) K →ₐ[K] TensorProduct R K S)
    (hpiK_surj : Function.Surjective piK)
    (hker : RingHom.ker piK ≠ ⊤) :
    ∃ (d : ℕ) (yK : Fin d → MvPolynomial (Fin n) K)
      (gK : MvPolynomial (Fin d) K →ₐ[K] TensorProduct R K S),
        (∀ i, yK i ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
          Fin n → MvPolynomial (Fin n) K))) ∧
          Function.Injective gK ∧ AlgHom.Finite gK ∧
            (∀ i, gK (MvPolynomial.X i) = piK (yK i)) := by
  -- Apply the field-case normalization theorem to the proper kernel quotient of `piK`.
  obtain ⟨d, yK, hyK, hquot⟩ :=
    exists_noether_normalization_polynomials_quotient_mvPolynomial
      (k := K) (n := n) (I := RingHom.ker piK) hker
  let h : MvPolynomial (Fin d) K →ₐ[K]
      (MvPolynomial (Fin n) K ⧸ RingHom.ker piK) :=
    MvPolynomial.aeval fun i ↦ Ideal.Quotient.mk (RingHom.ker piK) (yK i)
  have hhinj : Function.Injective h := by
    -- This is exactly the injective quotient-stage map supplied by Lemma `10.115.4`.
    simpa [h] using hquot.1
  have hkerLift_surj : Function.Surjective (Ideal.kerLiftAlg piK) := by
    -- Surjectivity of `piK` identifies the kernel quotient with the generic fiber itself.
    intro z
    rcases hpiK_surj z with ⟨p, rfl⟩
    exact ⟨Ideal.Quotient.mk _ p, by simp [Ideal.kerLiftAlg_mk]⟩
  let gK : MvPolynomial (Fin d) K →ₐ[K] TensorProduct R K S :=
    (Ideal.kerLiftAlg piK).comp h
  have hgK_injective : Function.Injective gK := by
    -- Injectivity survives composition because the kernel lift is injective.
    exact (Ideal.kerLiftAlg_injective piK).comp hhinj
  have hgK_finite : AlgHom.Finite gK := by
    have hkerLift_finite : AlgHom.Finite (Ideal.kerLiftAlg piK) := by
      -- The kernel-lift map is finite because it is surjective onto the generic fiber.
      exact AlgHom.Finite.of_surjective (Ideal.kerLiftAlg piK) hkerLift_surj
    have hh_finite : AlgHom.Finite h := by
      -- The quotient-stage normalization map is the finite map returned by Lemma `10.115.4`.
      simpa [h] using hquot.2
    exact AlgHom.Finite.comp hkerLift_finite hh_finite
  have hgK_X : ∀ i, gK (MvPolynomial.X i) = piK (yK i) := by
    intro i
    -- On variables, the composite is the quotient class followed by the canonical kernel lift.
    simp [gK, h, Ideal.kerLiftAlg_mk]
  have hyK' :
      ∀ i, yK i ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
        Fin n → MvPolynomial (Fin n) K)) := by
    intro i
    exact hyK i
  exact ⟨d, yK, gK, hyK', hgK_injective, hgK_finite, hgK_X⟩

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: every element of the coordinate `ℤ`-subalgebra of the generic
fiber polynomial ring can be evaluated in the fixed generators `x`, and its image in the generic
fiber agrees with the original polynomial expression. -/
private lemma exists_coordinate_int_expression_lift
    {n : ℕ}
    (piK : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (x : Fin n → S)
    (hpiK_X : ∀ i, piK (MvPolynomial.X i) = (1 : FractionRing R) ⊗ₜ[R] x i)
    {z : MvPolynomial (Fin n) (FractionRing R)}
    (hz : z ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
      Fin n → MvPolynomial (Fin n) (FractionRing R)))) :
    ∃ s : S, Algebra.TensorProduct.includeRight s = piK z := by
  let P :
      (p : MvPolynomial (Fin n) (FractionRing R)) →
        p ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
          Fin n → MvPolynomial (Fin n) (FractionRing R))) → Prop :=
    fun p _ ↦ ∃ s : S, Algebra.TensorProduct.includeRight s = piK p
  change P z hz
  -- Follow the source proof literally: expressions in the coordinate `ℤ`-subalgebra are built
  -- from the variables and integer scalars, and those already have evident lifts to `S`.
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · intro p hp
    rcases hp with ⟨i, rfl⟩
    refine ⟨x i, ?_⟩
    simpa using (hpiK_X i).symm
  · intro m
    refine ⟨algebraMap ℤ S m, ?_⟩
    -- Integer scalars agree in the ambient tensor product and in the generic-fiber polynomial map.
    calc
      Algebra.TensorProduct.includeRight (algebraMap ℤ S m)
          = algebraMap (FractionRing R) (TensorProduct R (FractionRing R) S)
              (algebraMap ℤ (FractionRing R) m) := by
                simp
      _ = piK (algebraMap ℤ (MvPolynomial (Fin n) (FractionRing R)) m) := by
            symm
            simpa using piK.commutes (algebraMap ℤ (FractionRing R) m)
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨sa, hsa⟩
    rcases hPb with ⟨sb, hsb⟩
    refine ⟨sa + sb, ?_⟩
    calc
      Algebra.TensorProduct.includeRight (sa + sb)
          = Algebra.TensorProduct.includeRight sa +
              Algebra.TensorProduct.includeRight sb := by
                simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add]
      _ = piK a + piK b := by rw [hsa, hsb]
      _ = piK (a + b) := by rw [map_add]
  · intro a b ha hb hPa hPb
    rcases hPa with ⟨sa, hsa⟩
    rcases hPb with ⟨sb, hsb⟩
    refine ⟨sa * sb, ?_⟩
    calc
      Algebra.TensorProduct.includeRight (sa * sb)
          = Algebra.TensorProduct.includeRight sa *
              Algebra.TensorProduct.includeRight sb := by
                simp [Algebra.TensorProduct.includeRight_apply]
      _ = piK a * piK b := by rw [hsa, hsb]
      _ = piK (a * b) := by rw [map_mul]

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: once the normalization generators are packaged inside the fixed
coordinate `ℤ`-subalgebra, they descend to actual elements of `S` with the same images in the
generic fiber. -/
private lemma descended_normalization_generators_from_coordinate_witnesses
    {n d : ℕ}
    (piK : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (x : Fin n → S)
    (hpiK_X : ∀ i, piK (MvPolynomial.X i) = (1 : FractionRing R) ⊗ₜ[R] x i)
    (yK : Fin d → MvPolynomial (Fin n) (FractionRing R))
    (hyK : ∀ i, yK i ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X :
      Fin n → MvPolynomial (Fin n) (FractionRing R))))
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hgK_X : ∀ i, gK (MvPolynomial.X i) = piK (yK i)) :
    ∃ y : Fin d → S,
      ∀ i, Algebra.TensorProduct.includeRight (y i) = gK (MvPolynomial.X i) := by
  -- Lift each coordinate expression separately, then rewrite with the generic-fiber
  -- normalization identity on variables.
  choose y hy using fun i ↦
    exists_coordinate_int_expression_lift
      (R := R) (S := S) piK x hpiK_X (hyK i)
  refine ⟨y, ?_⟩
  intro i
  rw [hgK_X i]
  exact hy i

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: after descending the generic-fiber normalization generators to a
tuple `y : Fin d → S`, the canonical generic-fiber polynomial map is evaluation at the tensorized
tuple `1 ⊗ y_i`. -/
private lemma generic_fiber_aeval_eq_descended_tuple
    {d : ℕ} (y : Fin d → S)
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hy_tensor_eq : ∀ i, Algebra.TensorProduct.includeRight (y i) = gK (MvPolynomial.X i)) :
    MvPolynomial.aeval (fun i : Fin d ↦ Algebra.TensorProduct.includeRight (y i)) = gK := by
  -- Two algebra maps from a polynomial ring agree once they agree on the coordinate variables.
  ext i
  -- The descended tuple was chosen exactly so that its tensor images match `gK(X_i)`.
  simpa using hy_tensor_eq i

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: comparing evaluation at the descended tuple with the injective
generic-fiber normalization map shows that `R[y₁, …, y_d] → S` is injective. -/
private lemma aeval_injective_of_generic_fiber_comparison
    {d : ℕ} (y : Fin d → S)
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hgK_injective : Function.Injective gK)
    (hy_tensor_eq : ∀ i, Algebra.TensorProduct.includeRight (y i) = gK (MvPolynomial.X i)) :
    Function.Injective (MvPolynomial.aeval y : MvPolynomial (Fin d) R →ₐ[R] S) := by
  have hcomp :
      (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp
          (MvPolynomial.aeval y) =
        (gK.restrictScalars R).comp
          (MvPolynomial.mapAlgHom (Algebra.ofId R (FractionRing R))) := by
    -- Both maps are polynomial evaluations, so it is enough to compare the variable images.
    ext i
    simp [hy_tensor_eq i]
  intro p q hpq
  have hmap_eq :
      MvPolynomial.map (algebraMap R (FractionRing R)) p =
        MvPolynomial.map (algebraMap R (FractionRing R)) q := by
    -- Applying the injective generic-fiber map converts equality in `S` to equality over `Frac(R)`.
    have hpq_tensor :
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp
          (MvPolynomial.aeval y)) p =
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp
          (MvPolynomial.aeval y)) q := by
      simpa [AlgHom.comp_apply] using
        congrArg
          (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S)
          hpq
    rw [hcomp] at hpq_tensor
    apply hgK_injective
    simpa [AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply] using hpq_tensor
  exact MvPolynomial.map_injective
    (σ := Fin d) (f := algebraMap R (FractionRing R))
    (IsFractionRing.injective R (FractionRing R)) hmap_eq

omit [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: a finite family of elements whose images vanish in the generic
fiber is killed in `S` after multiplying by one common nonzero element of `R`. -/
private lemma exists_nonzero_multiplier_of_tensor_zero_family
    {n : ℕ} (z : Fin n → S)
    (hz : ∀ i,
      (Algebra.TensorProduct.includeRight (z i) : TensorProduct R (FractionRing R) S) = 0) :
    ∃ f : R, f ≠ 0 ∧ ∀ i, algebraMap R S f * z i = 0 := by
  let _ : Algebra S (TensorProduct R (FractionRing R) S) := Algebra.TensorProduct.rightAlgebra
  let T : Submonoid S := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)
  choose m hm using fun i ↦
    (IsLocalization.map_eq_zero_iff T (TensorProduct R (FractionRing R) S) (z i)).mp (hz i)
  choose f hf_mem hf_eq using fun i ↦ (m i).2
  let g : R := ∏ i, f i
  have hg_ne_zero : g ≠ 0 := by
    -- Each factor lies in the nonzerodivisor submonoid of the domain `R`, so their product
    -- stays nonzero.
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact nonZeroDivisors.ne_zero (hf_mem i)
  refine ⟨g, hg_ne_zero, ?_⟩
  intro i
  have hm_i : algebraMap R S (f i) * z i = 0 := by
    -- Unpack the localization denominator chosen for the `i`-th zero relation.
    simpa [hf_eq i] using hm i
  have hfactor :
      algebraMap R S g =
        algebraMap R S (Finset.prod (Finset.univ.erase i) f) * algebraMap R S (f i) := by
    have hfactorR : Finset.prod (Finset.univ.erase i) f * f i = g := by
      simpa [g] using Finset.prod_erase_mul (s := Finset.univ) (f := f) (a := i) (by simp)
    rw [← hfactorR, map_mul]
  -- Reinsert the distinguished denominator factor on the right so that `hm_i` applies.
  calc
    algebraMap R S g * z i
        = (algebraMap R S (Finset.prod (Finset.univ.erase i) f) *
            algebraMap R S (f i)) * z i := by
              rw [hfactor]
    _ = algebraMap R S (Finset.prod (Finset.univ.erase i) f) *
          (algebraMap R S (f i) * z i) := by
            simp [mul_assoc]
    _ = 0 := by
          simp [hm_i]

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: if the polynomial map on `y` is injective and the extra generators
are integral over `R[y]`, then the intermediate algebra they generate is finite over that
polynomial algebra via an injective map. -/
private lemma exists_injective_finite_polynomial_map_to_intermediate_of_integral_generators
    {d n : ℕ} (y : Fin d → S) (x' : Fin n → S)
    (hy_inj : Function.Injective (MvPolynomial.aeval y : MvPolynomial (Fin d) R →ₐ[R] S))
    (hx'int : ∀ i, IsIntegral (Algebra.adjoin R (Set.range y)) (x' i)) :
    ∃ polynomialToIntermediate :
        MvPolynomial (Fin d) R →ₐ[R] Algebra.adjoin R (Set.range y ∪ Set.range x'),
      Function.Injective polynomialToIntermediate ∧ AlgHom.Finite polynomialToIntermediate := by
  let A : Subalgebra R S := Algebra.adjoin R (Set.range y)
  let B : Subalgebra R S := Algebra.adjoin R (Set.range y ∪ Set.range x')
  let ψS : MvPolynomial (Fin d) R →ₐ[R] S := MvPolynomial.aeval y
  have hψS_range : ψS.range = A := by
    -- The polynomial map generated by `y` has range exactly the subalgebra `R[y]`.
    simpa [A, ψS] using
      (Algebra.adjoin_range_eq_range_aeval (R := R) (f := y)).symm
  let eA : ψS.range ≃ₐ[R] A := Subalgebra.equivOfEq _ _ hψS_range
  let polynomialToA : MvPolynomial (Fin d) R →ₐ[R] A :=
    eA.toAlgHom.comp ψS.rangeRestrict
  have hpolynomialToA_inj : Function.Injective polynomialToA := by
    -- The range restriction is injective because the ambient evaluation map is injective.
    intro p q hpq
    apply hy_inj
    exact congrArg Subtype.val (eA.injective hpq)
  have hpolynomialToA_surj : Function.Surjective polynomialToA := by
    intro a
    let a' : ψS.range := eA.symm a
    rcases ψS.rangeRestrict_surjective a' with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    -- The range equivalence identifies the restricted polynomial map with `A`.
    change eA (ψS.rangeRestrict p) = a
    rw [hp]
    exact eA.apply_symm_apply a
  have hpolynomialToA_finite : AlgHom.Finite polynomialToA := by
    -- Surjective algebra maps are finite.
    exact AlgHom.Finite.of_surjective polynomialToA hpolynomialToA_surj
  let _ : Algebra A S := A.val.toAlgebra
  let B0 : Subalgebra A S := Algebra.adjoin A (Set.range x')
  have hB0_finite :
      RingHom.Finite (algebraMap A B0) := by
    -- The larger algebra is obtained by adjoining finitely many elements integral over `A`.
    change RingHom.Finite (algebraMap A (Algebra.adjoin A (Set.range x')))
    rw [RingHom.finite_algebraMap]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x')
      (fun z hz ↦ by
        rcases hz with ⟨i, rfl⟩
        exact hx'int i)
  have hA_le_B0 : A ≤ B0.restrictScalars R := by
    intro a ha
    change (a : S) ∈ B0
    exact Subalgebra.algebraMap_mem B0 ⟨a, ha⟩
  let inclusionToB0 : A →ₐ[R] B0.restrictScalars R := Subalgebra.inclusion hA_le_B0
  have hInclusionToB0_inj : Function.Injective inclusionToB0 := by
    -- Inclusions of subalgebras are injective on the underlying carrier.
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun t : B0.restrictScalars R ↦ (t : S)) hab
  have hInclusionToB0_finite : AlgHom.Finite inclusionToB0 := by
    -- This inclusion is the algebra map into the finite `A`-adjoin of the integral generators.
    simpa [AlgHom.Finite, RingHom.Finite, inclusionToB0] using hB0_finite
  have hB0_eq_B : B0.restrictScalars R = B := by
    -- Reassociate adjoining `x'` over `A = R[y]` with adjoining `y` and `x'` over `R`.
    simpa [A, B, B0] using
      (Algebra.adjoin_union_eq_adjoin_adjoin
        (R := R) (s := Set.range y) (t := Set.range x')).symm
  let eB : B0.restrictScalars R ≃ₐ[R] B := Subalgebra.equivOfEq _ _ hB0_eq_B
  let polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] B :=
    eB.toAlgHom.comp (inclusionToB0.comp polynomialToA)
  have hpolynomialToIntermediate_inj :
      Function.Injective polynomialToIntermediate := by
    -- The map factors through two injective inclusions and one algebra equivalence.
    exact eB.injective.comp (hInclusionToB0_inj.comp hpolynomialToA_inj)
  have heB_finite : AlgHom.Finite eB.toAlgHom := by
    -- Algebra equivalences are finite because they are surjective.
    exact AlgHom.Finite.of_surjective eB.toAlgHom eB.surjective
  have hpolynomialToIntermediate_finite :
      AlgHom.Finite polynomialToIntermediate := by
    exact AlgHom.Finite.comp heB_finite
      (AlgHom.Finite.comp hInclusionToB0_finite hpolynomialToA_finite)
  exact ⟨polynomialToIntermediate, hpolynomialToIntermediate_inj,
    hpolynomialToIntermediate_finite⟩

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: the scaled generators lie in the intermediate algebra generated by
the descended normalization tuple and those scaled generators. -/
private lemma mem_adjoin_union_scaled_generator
    {d n : ℕ} (y : Fin d → S) (x' : Fin n → S) (i : Fin n) :
    x' i ∈ Algebra.adjoin R (Set.range y ∪ Set.range x') := by
  -- By definition, every chosen scaled generator belongs to the adjoin of the union.
  exact Algebra.subset_adjoin (by
    exact Or.inr ⟨i, rfl⟩)

omit [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: finitely many generators that become integral after individual
nonzero scalings admit one common nonzero scaling that works for all of them at once. -/
private lemma exists_common_multiple_of_integral_family
    {n : ℕ} (A : Subalgebra R S) (x : Fin n → S)
    (hx : ∀ i : Fin n, ∃ r : R, r ≠ 0 ∧ IsIntegral A (algebraMap R S r * x i)) :
    ∃ f : R, f ≠ 0 ∧ ∀ i : Fin n, IsIntegral A (algebraMap R S f * x i) := by
  classical
  choose r hr0 hrint using hx
  let f : R := ∏ i, r i
  have hf : f ≠ 0 := by
    -- The common denominator is the product of the individual nonzero denominators.
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact hr0 i
  refine ⟨f, hf, ?_⟩
  intro i
  have hfactor : f = Finset.prod (Finset.univ.erase i) r * r i := by
    symm
    simpa [f, mul_comm] using
      (Finset.prod_erase_mul (s := Finset.univ) (f := r) (a := i) (by simp))
  have hcoeff :
      IsIntegral A (algebraMap R S (Finset.prod (Finset.univ.erase i) r)) := by
    -- The extra factor still comes from the base ring, hence is automatically integral over `A`.
    simpa only [IsScalarTower.algebraMap_apply R A S] using
      (isIntegral_algebraMap (R := A) (A := S)
        (x := algebraMap R A (Finset.prod (Finset.univ.erase i) r)))
  -- Multiply the integral element for the `i`-th generator by the remaining coefficient.
  have hscaled :
      IsIntegral A
        (algebraMap R S (Finset.prod (Finset.univ.erase i) r) *
          (algebraMap R S (r i) * x i)) := by
    -- Multiply the given integral element by the remaining coefficient from the base ring.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcoeff.mul (hrint i)
  -- Rewrite the common denominator as the distinguished factor times the remaining product.
  simpa [hfactor, map_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: after identifying `A = R[y]` with the polynomial ring on the
descended tuple, the induced map to the generic fiber is evaluation at `1 ⊗ y_i`. -/
private lemma generic_fiber_map_eq_adjoin_tensor_map
    {d : ℕ} (y : Fin d → S)
    (A : Subalgebra R S)
    (eA : MvPolynomial (Fin d) R ≃ₐ[R] A)
    (heA_X : ∀ i : Fin d, ((eA (MvPolynomial.X i) : A) : S) = y i)
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hy_tensor_eq : ∀ i, Algebra.TensorProduct.includeRight (y i) = gK (MvPolynomial.X i)) :
    let ψK : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) (FractionRing R) :=
      MvPolynomial.mapAlgHom (Algebra.ofId R (FractionRing R))
    letI : Algebra S (TensorProduct R (FractionRing R) S) := Algebra.TensorProduct.rightAlgebra
    let ιA : A →ₐ[R] TensorProduct R (FractionRing R) S :=
      (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp A.val
    ιA.comp eA = (gK.restrictScalars R).comp ψK := by
  let ψK : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) (FractionRing R) :=
    MvPolynomial.mapAlgHom (Algebra.ofId R (FractionRing R))
  letI : Algebra S (TensorProduct R (FractionRing R) S) := Algebra.TensorProduct.rightAlgebra
  let ιA : A →ₐ[R] TensorProduct R (FractionRing R) S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp A.val
  -- Compare the two maps on the coordinate variables; polynomial maps are determined by them.
  refine MvPolynomial.algHom_ext
    (R := R) (σ := Fin d) (A := TensorProduct R (FractionRing R) S) fun j ↦ ?_
  change
    Algebra.TensorProduct.includeRight (((eA (MvPolynomial.X j) : A) : S)) =
      ((gK.restrictScalars R).comp ψK) (MvPolynomial.X j)
  rw [heA_X j, hy_tensor_eq j]
  simp [ψK]

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: transporting the standard localization
`R[T₁, …, T_d] → Frac(R)[T₁, …, T_d]` across the polynomial presentation
`eA : R[T₁, …, T_d] ≃ A = R[y]` yields the localization of `A` at the
nonzero elements of `R`. -/
private lemma polynomial_fraction_isLocalization_over_adjoin_nonZeroDivisors
    {d : ℕ} (A : Subalgebra R S)
    (eA : MvPolynomial (Fin d) R ≃ₐ[R] A)
    (AtoK : A →ₐ[R] MvPolynomial (Fin d) (FractionRing R)) :
    AtoK.comp eA.toAlgHom =
      MvPolynomial.mapAlgHom (Algebra.ofId R (FractionRing R)) →
    letI : Algebra A (MvPolynomial (Fin d) (FractionRing R)) := AtoK.toRingHom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      (MvPolynomial (Fin d) (FractionRing R)) := by
  -- TODO: transport `MvPolynomial.isLocalization` across `eA` using the compatibility
  -- `AtoK.comp eA = mapAlgHom`, then rewrite the mapped denominator submonoid to
  -- `Algebra.algebraMapSubmonoid A (nonZeroDivisors R)`.
  sorry

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: the localization submonoid coming from `A = R[y]` is exactly the
ambient image of `nonZeroDivisors R` in `S`. -/
private lemma tensor_product_isLocalization_over_adjoin_nonZeroDivisors
    (A : Subalgebra R S) :
    Algebra.algebraMapSubmonoid S (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) =
      Algebra.algebraMapSubmonoid S (nonZeroDivisors R) := by
  ext z
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    -- Any denominator coming from `A` still comes from the original base ring `R`.
    exact ⟨r, hr, by simp only [IsScalarTower.algebraMap_apply R A S]⟩
  · rintro ⟨r, hr, rfl⟩
    -- Conversely, a denominator from `R` maps into `A` before entering `S`.
    exact ⟨algebraMap R A r, ⟨r, hr, rfl⟩, by
      simp only [IsScalarTower.algebraMap_apply R A S]⟩

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: a single generator becomes integral over `A = R[y]` in the generic
fiber after clearing one denominator coming from the localization `A → Frac(R)[y]`. -/
private lemma exists_integral_tensor_scaled_generator_over_adjoin
    {n d : ℕ} (A : Subalgebra R S)
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hgK_finite : AlgHom.Finite gK)
    [Algebra A S]
    [Algebra S (TensorProduct R (FractionRing R) S)]
    [Algebra A (MvPolynomial (Fin d) (FractionRing R))]
    [Algebra A (TensorProduct R (FractionRing R) S)]
    [Algebra (MvPolynomial (Fin d) (FractionRing R)) (TensorProduct R (FractionRing R) S)]
    [IsScalarTower A S (TensorProduct R (FractionRing R) S)]
    [IsScalarTower A (MvPolynomial (Fin d) (FractionRing R))
      (TensorProduct R (FractionRing R) S)]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R))
      (MvPolynomial (Fin d) (FractionRing R))]
    (hgK_alg :
      algebraMap (MvPolynomial (Fin d) (FractionRing R))
          (TensorProduct R (FractionRing R) S) = gK.toRingHom)
    (x : Fin n → S) (i : Fin n) :
    ∃ m : Algebra.algebraMapSubmonoid A (nonZeroDivisors R), IsIntegral A
      (algebraMap S (TensorProduct R (FractionRing R) S) (m • x i)) := by
  -- TODO: first rewrite integrality from `gK.toRingHom.IsIntegralElem` to the ambient
  -- `IsIntegral` statement via `hgK_alg`, then invoke
  -- `IsIntegral.exists_multiple_integral_of_isLocalization` for the localization
  -- `A → Frac(R)[y]`, and finally rewrite the resulting smul as the image of `m • x i`.
  sorry

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: after the tensor-level denominator is cleared, one more
localization step clears the denominator back in `S`, producing an `R`-multiple integral over
`A = R[y]`. -/
private lemma exists_integral_scaled_generator_over_adjoin
    {n : ℕ} (A : Subalgebra R S)
    [Algebra A S]
    [Algebra S (TensorProduct R (FractionRing R) S)]
    [Algebra A (TensorProduct R (FractionRing R) S)]
    [IsScalarTower A S (TensorProduct R (FractionRing R) S)]
    [IsLocalization
      (Algebra.algebraMapSubmonoid S
        (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)))
      (TensorProduct R (FractionRing R) S)]
    (x : Fin n → S) (i : Fin n)
    (hx :
      ∃ m : Algebra.algebraMapSubmonoid A (nonZeroDivisors R), IsIntegral A
        (algebraMap S (TensorProduct R (FractionRing R) S) (m • x i))) :
    ∃ r : R, r ≠ 0 ∧ IsIntegral A (algebraMap R S r * x i) := by
  -- TODO: descend the tensor-level integral relation through
  -- `IsLocalization.exists_isIntegral_smul_of_isIntegral_map`, unpack both submonoid elements
  -- as images of nonzero elements of `R`, and combine them into one product scalar in `R`.
  sorry

omit [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.115.7: once the generic-fiber normalization tuple has descended to `S`,
one still has to clear one common denominator so that the original finite-type generators become
integral over `R[y₁, …, y_d]`. -/
private lemma exists_common_scaled_integral_generators_over_adjoin_range
    {n d : ℕ} (x : Fin n → S) (y : Fin d → S)
    (hy_inj : Function.Injective (MvPolynomial.aeval y : MvPolynomial (Fin d) R →ₐ[R] S))
    (gK : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
        TensorProduct R (FractionRing R) S)
    (hgK_finite : AlgHom.Finite gK)
    (hy_tensor_eq : ∀ i, Algebra.TensorProduct.includeRight (y i) = gK (MvPolynomial.X i)) :
    ∃ f : R, f ≠ 0 ∧ ∃ x' : Fin n → S,
      (∀ i, x' i = algebraMap R S f * x i) ∧
      (∀ i, IsIntegral (Algebra.adjoin R (Set.range y)) (x' i)) := by
  let A : Subalgebra R S := Algebra.adjoin R (Set.range y)
  let ψS : MvPolynomial (Fin d) R →ₐ[R] S := MvPolynomial.aeval y
  have hψS_range : ψS.range = A := by
    -- The source-faithful polynomial subalgebra on `y` is exactly the adjoin of the descended
    -- normalization tuple.
    simpa [A, ψS] using
      (Algebra.adjoin_range_eq_range_aeval (R := R) (f := y)).symm
  let eA_range : ψS.range ≃ₐ[R] A := Subalgebra.equivOfEq _ _ hψS_range
  let ψA : MvPolynomial (Fin d) R →ₐ[R] A := eA_range.toAlgHom.comp ψS.rangeRestrict
  have hψA_bijective : Function.Bijective ψA := by
    refine ⟨?_, ?_⟩
    · intro p q hpq
      -- Injectivity is exactly the previously established comparison with the generic fiber.
      apply hy_inj
      exact congrArg Subtype.val (eA_range.injective hpq)
    · intro a
      let a' : ψS.range := eA_range.symm a
      rcases ψS.rangeRestrict_surjective a' with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      -- Surjectivity is the usual range-restriction surjectivity rewritten through the adjoin.
      change eA_range (ψS.rangeRestrict p) = a
      rw [hp]
      exact eA_range.apply_symm_apply a
  let eA : MvPolynomial (Fin d) R ≃ₐ[R] A := AlgEquiv.ofBijective ψA hψA_bijective
  have heA_X : ∀ i : Fin d, ((eA (MvPolynomial.X i) : A) : S) = y i := by
    intro i
    -- The equivalence `eA` extends the original evaluation map on the chosen variables.
    change ((ψS.rangeRestrict (MvPolynomial.X i) : ψS.range) : S) = y i
    simp [ψS]
  let ψK : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) (FractionRing R) :=
    MvPolynomial.mapAlgHom (Algebra.ofId R (FractionRing R))
  have hA_tensor :
      letI : Algebra S (TensorProduct R (FractionRing R) S) := Algebra.TensorProduct.rightAlgebra
      let ιA : A →ₐ[R] TensorProduct R (FractionRing R) S :=
        (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp A.val
      ιA.comp eA = (gK.restrictScalars R).comp ψK := by
    -- This packages the transported `A`-algebra structure on the generic fiber.
    simpa using generic_fiber_map_eq_adjoin_tensor_map
      (R := R) (S := S) y A eA heA_X gK hy_tensor_eq
  have hlocal_submonoid :
      Algebra.algebraMapSubmonoid S (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) =
        Algebra.algebraMapSubmonoid S (nonZeroDivisors R) := by
    -- The localization denominators over `A` are exactly the original nonzero elements of `R`.
    simpa using tensor_product_isLocalization_over_adjoin_nonZeroDivisors
      (R := R) (S := S) A
  letI : Algebra S (TensorProduct R (FractionRing R) S) := Algebra.TensorProduct.rightAlgebra
  let ιA : A →ₐ[R] TensorProduct R (FractionRing R) S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] TensorProduct R (FractionRing R) S).comp A.val
  let AtoK : A →ₐ[R] MvPolynomial (Fin d) (FractionRing R) := ψK.comp eA.symm
  have hA_comp :
      ιA = (gK.restrictScalars R).comp AtoK := by
    ext a
    -- The transported `A`-algebra structure on the generic fiber is exactly the one from `gK`.
    have h := congrArg
      (fun φ : MvPolynomial (Fin d) R →ₐ[R] TensorProduct R (FractionRing R) S ↦
        φ (eA.symm a)) hA_tensor
    simpa [AtoK, ιA] using h
  letI : Algebra A (MvPolynomial (Fin d) (FractionRing R)) := AtoK.toRingHom.toAlgebra
  letI : Algebra A (TensorProduct R (FractionRing R) S) := ιA.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) (FractionRing R))
      (TensorProduct R (FractionRing R) S) := gK.toRingHom.toAlgebra
  letI : IsScalarTower A (MvPolynomial (Fin d) (FractionRing R))
      (TensorProduct R (FractionRing R) S) :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hA_comp)
  let M : Submonoid A := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  have hM_local :
      IsLocalization M (MvPolynomial (Fin d) (FractionRing R)) := by
    -- Use the standalone transport lemma so the main proof keeps only the source-faithful
    -- localization step instead of redoing the coercion-heavy comparison inline.
    simpa [M] using
      polynomial_fraction_isLocalization_over_adjoin_nonZeroDivisors
        (R := R) (S := S) A eA AtoK (by
          ext p
          simp [AtoK, ψK])
  letI : IsLocalization M (MvPolynomial (Fin d) (FractionRing R)) := hM_local
  letI : Algebra A S := A.val.toAlgebra
  letI : IsScalarTower A S (TensorProduct R (FractionRing R) S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hS_local :
      IsLocalization (Algebra.algebraMapSubmonoid S M) (TensorProduct R (FractionRing R) S) := by
    -- Localizing `S` at the denominators coming from `A` is the same as localizing away from
    -- the original nonzero elements of `R`.
    simpa [M, hlocal_submonoid] using
      (inferInstance :
        IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
          (TensorProduct R (FractionRing R) S))
  letI : IsLocalization (Algebra.algebraMapSubmonoid S M)
      (TensorProduct R (FractionRing R) S) := hS_local
  have hx_each :
      ∀ i : Fin n, ∃ r : R, r ≠ 0 ∧ IsIntegral A (algebraMap R S r * x i) := by
    intro i
    have hx_tensor :
        ∃ m : Algebra.algebraMapSubmonoid A (nonZeroDivisors R), IsIntegral A
          (algebraMap S (TensorProduct R (FractionRing R) S) (m • x i)) := by
      -- First clear the denominator created in the generic fiber `Frac(R)[y] ⊂ S_K`.
      exact exists_integral_tensor_scaled_generator_over_adjoin
        (R := R) (S := S) A gK hgK_finite (hgK_alg := rfl) x i
    -- Then descend that integral relation through the localization `S → S_K`.
    exact exists_integral_scaled_generator_over_adjoin
      (R := R) (S := S) A x i hx_tensor
  obtain ⟨f, hf, hxf⟩ :=
    exists_common_multiple_of_integral_family (R := R) (S := S) A x hx_each
  refine ⟨f, hf, fun i ↦ algebraMap R S f * x i, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    simpa using hxf i

-- Proof sketch: pass from the injective finite type `R`-algebra `S` to its generic fiber over the
-- fraction field of the domain `R`, apply the field case of Noether normalization there, and then
-- clear denominators to descend the normalization data back to a localization of `R`. This
-- produces an injective polynomial subalgebra, a finite intermediate algebra, and a nonzero
-- element `f ∈ R` away from which the canonical localized map from the intermediate algebra to `S`
-- is bijective.
/-- Lemma 10.115.7: let `R → S` be an injective finite type ring map with `R` a domain. Then
there exist an integer `d` and a factorization `R → R[y₁, …, y_d] → S' → S` by injective maps
such that `S'` is finite over `R[y₁, …, y_d]` and such that `S'_f ≃ S_f` for some nonzero
`f ∈ R`. -/
theorem exists_injective_polynomial_factorization_of_injective_finiteType
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (d : ℕ) (S' : Subalgebra R S)
      (polynomialToIntermediate : MvPolynomial (Fin d) R →ₐ[R] S') (f : R),
      IsInjectivePolynomialFactorizationAway d S' polynomialToIntermediate f := by
  -- Follow the source proof by fixing one polynomial presentation of `S` and naming its
  -- coordinate images as the generators that all later denominator clearing refers to.
  obtain ⟨n, π, hπsurj⟩ :=
    exists_surjective_mvPolynomial_presentation (R := R) (S := S)
  let x : Fin n → S := fun i ↦ π (MvPolynomial.X i)
  have hx_top : Algebra.adjoin R (Set.range x) = ⊤ := by
    -- This is the source-side generator tuple `x₁, …, xₙ` fixed once and for all.
    simpa [x] using
      adjoin_range_presentation_variables_eq_top (R := R) (S := S) π hπsurj
  have hx_inj : Function.Injective (algebraMap R ((Algebra.adjoin R (Set.range x)))) := by
    -- Any eventual intermediate subalgebra built from these generators still sees `R`
    -- injectively, because the ambient map `R → S` is injective.
    exact algebraMap_injective_subalgebra (R := R) (S := S)
      (Algebra.adjoin R (Set.range x)) hinj
  have hpiK_data :
      ∃ piK : MvPolynomial (Fin n) (FractionRing R) →ₐ[FractionRing R]
          TensorProduct R (FractionRing R) S,
        Function.Surjective piK ∧
          (∀ i, piK (MvPolynomial.X i) = (1 : FractionRing R) ⊗ₜ[R] x i) := by
    -- The generic fiber is now packaged directly from the fixed generators `x`.
    simpa [x] using
      generic_fiber_presentation_from_fixed_generators (R := R) (S := S) π hπsurj
  -- Route correction: the earlier quotient-transport route was too coercion-heavy. The next step
  -- should define the generic-fiber map directly from the fixed generators `x` and work with its
  -- kernel, matching the source proof's normalization-over-the-fraction-field argument.
  obtain ⟨piK, hpiK_surj, hpiK_X⟩ := hpiK_data
  have hpiK_ker_proper : RingHom.ker piK ≠ ⊤ := by
    -- The generic fiber is nontrivial because `R → S` was assumed injective.
    exact generic_fiber_kernel_proper_from_injective_base_change
      (R := R) (S := S) piK hinj
  obtain ⟨d, yK, gK, hyK, hgK_injective, hgK_finite, hgK_X⟩ :=
    generic_fiber_normalization_data_from_kernel
      (R := R) (S := S) piK hpiK_surj hpiK_ker_proper
  obtain ⟨y, hy_tensor_eq⟩ :=
    descended_normalization_generators_from_coordinate_witnesses
      (R := R) (S := S) piK x hpiK_X yK hyK gK hgK_X
  have hpoly_inj :
      Function.Injective (MvPolynomial.aeval y : MvPolynomial (Fin d) R →ₐ[R] S) := by
    -- Comparing evaluation at `y` with the injective generic-fiber normalization map gives the
    -- injective polynomial algebra `R[y] ⊂ S`.
    exact aeval_injective_of_generic_fiber_comparison
      (R := R) (S := S) y gK hgK_injective hy_tensor_eq
  obtain ⟨f, hf, x', hxscaled, hx'int⟩ :=
    exists_common_scaled_integral_generators_over_adjoin_range
      (R := R) (S := S) x y hpoly_inj gK hgK_finite hy_tensor_eq
  obtain ⟨polynomialToIntermediate, hpoly'_inj, hpoly'_finite⟩ :=
    exists_injective_finite_polynomial_map_to_intermediate_of_integral_generators
      (R := R) (S := S) y x' hpoly_inj hx'int
  let S' : Subalgebra R S := Algebra.adjoin R (Set.range y ∪ Set.range x')
  let xSub : Fin n → S' := fun i ↦
    ⟨x' i, mem_adjoin_union_scaled_generator (R := R) (S := S) y x' i⟩
  have hxSub : ∀ i, (xSub i : S) = algebraMap R S f * x i := by
    -- The chosen generators of the intermediate algebra are exactly the scaled source generators.
    intro i
    simpa [xSub] using hxscaled i
  have hsurj :
      Function.Surjective (Localization.awayMapₐ S'.val (algebraMap R S' f)) := by
    -- After inverting `f`, the original generating tuple is recovered inside the intermediate
    -- algebra, so the away map is surjective.
    exact awayMap_surjective_of_scaled_generators
      (R := R) (S := S) S' f x xSub hx_top hxSub
  refine ⟨d, S', polynomialToIntermediate, f, ?_⟩
  -- The remaining data are now exactly the injective finite polynomial map and the bijective away
  -- comparison assembled above.
  exact factorizationAway_of_surjective_awayMap
    (R := R) (S := S) S' polynomialToIntermediate f
    hpoly'_inj hpoly'_finite hf hsurj

end
