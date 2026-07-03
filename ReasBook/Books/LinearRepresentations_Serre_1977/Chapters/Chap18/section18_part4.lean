import Mathlib
import Mathlib.RingTheory.Morita.Matrix

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_18_18_2_8 (from Chap18) -/
noncomputable section

open scoped Representation TensorProduct

universe u v w

namespace Representation

section PrimeSpectrumOfRepresentationRing

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Type v} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type w}

open PrimeSpectrum

local notation "RK" => K ⊗[ℤ] R₀[k](G)
local notation "ClassFnK" => PRegularConjClass G p → K

/- Domain-style sampling for this item:
* primary domain: prime ideals of the commutative ring `RK` and their classification through the
  function ring on `PRegularConjClass G p`.
* inspected owner declarations in this domain:
  `scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom`,
  `scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv`,
  `PrimeSpectrum.exists_comap_evalRingHom_eq`,
  and `Pi.evalRingHom`.
* best owner abstraction: the algebra equivalence
  `scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv`, with prime ideals of `RK`
  obtained by transport from the canonical evaluation primes of the function ring `ClassFnK`.
* `PRegularConjClass.ofSubtype` remains the quotient-level bridge from chosen `p`-regular
  representatives to the owner `PRegularConjClass G p`.

Layer triage:
* source-facing: prime ideals of LinearRepresentations_Serre_1977's scalar-extended representation ring
  `RK`.
* core/canonical: `scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv`.
* bridge/view: `pRegularPrime`, obtained by comapping the evaluation prime of `ClassFnK`, together
  with representative-indexed reformulations via `PRegularConjClass.ofSubtype`.

Primitive data vs. derived API:
* primitive data: the scalar-extended ring `RK`, a multiplicative lift
  `PrimeToPRoot p k →* Kˣ`, and a `p`-regular conjugacy class.
* derived API: the indexed prime `pRegularPrime`, the classification theorem under injectivity of
  the lift, and the kernel-style reformulations obtained by evaluating the algebra equivalence and
  by passing to chosen representatives.
-/

-- Proof sketch: evaluate the scalar-extension Brauer-character algebra homomorphism at the class
-- `c` using the canonical `K`-algebra evaluation map on `ClassFnK`, then comap the unique prime
-- of the field `K`.
/-- Bridge/view: the prime ideal of `RK` attached to a `p`-regular conjugacy class `c`, obtained
by transporting the evaluation prime of the function ring `ClassFnK` along the scalar-extension
Brauer-character algebra homomorphism. -/
noncomputable def pRegularPrime
    (lift : PrimeToPRoot p k →* Kˣ) (c : PRegularConjClass G p) : PrimeSpectrum RK :=
  PrimeSpectrum.comap
    (((Pi.evalAlgHom K (fun _ : PRegularConjClass G p ↦ K) c).comp
      (scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
        (p := p) (k := k) (K := K) (G := G) lift)) : RK →+* K)
    ⟨(⊥ : Ideal K), by infer_instance⟩

-- Proof sketch: unfold `pRegularPrime`; membership in the comap of the zero prime of `K` is
-- exactly vanishing of the evaluated scalar-extension Brauer character.
/-- Membership in `pRegularPrime lift c` is exactly vanishing of the scalar-extension Brauer
character at `c`. -/
theorem mem_pRegularPrime_iff
    (lift : PrimeToPRoot p k →* Kˣ) (c : PRegularConjClass G p) (x : RK) :
    x ∈ (pRegularPrime lift c).asIdeal ↔
      scalarExtensionBrauerCharacterOnPRegularConjClass
        (p := p) (k := k) (K := K) (G := G) lift x c = 0 := by
  -- Unfold the defining comap prime and reduce membership in the bottom ideal to vanishing.
  rw [pRegularPrime, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  -- The evaluation algebra homomorphism simply reads off the value at `c`.
  simp

/-- Helper for Exercise 18-18.2-8: every prime of the function ring on
`PRegularConjClass G p` is the coordinate-evaluation prime at some class. -/
theorem exists_eq_eval_prime_of_primeSpectrum_classFnK
    (P : PrimeSpectrum ClassFnK) :
    ∃ c : PRegularConjClass G p,
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
        ⟨(⊥ : Ideal K), inferInstance⟩ = P := by
  -- First classify the prime by a coordinate and an arbitrary prime of the field factor.
  obtain ⟨c, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (R := fun _ : PRegularConjClass G p ↦ K) P
  refine ⟨c, ?_⟩
  -- A field has only the zero prime, so the residual prime factor is forced to be `⊥`.
  have hqbot : q = ⟨(⊥ : Ideal K), inferInstance⟩ := by
    exact Subsingleton.elim q ⟨(⊥ : Ideal K), inferInstance⟩
  simpa [hqbot] using hq

section

omit [Finite G] in
/-- Helper for Exercise 18-18.2-8: on the function ring side, two coordinate-evaluation primes
agree exactly when their `p`-regular class parameters agree. -/
theorem classFnK_eval_prime_eq_iff
    (c₁ c₂ : PRegularConjClass G p) :
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
        ⟨(⊥ : Ideal K), inferInstance⟩ =
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂)
        ⟨(⊥ : Ideal K), inferInstance⟩ ↔
      c₁ = c₂ := by
  constructor
  · intro hprime
    by_contra hne
    classical
    let f : PRegularConjClass G p → K := fun d ↦ if d = c₁ then 1 else 0
    have hf₂ :
        f ∈ (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂)
          ⟨(⊥ : Ideal K), inferInstance⟩).asIdeal := by
      -- The point mass at `c₁` vanishes at `c₂` when the classes are distinct.
      change Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂ f = 0
      simp [f, eq_comm, hne]
    have hf₁ :
        f ∉ (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
          ⟨(⊥ : Ideal K), inferInstance⟩).asIdeal := by
      -- The same function does not vanish at its distinguished coordinate `c₁`.
      change Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁ f ≠ 0
      simp [f]
    have hmem_eq :
        (f ∈ (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
          ⟨(⊥ : Ideal K), inferInstance⟩).asIdeal) =
          (f ∈ (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂)
            ⟨(⊥ : Ideal K), inferInstance⟩).asIdeal) := by
      exact congrArg (fun Q ↦ f ∈ Q.asIdeal) hprime
    have hmem :
        f ∈ (PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
          ⟨(⊥ : Ideal K), inferInstance⟩).asIdeal := by
      exact hmem_eq.mpr hf₂
    exact hf₁ hmem
  · intro hc
    -- Matching coordinates give definitionally the same evaluation prime.
    subst hc
    rfl

end

section Equivalence

variable [CharP k p]

section

/-- Helper for Exercise 18-18.2-8: transporting `pRegularPrime lift c` across the temporary
scalar-extension Brauer-character algebra equivalence recovers the coordinate-evaluation prime on
`ClassFnK`. -/
theorem comap_pRegularPrime_eq_eval_prime_aux
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (c : PRegularConjClass G p) :
    PrimeSpectrum.comap
        (↑((scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
            (p := p) (k := k) (K := K) (G := G) lift hlift).toRingEquiv.symm))
        (pRegularPrime lift c) =
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
        ⟨(⊥ : Ideal K), inferInstance⟩ := by
  let e :=
    scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
      (p := p) (k := k) (K := K) (G := G) lift hlift
  let f : ClassFnK →+* RK := ↑(e.toRingEquiv.symm)
  have hcomp :
      ((((Pi.evalAlgHom K (fun _ : PRegularConjClass G p ↦ K) c).comp
            (scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
              (p := p) (k := k) (K := K) (G := G) lift)) : RK →ₐ[K] K).toRingHom.comp
          f) =
        Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c := by
    -- Route correction: compare the transported prime through the concrete composite ring map,
    -- then identify that composite with plain coordinate evaluation on `ClassFnK`.
    ext x
    change
      (scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
        (p := p) (k := k) (K := K) (G := G) lift (e.symm x)) c = x c
    -- The local equivalence and algebra hom encode the same map, so `e (e.symm x) = x`.
    rw [← scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv_toAlgHom
      (p := p) (k := k) (K := K) (G := G) (lift := lift) (hlift := hlift)]
    simp [e]
  -- Rewrite the iterated comap as comap along the composite and then replace the composite map
  -- by the coordinate-evaluation homomorphism.
  rw [pRegularPrime]
  change PrimeSpectrum.comap
      ((((Pi.evalAlgHom K (fun _ : PRegularConjClass G p ↦ K) c).comp
            (scalarExtensionBrauerCharacterOnPRegularConjClassAlgHom
              (p := p) (k := k) (K := K) (G := G) lift)) : RK →ₐ[K] K).toRingHom.comp
          f)
      ⟨(⊥ : Ideal K), inferInstance⟩ =
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
      ⟨(⊥ : Ideal K), inferInstance⟩
  rw [hcomp]

/-- Helper for Exercise 18-18.2-8: transporting `pRegularPrime lift c` across the temporary
scalar-extension Brauer-character algebra equivalence recovers the coordinate-evaluation prime on
`ClassFnK`. -/
theorem comap_pRegularPrime_eq_eval_prime
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (c : PRegularConjClass G p) :
    PrimeSpectrum.comap
        (↑((scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
            (p := p) (k := k) (K := K) (G := G) lift hlift).toRingEquiv.symm))
        (pRegularPrime lift c) =
      PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
        ⟨(⊥ : Ideal K), inferInstance⟩ := by
  simpa using comap_pRegularPrime_eq_eval_prime_aux
    (p := p) (k := k) (K := K) (G := G) lift hlift c

-- Proof sketch: transport a prime of `RK` across
-- `scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv`; then
-- `PrimeSpectrum.exists_comap_evalRingHom_eq` classifies primes of the function ring `ClassFnK`
-- by evaluation at a coordinate, and the field factor contributes only the zero prime.
section

/-- Exercise 18-18.2-8 (core/canonical form): every prime ideal of `RK` is one of the evaluation
primes `pRegularPrime lift c`. -/
theorem exists_eq_pRegularPrime_aux
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (P : PrimeSpectrum RK) :
    ∃ c : PRegularConjClass G p,
      pRegularPrime lift c = P := by
  let e := (scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
    (p := p) (k := k) (K := K) (G := G) lift hlift).toRingEquiv
  let E : PrimeSpectrum RK ≃o PrimeSpectrum ClassFnK := PrimeSpectrum.comapEquiv e
  -- Push the prime to the function ring, where finite products of fields have coordinate primes.
  obtain ⟨c, hc⟩ := exists_eq_eval_prime_of_primeSpectrum_classFnK (K := K) (P := E P)
  refine ⟨c, ?_⟩
  -- Pull the coordinate prime back through the spectrum equivalence to recover `P`.
  apply E.injective
  calc
    E (pRegularPrime lift c) =
        PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c)
          ⟨(⊥ : Ideal K), inferInstance⟩ := by
      simpa [E] using comap_pRegularPrime_eq_eval_prime lift hlift c
    _ = E P := hc

/-- Exercise 18-18.2-8 (core/canonical form): every prime ideal of `RK` is one of the evaluation
primes `pRegularPrime lift c`. -/
theorem exists_eq_pRegularPrime
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (P : PrimeSpectrum RK) :
    ∃ c : PRegularConjClass G p,
      pRegularPrime lift c = P := by
  simpa using exists_eq_pRegularPrime_aux
    (p := p) (k := k) (K := K) (G := G) lift hlift P

end

-- Proof sketch: transport equality of indexed primes through the scalar-extension Brauer-character
-- algebra equivalence and use injectivity of `PrimeSpectrum.sigmaToPi` for finite products of
-- fields.
section

/-- Under an injective multiplicative lift, the primes `pRegularPrime lift c` are indexed
faithfully by `p`-regular conjugacy classes. -/
theorem pRegularPrime_eq_iff_aux
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (c₁ c₂ : PRegularConjClass G p) :
    pRegularPrime lift c₁ = pRegularPrime lift c₂ ↔
      c₁ = c₂ := by
  let e := (scalarExtensionBrauerCharacterOnPRegularConjClassAlgEquiv
    (p := p) (k := k) (K := K) (G := G) lift hlift).toRingEquiv
  let E : PrimeSpectrum RK ≃o PrimeSpectrum ClassFnK := PrimeSpectrum.comapEquiv e
  constructor
  · intro hprime
    -- Transport equality to the function-ring side and use the point-mass separator.
    have htransport :
        PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
            ⟨(⊥ : Ideal K), inferInstance⟩ =
          PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂)
            ⟨(⊥ : Ideal K), inferInstance⟩ := by
      calc
        PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₁)
            ⟨(⊥ : Ideal K), inferInstance⟩ =
            E (pRegularPrime lift c₁) := by
          simpa [E] using (comap_pRegularPrime_eq_eval_prime lift hlift c₁).symm
        _ = E (pRegularPrime lift c₂) := by
          simpa using congrArg E hprime
        _ = PrimeSpectrum.comap (Pi.evalRingHom (fun _ : PRegularConjClass G p ↦ K) c₂)
              ⟨(⊥ : Ideal K), inferInstance⟩ := by
          simpa [E] using comap_pRegularPrime_eq_eval_prime lift hlift c₂
    exact (classFnK_eval_prime_eq_iff (K := K) c₁ c₂).1 htransport
  · intro hc
    -- Equal class parameters give the same indexed prime by substitution.
    subst hc
    rfl

/-- Under an injective multiplicative lift, the primes `pRegularPrime lift c` are indexed
faithfully by `p`-regular conjugacy classes. -/
theorem pRegularPrime_eq_iff
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (c₁ c₂ : PRegularConjClass G p) :
    pRegularPrime lift c₁ = pRegularPrime lift c₂ ↔
      c₁ = c₂ := by
  simpa using pRegularPrime_eq_iff_aux
    (p := p) (k := k) (K := K) (G := G) lift hlift c₁ c₂

end

end

-- Proof sketch: apply `exists_eq_pRegularPrime` and rewrite membership using
-- `mem_pRegularPrime_iff`.
section

/-- Exercise 18-18.2-8, kernel form: every prime ideal of `RK` is the kernel of evaluation of the
scalar-extension Brauer character at a `p`-regular conjugacy class. -/
theorem
    primeSpectrum_mem_iff_scalarExtensionVirtualModularCharacterOnPRegularConjClass_eq_zero
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (P : PrimeSpectrum RK) :
    ∃ c : PRegularConjClass G p, ∀ x : RK,
      x ∈ P.asIdeal ↔
        scalarExtensionBrauerCharacterOnPRegularConjClass
          (p := p) (k := k) (K := K) (G := G) lift x c = 0 := by
  -- Classify `P` by an indexed prime `pRegularPrime lift c`.
  rcases exists_eq_pRegularPrime lift hlift P with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  intro x
  -- Membership is exactly the vanishing criterion from `mem_pRegularPrime_iff`.
  simpa using mem_pRegularPrime_iff (lift := lift) c x

end

-- Proof sketch: choose `c` from `exists_eq_pRegularPrime`, then pick a representative from the
-- surjective family and rewrite through `PRegularConjClass.ofSubtype`.
section

/-- Exercise 18-18.2-8, representative form: any surjective family of `p`-regular
representatives indexes the prime ideals of `RK` through scalar-extension
Brauer-character kernels. -/
theorem exists_representative_mem_primeSpectrum_iff_scalarExtensionVirtualModularCharacter_eq_zero
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (s : ι → { g : G // IsPRegular p g })
    (hs_complete : Function.Surjective fun i ↦ PRegularConjClass.ofSubtype p (s i))
    (P : PrimeSpectrum RK) :
    ∃ i, ∀ x : RK,
      x ∈ P.asIdeal ↔
        scalarExtensionBrauerCharacterOnPRegularConjClass
          (p := p) (k := k) (K := K) (G := G) lift x
          (PRegularConjClass.ofSubtype p (s i)) = 0 := by
  -- First classify `P` by a `p`-regular conjugacy class.
  rcases
      primeSpectrum_mem_iff_scalarExtensionVirtualModularCharacterOnPRegularConjClass_eq_zero
        lift hlift P with
    ⟨c, hc⟩
  -- Then choose an index whose representative maps to that class.
  rcases hs_complete c with ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  intro x
  simpa using hc x

end

-- Proof sketch: rewrite the two kernel conditions as equalities of the indexed primes
-- `pRegularPrime lift (PRegularConjClass.ofSubtype p (s i))` and
-- `pRegularPrime lift (PRegularConjClass.ofSubtype p (s j))`, then apply `pRegularPrime_eq_iff`
-- together with the pairwise-distinct representative hypothesis.
section

/-- Representatives whose images in `PRegularConjClass G p` are pairwise distinct determine
distinct scalar-extension Brauer-character kernels on `RK`. -/
theorem scalarExtensionVirtualModularCharacter_kernel_eq_iff_of_pRegular_representatives
    (lift : PrimeToPRoot p k →* Kˣ) (hlift : Function.Injective lift)
    (s : ι → { g : G // IsPRegular p g })
    (hs_pairwise :
      Pairwise fun i j ↦ PRegularConjClass.ofSubtype p (s i) ≠ PRegularConjClass.ofSubtype p (s j))
    (i j : ι) :
    (∀ x : RK,
        scalarExtensionBrauerCharacterOnPRegularConjClass
            (p := p) (k := k) (K := K) (G := G) lift x
            (PRegularConjClass.ofSubtype p (s i)) = 0 ↔
          scalarExtensionBrauerCharacterOnPRegularConjClass
              (p := p) (k := k) (K := K) (G := G) lift x
            (PRegularConjClass.ofSubtype p (s j)) = 0) ↔
      i = j := by
  constructor
  · intro hker
    -- Turn the kernel equivalence into equality of the corresponding indexed prime ideals.
    have hIdeal :
        (pRegularPrime lift (PRegularConjClass.ofSubtype p (s i))).asIdeal =
          (pRegularPrime lift (PRegularConjClass.ofSubtype p (s j))).asIdeal := by
      apply Ideal.ext
      intro x
      rw [mem_pRegularPrime_iff (lift := lift) (c := PRegularConjClass.ofSubtype p (s i)) (x := x),
        mem_pRegularPrime_iff (lift := lift) (c := PRegularConjClass.ofSubtype p (s j)) (x := x)]
      exact hker x
    have hprime :
        pRegularPrime lift (PRegularConjClass.ofSubtype p (s i)) =
          pRegularPrime lift (PRegularConjClass.ofSubtype p (s j)) := by
      apply PrimeSpectrum.ext
      simpa using hIdeal
    have hclass :
        PRegularConjClass.ofSubtype p (s i) = PRegularConjClass.ofSubtype p (s j) :=
      (pRegularPrime_eq_iff lift hlift _ _).1 hprime
    by_cases hij : i = j
    · exact hij
    · exact False.elim ((hs_pairwise hij) hclass)
  · intro hij
    -- Equal indices give literally the same vanishing criterion.
    subst hij
    intro x
    exact Iff.rfl

end

end Equivalence

end PrimeSpectrumOfRepresentationRing

end Representation

/-! ### Exercise_18_18_2_9 (from Chap18) -/
noncomputable section

open CategoryTheory

universe u x

namespace Representation

section BrauerBasisOverCoefficientRing

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type u} [CommRing A]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Exercise 18-18.2-9 / LinearRepresentations_Serre_1977 Exercise 18.4: for a complete family of pairwise nonisomorphic
simple finite-dimensional `k[G]`-representations, the corresponding modular characters form a
basis of the coefficient-ring-valued functions on the `p`-regular conjugacy classes. -/
def exercise_18_18_2_9_irreducible_modular_characters_basis
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι A (PRegularConjClass G p → A) :=
  irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_overSemiring
    (p := p) lift hlift E hE_pairwise hE_complete

@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_apply
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift := by
  -- This is the exercise-facing evaluation identity inherited from the canonical semiring basis.
  rw [exercise_18_18_2_9_irreducible_modular_characters_basis]
  simp

/-- Helper for Exercise 18-18.2-9: the basis coordinates of the `i`-th modular character are the
standard basis vector at `i`. -/
@[simp]
theorem exercise_18_18_2_9_irreducible_modular_characters_basis_repr_modularCharacter
    (lift : PrimeToPRoot p k → A)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    (exercise_18_18_2_9_irreducible_modular_characters_basis
        (p := p) lift hlift E hE_pairwise hE_complete).repr
      (FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) lift) =
        Finsupp.single i 1 := by
  -- After rewriting the vector as the `i`-th basis element, this is the standard `repr_self`.
  simpa using
    (exercise_18_18_2_9_irreducible_modular_characters_basis
      (p := p) lift hlift E hE_pairwise hE_complete).repr_self i

end BrauerBasisOverCoefficientRing

end Representation

/-! ### Theorem_18_18_2_1 (from Chap18) -/
noncomputable section

universe u x

open CategoryTheory

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ

local instance : NumberField Lexp := inferInstance

local instance : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

/-- Helper for Theorem 18-18.2-1: a family is linearly independent once every finite-support
relation among its vectors forces each supported coefficient to vanish. -/
private theorem linearIndependent_of_supported_coefficient_vanishes_local
    {V : Type*} [AddCommGroup V] [Module K V]
    (v : ι → V)
    (hvanish :
      ∀ (s : Finset ι) (a : ι → K),
        (Finset.sum s fun j ↦ a j • v j) = 0 →
        ∀ ⦃i : ι⦄, i ∈ s → a i = 0) :
    LinearIndependent K v := by
  -- Repackage the finite-support vanishing criterion through the standard `Finset` formulation of
  -- linear independence.
  rw [linearIndependent_iff']
  intro s a hsum i hi
  exact hvanish s a hsum hi

/-- Helper for Theorem 18-18.2-1: in every characteristic-zero coefficient field, the order of the
finite group `G` stays nonzero. This is the Maschke-side arithmetic input needed when freezing
LinearRepresentations_Serre_1977 part `(b)` over an algebraically closed characteristic-zero owner. -/
private theorem nat_card_ne_zero_of_charZero_local
    {L : Type*} [Field L] [CharZero L] :
    (Nat.card G : L) ≠ 0 := by
  -- Positive group cardinality survives in every characteristic-zero field.
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/-- Helper for Theorem 18-18.2-1: at the full cyclotomic owner `Lexp`, the fixing subgroup of the
top intermediate field maps to the trivial subgroup of exponent units. This records the exact
cyclotomic arithmetic simplification that would feed the final owner step in part `(b)`. -/
private theorem top_cyclotomic_fixing_subgroup_maps_to_bot_local :
    (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup
        ((⊤ : IntermediateField ℚ Lexp).fixingSubgroup) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- The top cyclotomic field has trivial fixing subgroup, so its image is also trivial.
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot
    (IsCyclotomicExtension.Rat.galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

/-- Helper for Theorem 18-18.2-1: after normalizing one supported coefficient, LinearRepresentations_Serre_1977 part `(a)`
reduces coefficient vanishing to the imported mixed-character contradiction. -/
private theorem supported_coefficient_zero_after_transport_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι)
    (a : ι → K)
    (hsum :
      (Finset.sum s
          fun j ↦ a j •
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E j)
              (PrimeToPRoot.toFieldLift lift)) =
        (0 : PRegularConjClass G p → K))
    {i : ι} (hi : i ∈ s) :
    a i = 0 := by
  by_contra hai
  -- Route correction: normalize the chosen coefficient locally, then hand the source-faithful
  -- mixed-character contradiction to the theorem-local support module.
  obtain ⟨aNorm, _haNorm_def, hsumNorm, haNorm_i⟩ :=
    normalized_supported_brauer_relation_local
      (p := p) (k := k) (K := K) (G := G) lift E s a hsum hi hai
  exact
    supported_normalized_brauer_relation_contradiction_over_residue_local
      (p := p) (k := k) (K := K) (G := G)
      lift hlift E hE_simple hE_pairwise s aNorm hsumNorm hi haNorm_i

/-- Helper for Theorem 18-18.2-1: LinearRepresentations_Serre_1977 part `(b)` now reduces directly to the canonical
finite-table transport theorem from the theorem-local support files. -/
private theorem regularClassFunction_mem_span_after_mixed_character_transport_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- Route correction: the remaining source-faithful work for part `(b)` is already packaged in
  -- the imported finite transport theorem, so this file only keeps the outer span wrapper.
  exact
    finite_regular_and_brauer_table_span_transfer_over_witt_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: every `K`-valued function on `PRegularConjClass G p` already
lies in the span of the Brauer characters of a complete irreducible family. This is the explicit
one-function form of LinearRepresentations_Serre_1977 part `(b)` used before packaging the full `span = ⊤` statement. -/
theorem regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- Route correction: keep LinearRepresentations_Serre_1977 part `(b)` at the wrapper level as a one-function span statement,
  -- and let the theorem-local mixed-character transport module supply the only remaining heavy
  -- owner-change step.
  exact
    regularClassFunction_mem_span_after_mixed_character_transport_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: in the field-valued setting, pairwise nonisomorphic simple
modules have linearly independent Brauer characters on `PRegularConjClass G p`. -/
theorem linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E) :
    LinearIndependent K
      (fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- LinearRepresentations_Serre_1977 part `(a)` reduces to vanishing of every supported coefficient in a finite relation.
  refine
    linearIndependent_of_supported_coefficient_vanishes_local
      (K := K)
      (v := fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) ?_
  intro s a hsum i hi
  exact
    supported_coefficient_zero_after_transport_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_simple hE_pairwise s a hsum hi

/-- Helper for Theorem 18-18.2-1: in the field-valued setting, the Brauer characters of a
complete irreducible family span the whole function space on `PRegularConjClass G p`. -/
theorem span_irreducibleModularCharacters_eq_top_of_complete_family
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  -- LinearRepresentations_Serre_1977 part `(b)` is the statement that every regular class function already lies in the
  -- Brauer-character span.
  apply top_unique
  intro f _
  exact
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f

/-- Helper for Theorem 18-18.2-1: once LinearRepresentations_Serre_1977 parts `(a)` and `(b)` are available in the
field-valued setting, the Brauer-character family is a basis of the full function space. -/
private theorem brauer_character_linearIndependent_and_span_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    LinearIndependent K
        (fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) ∧
      Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) =
        ⊤ := by
  -- Record LinearRepresentations_Serre_1977 parts `(a)` and `(b)` together as the stable proof skeleton used by the final
  -- basis construction.
  constructor
  · exact
      linearIndependent_irreducibleModularCharacters_of_pairwiseNonisomorphic
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_complete.isSimple hE_pairwise
  · exact
      span_irreducibleModularCharacters_eq_top_of_complete_family
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

/-- Helper for Theorem 18-18.2-1: once LinearRepresentations_Serre_1977 parts `(a)` and `(b)` are available in the
field-valued setting, the Brauer-character family is a basis of the full function space. -/
private theorem basis_of_linearIndependent_and_span_eq_top_local
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) := by
  obtain ⟨hlin, hspan⟩ :=
    brauer_character_linearIndependent_and_span_local
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  -- Assemble the basis directly from the linearly independent Brauer rows and their span.
  refine
    Module.Basis.mk
      hlin
      ?_
  -- The spanning statement from LinearRepresentations_Serre_1977 part `(b)` is exactly the second basis axiom.
  exact hspan.ge

/-- Theorem 18-18.2-1: for a complete pairwise nonisomorphic family of simple finite-dimensional
`k[G]`-representations, the corresponding Brauer characters form a `K`-basis of the
`K`-vector space of `K`-valued functions on the `p`-regular conjugacy classes of `G`, viewed
through an injective multiplicative lift of the prime-to-`p` roots of unity into the field `K`. -/
def irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Module.Basis ι K (PRegularConjClass G p → K) :=
  -- Reduce the theorem statement to the already-isolated linear independence and spanning parts.
  basis_of_linearIndependent_and_span_eq_top_local
    (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

@[simp]
theorem irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (i : ι) :
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        lift hlift E hE_pairwise hE_complete i =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
        (PrimeToPRoot.toFieldLift lift) := by
  -- Unfold the basis construction and read off the indexed basis vector.
  rw [irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions]
  simp

/-- Helper for Theorem 18-18.2-1: every regular class function has a canonical finite expansion
in the Brauer-character basis returned by the theorem. This packages the basis coordinates as the
finite witness that later span arguments can reuse without reopening the basis construction. -/
theorem exists_finite_brauer_character_expansion_of_complete_family
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    ∃ c : ι →₀ K,
      (Finset.sum c.support fun i ↦ c i •
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) = f := by
  let b :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  refine ⟨b.repr f, ?_⟩
  -- Expand `f` in the theorem's basis, then rewrite each basis vector back to the matching
  -- Brauer character.
  simpa [b, irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply] using
    b.sum_repr f

end

end Representation

/-! ### Theorem_18_18_2_2 (from Chap18) -/
open scoped TensorProduct

noncomputable section

universe u v

namespace Representation

section PRegularConjClassFunctions

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [AddCommGroup A]
variable {G : Type u} [Group G] [Finite G]

private abbrev virtualModularCharacterOnPRegularConjClassLift
    (lift : PrimeToPRoot p k → A) :
    FreeAbelianGroup (FDRep k G) →+ (PRegularConjClass G p → A) :=
  FreeAbelianGroup.lift fun E ↦
    FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) E lift

private theorem
    finiteRepGrothendieckRelations_le_virtualModularCharacterOnPRegularConjClassLift_ker
    (lift : PrimeToPRoot p k → A) :
    finiteRepGrothendieckRelations k G ≤
      (virtualModularCharacterOnPRegularConjClassLift lift).ker := sorry

variable (p)

/-
Domain-style sampling:
* primary domain: Brauer/modular characters descended from `FDRep k G` to LinearRepresentations_Serre_1977's Grothendieck
  group and then restricted to the owner `PRegularConjClass G p`;
* inspected owner declarations in this domain:
  `FDRep.modularCharacterOnPRegularConjClass`,
  `virtualModularCharacter`,
  `modularCharacter_one_eq_finrank`,
  and `modularCharacter_tensor`;
* best owner abstraction: the additive Grothendieck descent of the canonical owner
  `FDRep.modularCharacterOnPRegularConjClass`, followed by scalar extension;
* primitive data: a lift `PrimeToPRoot p k → A`, the finite-representation Grothendieck relations,
  and the additive owner `virtualModularCharacter`;
* derived API: descent to `PRegularConjClass G p`, then multiplicativity and scalar extension.

Characteristic `p` is not primitive data for this descent layer. It first becomes essential only in
the later bijectivity/equivalence layer via Theorem `18-18.2-1`.
-/
/-- Bridge/view: the virtual modular character on LinearRepresentations_Serre_1977's Grothendieck group, descended from the
canonical `FDRep.modularCharacterOnPRegularConjClass` owner. -/
def virtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k → A) :
    R₀[k](G) →+ (PRegularConjClass G p → A) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations k G)
    (virtualModularCharacterOnPRegularConjClassLift lift)
    (finiteRepGrothendieckRelations_le_virtualModularCharacterOnPRegularConjClassLift_ker lift)

@[simp] theorem virtualModularCharacterOnPRegularConjClass_class
    (lift : PrimeToPRoot p k → A) (E : FDRep k G) :
    virtualModularCharacterOnPRegularConjClass p lift [E]₀ =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) E lift := sorry

@[simp] theorem virtualModularCharacterOnPRegularConjClass_ofSubtype
    (lift : PrimeToPRoot p k → A) (x : R₀[k](G))
    (s : { x : G // IsPRegular p x }) :
    virtualModularCharacterOnPRegularConjClass p lift x (PRegularConjClass.ofSubtype p s) =
      virtualModularCharacter lift x s := sorry

@[simp] theorem virtualModularCharacterOnPRegularConjClass_class_ofSubtype
    (lift : PrimeToPRoot p k → A) (E : FDRep k G)
    (s : { x : G // IsPRegular p x }) :
    virtualModularCharacterOnPRegularConjClass p lift [E]₀ (PRegularConjClass.ofSubtype p s) =
      modularCharacter lift E.ρ s := by
  rw [virtualModularCharacterOnPRegularConjClass_ofSubtype]
  exact congrFun (virtualModularCharacter_class lift E) s

section Multiplicative

variable [CommRing A]

-- Proof sketch: on the unit class this is Proposition `18-18.1-2 (1)` after descending from the
-- `p`-regular locus to `PRegularConjClass G p`.
/-- On LinearRepresentations_Serre_1977's representation ring, the descended virtual modular character sends `1` to the
constant function `1`. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_one
    (lift : PrimeToPRoot p k →* A) :
    virtualModularCharacterOnPRegularConjClass p lift (1 : R₀[k](G)) = 1 := by
  sorry

-- Proof sketch: compare both sides on actual classes using Proposition `18-18.1-2 (4)` and
-- `finiteRepGrothendieckClass_mul`, then extend the identity from generators to `R₀[k](G)`.
/-- On LinearRepresentations_Serre_1977's representation ring, the descended virtual modular character is multiplicative. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_mul
    (lift : PrimeToPRoot p k →* A) (x y : R₀[k](G)) :
    virtualModularCharacterOnPRegularConjClass p lift (x * y) =
      virtualModularCharacterOnPRegularConjClass p lift x *
        virtualModularCharacterOnPRegularConjClass p lift y := by
  sorry

end Multiplicative

end PRegularConjClassFunctions

section ScalarExtension

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Type v} [Field K]
variable {G : Type u} [Group G] [Finite G]

-- source-facing: LinearRepresentations_Serre_1977's theorem identifies the scalar extension of `R₀[k](G)` with the full
-- function space on `PRegularConjClass G p`.
-- core/canonical: `virtualModularCharacter` from Remark `18-18.1-3`.
-- bridge/view: `virtualModularCharacterOnPRegularConjClass` descends that owner to regular
-- conjugacy classes, and `scalarExtensionVirtualModularCharacterOnPRegularConjClass` is its
-- canonical scalar extension to a `K`-linear map.
-- Proof sketch: extend `x ↦ φ_x` `K`-linearly from `R_k(G)` to `K ⊗[ℤ] R_k(G)`, then use
-- Theorem `18-18.2-1` together with the `ℤ`-basis theorem for `R_k(G)` to show that the resulting
-- map sends a scalar-extended simple-class basis to a basis of the full function space on
-- `PRegularConjClass G p`.
private def scalarExtensionVirtualModularCharacterOnPRegularConjClassLift
    (lift : PrimeToPRoot p k →* Kˣ) :
    K →ₗ[K] R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) where
  toFun := fun a ↦
    let φ : R₀[k](G) →+ (PRegularConjClass G p → K) :=
      (virtualModularCharacterOnPRegularConjClass
        (k := k) (A := K) (G := G) p (PrimeToPRoot.toFieldLift lift) :
        R₀[k](G) →+ (PRegularConjClass G p → K))
    { toFun := fun x ↦ a • φ x
      map_add' := by
        intro x y
        ext c
        rw [map_add]
        simp [Pi.smul_apply, mul_add]
      map_smul' := by
        sorry }
  map_add' a b := by
    sorry
  map_smul' a b := by
    sorry

/-- Bridge/view: the canonical `K`-linear scalar extension of the virtual modular character map on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K) :=
  TensorProduct.AlgebraTensorModule.lift <|
    scalarExtensionVirtualModularCharacterOnPRegularConjClassLift lift

@[simp] theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul
    (lift : PrimeToPRoot p k →* Kˣ) (a : K) (x : R₀[k](G)) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClass lift (a ⊗ₜ[ℤ] x) =
      a •
        (virtualModularCharacterOnPRegularConjClass
          (k := k) (A := K) (G := G) p (PrimeToPRoot.toFieldLift lift) :
          R₀[k](G) →+ (PRegularConjClass G p → K)) x := by
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClass,
    scalarExtensionVirtualModularCharacterOnPRegularConjClassLift]

/-- Core/canonical multiplicative refinement of Theorem `18-18.2-2`: the scalar-extension
Brauer-character map is a `K`-algebra homomorphism to the function ring on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₐ[K] (PRegularConjClass G p → K) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift)
    (by
      sorry)
    (by
      sorry)

/-
The remaining statements use Theorem `18-18.2-1`, whose basis theorem genuinely requires
characteristic `p`. That hypothesis is therefore confined to this equivalence layer rather than the
owner declarations above.
-/
section Equivalence

variable [CharP k p]

/-- Theorem 18-18.2-2: the canonical `K`-linear scalar extension of the virtual modular character
map is a linear isomorphism from `K ⊗[ℤ] R_k(G)` onto the `K`-algebra of `K`-valued functions on
the `p`-regular conjugacy classes of `G`. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₗ[K] (PRegularConjClass G p → K) :=
  LinearEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift)
    (by
      sorry)

/-- Companion: the underlying linear map of
`scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv` is bijective. -/
theorem bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Bijective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) := by
  simpa [scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv] using
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv lift hlift).bijective

/-- Theorem 18-18.2-2, canonical multiplicative form: the scalar-extension Brauer-character map is
a `K`-algebra isomorphism from `K ⊗[ℤ] R_k(G)` onto the function ring on the `p`-regular
conjugacy classes of `G`. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₐ[K] (PRegularConjClass G p → K) :=
  AlgEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom lift)
    (by
      let h :=
        bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (K := K) (G := G) lift hlift
      exact ⟨h.1, h.2⟩)

end Equivalence

end ScalarExtension

end Representation
