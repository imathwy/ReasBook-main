import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_2_8.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation TensorProduct

universe u v w

namespace Representation

section PrimeSpectrumOfRepresentationRing

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
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
* source-facing: prime ideals of Serre's scalar-extended representation ring
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
