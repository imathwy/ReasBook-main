import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.ScalarExtensionTransport

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278ZeroFiberClassificationGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278ZeroFiberClassificationGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

/-- Helper for Exercise 12-12.7-8: the algebra map from the bottom residue field into `K` is
surjective because both fields are built from the same fraction expressions over `A`. -/
private theorem botResidueField_algebraMap_surjective :
    Function.Surjective (algebraMap ((⊥ : Ideal A).ResidueField) K) := by
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  refine ⟨algebraMap A ((⊥ : Ideal A).ResidueField) a /
      algebraMap A ((⊥ : Ideal A).ResidueField) b, ?_⟩
  rw [map_div₀]
  rw [IsScalarTower.algebraMap_apply A ((⊥ : Ideal A).ResidueField) K a]
  rw [IsScalarTower.algebraMap_apply A ((⊥ : Ideal A).ResidueField) K b]

/-- Helper for Exercise 12-12.7-8: the coefficient maps
`A → ((0).ResidueField) → K` agree with the original scalar map `A → K`. -/
private theorem botResidueField_algebraMap_commutes (a : A) :
    (algebraMap ((⊥ : Ideal A).ResidueField) K)
        ((algebraMap A ((⊥ : Ideal A).ResidueField)) a) =
      algebraMap A K a := by
  simpa using (IsScalarTower.algebraMap_apply A ((⊥ : Ideal A).ResidueField) K a).symm

/-- Helper for Exercise 12-12.7-8: the bottom residue field `((0).ResidueField)` is another
fraction-field model of `A`, so its scalar map into `K` is an `A`-algebra equivalence. This
closes the coefficient-side mismatch in the zero-fiber route before any prime-spectrum transport
is invoked. -/
private noncomputable def botResidueField_algEquiv_fractionField :
    ((⊥ : Ideal A).ResidueField) ≃ₐ[A] K :=
  let φ : ((⊥ : Ideal A).ResidueField) →ₐ[A] K :=
    { toRingHom := algebraMap ((⊥ : Ideal A).ResidueField) K
      commutes' := botResidueField_algebraMap_commutes (A := A) (K := K) }
  -- Two fraction-field models of the same domain are equivalent once the scalar map is known to
  -- be bijective.
  AlgEquiv.ofBijective φ
    ⟨(algebraMap ((⊥ : Ideal A).ResidueField) K).injective,
      botResidueField_algebraMap_surjective (A := A) (K := K)⟩

/-- Helper for Exercise 12-12.7-8: because `((0).ResidueField)` and `K` are isomorphic fraction
fields of `A`, they generate the same scalar-extension submodule inside `G → K`. -/
private theorem
    mem_characterRingOverFieldAlgebraScalarExtension_over_botResidueField_iff_mem_over_K
    {f : G → K} :
    f ∈ ((⊥ : Ideal A).ResidueField) ⊗R[K](G) ↔ f ∈ K ⊗R[K](G) := by
  constructor
  · intro hf
    -- Any `((0).ResidueField)`-linear combination of character generators is a fortiori a
    -- `K`-linear combination of the same generators.
    induction hf using Submodule.span_induction with
    | mem g hg =>
        exact Submodule.subset_span hg
    | zero =>
        simpa using (K ⊗R[K](G) : Submodule K (G → K)).zero_mem
    | add f g _ _ hf hg =>
        exact (K ⊗R[K](G) : Submodule K (G → K)).add_mem hf hg
    | smul a g _ hg =>
        show (algebraMap ((⊥ : Ideal A).ResidueField) K a) • g ∈
            (K ⊗R[K](G) : Submodule K (G → K))
        exact (K ⊗R[K](G) : Submodule K (G → K)).smul_mem _ hg
  · intro hf
    -- Conversely, every scalar from `K` already comes from the bottom residue field via the
    -- fraction-field equivalence, so the same span is generated over `((0).ResidueField)`.
    induction hf using Submodule.span_induction with
    | mem g hg =>
        exact Submodule.subset_span hg
    | zero =>
        simpa using
          (((⊥ : Ideal A).ResidueField) ⊗R[K](G) :
            Submodule ((⊥ : Ideal A).ResidueField) (G → K)).zero_mem
    | add f g _ _ hf hg =>
        exact
          (((⊥ : Ideal A).ResidueField) ⊗R[K](G) :
            Submodule ((⊥ : Ideal A).ResidueField) (G → K)).add_mem hf hg
    | smul a g _ hg =>
        obtain ⟨b, rfl⟩ := botResidueField_algebraMap_surjective (A := A) (K := K) a
        exact
          (((⊥ : Ideal A).ResidueField) ⊗R[K](G) :
            Submodule ((⊥ : Ideal A).ResidueField) (G → K)).smul_mem b hg

/-- Helper for Exercise 12-12.7-8: extending scalars from `A` to a coefficient field `F` mapping
to `K` preserves Serre's scalar-extension owner `A ⊗ R_K(G)` inside `G → K`. This is the
coefficient half of the fiber-first route before quotient functions enter the picture. -/
private theorem mem_characterRingOverFieldAlgebraScalarExtension_of_mem_baseChange
    {F : Type*} [Field F] [Algebra A F] [Algebra F K] [IsScalarTower A F K] {f : G → K}
    (hf : f ∈ A ⊗R[K](G)) :
    f ∈ F ⊗R[K](G) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      exact Submodule.subset_span (by simpa using hg)
  | zero =>
      simpa using (F ⊗R[K](G) : Submodule F (G → K)).zero_mem
  | add f g _ _ hf hg =>
      exact (F ⊗R[K](G) : Submodule F (G → K)).add_mem hf hg
  | smul a g _ hg =>
      have hs :
          algebraMap A (G → K) a =
            algebraMap F (G → K) (algebraMap A F a) := by
        ext x
        simp [IsScalarTower.algebraMap_apply A F K a]
      simpa [Pi.smul_apply, Algebra.smul_def, hs, mul_assoc, mul_left_comm, mul_comm] using
        (F ⊗R[K](G) : Submodule F (G → K)).smul_mem (algebraMap A F a) hg

/-- Helper for Exercise 12-12.7-8: after changing coefficients from `A` to the bottom residue
field `((0).ResidueField)`, the resulting fiber owner is linearly the same as the coefficient
changed scalar-extension owner. This certifies the span-theoretic part of Serre's zero-fiber
normalization route. -/
private noncomputable def
    botFiber_characterRingOverFieldAlgebraScalarExtensionSubalgebra_to_baseChangeLinearEquiv :
    TensorProduct A ((⊥ : Ideal A).ResidueField)
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) ≃ₗ[((⊥ : Ideal A).ResidueField)]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra ((⊥ : Ideal A).ResidueField) K G := by
  letI : Module.Flat A ((⊥ : Ideal A).ResidueField) :=
    IsLocalization.flat (R := A) (S := ((⊥ : Ideal A).ResidueField)) (nonZeroDivisors A)
  change TensorProduct A ((⊥ : Ideal A).ResidueField)
      (characterRingOverFieldAlgebraScalarExtension A K G) ≃ₗ[((⊥ : Ideal A).ResidueField)]
        characterRingOverFieldAlgebraScalarExtension ((⊥ : Ideal A).ResidueField) K G
  simpa [characterRingOverFieldAlgebraScalarExtension] using
    (Submodule.tensorSpanEquivSpan A ((⊥ : Ideal A).ResidueField)
      ((((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))))

/-- Helper for Exercise 12-12.7-8: transporting a prime of the bottom fiber over `(0)` back
through `PrimeSpectrum.primesOverOrderIsoFiber` gives the corresponding ambient prime of
`A ⊗ R_K(G)`. -/
noncomputable def zero_fiber_prime_to_specAKG
    (q :
      PrimeSpectrum
        (((⊥ : Ideal A).Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))) :
    SpecAKG :=
  ⟨((PrimeSpectrum.primesOverOrderIsoFiber
      A
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
      (⊥ : Ideal A)).symm q).1,
    inferInstance⟩

/-- Helper for Exercise 12-12.7-8: sending an ambient prime with zero contraction into the bottom
fiber and transporting it back through `zero_fiber_prime_to_specAKG` returns the original prime.
-/
theorem zero_fiber_prime_to_specAKG_prime_over_bot_to_fiber
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
        (prime_over_bot_to_fiber (A := A) (K := K) (G := G) 𝔭 h𝔭) =
      𝔭 := by
  apply PrimeSpectrum.ext
  -- The inverse packaging theorem identifies the underlying ideals.
  simpa [zero_fiber_prime_to_specAKG] using
    prime_over_bot_to_fiber_symm (A := A) (K := K) (G := G) 𝔭 h𝔭

/-- Helper for Exercise 12-12.7-8: every prime of a finite product of fields indexed by
`Γ_K`-classes is a coordinate-evaluation prime. -/
private theorem exists_eq_comap_evalRingHom_bot_of_primeSpectrum_galoisPowerClass
    (P : PrimeSpectrum (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))) :
    ∃ c : GaloisPowerClass ΓK,
      PrimeSpectrum.comap
          (Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c)
          ⟨(⊥ : Ideal ((⊥ : Ideal A).ResidueField)), inferInstance⟩ = P := by
  -- First classify the prime by a coordinate and an arbitrary prime of the residue field factor.
  obtain ⟨c, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) P
  refine ⟨c, ?_⟩
  -- A field has only the zero prime, so the residual factor is forced to be `⊥`.
  have hqbotIdeal : q.asIdeal = ⊥ := by
    exact Ideal.eq_bot_of_prime q.asIdeal
  have hqbot : q = ⟨(⊥ : Ideal ((⊥ : Ideal A).ResidueField)), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  simpa [hqbot] using hq

/-- Helper for Exercise 12-12.7-8: the coordinate-evaluation prime in the function ring on
`Γ_K`-classes over the bottom residue field. -/
private noncomputable def zero_fiber_eval_prime
    (c : GaloisPowerClass ΓK) :
    PrimeSpectrum (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) :=
  PrimeSpectrum.comap
    (Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c)
    ⟨(⊥ : Ideal ((⊥ : Ideal A).ResidueField)), inferInstance⟩

/-- Helper for Exercise 12-12.7-8: distinct `Γ_K`-classes define distinct coordinate-evaluation
primes in the bottom-fiber function ring. -/
private theorem zero_fiber_eval_prime_eq_iff
    (c₁ c₂ : GaloisPowerClass ΓK) :
    zero_fiber_eval_prime (A := A) (K := K) (G := G) c₁ =
        zero_fiber_eval_prime (A := A) (K := K) (G := G) c₂ ↔
      c₁ = c₂ := by
  constructor
  · intro hprime
    by_contra hne
    classical
    let f : GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField) :=
      fun d ↦ if d = c₁ then 1 else 0
    have hne' : c₂ ≠ c₁ := fun h ↦ hne h.symm
    have hf₂ : f ∈ (zero_fiber_eval_prime (A := A) (K := K) (G := G) c₂).asIdeal := by
      change f c₂ = 0
      simpa [f] using hne'
    have hf₁ : f ∉ (zero_fiber_eval_prime (A := A) (K := K) (G := G) c₁).asIdeal := by
      change f c₁ ≠ 0
      simp [f]
    exact hf₁ (by simpa [hprime] using hf₂)
  · intro hc
    subst hc
    rfl

/-- Helper for Exercise 12-12.7-8: an algebra equivalence from the bottom fiber to the function
ring on `Γ_K`-classes transports coordinate-evaluation primes back to the fiber. -/
noncomputable def zero_fiber_lift
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK) :
    PrimeSpectrum
      (((⊥ : Ideal A).Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) :=
  (PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    (zero_fiber_eval_prime (A := A) (K := K) (G := G) c)

/-- Helper for Exercise 12-12.7-8: once the bottom fiber is identified with the function ring on
`Γ_K`-classes, every bottom-fiber prime is the lift of a coordinate-evaluation prime. -/
theorem zero_fiber_lift_surjective
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))) :
    Function.Surjective (zero_fiber_lift (A := A) (K := K) (G := G) e) := by
  intro q
  let E :
      PrimeSpectrum (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) ≃o
        PrimeSpectrum
          (((⊥ : Ideal A).Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) :=
    (PrimeSpectrum.comapEquiv
      (R := ((⊥ : Ideal A).Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
      (S := GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))
      e.toRingEquiv).symm
  -- Classify the pushed-forward bottom-fiber prime by a coordinate of the function ring.
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_galoisPowerClass
      (A := A) (K := K) (G := G) (E.symm q)
  refine ⟨c, ?_⟩
  calc
    zero_fiber_lift (A := A) (K := K) (G := G) e c
        = E (zero_fiber_eval_prime (A := A) (K := K) (G := G) c) := by
            rfl
    _ = E (E.symm q) := by
          simpa [E, zero_fiber_eval_prime] using congrArg E hc
    _ = q := by
          simpa [E] using E.apply_symm_apply q

/-- Helper for Exercise 12-12.7-8: after transporting the bottom fiber to the `Γ_K`-class
function ring, equality of lifted coordinate primes is equivalent to equality of the underlying
`Γ_K`-classes. -/
private theorem zero_fiber_lift_eq_iff
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c₁ c₂ : GaloisPowerClass ΓK) :
    zero_fiber_lift (A := A) (K := K) (G := G) e c₁ =
        zero_fiber_lift (A := A) (K := K) (G := G) e c₂ ↔
      c₁ = c₂ := by
  let E :
      PrimeSpectrum (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) ≃o
        PrimeSpectrum
          (((⊥ : Ideal A).Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) :=
    (PrimeSpectrum.comapEquiv
      (R := ((⊥ : Ideal A).Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
      (S := GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))
      e.toRingEquiv).symm
  constructor
  · intro hlift
    have heval :
        zero_fiber_eval_prime (A := A) (K := K) (G := G) c₁ =
          zero_fiber_eval_prime (A := A) (K := K) (G := G) c₂ := by
      exact E.injective <| by simpa [zero_fiber_lift, E] using hlift
    exact (zero_fiber_eval_prime_eq_iff (A := A) (K := K) (G := G) c₁ c₂).mp heval
  · intro hc
    subst hc
    rfl

/-- Helper for Exercise 12-12.7-8: evaluation at a `Γ_K`-class in the bottom-fiber function ring,
followed by the canonical coefficient map to `K`, is an algebra map over `((0).ResidueField)`. -/
private theorem zero_fiber_evalAlgHomToK_commutes
    (c : GaloisPowerClass ΓK) (x : ((⊥ : Ideal A).ResidueField)) :
    ((algebraMap ((⊥ : Ideal A).ResidueField) K).comp
      (Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c))
      (algebraMap ((⊥ : Ideal A).ResidueField)
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) x) =
      algebraMap ((⊥ : Ideal A).ResidueField) K x := by
  -- Evaluation of a constant function just returns the chosen scalar.
  rfl

/-- Helper for Exercise 12-12.7-8: after choosing a bottom-fiber equivalence `e`, the induced
`A`-algebra map to `K` obtained by evaluating at `c` is the exact transport object whose kernel
defines the ambient prime coming from `zero_fiber_lift e c`. -/
private noncomputable def zero_fiber_evalAlgHomToK
    (c : GaloisPowerClass ΓK) :
    (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) →ₐ[((⊥ : Ideal A).ResidueField)] K :=
  { toRingHom := (algebraMap ((⊥ : Ideal A).ResidueField) K).comp
      (Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c)
    commutes' := zero_fiber_evalAlgHomToK_commutes (A := A) (K := K) (G := G) c
  }

/-- Helper for Exercise 12-12.7-8: over its own coefficient ring, the bottom residue field is
canonically identified with the fraction field `K`. This is the coefficient transport used to
convert `K`-valued quotient functions back to `((0).ResidueField)`-valued ones. -/
private noncomputable def botResidueField_algEquiv_fractionField_over_botResidueField :
    ((⊥ : Ideal A).ResidueField) ≃ₐ[((⊥ : Ideal A).ResidueField)] K :=
  let φ : ((⊥ : Ideal A).ResidueField) →ₐ[((⊥ : Ideal A).ResidueField)] K :=
    { toRingHom := algebraMap ((⊥ : Ideal A).ResidueField) K
      commutes' := fun x ↦ rfl }
  AlgEquiv.ofBijective φ
    ⟨(algebraMap ((⊥ : Ideal A).ResidueField) K).injective,
      botResidueField_algebraMap_surjective (A := A) (K := K)⟩

/-- Helper for Exercise 12-12.7-8: after changing coefficients from `A` to `((0).ResidueField)`,
the resulting scalar-extension subalgebra inside `G → K` is still the same subring of functions
as the `K`-coefficient scalar extension. This isolates the coefficient-only transport. -/
private noncomputable def
    characterRingOverFieldAlgebraScalarExtension_over_botResidueField_algEquiv_over_K :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra ((⊥ : Ideal A).ResidueField) K G ≃ₐ[((⊥ : Ideal A).ResidueField)]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G :=
  { toFun := fun f ↦
      ⟨(f : G → K),
        (mem_characterRingOverFieldAlgebraScalarExtension_over_botResidueField_iff_mem_over_K
          (A := A) (K := K) (G := G)).1 f.2⟩
    invFun := fun f ↦
      ⟨(f : G → K),
        (mem_characterRingOverFieldAlgebraScalarExtension_over_botResidueField_iff_mem_over_K
          (A := A) (K := K) (G := G)).2 f.2⟩
    left_inv := by
      intro f
      rfl
    right_inv := by
      intro f
      rfl
    map_mul' := by
      intro f g
      rfl
    map_add' := by
      intro f g
      rfl
    commutes' := by
      intro a
      ext g
      rfl }

/-- Helper for Exercise 12-12.7-8: over the coefficient field `K` itself, Serre's owner
`K ⊗ R_K(G)` is exactly the `K`-algebra of `K`-valued functions on `Γ_K`-classes. This is the
endpoint owner equivalence needed before transporting back to the bottom fiber. -/
private theorem
    mem_characterRingOverFieldAlgebraScalarExtension_over_field_of_mem_scalarExtension
    {f : G → K} (hf : f ∈ ℚ ⊗R[K](G)) :
    f ∈ K ⊗R[K](G) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      exact Submodule.subset_span hg
  | zero =>
      simpa using (K ⊗R[K](G) : Submodule K (G → K)).zero_mem
  | add f g _ _ hf hg =>
      exact (K ⊗R[K](G) : Submodule K (G → K)).add_mem hf hg
  | smul a g _ hg =>
      simpa [Pi.smul_apply, Algebra.smul_def, mul_assoc, mul_left_comm, mul_comm] using
        (K ⊗R[K](G) : Submodule K (G → K)).smul_mem (algebraMap ℚ K a) hg

/-- Helper for Exercise 12-12.7-8: over the coefficient field `K` itself, Serre's owner
`K ⊗ R_K(G)` is exactly the `K`-algebra of `K`-valued functions on `Γ_K`-classes. This is the
endpoint owner equivalence needed before transporting back to the bottom fiber. -/
private theorem
    mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
    {f : G → K} :
    f ∈ characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ↔
      IsConstantOnGaloisPowerClasses ΓK f := by
  constructor
  · intro hf
    have hfClass : _root_.IsClassFunction f := by
      induction hf using Submodule.span_induction with
      | mem ψ hψ =>
          exact Representation.isClassFunction_of_mem_characterRingOverField ψ hψ
      | zero =>
          simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K)))
      | add f g _ _ hf hg =>
          letI : _root_.IsClassFunction f := hf
          letI : _root_.IsClassFunction g := hg
          simpa using (inferInstance : _root_.IsClassFunction (f + g))
      | smul a f _ hf =>
          letI : _root_.IsClassFunction f := hf
          simpa using (inferInstance : _root_.IsClassFunction (a • f))
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hfClass⟩
    exact
      (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hfClass).2 <|
        (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
          G K φ).1 <| by
            simpa using hf
  · intro hf
    let φ : classFunctionSubmodule K G :=
      ⟨f, (mem_classFunctionSubmodule_iff K f).2 hf.isClassFunction⟩
    have hpow :
        ∀ s (t : ΓK), φ s = φ (s ^ t) :=
      (isConstantOnGaloisPowerClasses_iff_forall_pow_eq hf.isClassFunction).1 hf
    simpa using
      (classFunction_mem_characterRingOverFieldScalarExtension_iff_gammaSubgroup_invariant
        G K φ).2 hpow

/-- Helper for Exercise 12-12.7-8: Serre's `K`-coefficient owner `K ⊗ R_K(G)` is canonically the
full function algebra on `Γ_K`-classes. This packages the quotient-function endpoint
multiplicatively before the bottom-fiber transport is applied. -/
private noncomputable def
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₐ[K]
      (GaloisPowerClass ΓK → K) := by
  let e :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G ≃ₗ[K]
        (GaloisPowerClass ΓK → K) :=
    { toFun := fun φ ↦
        let hφ : IsConstantOnGaloisPowerClasses ΓK ((φ :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).1 φ.2
        hφ.lift
      invFun := fun φ ↦
        ⟨φ ∘ galoisPowerClassMk ΓK,
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).2 inferInstance⟩
      left_inv := by
        intro φ
        ext g
        let hφ : IsConstantOnGaloisPowerClasses ΓK ((φ :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
          (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
            (G := G) (L := L) (K := K)).1 φ.2
        simpa using hφ.lift_mk g
      right_inv := by
        intro φ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
        let hφ : IsConstantOnGaloisPowerClasses ΓK (φ ∘ galoisPowerClassMk ΓK) :=
          inferInstance
        simpa using hφ.lift_mk g
      map_add' := by
        intro φ ψ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
        rfl
      map_smul' := by
        intro a φ
        ext c
        obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
        rfl }
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · -- The quotient avatar of the unit character is the constant-one function.
    ext c
    obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
    let h1 :
        IsConstantOnGaloisPowerClasses ΓK
          ((1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 (by simpa using (show
          ((1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) ∈
            characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G from
          (1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G).2))
    have he1 : e 1 = h1.lift := rfl
    rw [he1]
    simpa using h1.lift_mk g
  · intro φ ψ
    -- Multiplication is pointwise, so it suffices to evaluate on quotient representatives.
    ext c
    obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
    let hφ : IsConstantOnGaloisPowerClasses ΓK ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 φ.2
    let hψ : IsConstantOnGaloisPowerClasses ΓK ((ψ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 ψ.2
    let hφψ :
        IsConstantOnGaloisPowerClasses ΓK
          (((φ * ψ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K)) :=
      (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
        (G := G) (L := L) (K := K)).1 (φ * ψ).2
    have hK :
        hφψ.lift (galoisPowerClassMk ΓK g) =
          hφ.lift (galoisPowerClassMk ΓK g) * hψ.lift (galoisPowerClassMk ΓK g) := by
      rw [hφψ.lift_mk, hφ.lift_mk, hψ.lift_mk]
      rfl
    have hφe : e φ = hφ.lift := rfl
    have hψe : e ψ = hψ.lift := rfl
    have hφψe : e (φ * ψ) = hφψ.lift := rfl
    rw [hφψe, hφe, hψe]
    rw [Pi.mul_apply]
    exact congrArg Subtype.val hK

/-- Helper for Exercise 12-12.7-8: evaluating the quotient-function realization of the
`K`-coefficient owner on the `Γ_K`-class of `g` recovers the original value at `g`. -/
@[simp] private theorem
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions_apply_mk
    (φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) (g : G) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
        (G := G) (L := L) (K := K) φ
        (galoisPowerClassMk ΓK g) =
      (φ : G → K) g := by
  let hφ : IsConstantOnGaloisPowerClasses ΓK
      ((φ : characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) :=
    (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
      (G := G) (L := L) (K := K)).1 φ.2
  have hφe :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
          (G := G) (L := L) (K := K) φ =
        hφ.lift := rfl
  rw [hφe]
  simpa using hφ.lift_mk g

/-- Helper for Exercise 12-12.7-8: this is the canonical linear zero-fiber composite promised by
Serre's source route. The only remaining work afterwards is to upgrade this fixed linear
normalization to an algebra equivalence by proving multiplicativity on the fiber. -/
private noncomputable def zero_fiber_linearEquiv_galoisPowerClass_functions :
    (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₗ[((⊥ : Ideal A).ResidueField)]
      (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) :=
  botFiber_characterRingOverFieldAlgebraScalarExtensionSubalgebra_to_baseChangeLinearEquiv
      (A := A) (K := K) (G := G)
    |>.trans
      ((characterRingOverFieldAlgebraScalarExtension_over_botResidueField_algEquiv_over_K
        (A := A) (K := K) (G := G)).toLinearEquiv.trans <|
        (((characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
          (G := G) (L := L) (K := K)).restrictScalars ((⊥ : Ideal A).ResidueField)).toLinearEquiv.trans <|
          (AlgEquiv.piCongrRight fun _ : GaloisPowerClass ΓK ↦
            (botResidueField_algEquiv_fractionField_over_botResidueField
              (A := A) (K := K)).symm).toLinearEquiv))

/-- Helper for Exercise 12-12.7-8: on a pure tensor in the bottom fiber, the canonical
zero-fiber linear equivalence evaluates at a `Γ_K`-class by multiplying the scalar coefficient
with the underlying `K`-valued owner function. -/
private theorem zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
    (a : ((⊥ : Ideal A).ResidueField))
    (x : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (g : G) :
    algebraMap ((⊥ : Ideal A).ResidueField) K
      (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
        (a ⊗ₜ[A] x) (galoisPowerClassMk ΓK g)) =
      algebraMap ((⊥ : Ideal A).ResidueField) K a * (x : G → K) g := by
  let e₁ := botFiber_characterRingOverFieldAlgebraScalarExtensionSubalgebra_to_baseChangeLinearEquiv
    (A := A) (K := K) (G := G)
  let e₂ := (characterRingOverFieldAlgebraScalarExtension_over_botResidueField_algEquiv_over_K
    (A := A) (K := K) (G := G)).toLinearEquiv
  let e₃ := ((characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions
    (G := G) (L := L) (K := K)).restrictScalars ((⊥ : Ideal A).ResidueField)).toLinearEquiv
  let e₄ := (AlgEquiv.piCongrRight fun _ : GaloisPowerClass ΓK ↦
    (botResidueField_algEquiv_fractionField_over_botResidueField
      (A := A) (K := K)).symm).toLinearEquiv
  change (algebraMap ((⊥ : Ideal A).ResidueField) K)
      (((e₁.trans (e₂.trans (e₃.trans e₄))) (a ⊗ₜ[A] x)) (galoisPowerClassMk ΓK g)) =
    algebraMap ((⊥ : Ideal A).ResidueField) K a * (x : G → K) g
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  letI : Module.Flat A ((⊥ : Ideal A).ResidueField) :=
    IsLocalization.flat (R := A) (S := ((⊥ : Ideal A).ResidueField)) (nonZeroDivisors A)
  have he₁ :
      ((e₁ (a ⊗ₜ[A] x) :
        characterRingOverFieldAlgebraScalarExtensionSubalgebra ((⊥ : Ideal A).ResidueField) K G) :
          G → K) =
        a •
          ((x :
            characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K) := by
    change
      Submodule.tensorSpanEquivSpan A ((⊥ : Ideal A).ResidueField)
          ((((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K)))
          (a ⊗ₜ[A] x) =
        a •
          ((x :
            characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K)
    simpa using
      (Submodule.coe_tensorSpanEquivSpan_apply_tmul
        (R := A) (A := ((⊥ : Ideal A).ResidueField))
        (s := ((((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))))
        a x)
  have hclass :
      e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g) =
        (((e₂ (e₁ (a ⊗ₜ[A] x)) :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) g) :=
    characterRingOverFieldAlgebraScalarExtensionSubalgebra_over_field_algEquiv_galoisPowerClass_functions_apply_mk
      (G := G) (L := L) (K := K) (e₂ (e₁ (a ⊗ₜ[A] x))) g
  have hcoeff :
      (algebraMap ((⊥ : Ideal A).ResidueField) K)
          (e₄ (e₃ (e₂ (e₁ (a ⊗ₜ[A] x)))) (galoisPowerClassMk ΓK g)) =
        e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g) := by
    change
      (algebraMap ((⊥ : Ideal A).ResidueField) K)
          (((botResidueField_algEquiv_fractionField_over_botResidueField
              (A := A) (K := K)).symm)
            (e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g))) =
        e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g)
    exact
      (botResidueField_algEquiv_fractionField_over_botResidueField
        (A := A) (K := K)).apply_symm_apply
          (e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g))
  calc
    (algebraMap ((⊥ : Ideal A).ResidueField) K)
        (e₄ (e₃ (e₂ (e₁ (a ⊗ₜ[A] x)))) (galoisPowerClassMk ΓK g)) =
          e₃ (e₂ (e₁ (a ⊗ₜ[A] x))) (galoisPowerClassMk ΓK g) := hcoeff
    _ = (((e₂ (e₁ (a ⊗ₜ[A] x)) :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra K K G) : G → K) g) :=
            hclass
    _ = (algebraMap ((⊥ : Ideal A).ResidueField) K) a * (x : G → K) g := by
          simpa [e₂, he₁, Pi.smul_apply, Algebra.smul_def]

/-- Helper for Exercise 12-12.7-8: generic pointwise multiplicativity comparison, zero case in
the left factor. Stated over opaque types so that instantiating it at the huge fiber types is a
single cheap unification instead of a normalization storm. -/
private theorem pointwiseMulComparison_zero_left
    {B C D I : Type*} [CommRing B] [CommRing C] [CommRing D]
    (M : B → I → C) (ρ : C →+* D) (c : I) (hM0 : M 0 = 0) (η : B) :
    ρ (M (0 * η) c) = ρ ((M 0 * M η) c) := by
  rw [zero_mul, hM0]
  simp

/-- Helper for Exercise 12-12.7-8: generic pointwise multiplicativity comparison, zero case in
the right factor. -/
private theorem pointwiseMulComparison_zero_right
    {B C D I : Type*} [CommRing B] [CommRing C] [CommRing D]
    (M : B → I → C) (ρ : C →+* D) (c : I) (hM0 : M 0 = 0) (ξ : B) :
    ρ (M (ξ * 0) c) = ρ ((M ξ * M 0) c) := by
  rw [mul_zero, hM0]
  simp

/-- Helper for Exercise 12-12.7-8: generic pointwise multiplicativity comparison, additivity in
the right factor. -/
private theorem pointwiseMulComparison_add_right
    {B C D I : Type*} [CommRing B] [CommRing C] [CommRing D]
    (M : B → I → C) (ρ : C →+* D) (c : I)
    (hMadd : ∀ u v : B, M (u + v) = M u + M v)
    (ξ η₁ η₂ : B)
    (h₁ : ρ (M (ξ * η₁) c) = ρ ((M ξ * M η₁) c))
    (h₂ : ρ (M (ξ * η₂) c) = ρ ((M ξ * M η₂) c)) :
    ρ (M (ξ * (η₁ + η₂)) c) = ρ ((M ξ * M (η₁ + η₂)) c) := by
  have hL : M (ξ * (η₁ + η₂)) c = M (ξ * η₁) c + M (ξ * η₂) c := by
    rw [mul_add, hMadd]
    rfl
  have hR : (M ξ * M (η₁ + η₂)) c = (M ξ * M η₁) c + (M ξ * M η₂) c := by
    rw [hMadd]
    exact mul_add (M ξ c) (M η₁ c) (M η₂ c)
  rw [hL, hR, map_add, map_add, h₁, h₂]

/-- Helper for Exercise 12-12.7-8: generic pointwise multiplicativity comparison, additivity in
the left factor. -/
private theorem pointwiseMulComparison_add_left
    {B C D I : Type*} [CommRing B] [CommRing C] [CommRing D]
    (M : B → I → C) (ρ : C →+* D) (c : I)
    (hMadd : ∀ u v : B, M (u + v) = M u + M v)
    (ξ₁ ξ₂ η : B)
    (h₁ : ρ (M (ξ₁ * η) c) = ρ ((M ξ₁ * M η) c))
    (h₂ : ρ (M (ξ₂ * η) c) = ρ ((M ξ₂ * M η) c)) :
    ρ (M ((ξ₁ + ξ₂) * η) c) = ρ ((M (ξ₁ + ξ₂) * M η) c) := by
  have hL : M ((ξ₁ + ξ₂) * η) c = M (ξ₁ * η) c + M (ξ₂ * η) c := by
    rw [add_mul, hMadd]
    rfl
  have hR : (M (ξ₁ + ξ₂) * M η) c = (M ξ₁ * M η) c + (M ξ₂ * M η) c := by
    rw [hMadd]
    exact add_mul (M ξ₁ c) (M ξ₂ c) (M η c)
  rw [hL, hR, map_add, map_add, h₁, h₂]

/-- Helper for Exercise 12-12.7-8: on pure tensors, both sides of the multiplicativity
comparison for the canonical linear zero-fiber composite reduce to the same scalar multiple of
the product function. -/
private theorem zero_fiber_linearEquiv_galoisPowerClass_functions_mul_apply_mk_tmul
    (a b : ((⊥ : Ideal A).ResidueField))
    (x y : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (g : G) :
    algebraMap ((⊥ : Ideal A).ResidueField) K
      (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
        ((a ⊗ₜ[A] x) * (b ⊗ₜ[A] y)) (galoisPowerClassMk ΓK g)) =
      algebraMap ((⊥ : Ideal A).ResidueField) K
        ((zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
            (a ⊗ₜ[A] x) *
          zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
            (b ⊗ₜ[A] y))
          (galoisPowerClassMk ΓK g)) := by
  -- On pure tensors, both sides reduce to the same scalar multiple of the product function.
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  have hmul :=
    zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
      (A := A) (K := K) (G := G) (L := L) (a := a * b) (x := x * y) g
  have hξ :=
    zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
      (A := A) (K := K) (G := G) (L := L) (a := a) (x := x) g
  have hη :=
    zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
      (A := A) (K := K) (G := G) (L := L) (a := b) (x := y) g
  calc
    algebraMap ((⊥ : Ideal A).ResidueField) K
        (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
          ((a * b) ⊗ₜ[A] (x * y)) (galoisPowerClassMk ΓK g)) =
        algebraMap ((⊥ : Ideal A).ResidueField) K (a * b) * ((x * y : G → K) g) := by
          simpa using hmul
    _ = (algebraMap ((⊥ : Ideal A).ResidueField) K a * (x : G → K) g) *
          (algebraMap ((⊥ : Ideal A).ResidueField) K b * (y : G → K) g) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = algebraMap ((⊥ : Ideal A).ResidueField) K
          ((zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
            (a ⊗ₜ[A] x)) (galoisPowerClassMk ΓK g)) *
        algebraMap ((⊥ : Ideal A).ResidueField) K
          ((zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
            (b ⊗ₜ[A] y)) (galoisPowerClassMk ΓK g)) := by
          rw [← hξ, ← hη]
    _ = algebraMap ((⊥ : Ideal A).ResidueField) K
          (((zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
              (a ⊗ₜ[A] x)) *
            (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
              (b ⊗ₜ[A] y))) (galoisPowerClassMk ΓK g)) := by
          rw [Pi.mul_apply, map_mul]

/-- Helper for Exercise 12-12.7-8: after evaluating the canonical linear zero-fiber composite at
the `Γ_K`-class of a representative `g`, multiplication in the bottom fiber matches pointwise
multiplication in the function ring. This is the multiplicativity input needed to upgrade the
linear normalization to an algebra equivalence. -/
private theorem zero_fiber_linearEquiv_galoisPowerClass_functions_mul_apply_mk
    (ξ η :
      ((⊥ : Ideal A).Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))
    (g : G) :
    algebraMap ((⊥ : Ideal A).ResidueField) K
      (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
        (ξ * η) (galoisPowerClassMk ΓK g)) =
      algebraMap ((⊥ : Ideal A).ResidueField) K
        ((zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) ξ *
          zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) η)
          (galoisPowerClassMk ΓK g)) := by
  -- Route correction: prove multiplicativity at each chosen `Γ_K`-class by tensor induction,
  -- delegating every branch to a fresh-budget helper lemma stated over opaque types.
  have hM0 :
      zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) 0 = 0 := by
    simpa using
      (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)).map_zero
  have hMadd :
      ∀ u v :
        ((⊥ : Ideal A).Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)),
        zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) (u + v) =
          zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) u +
            zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) v :=
    fun u v ↦
      (zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)).map_add u v
  refine TensorProduct.induction_on ξ ?_ ?_ ?_
  · exact pointwiseMulComparison_zero_left
      (M := fun ζ ↦
        zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) ζ)
      (algebraMap ((⊥ : Ideal A).ResidueField) K) (galoisPowerClassMk ΓK g) hM0 η
  · intro a x
    refine TensorProduct.induction_on η ?_ ?_ ?_
    · exact pointwiseMulComparison_zero_right
        (M := fun ζ ↦
          zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) ζ)
        (algebraMap ((⊥ : Ideal A).ResidueField) K) (galoisPowerClassMk ΓK g) hM0 (a ⊗ₜ[A] x)
    · intro b y
      exact zero_fiber_linearEquiv_galoisPowerClass_functions_mul_apply_mk_tmul
        (A := A) (K := K) (G := G) (L := L) a b x y g
    · intro η₁ η₂ h₁ h₂
      exact pointwiseMulComparison_add_right
        (M := fun ζ ↦
          zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) ζ)
        (algebraMap ((⊥ : Ideal A).ResidueField) K) (galoisPowerClassMk ΓK g) hMadd
        (a ⊗ₜ[A] x) η₁ η₂ h₁ h₂
  · intro ξ₁ ξ₂ h₁ h₂
    exact pointwiseMulComparison_add_left
      (M := fun ζ ↦
        zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G) ζ)
      (algebraMap ((⊥ : Ideal A).ResidueField) K) (galoisPowerClassMk ΓK g) hMadd
      ξ₁ ξ₂ η h₁ h₂

/-- Helper for Exercise 12-12.7-8: Serre's zero branch first identifies the bottom fiber over
`(0)` with the function ring on `Γ_K`-classes. This is the structural bottom-fiber equivalence
that turns the ambient zero-prime classification into pure fiber transport. -/
noncomputable def zero_fiber_algEquiv_galoisPowerClass_functions :
    (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
      (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)) :=
  let e :=
    zero_fiber_linearEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G)
  AlgEquiv.ofLinearEquiv e
    (by
      -- The linear zero-fiber composite sends the tensor unit to the constant-one function.
      ext c
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
      apply (algebraMap ((⊥ : Ideal A).ResidueField) K).injective
      simpa using
        (zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
          (A := A) (K := K) (G := G) (L := L)
          (a := (1 : ((⊥ : Ideal A).ResidueField)))
          (x := (1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
          g))
    (by
      intro ξ η
      -- Equality of residue-field-valued functions is checked coordinatewise and reflected
      -- through the injective map `((0).ResidueField) → K`.
      ext c
      obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
      apply (algebraMap ((⊥ : Ideal A).ResidueField) K).injective
      simpa using
        (zero_fiber_linearEquiv_galoisPowerClass_functions_mul_apply_mk
          (A := A) (K := K) (G := G) (L := L) ξ η g))

/-- Helper for Exercise 12-12.7-8: after choosing a bottom-fiber equivalence `e`, evaluating at
`c` and then mapping the bottom residue field into `K` gives the exact transported `A`-algebra
map whose kernel defines the ambient zero-fiber prime. -/
private noncomputable def transported_zero_fiber_evalAlgHom
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →ₐ[A] K :=
  { toRingHom := ((algebraMap ((⊥ : Ideal A).ResidueField) K).comp
      (((Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c).comp
        e.toRingHom).comp
        (Algebra.TensorProduct.includeRight
          (R := A) (A := ((⊥ : Ideal A).ResidueField))
          (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)).toRingHom))
    commutes' := by
      -- Evaluating a scalar from `A` in the transported bottom fiber and then mapping to `K`
      -- reproduces the original scalar map `A → K`.
      intro a
      have he :
          e.toRingEquiv (((algebraMap A ((⊥ : Ideal A).ResidueField)) a) ⊗ₜ[A]
            (1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) =
            algebraMap ((⊥ : Ideal A).ResidueField)
              (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))
              ((algebraMap A ((⊥ : Ideal A).ResidueField)) a) := by
        simpa using e.commutes ((algebraMap A ((⊥ : Ideal A).ResidueField)) a)
      have he' :
          e.toRingEquiv.toRingHom
              (((algebraMap A ((⊥ : Ideal A).ResidueField)) a) ⊗ₜ[A]
                (1 : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) =
            algebraMap ((⊥ : Ideal A).ResidueField)
              (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField))
              ((algebraMap A ((⊥ : Ideal A).ResidueField)) a) := by
        simpa using he
      calc
        ((algebraMap ((⊥ : Ideal A).ResidueField) K).comp
            (((Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c).comp
              e.toRingEquiv.toRingHom).comp
              (Algebra.TensorProduct.includeRight
                (R := A) (A := ((⊥ : Ideal A).ResidueField))
                (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)).toRingHom))
            (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) =
            (algebraMap ((⊥ : Ideal A).ResidueField) K)
              ((algebraMap A ((⊥ : Ideal A).ResidueField)) a) := by
                simp [RingHom.comp_apply]
                exact
                  congrArg
                    (Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c)
                    he
        _ = algebraMap A K a := by
              rw [IsScalarTower.algebraMap_apply A ((⊥ : Ideal A).ResidueField) K] }

/-- Helper for Exercise 12-12.7-8: the residue-field-valued transported evaluation map before
postcomposing with the canonical coefficient embedding `((0).ResidueField) → K`. This isolates
the pure bottom-fiber coordinate evaluation from the later comparison with Serre's defining
`K`-valued evaluation map. -/
private noncomputable def transported_zero_fiber_residue_evalRingHom
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →+*
      ((⊥ : Ideal A).ResidueField) :=
  (((Pi.evalRingHom (fun _ : GaloisPowerClass ΓK ↦ ((⊥ : Ideal A).ResidueField)) c).comp
      e.toRingHom).comp
      (Algebra.TensorProduct.includeRight
        (R := A) (A := ((⊥ : Ideal A).ResidueField))
        (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)).toRingHom)

/-- Helper for Exercise 12-12.7-8: postcomposing the transported residue-field evaluation map
with the canonical embedding `((0).ResidueField) → K` does not change its kernel. -/
private theorem transported_zero_fiber_evalAlgHom_ker_eq_residue_eval_ker
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK) :
    RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G) e c).toRingHom =
      RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (K := K) (G := G) e c) := by
  -- The only extra map is the injective scalar extension from the bottom residue field into `K`.
  simpa [transported_zero_fiber_evalAlgHom, transported_zero_fiber_residue_evalRingHom,
    zero_fiber_evalAlgHomToK]
    using RingHom.ker_comp_of_injective
      (transported_zero_fiber_residue_evalRingHom (A := A) (K := K) (G := G) e c)
      (algebraMap ((⊥ : Ideal A).ResidueField) K).injective

/-- Helper for Exercise 12-12.7-8: transporting the residue-field coordinate-evaluation prime back
through the bottom-fiber identifications produces the kernel of the corresponding residue-field
evaluation map on `A ⊗ R_K(G)`. -/
private theorem transportedZeroFiberEvalPrimeAsIdeal_eq_ker_residue_evalRingHom
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK) :
    ((PrimeSpectrum.primesOverOrderIsoFiber
        A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
        (⊥ : Ideal A)).symm
      (zero_fiber_lift (A := A) (K := K) (G := G) e c)).1 =
        RingHom.ker (transported_zero_fiber_residue_evalRingHom (A := A) (K := K) (G := G) e c) := by
  -- Unfold both transports until the statement is just membership in a twice-comapped kernel.
  ext x
  change (Algebra.TensorProduct.includeRight
      (R := A) (A := ((⊥ : Ideal A).ResidueField))
      (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) x) ∈
        (((PrimeSpectrum.comapEquiv e.toRingEquiv).symm
          (zero_fiber_eval_prime (A := A) (K := K) (G := G) c)).asIdeal) ↔
      transported_zero_fiber_residue_evalRingHom (A := A) (K := K) (G := G) e c x = 0
  change (Algebra.TensorProduct.includeRight
      (R := A) (A := ((⊥ : Ideal A).ResidueField))
      (B := characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) x) ∈
        Ideal.comap e.toRingHom
          ((zero_fiber_eval_prime (A := A) (K := K) (G := G) c).asIdeal) ↔
      transported_zero_fiber_residue_evalRingHom (A := A) (K := K) (G := G) e c x = 0
  -- The transported coordinate prime is exactly the kernel of the composed residue evaluation map.
  constructor <;> intro h <;> simpa [zero_fiber_eval_prime,
    transported_zero_fiber_residue_evalRingHom, RingHom.mem_ker, RingHom.comp_apply] using h

/-- Helper for Exercise 12-12.7-8: once the transported bottom-fiber evaluation map agrees with
Serre's defining evaluation map for `P₀,c`, the corresponding transported coordinate prime is
already exactly `P₀,c`. This isolates the final kernel comparison from the still-missing
structural bottom-fiber equivalence. -/
theorem transported_zero_fiber_eval_prime_eq_zero_prime_of_evalAlgHom_eq
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (c : GaloisPowerClass ΓK)
    (hfg :
      transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G) e c =
        { toRingHom := galoisPowerClassScalarExtensionZeroPrimeIdealEval K c
          commutes' := galoisPowerClassScalarExtensionZeroPrimeIdealEval_algebraMap
            (A := A) (K := K) (G := G) c }) :
    zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
        (zero_fiber_lift (A := A) (K := K) (G := G) e c) =
      galoisPowerClassScalarExtensionZeroPrimeIdeal K c := by
  apply PrimeSpectrum.ext
  -- Matching the transported evaluation map with Serre's owner map identifies their kernels.
  have hker :
      RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G) e c).toRingHom =
        RingHom.ker (galoisPowerClassScalarExtensionZeroPrimeIdealEval K c) := by
    rw [show
        (transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G) e c).toRingHom =
          galoisPowerClassScalarExtensionZeroPrimeIdealEval K c by
            exact congrArg AlgHom.toRingHom hfg]
  have hresidueKer :
      RingHom.ker (transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G) e c).toRingHom =
        RingHom.ker (transported_zero_fiber_residue_evalRingHom
          (A := A) (K := K) (G := G) e c) :=
    transported_zero_fiber_evalAlgHom_ker_eq_residue_eval_ker (A := A) (K := K) (G := G) e c
  have htransported :
      (zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
        (zero_fiber_lift (A := A) (K := K) (G := G) e c)).asIdeal =
          RingHom.ker (transported_zero_fiber_residue_evalRingHom
            (A := A) (K := K) (G := G) e c) := by
    -- The transported coordinate prime is exactly the structural kernel identified above.
    simpa [zero_fiber_prime_to_specAKG] using
      transportedZeroFiberEvalPrimeAsIdeal_eq_ker_residue_evalRingHom
        (A := A) (K := K) (G := G) e c
  -- With the structural kernel normalized, the map-equality hypothesis identifies it with the
  -- defining kernel of `P₀,c`.
  calc
    (zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
      (zero_fiber_lift (A := A) (K := K) (G := G) e c)).asIdeal
        = RingHom.ker (transported_zero_fiber_residue_evalRingHom
            (A := A) (K := K) (G := G) e c) :=
          htransported
    _ = RingHom.ker (galoisPowerClassScalarExtensionZeroPrimeIdealEval K c) := by
          exact hresidueKer.symm.trans hker
    _ = (galoisPowerClassScalarExtensionZeroPrimeIdeal K c).asIdeal := by
          rfl

/-- Helper for Exercise 12-12.7-8: evaluating the transported bottom-fiber map on the class of a
group element recovers the original owner value at that element. -/
private theorem transported_zero_fiber_evalAlgHom_apply_mk
    (x : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (g : G) :
    transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G)
        (zero_fiber_algEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G))
        (galoisPowerClassMk ΓK g) x =
      (x : G → K) g := by
  -- The canonical algebra equivalence is built from the linear composite, so evaluating on an
  -- `includeRight` generator is exactly the pure-tensor formula with coefficient `1`.
  simpa [transported_zero_fiber_evalAlgHom, zero_fiber_algEquiv_galoisPowerClass_functions,
    RingHom.comp_apply] using
    (zero_fiber_linearEquiv_galoisPowerClass_functions_apply_tmul
      (A := A) (K := K) (G := G) (L := L)
      (a := (1 : ((⊥ : Ideal A).ResidueField))) (x := x) g)

/-- Helper for Exercise 12-12.7-8: Serre's defining owner map for `P₀,c` may be evaluated on
any representative of the `Γ_K`-class `c`. -/
private theorem galoisPowerClassScalarExtensionZeroPrimeIdealEval_apply_mk
    (x : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (g : G) :
    galoisPowerClassScalarExtensionZeroPrimeIdealEval K (galoisPowerClassMk ΓK g) x =
      (x : G → K) g := by
  let g' : G :=
    Classical.choose ((galoisPowerClassMk_surjective ΓK) (galoisPowerClassMk ΓK g))
  have hg' : galoisPowerClassMk ΓK g' = galoisPowerClassMk ΓK g :=
    Classical.choose_spec ((galoisPowerClassMk_surjective ΓK) (galoisPowerClassMk ΓK g))
  have hxconst :
      IsConstantOnGaloisPowerClasses ΓK
        ((x : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) : G → K) :=
    (mem_characterRingOverFieldAlgebraScalarExtension_over_field_iff_isConstantOnGaloisPowerClasses
      (G := G) (L := L) (K := K)).1 <|
      mem_characterRingOverFieldAlgebraScalarExtension_of_mem_baseChange
        (A := A) (K := K) (G := G) (F := K) x.2
  calc
    galoisPowerClassScalarExtensionZeroPrimeIdealEval K (galoisPowerClassMk ΓK g) x =
        (x : G → K) g' := by
          rfl
    _ = (x : G → K) g := by
          exact hxconst.eq_of_mk_eq hg'

/-- Helper for Exercise 12-12.7-8: for the canonical bottom-fiber equivalence fixed above, the
transported coordinate evaluation map at `c` is exactly Serre's defining `K`-valued owner map for
`P₀,c`. This is the last zero-branch interface step before the kernel comparison closes. -/
theorem transported_zero_fiber_evalAlgHom_eq_zeroPrimeIdealEval
    (c : GaloisPowerClass ΓK) :
    transported_zero_fiber_evalAlgHom (A := A) (K := K) (G := G)
        (zero_fiber_algEquiv_galoisPowerClass_functions (A := A) (K := K) (G := G))
        c =
      { toRingHom := galoisPowerClassScalarExtensionZeroPrimeIdealEval K c
        commutes' := galoisPowerClassScalarExtensionZeroPrimeIdealEval_algebraMap
          (A := A) (K := K) (G := G) c } :=
  -- Route correction: the previous helper was false for an arbitrary equivalence `e`, since
  -- precomposing `e` with a nontrivial quotient-coordinate permutation changes the transported
  -- evaluation map. After the canonical `e` above is constructed, this comparison should be
  -- proved by comparing both maps on representatives of the chosen `Γ_K`-class.
  by
    ext x
    obtain ⟨g, rfl⟩ := galoisPowerClassMk_surjective (G := G) ΓK c
    rw [transported_zero_fiber_evalAlgHom_apply_mk (A := A) (K := K) (G := G) (L := L)]
    simpa using
      (galoisPowerClassScalarExtensionZeroPrimeIdealEval_apply_mk
        (A := A) (K := K) (G := G) (L := L) (x := x) g).symm

/-- Helper for Exercise 12-12.7-8: after identifying the bottom fiber with the function ring on
`Γ_K`-classes, classifying bottom-fiber primes reduces to comparing transported
coordinate-evaluation primes with the ambient owners `P₀,c`. -/
theorem zero_fiber_prime_classification_of_algEquiv
    (e : (((⊥ : Ideal A).Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) ≃ₐ[((⊥ : Ideal A).ResidueField)]
        (GaloisPowerClass ΓK → ((⊥ : Ideal A).ResidueField)))
    (htransport : ∀ c : GaloisPowerClass ΓK,
      zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
          (zero_fiber_lift (A := A) (K := K) (G := G) e c) =
        galoisPowerClassScalarExtensionZeroPrimeIdeal K c)
    (q :
      PrimeSpectrum
        (((⊥ : Ideal A).Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))) :
    ∃ c : GaloisPowerClass ΓK,
      zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G) q =
        galoisPowerClassScalarExtensionZeroPrimeIdeal K c := by
  -- Surjectivity of the lifted coordinate primes reduces the classification to the transport
  -- identity for those coordinate primes.
  obtain ⟨c, hc⟩ :=
    zero_fiber_lift_surjective (A := A) (K := K) (G := G) e q
  refine ⟨c, ?_⟩
  calc
    zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G) q
      = zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
          (zero_fiber_lift (A := A) (K := K) (G := G) e c) := by
            simpa [hc]
    _ = galoisPowerClassScalarExtensionZeroPrimeIdeal K c := htransport c

end

end Representation
