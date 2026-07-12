import Mathlib
import StacksProject_2024.Chap09.Lemma_9_27_3
import StacksProject_2024.Chap10.Definition_10_161_1
import StacksProject_2024.Chap10.Lemma_10_36_16
import StacksProject_2024.Chap10.Lemma_10_161_7

-- Declarations for this item will be appended below by the statement pipeline.

open IntermediateField

universe u v

section

/-  
Domain triage: this file is in the commutative algebra of Japanese (`N-2`) domains in positive
characteristic, with the source test family restricted to finite purely inseparable fraction-field
extensions.

Owner abstractions sampled for this item:
- `IsN2Ring`, the source-facing owner from `Definition_10_161_1`;
- `IsN2Ring.integralClosure_finite_of_finiteDimensional`, the arbitrary-universe bridge theorem
  for finite normalization in finite fraction-field extensions;
- `isGalois_over_relative_perfectClosure_of_normal`, the local source-faithful decomposition step
  for the relative perfect closure inside a finite normal extension;
- `IsIntegralClosure.finite`, recalled in `Lemma_10_161_8` for the separable normalization step.

This file is `source-facing`: the textbook item is a characteristic-`p` test criterion for the
existing owner `IsN2Ring`, not a new owner. The primitive data are the Noetherian domain `R`, the
positive characteristic prime `p`, and the family of finite purely inseparable extensions of
`FractionRing R`. Finiteness of integral closures is derived API from `IsN2Ring` and the sampled
integral-closure owners, so no extra wrapper predicate should be introduced here.
-/
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]

/-- Helper for Lemma 10.161.12: a finite normal extension is Galois over its relative perfect
closure, hence separable over that purely inseparable subextension. -/
theorem isGalois_over_relative_perfectClosure_of_normal
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Normal F E] :
    IsGalois (perfectClosure F E) E := by
  -- Route correction: reuse the Chapter 9 normal/perfect-closure theorem instead of
  -- reproving the fixed-field characterization locally.
  exact isGalois_over_perfectClosure_of_normal_algebraic (F := F) (E := E)

omit [IsDomain R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.161.12: the one-step and iterated integral closures inside `M` agree
after restricting scalars back to the original base ring `R`. -/
lemma iterated_integralClosure_eq_restrictScalars
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {M_insep : Type v} [Field M_insep] [Algebra K M_insep] [Algebra R M_insep]
    [IsScalarTower R K M_insep]
    {M : Type v} [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
    [Algebra M_insep M] [IsScalarTower K M_insep M] [IsScalarTower R M_insep M] :
    integralClosure R M =
      (integralClosure (integralClosure R M_insep) M).restrictScalars R := by
  -- Route correction: compare the two subalgebras by the integrality predicates they encode,
  -- instead of transporting through `IsIntegralClosure.trans` on the carrier aliases.
  ext x
  rw [Subalgebra.mem_restrictScalars]
  constructor
  · intro hx
    -- Integrality over `R` ascends to integrality over the intermediate integral closure.
    exact IsIntegral.tower_top (A := integralClosure R M_insep) hx
  · intro hx
    -- Integrality over the intermediate integral closure descends back to integrality over `R`.
    exact isIntegral_trans (R := R) (A := integralClosure R M_insep) (x := x) hx

/-- Helper for Lemma 10.161.12: finiteness of the integral closure descends along an embedding
into a larger normal overfield without changing the base ring. -/
lemma finite_integralClosure_of_normal_overfield
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type v} [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    {M : Type v} [Field M] [Algebra R M] [Algebra K M] [IsScalarTower R K M]
    (f : L →ₐ[K] M) (hfin : Module.Finite R (integralClosure R M)) :
    Module.Finite R (integralClosure R L) := by
  let fR : L →ₐ[R] M := AlgHom.restrictScalars R f
  exact finite_of_integralClosure_map_to_larger_base (R := R) (S := R) fR fR.injective hfin

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Helper for Lemma 10.161.12: for a finite normal extension, finiteness of the normalization
over the purely inseparable perfect closure and the separable upper step implies finiteness over
the original base ring `R`. -/
lemma finite_integralClosure_of_finite_normal_extension
    (hpure :
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L))
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [Normal (FractionRing R) M] :
    Module.Finite R (integralClosure R M) := by
  let P₀ : IntermediateField (FractionRing R) M := perfectClosure (FractionRing R) M
  letI : Algebra (FractionRing R) ↥P₀ := P₀.algebra'
  letI : Algebra R ↥P₀ :=
    (RingHom.comp (algebraMap (FractionRing R) ↥P₀) (algebraMap R (FractionRing R))).toAlgebra
  letI : Algebra ↥P₀ M := P₀.toAlgebra
  letI : IsScalarTower R (FractionRing R) ↥P₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (FractionRing R) ↥P₀ M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  letI : IsScalarTower R ↥P₀ M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) M]
    rfl
  letI : FiniteDimensional (FractionRing R) ↥P₀ :=
    IntermediateField.finiteDimensional_left (K := FractionRing R) (F := P₀) (L := M)
  letI : FiniteDimensional ↥P₀ M :=
    IntermediateField.finiteDimensional_right (K := FractionRing R) (F := P₀) (L := M)
  letI : IsPurelyInseparable (FractionRing R) ↥P₀ := by
    simpa [P₀] using
      (perfectClosure.isPurelyInseparable (F := FractionRing R) (E := M))
  have hfinLower : Module.Finite R (integralClosure R ↥P₀) :=
    hpure ↥P₀
  letI : IsGalois ↥P₀ M := by
    simpa [P₀] using
      (isGalois_over_relative_perfectClosure_of_normal (F := FractionRing R) (E := M))
  let S := integralClosure R ↥P₀
  letI : Module.Finite R S := hfinLower
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : Algebra S ↥P₀ := Subalgebra.toAlgebra S
  letI : SMul S ↥P₀ :=
    (show Algebra S ↥P₀ from inferInstance).toSMul
  letI : Algebra S M :=
    (RingHom.comp (algebraMap ↥P₀ M) (algebraMap S ↥P₀)).toAlgebra
  letI : SMul S M :=
    (show Algebra S M from inferInstance).toSMul
  letI : Module S M := RingHom.toModule (algebraMap S M)
  letI : IsScalarTower S ↥P₀ M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower R S M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) M]
    rfl
  letI : IsFractionRing S ↥P₀ :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := ↥P₀)
  letI : IsIntegrallyClosed S :=
    integralClosure.isIntegrallyClosedOfFiniteExtension
      (R := R) (K := FractionRing R) (L := ↥P₀)
  letI : Algebra.IsSeparable ↥P₀ M := inferInstance
  letI : Algebra S (integralClosure S M) := SubalgebraClass.toAlgebra (s := integralClosure S M)
  letI : SMul S (integralClosure S M) :=
    (show Algebra S (integralClosure S M) from inferInstance).toSMul
  letI : Module S (integralClosure S M) :=
    RingHom.toModule (algebraMap S (integralClosure S M))
  letI : IsScalarTower S (integralClosure S M) M := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    cases x
    rfl
  letI : Algebra R (integralClosure S M) :=
    (RingHom.comp (algebraMap S (integralClosure S M)) (algebraMap R S)).toAlgebra
  letI : Module R (integralClosure S M) :=
    RingHom.toModule (algebraMap R (integralClosure S M))
  letI : IsScalarTower R S (integralClosure S M) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite S (integralClosure S M) :=
    IsIntegralClosure.finite
      (A := S) (K := ↥P₀) (L := M) (C := integralClosure S M)
  have hfinRestrict : Module.Finite R ((integralClosure S M).restrictScalars R) := by
    let C' := (integralClosure S M).restrictScalars R
    let f : S →+* C' :=
      { toFun := fun s => ⟨algebraMap S M s, isIntegral_algebraMap⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp
        map_zero' := by
          ext
          simp
        map_add' := by
          intro x y
          ext
          simp }
    letI : Algebra S C' := f.toAlgebra
    letI : Module S C' := RingHom.toModule f
    letI : Module.Finite S C' := by
      simpa [C'] using (inferInstance : Module.Finite S (integralClosure S M))
    letI : IsScalarTower R S C' := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro x
      ext
      change (algebraMap R M) x = (algebraMap S M) ((algebraMap R S) x)
      simpa using congrArg (fun g : R →+* M => g x) (IsScalarTower.algebraMap_eq R S M)
    exact Module.Finite.trans (R := R) (A := S) (M := C')
  rw [iterated_integralClosure_eq_restrictScalars
    (R := R) (K := FractionRing R) (M_insep := ↥P₀) (M := M)]
  exact hfinRestrict

set_option synthInstance.maxHeartbeats 100000 in
/-- Helper for Lemma 10.161.12: finiteness for arbitrary finite extensions follows by passing to
their normal closures and descending back. -/
lemma finite_integralClosure_of_finite_extension_via_normal_closure
    (hpure :
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L))
    {L : Type u} [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L] :
    Module.Finite R (integralClosure R L) := by
  let Ω := AlgebraicClosure (FractionRing R)
  letI : Algebra R Ω :=
    (RingHom.comp (algebraMap (FractionRing R) Ω) (algebraMap R (FractionRing R))).toAlgebra
  let iotaΩ : L →ₐ[FractionRing R] Ω :=
    IsAlgClosed.lift (R := FractionRing R) (S := L) (M := Ω)
  letI : Algebra L Ω := iotaΩ.toAlgebra
  letI : IsScalarTower (FractionRing R) L Ω := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    exact (iotaΩ.commutes x).symm
  let M₀ : IntermediateField (FractionRing R) Ω := normalClosure (FractionRing R) L Ω
  letI : Algebra (FractionRing R) ↥M₀ := M₀.algebra'
  letI : Algebra R ↥M₀ :=
    (RingHom.comp (algebraMap (FractionRing R) ↥M₀) (algebraMap R (FractionRing R))).toAlgebra
  letI : IsScalarTower R (FractionRing R) ↥M₀ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Normal (FractionRing R) ↥M₀ := by
    simpa [M₀] using normalClosure.normal (F := FractionRing R) (K := L) (L := Ω)
  letI : FiniteDimensional (FractionRing R) ↥M₀ := by
    simpa [M₀] using normalClosure.is_finiteDimensional (F := FractionRing R) (K := L) (L := Ω)
  let iota : L →ₐ[FractionRing R] ↥M₀ :=
    (normalClosure.algHomEquiv (FractionRing R) L Ω).symm iotaΩ
  have hfinM : Module.Finite R (integralClosure R ↥M₀) :=
    finite_integralClosure_of_finite_normal_extension (R := R) hpure (M := ↥M₀)
  exact finite_integralClosure_of_normal_overfield
    (R := R) (K := FractionRing R) iota hfinM

-- Proof sketch: the forward implication is immediate by restricting the `N-2` finiteness
-- condition to finite purely inseparable extensions. For the converse, given a finite extension
-- `L / FractionRing R`, choose a finite normal closure `M`, decompose `M` into the purely
-- inseparable relative perfect closure and the separable upper step, and then descend the finite
-- normalization of `M` back to `L`.
/-- Lemma 10.161.12: for a Noetherian domain whose fraction field has characteristic `p > 0`, the
`N-2` condition is equivalent to requiring finite integral closure only for finite purely
inseparable extensions of the fraction field. -/
@[stacks 032N]
theorem isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions
    :
    IsN2Ring R ↔
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L) := by
  constructor
  · intro hR L _ _ _ _ _ _
    letI : IsN2Ring R := hR
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional L
  · intro hpure
    -- The converse is now the packaged source proof: use the normal-closure descent lemma as the
    -- small-universe `N-2` field required by `IsN2Ring.mk`.
    refine IsN2Ring.mk ?_
    intro L _ _ _ _ _
    exact finite_integralClosure_of_finite_extension_via_normal_closure (R := R) hpure (L := L)

end
