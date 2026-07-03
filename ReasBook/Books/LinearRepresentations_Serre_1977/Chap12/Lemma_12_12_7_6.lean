import Mathlib
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_5
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_7_6.Index

noncomputable section

open Representation
open PrimeSpectrum
open scoped Representation SubgroupInduction

universe u v w

namespace Representation

open IsCyclotomicExtension.Rat

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] Classical.propDecidable
local notation "ΓK" => Γ[K](G)

section

omit [Fact p.Prime]

/-- Helper for Lemma 12-12.7-6: the induced witness on `G` already lies in LinearRepresentations_Serre_1977's owner
`A ⊗ R_K(G)`, so it is constant on ambient `Γ_K`-power classes. This is the owner-level
invariance that the remaining Lemma `16` bridge must specialize. -/
lemma induced_lifted_orbit_supported_isConstantOnGaloisPowerClasses_local
    (x : G) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P)) :
    IsConstantOnGaloisPowerClasses ΓK
      (((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K)) := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  -- The induced witness already lies in the owner `A ⊗ R_K(G)`, so the owner-level constancy
  -- theorem applies without any further subgroup-specific work.
  simpa [χ, χA] using
    isConstantOnGaloisPowerClasses_of_mem_characterRingOverFieldAlgebraScalarExtension_local
      (K := K) (A := A) χA.2

/-- Helper for Lemma 12-12.7-6: equality of ambient `Γ_K`-power classes forces equality of the
induced witness values. This is the pointwise form of the previous owner-level constancy lemma. -/
lemma induced_lifted_orbit_supported_eq_of_galoisPowerClass_eq_local
    (x : G) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    {g h : G}
    (hclass : galoisPowerClassMk ΓK g = galoisPowerClassMk ΓK h) :
    ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
        (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
        G → K) g =
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
        (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
        G → K) h := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  have hχconst : IsConstantOnGaloisPowerClasses ΓK χ := by
    simpa [χ, χA] using
      induced_lifted_orbit_supported_isConstantOnGaloisPowerClasses_local
        (K := K) (A := A) x P ψ
  simpa [χ, χA] using hχconst.eq_of_mk_eq hclass

end

/-- Helper for Lemma 12-12.7-6: LinearRepresentations_Serre_1977's Lemma `16` step compares the induced separator
with its `p`-regular component modulo any prime ideal above `(p)`. Because the owner values live in
`K`, the congruence is expressed by an `A`-lift lying in `Q.asIdeal`. -/
lemma induced_lifted_orbit_supported_sub_mem_primeIdealOverPrime_of_pRegularComponent_local
    (x : G) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (Q : PrimeSpectrum A)
    (hQ : Ideal.span {(p : A)} ≤ Q.asIdeal)
    (g : G) :
    ∃ q : Q.asIdeal,
      algebraMap A K q.1 =
        ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) g -
        ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) (pRegularComponent p g) := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  have hclass :
      pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p g, isPRegular_pRegularComponent (p := p) g⟩ =
        pRegularGaloisPowerClassMk ΓK p
          ⟨pRegularComponent p (pRegularComponent p g),
            isPRegular_pRegularComponent (p := p) (pRegularComponent p g)⟩ := by
    apply congrArg (pRegularGaloisPowerClassMk ΓK p)
    apply Subtype.ext
    exact (pRegularComponent_eq_self_of_isPRegular
      (p := p) (x := pRegularComponent p g)
      (isPRegular_pRegularComponent (p := p) g)).symm
  simpa [χ, χA] using
    character_value_sub_mem_primeIdealOverPrime_of_pRegularComponents_galoisPowerConjugate
      (K := K) (A := A) (p := p) χA.2 hclass Q hQ

/-- Helper for Lemma 12-12.7-6: if the `p`-regular component value comes from `A`, then the value at
`g` is congruent to that same `A`-witness modulo every prime above `(p)`, expressed by an `A`-lift in
the prime ideal. -/
lemma induced_lifted_orbit_supported_exists_range_witness_with_mod_primeIdealOverPrime_eq_local
    (x : G) (_hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (g : G)
    (hg_range :
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
            A ⊗R[K](G)) : G → K) (pRegularComponent p g) ∈
        Set.range (algebraMap A K)) :
    ∃ a : A,
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
            A ⊗R[K](G)) : G → K) (pRegularComponent p g) =
        algebraMap A K a ∧
      ∀ (Q : PrimeSpectrum A) (_hQ : Ideal.span {(p : A)} ≤ Q.asIdeal),
        ∃ q : Q.asIdeal,
          algebraMap A K q.1 =
            ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
              (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
                A ⊗R[K](G)) : G → K) g - algebraMap A K a := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  rcases hg_range with ⟨a, ha⟩
  refine ⟨a, ha.symm, ?_⟩
  intro Q hQ
  rcases induced_lifted_orbit_supported_sub_mem_primeIdealOverPrime_of_pRegularComponent_local
      (K := K) (A := A) (p := p) x P ψ Q hQ g with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa [χ, χA, ha] using hq

/-- Helper for Lemma 12-12.7-6: LinearRepresentations_Serre_1977's Lemma `16` step should transfer `A`-valuedness from the
`p`-regular component back to the original element for the induced separator built from the
associated subgroup witness. -/
lemma induced_lifted_orbit_supported_value_mem_range_of_pRegularComponent_local
    (x : G) (_hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (_hψ :
      ∀ h : associatedGammaPElementarySubgroup ΓK x P, IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
          associated_orbit_supported_function (K := K) (A := A) x P h)
    (hψ_nonpregular :
      ∀ h : associatedGammaPElementarySubgroup ΓK x P, ¬ IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h = 0)
    (g : G)
    (hg_range :
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
            A ⊗R[K](G)) : G → K) (pRegularComponent p g) ∈
        Set.range (algebraMap A K)) :
    ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
        (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
        G → K) g ∈
      Set.range (algebraMap A K) := by
  by_cases hg : IsPRegular p g
  · -- On the `p`-regular branch, the comparison element is just `g` itself, so the already
    -- proved range statement at `pRegularComponent p g` closes the goal directly.
    simpa [pRegularComponent_eq_self_of_isPRegular (p := p) (x := g) hg] using hg_range
  · -- Route correction: LinearRepresentations_Serre_1977 only needs the chosen `H = C ⋅ P`-lift to vanish on the
    -- non-`p`-regular locus. The existing induction lemma then forces the induced value at `g`
    -- itself to be zero, so it is automatically `A`-valued.
    refine ⟨0, ?_⟩
    simpa using
      (induced_lifted_orbit_supported_eq_zero_of_not_isPRegular_local
        (K := K) (A := A) (p := p) x P ψ hψ_nonpregular g hg).symm

/-- Helper for Lemma 12-12.7-6: LinearRepresentations_Serre_1977's cyclic source `ψ_C` on `C = ⟨x⟩` belongs to
`A ⊗ R_K(C)`. This packages the source proof's first step before the restriction lift to
`H = associatedGammaPElementarySubgroup Γ[K](G) x P`. -/
lemma orbit_supported_zpowers_character_exists_local
    (x : G) :
    ∃ χC : A ⊗R[K](Subgroup.zpowers x),
      ∀ c : Subgroup.zpowers x,
        (χC : Subgroup.zpowers x → K) c =
          ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c := by
  refine ⟨⟨((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x), ?_⟩, ?_⟩
  · -- LinearRepresentations_Serre_1977's `ψ_C` is exactly the orbit-supported cyclic source on `C = ⟨x⟩`; the reduced
    -- ambient arithmetic subgroup packages the Lemma `15` descent already proved in the helper
    -- file.
    exact
      orbit_supported_zpowers_mem_characterRingOverFieldAlgebraScalarExtension_of_reducedAmbientGamma_local
        (K := K) (A := A) x
  · intro c
    rfl
section

omit [IsDomain A] [IsFractionRing A K]

/-- Helper for Lemma 12-12.7-6: the already-proved restriction surjectivity from
Lemma `12-12.7-5` lifts any element of `A ⊗ R_K(⟨x⟩)` to the associated subgroup
`H = associatedGammaPElementarySubgroup ΓK x P`. This isolates the purely formal scalar-extension
step before the source-faithful support-zero argument is added. -/
lemma exists_lifted_character_on_associated_subgroup_with_prescribed_restriction_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (χC : A ⊗R[K](Subgroup.zpowers x)) :
    ∃ ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P),
      ∀ c : Subgroup.zpowers x,
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K)
            (Subgroup.inclusion (zpowers_le_associatedGammaPElementarySubgroup ΓK p x P) c) =
          (χC : Subgroup.zpowers x → K) c := by
  classical
  let H := associatedGammaPElementarySubgroup ΓK x P
  let C : Subgroup G := Subgroup.zpowers x
  let hC : C ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
  have hlift :
      ∀ {ψC : C → K}, ψC ∈ A ⊗R[K](C) →
      ∃ ψ : A ⊗R[K](H),
        ∀ c : C,
          (ψ : H → K) (Subgroup.inclusion hC c) = ψC c := by
    intro ψC hψC
    induction hψC using Submodule.span_induction with
    | mem ψC hψC =>
        have hψC' : ψC ∈ R[K](C) := by
          simpa using hψC
        obtain ⟨η, hη⟩ :=
          associatedGammaPElementarySubgroupRestrictionOverField_surjective
            (K := K) (p := p) (x := x) (P := P) hx ⟨ψC, hψC'⟩
        refine ⟨⟨η, mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
          (A := A) (K := K) η.2⟩, ?_⟩
        intro c
        -- Evaluate the chosen field-level lift on the cyclic factor to recover the original
        -- character generator.
        let ψCR : R[K](C) := ⟨ψC, hψC'⟩
        have hηfun :
            (((hC ↾R[K]) η : R[K](C)) : C → K) = (ψCR : C → K) := by
          exact congrArg (fun ξ : R[K](C) ↦ (ξ : C → K)) hη
        simpa [H, C, hC, Subgroup.characterRingOverFieldRestrictionOfLe_apply] using
          congrFun hηfun c
    | zero =>
        refine ⟨0, ?_⟩
        intro c
        rfl
    | add ψC φC _ _ hψ hφ =>
        rcases hψ with ⟨ψ, hψ⟩
        rcases hφ with ⟨φ, hφ⟩
        refine ⟨ψ + φ, ?_⟩
        intro c
        -- Restriction is additive, so the lifted witnesses add pointwise on `⟨x⟩`.
        calc
          ((ψ + φ : A ⊗R[K](H)) : H → K) (Subgroup.inclusion hC c) =
              (ψ : H → K) (Subgroup.inclusion hC c) +
                (φ : H → K) (Subgroup.inclusion hC c) := rfl
          _ = ψC c + φC c := by rw [hψ c, hφ c]
    | smul a ψC _ hψ =>
        rcases hψ with ⟨ψ, hψ⟩
        refine ⟨a • ψ, ?_⟩
        intro c
        -- Scalar multiplication commutes with evaluation along the subgroup inclusion.
        calc
          ((a • ψ : A ⊗R[K](H)) : H → K) (Subgroup.inclusion hC c) =
              a • (ψ : H → K) (Subgroup.inclusion hC c) := rfl
          _ = a • ψC c := by rw [hψ c]
  obtain ⟨ψ, hψ⟩ := hlift (ψC := (χC : C → K)) χC.2
  refine ⟨ψ, ?_⟩
  intro c
  simpa [H, C, hC] using hψ c

end

/-- Helper for Lemma 12-12.7-6: LinearRepresentations_Serre_1977 first builds the cyclic source on
`C = ⟨x⟩` and then lifts it to `H = associatedGammaPElementarySubgroup ΓK x P` by the plain
restriction-surjectivity statement from Lemma `12-12.7-5`. -/
lemma exists_lifted_orbit_supported_character_on_associated_subgroup_from_ambient_gamma_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    ∃ ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P),
      ∀ c : Subgroup.zpowers x,
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K)
            (Subgroup.inclusion (zpowers_le_associatedGammaPElementarySubgroup ΓK p x P) c) =
          ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c := by
  -- Route correction: LinearRepresentations_Serre_1977's source only needs a restriction lift from `C = ⟨x⟩` to
  -- `H = associatedGammaPElementarySubgroup ΓK x P`; the old demand for a lift vanishing on all
  -- of `H \ ⟨x⟩` was stronger than the source proof.
  -- The cyclic source step now uses the reduced ambient arithmetic subgroup on `C = ⟨x⟩`, so the
  -- remaining work here is only to package LinearRepresentations_Serre_1977's `ψ_C` in `A ⊗ R_K(C)` before invoking the
  -- already-stable restriction-surjectivity bridge.
  obtain ⟨χC, hχC⟩ :=
    orbit_supported_zpowers_character_exists_local (K := K) (A := A) x
  -- Once LinearRepresentations_Serre_1977's cyclic source `ψ_C` is packaged as an owner element on `C = ⟨x⟩`, the
  -- associated-subgroup witness is exactly the already-proved restriction lift from Lemma
  -- `12-12.7-5`.
  obtain ⟨ψ, hψ⟩ :=
    exists_lifted_character_on_associated_subgroup_with_prescribed_restriction_local
      (K := K) (A := A) (p := p) x hx P χC
  refine ⟨ψ, ?_⟩
  intro c
  calc
    (ψ : associatedGammaPElementarySubgroup ΓK x P → K)
        (Subgroup.inclusion (zpowers_le_associatedGammaPElementarySubgroup ΓK p x P) c) =
      (χC : Subgroup.zpowers x → K) c := hψ c
    _ = ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c := hχC c

/-- Helper for Lemma 12-12.7-6: after lifting LinearRepresentations_Serre_1977's cyclic source from `C = ⟨x⟩` to
`H = associatedGammaPElementarySubgroup ΓK x P`, the lifted witness agrees with the associated
orbit-supported formula on every `p`-regular element of `H`. -/
lemma exists_lifted_orbit_supported_character_on_associated_subgroup_pregular_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    ∃ ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P),
      ∀ h : associatedGammaPElementarySubgroup ΓK x P, IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
          associated_orbit_supported_function (K := K) (A := A) x P h := by
  classical
  obtain ⟨ψ, hψres⟩ :=
    exists_lifted_orbit_supported_character_on_associated_subgroup_from_ambient_gamma_local
      (K := K) (A := A) (p := p) x hx P
  refine ⟨ψ, ?_⟩
  intro h hh
  let H := associatedGammaPElementarySubgroup ΓK x P
  let hC : Subgroup.zpowers x ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
  -- Every `p`-regular element of `H = ⟨x⟩ ⋅ P` already lies in the cyclic factor `⟨x⟩`, so the
  -- restriction identity on `⟨x⟩` is enough.
  obtain ⟨c, hc⟩ :=
    pregular_eq_inclusion_zpowers_of_mem_associatedGammaPElementarySubgroup
      (K := K) (p := p) x hx P h hh
  calc
    (ψ : H → K) h = (ψ : H → K) (Subgroup.inclusion hC c) := by
      exact congrArg (fun z : H ↦ (ψ : H → K) z) hc.symm
    _ = ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c := hψres c
    _ = associated_orbit_supported_function (K := K) (A := A) x P
          (Subgroup.inclusion hC c) := by
          symm
          simpa [H, hC] using
            associated_orbit_supported_function_inclusion_eq_orbit_supported_zpowers_local
              (K := K) (A := A) (p := p) x P c
    _ = associated_orbit_supported_function (K := K) (A := A) x P h := by
          exact congrArg
            (associated_orbit_supported_function (K := K) (A := A) x P) hc

/-- Helper for Lemma 12-12.7-6: the restriction-lifted witness already vanishes on the
`p`-regular part of `H \ ⟨x⟩`, because on that locus it agrees with LinearRepresentations_Serre_1977's orbit-supported
formula and the orbit-supported formula is supported on `⟨x⟩`. -/
lemma exists_lifted_orbit_supported_character_on_associated_subgroup_pregular_zero_off_not_mem_zpowers_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    ∃ ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P),
      (∀ h : associatedGammaPElementarySubgroup ΓK x P, IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
          associated_orbit_supported_function (K := K) (A := A) x P h) ∧
      (∀ h : associatedGammaPElementarySubgroup ΓK x P,
          IsPRegular p h.1 → h.1 ∉ Subgroup.zpowers x →
            (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h = 0) := by
  obtain ⟨ψ, hψ⟩ :=
    exists_lifted_orbit_supported_character_on_associated_subgroup_pregular_local
      (K := K) (A := A) (p := p) x hx P
  refine ⟨ψ, hψ, ?_⟩
  intro h hh hz
  -- On the `p`-regular locus, the lifted witness is the orbit-supported formula, so support on
  -- `⟨x⟩` gives the required vanishing immediately.
  exact
    lifted_orbit_supported_eq_zero_of_not_mem_zpowers_of_isPRegular_local
      (K := K) (A := A) (p := p) x hx P ψ hψ hh hz

/-- Helper for Lemma 12-12.7-6: a non-`p`-regular element of
`H = associatedGammaPElementarySubgroup ΓK x P` cannot be an ambient `Γ_K`-power of the
`p`-regular generator `x`. This isolates the exact contradiction used in the source proof before
the explicit Lemma `17(b)` extension is inserted. -/
lemma not_exists_gamma_power_of_not_isPRegular_in_associated_subgroup_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    {h : associatedGammaPElementarySubgroup ΓK x P}
    (hh : ¬ IsPRegular p h.1) :
    ¬ ∃ t : ΓK, h.1 = x ^ t := by
  intro hpow
  rcases hpow with ⟨t, ht⟩
  -- Every ambient `Γ_K`-power of `x` still lies in the cyclic subgroup `⟨x⟩`, hence remains
  -- `p`-regular because `x` itself is `p`-regular.
  have hxpow_mem : x ^ t ∈ Subgroup.zpowers x := by
    rw [pow_subgroup_eq_pow_nat]
    exact Subgroup.pow_mem (Subgroup.zpowers x)
      (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩) _
  have hxpow_reg : IsPRegular p (x ^ t) :=
    isPRegular_of_mem_zpowers_local (p := p) x hx hxpow_mem
  exact hh (ht ▸ hxpow_reg)

/-- Helper for Lemma 12-12.7-6: once a lift on `H = C ⋅ P` restricts to LinearRepresentations_Serre_1977's cyclic source on
`C = ⟨x⟩` and is already known to vanish off `C`, the source proof's support conclusions are
formal. Namely, the lift agrees with the associated orbit-supported function on every `p`-regular
element of `H`, and the zero-off-`⟨x⟩` hypothesis is simply carried along unchanged. -/
lemma lifted_character_matches_associated_orbit_supported_of_restriction_and_zero_off_zpowers_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (hψres :
      ∀ c : Subgroup.zpowers x,
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K)
            (Subgroup.inclusion (zpowers_le_associatedGammaPElementarySubgroup ΓK p x P) c) =
          ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c)
    (hψ_off :
      ∀ h : associatedGammaPElementarySubgroup ΓK x P,
        h.1 ∉ Subgroup.zpowers x →
          (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h = 0) :
    (∀ h : associatedGammaPElementarySubgroup ΓK x P, IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
          associated_orbit_supported_function (K := K) (A := A) x P h) ∧
      (∀ h : associatedGammaPElementarySubgroup ΓK x P,
          h.1 ∉ Subgroup.zpowers x →
            (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h = 0) := by
  constructor
  · intro h hh
    let H := associatedGammaPElementarySubgroup ΓK x P
    let hC : Subgroup.zpowers x ≤ H := zpowers_le_associatedGammaPElementarySubgroup ΓK p x P
    -- Every `p`-regular element of `H = ⟨x⟩ ⋅ P` already lies in `⟨x⟩`, so the restriction
    -- identity on `C = ⟨x⟩` recovers the ambient orbit-supported formula.
    obtain ⟨c, hc⟩ :=
      pregular_eq_inclusion_zpowers_of_mem_associatedGammaPElementarySubgroup
        (K := K) (p := p) x hx P h hh
    calc
      (ψ : H → K) h = (ψ : H → K) (Subgroup.inclusion hC c) := by
        exact congrArg (fun z : H ↦ (ψ : H → K) z) hc.symm
      _ = ((algebraMap A K) ∘ orbit_supported_zpowers_function (K := K) (A := A) x) c := hψres c
      _ = associated_orbit_supported_function (K := K) (A := A) x P
            (Subgroup.inclusion hC c) := by
            symm
            simpa [H, hC] using
              associated_orbit_supported_function_inclusion_eq_orbit_supported_zpowers_local
                (K := K) (A := A) (p := p) x P c
      _ = associated_orbit_supported_function (K := K) (A := A) x P h := by
            exact congrArg
              (associated_orbit_supported_function (K := K) (A := A) x P) hc
  · intro h hh
    -- The second component is exactly the input support hypothesis.
    exact hψ_off h hh

/-- Helper for Lemma 12-12.7-6: LinearRepresentations_Serre_1977's actual lift on
`H = associatedGammaPElementarySubgroup ΓK x P` only needs to agree with the orbit-supported
source on the `p`-regular locus of `H`. The stronger zero-off-`H \ ⟨x⟩` statement is no longer on
the critical path. -/
lemma exists_lifted_orbit_supported_character_on_associated_subgroup_with_support_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    ∃ ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P),
      ∀ h : associatedGammaPElementarySubgroup ΓK x P, IsPRegular p h.1 →
        (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
          associated_orbit_supported_function (K := K) (A := A) x P h := by
  -- Route correction: the source proof only lifts `ψ_C` from `C = ⟨x⟩` to `H = C ⋅ P` and then
  -- uses the fact that every `p`-regular element of `H` already lies in `C`.
  exact
    exists_lifted_orbit_supported_character_on_associated_subgroup_pregular_local
      (K := K) (A := A) (p := p) x hx P
/-- Helper for Lemma 12-12.7-6: once the induced value at the `p`-regular component of `g` is
known to come from `A`, the source-faithful Chapter `12.7.4` specialization already produces the
exact arithmetic frontier left to close. Namely, one obtains a fixed witness `a : A` whose image
matches the `p`-regular component value and whose difference from the value at `g` is represented
by an `A`-lift lying in every prime ideal above `(p)`. -/
lemma induced_lifted_orbit_supported_exact_range_frontier_local
    (x : G) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (g : G)
    (hg_range :
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) (pRegularComponent p g) ∈
        Set.range (algebraMap A K)) :
    ∃ a : A,
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) (pRegularComponent p g) =
        algebraMap A K a ∧
      ∀ (Q : PrimeSpectrum A) (_hQ : Ideal.span {(p : A)} ≤ Q.asIdeal),
        ∃ q : Q.asIdeal,
          algebraMap A K q.1 =
            ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
              (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
                A ⊗R[K](G)) : G → K) g -
              algebraMap A K a := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  rcases hg_range with ⟨a, ha⟩
  refine ⟨a, ha.symm, ?_⟩
  intro Q hQ
  -- Compare `χ g` with the already controlled `p`-regular component, then rewrite that value by
  -- the chosen witness `a`.
  rcases induced_lifted_orbit_supported_sub_mem_primeIdealOverPrime_of_pRegularComponent_local
      (K := K) (A := A) (p := p) x P ψ Q hQ g with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  simpa [χ, χA, ha] using hq

/-- Helper for Lemma 12-12.7-6: when `(p)` is a proper ideal of `A`, one prime ideal above `(p)`
already turns the exact Chapter `12.7.4` frontier into a genuine `A`-lift of the induced value at
`g`. -/
lemma induced_lifted_orbit_supported_value_mem_range_of_exact_frontier_of_span_prime_ne_top_local
    (x : G) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (g : G)
    (hg_range :
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) (pRegularComponent p g) ∈
        Set.range (algebraMap A K))
    (hproper : Ideal.span ({(p : A)} : Set A) ≠ ⊤) :
    ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
        (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
        G → K) g ∈
      Set.range (algebraMap A K) := by
  let χA : A ⊗R[K](G) :=
    Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ
  let χ : G → K := χA
  obtain ⟨a, ha, hmoda⟩ :=
    induced_lifted_orbit_supported_exact_range_frontier_local
      (K := K) (A := A) (p := p) x P ψ g hg_range
  obtain ⟨M, hMmax, hle⟩ :=
    Ideal.exists_le_maximal (Ideal.span ({(p : A)} : Set A)) hproper
  let Q : PrimeSpectrum A := ⟨M, hMmax.isPrime⟩
  rcases hmoda Q hle with ⟨q, hq⟩
  refine ⟨a + q.1, ?_⟩
  -- A single prime-over-`(p)` witness is enough in the proper-ideal branch.
  calc
    algebraMap A K (a + q.1) = algebraMap A K a + algebraMap A K q.1 := by simp
    _ = algebraMap A K a + (χ g - algebraMap A K a) := by rw [hq]
    _ = χ g := by abel
section

omit [IsDomain A] [Fact p.Prime]

/-- Helper for Lemma 12-12.7-6: if `(p) = ⊤`, then there are no prime ideals of `A` lying over
`(p)`. This isolates the vacuous prime-over-`(p)` part of the top-ideal branch before the
remaining denominator rewrite is handled. -/
lemma not_span_prime_le_primeIdeal_of_span_prime_eq_top_local
    (Q : PrimeSpectrum A)
    (htop : Ideal.span ({(p : A)} : Set A) = ⊤) :
    ¬ Ideal.span ({(p : A)} : Set A) ≤ Q.asIdeal := by
  intro hQ
  -- Rewrite the comparison with the top ideal, which would force the prime ideal itself to be
  -- the whole ring.
  have htopQ : Q.asIdeal = ⊤ := by
    exact top_le_iff.mp (by simpa [htop] using hQ)
  exact Q.isPrime.ne_top htopQ

/-- Helper for Lemma 12-12.7-6: once `(p) = ⊤`, the prime `p` is already a unit in `A`, so every
power of `p` is a unit as well. This isolates the denominator-clearing input for the top-ideal
branch of LinearRepresentations_Serre_1977's argument. -/
lemma prime_pow_isUnit_of_span_prime_eq_top_local
    (n : ℕ)
    (htop : Ideal.span ({(p : A)} : Set A) = ⊤) :
    IsUnit ((p : A) ^ n) := by
  -- Turn the ideal-theoretic hypothesis into the concrete unit statement needed for later
  -- denominator clearing.
  have hp_unit : IsUnit (p : A) := by
    simpa using (Ideal.span_singleton_eq_top.mp htop : IsUnit (p : A))
  exact hp_unit.pow n

end

section

omit [IsDomain A] [IsFractionRing A K] [Fact p.Prime]

/-- Helper for Lemma 12-12.7-6: any fraction in the fraction field `K` whose denominator is
already a unit of `A` comes from `A` itself. -/
lemma algebraMap_div_mem_range_of_isUnit_denom_local
    (a b : A) (hb : IsUnit b) :
    algebraMap A K a / algebraMap A K b ∈ Set.range (algebraMap A K) := by
  rcases hb with ⟨u, rfl⟩
  -- Replace the denominator by the inverse unit inside `A` before mapping to the fraction field.
  refine ⟨a * ↑u⁻¹, ?_⟩
  simp [div_eq_mul_inv, map_mul]

/-- Helper for Lemma 12-12.7-6: under `(p) = ⊤`, every fraction with denominator a power of `p`
already lies in the image of `A → K`. This is the exact arithmetic closure LinearRepresentations_Serre_1977's top-case branch
still needs once the induced value is rewritten with a `p`-power denominator. -/
lemma algebraMap_div_prime_pow_mem_range_of_span_prime_eq_top_local
    (a : A) (n : ℕ)
    (htop : Ideal.span ({(p : A)} : Set A) = ⊤) :
    algebraMap A K a / algebraMap A K ((p : A) ^ n) ∈ Set.range (algebraMap A K) := by
  -- The previous lemma applies because powers of `p` become units when `(p) = ⊤`.
  exact
    algebraMap_div_mem_range_of_isUnit_denom_local
      (K := K) (A := A) a ((p : A) ^ n)
      (prime_pow_isUnit_of_span_prime_eq_top_local (A := A) (p := p) n htop)

end

/-- Helper for Lemma 12-12.7-6: after lifting LinearRepresentations_Serre_1977's cyclic witness from `C = ⟨x⟩` to
`H = C ⋅ P`, the Chapter `12.7.4` exact-frontier argument gives pointwise `A`-valuedness as soon
as `(p)` is a proper ideal. -/
lemma induced_lifted_orbit_supported_value_mem_range_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (hψ :
      ∀ h : associatedGammaPElementarySubgroup ΓK x P,
        IsPRegular p h.1 →
          (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
            associated_orbit_supported_function (K := K) (A := A) x P h)
    (g : G)
    (hproper : Ideal.span ({(p : A)} : Set A) ≠ ⊤) :
    ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
        (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
        G → K) g ∈
      Set.range (algebraMap A K) := by
  -- First control the induced value at the `p`-regular component; the only remaining arithmetic
  -- step is to transfer that `A`-valuedness back to the original element `g` in the proper-ideal
  -- branch where the exact-frontier comparison produces a genuine `A`-lift.
  have hg_range :
      ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
          G → K) (pRegularComponent p g) ∈
        Set.range (algebraMap A K) :=
    induced_lifted_orbit_supported_value_mem_range_at_pRegularComponent_local
      (K := K) (A := A) (p := p) x hx P ψ hψ g
  exact
    induced_lifted_orbit_supported_value_mem_range_of_exact_frontier_of_span_prime_ne_top_local
      (K := K) (A := A) (p := p) x P ψ g hg_range hproper

/-- Helper for Lemma 12-12.7-6: once the induced witness is known pointwise to lie in the image
of `A → K` in the proper-ideal branch, choose a pointwise `A`-valued lift. This is the only
branch where LinearRepresentations_Serre_1977's exact-frontier comparison is needed. -/
lemma induced_character_has_A_valued_lift_local
    (x : G) (hx : IsPRegular p x) (P : Sylow p N[ΓK](x))
    (ψ : A ⊗R[K](associatedGammaPElementarySubgroup ΓK x P))
    (hψ :
      ∀ h : associatedGammaPElementarySubgroup ΓK x P,
        IsPRegular p h.1 →
          (ψ : associatedGammaPElementarySubgroup ΓK x P → K) h =
            associated_orbit_supported_function (K := K) (A := A) x P h)
    (hproper : Ideal.span ({(p : A)} : Set A) ≠ ⊤) :
    ∃ f : G → A,
      ((algebraMap A K) ∘ f) =
        ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
          (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
            A ⊗R[K](G)) : G → K) := by
  let χ : G → K :=
    ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
      (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ : A ⊗R[K](G)) :
      G → K)
  classical
  have hχ_range : ∀ g : G, χ g ∈ Set.range (algebraMap A K) := by
    intro g
    -- In the proper-ideal branch, the exact-frontier range statement supplies the needed
    -- preimage in `A` at each point.
    simpa [χ] using
      induced_lifted_orbit_supported_value_mem_range_local
        (K := K) (A := A) (p := p) x hx P ψ hψ g hproper
  refine ⟨fun g ↦ Classical.choose (hχ_range g), ?_⟩
  funext g
  -- Choose a preimage of each induced value independently.
  exact Classical.choose_spec (hχ_range g)

/-- Lemma 12-12.7-6: with `Γ_K = Γ[K](G)` attached to the intermediate field `K ⊆ L` in the
cyclotomic realization of the exponent of `G`, there exists an element of LinearRepresentations_Serre_1977's scalar-extended
owner `A ⊗ V_{K,p}` whose realized function on `G` comes from induction from the associated
subgroup `H = ⟨x⟩ ⋅ P`, has nonzero value at `x` modulo every prime ideal of `A` containing `p`,
and vanishes on every `p'`-element not `Γ_K`-conjugate to `x`. -/
theorem exists_associatedGammaPElementary_character_nonzero_mod_primeIdeals_vanishing_off_galoisClass
    (x : G)
    (hx : IsPRegular p x) (P : Sylow p N[ΓK](x)) :
    let H := associatedGammaPElementarySubgroup ΓK x P
    let xClass := pRegularGaloisPowerClassMk ΓK p ⟨x, hx⟩
    ∃ ψ : A ⊗R[K](H), ∃ χ : G → K, ∃ f : G → A,
      χ = H.characterRingOverFieldAlgebraScalarExtensionInduction ψ ∧
        ((algebraMap A K) ∘ f) = χ ∧
          (∀ (Q : PrimeSpectrum A) (_hQ : Ideal.span {(p : A)} ≤ Q.asIdeal),
            f x ∉ Q.asIdeal) ∧
          ∀ s (hs : IsPRegular p s),
            pRegularGaloisPowerClassMk ΓK p ⟨s, hs⟩ ≠ xClass →
              χ s = 0 := by
  -- Proof skeleton: package the ambient orbit-supported source on `C = ⟨x⟩`, lift it to
  -- `H = associatedGammaPElementarySubgroup ΓK x P`, induce to `G`, then combine the explicit
  -- value-at-`x` computation with the vanishing-off-class lemma and the pointwise `A`-valued
  -- range bridge.
  -- Route correction: the broken intrinsic-`Γ[K](⟨x⟩)` branch has been removed. The remaining
  -- blocker is now exactly the theorem-local exact-range closure for the induced function after
  -- the Chapter `12.7.4` congruence step from `g` to `pRegularComponent p g` has been separated.
  classical
  dsimp
  let H := associatedGammaPElementarySubgroup ΓK x P
  by_cases htop : Ideal.span ({(p : A)} : Set A) = ⊤
  · -- Route correction: when `(p) = ⊤`, the prime-over-`(p)` condition is vacuous, so the
    -- theorem may use the trivial induced witness instead of forcing the generic top-branch
    -- arithmetic on LinearRepresentations_Serre_1977's nontrivial source lift.
    let χ : G → K := H.characterRingOverFieldAlgebraScalarExtensionInduction (0 : A ⊗R[K](H))
    refine ⟨0, χ, (fun _ ↦ 0), rfl, ?_, ?_, ?_⟩
    · funext g
      -- The trivial subgroup witness induces the zero class function.
      dsimp [χ]
      simp
    · intro Q hQ
      exact
        (not_span_prime_le_primeIdeal_of_span_prime_eq_top_local
          (A := A) (p := p) Q htop) hQ |>.elim
    · intro s hs hs_ne
      -- The induced function of the zero witness vanishes identically.
      dsimp [χ]
      simp
  · obtain ⟨ψ, hψ⟩ :=
      exists_lifted_orbit_supported_character_on_associated_subgroup_with_support_local
        (K := K) (A := A) (p := p) x hx P
    let χ : G → K := H.characterRingOverFieldAlgebraScalarExtensionInduction ψ
    obtain ⟨f, hf⟩ :=
      induced_character_has_A_valued_lift_local
        (K := K) (A := A) (p := p) x hx P ψ hψ htop
    refine ⟨ψ, χ, f, rfl, hf, ?_, ?_⟩
    · intro Q hQ
      have hχx :
          χ x = algebraMap A K (Nat.card N[ΓK](x) / Nat.card (P : Subgroup N[ΓK](x))) := by
        -- LinearRepresentations_Serre_1977's right-`P` orbit count gives the explicit nonzero value at the distinguished
        -- element `x`.
        change
          ((Subgroup.characterRingOverFieldAlgebraScalarExtensionInduction
              (A := A) (K := K) (H := associatedGammaPElementarySubgroup ΓK x P) ψ :
                A ⊗R[K](G)) : G → K) x =
            algebraMap A K (Nat.card N[ΓK](x) / Nat.card (P : Subgroup N[ΓK](x)))
        exact
          induced_lifted_orbit_supported_at_x_eq_normalizer_quotient_local
            (K := K) (A := A) (p := p) x hx P ψ hψ
      have hfx :
          f x = Nat.card N[ΓK](x) / Nat.card (P : Subgroup N[ΓK](x)) := by
        apply IsFractionRing.injective A K
        calc
          algebraMap A K (f x) = χ x := by
            exact congrFun hf x
          _ = algebraMap A K (Nat.card N[ΓK](x) / Nat.card (P : Subgroup N[ΓK](x))) := hχx
      rw [hfx]
      exact
        nat_cast_not_mem_primeIdealOverPrime_of_coprime
          (A := A) p (Nat.card N[ΓK](x) / Nat.card (P : Subgroup N[ΓK](x)))
          (associatedGammaPElementary_index_coprime_p (K := K) (p := p) x P) Q hQ
    · intro s hs hs_ne
      -- Away from the `p`-regular `Γ_K`-class of `x`, the induced source witness already
      -- vanishes.
      simpa [χ, H] using
        induced_lifted_orbit_supported_eq_zero_of_pregular_class_ne_local
          (K := K) (A := A) (p := p) x hx P ψ hψ s hs hs_ne

end

end Representation
