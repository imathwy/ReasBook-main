import Mathlib
import stacks_project.Chap10.Lemma_10_113_2
import stacks_project.Chap10.Lemma_10_119_9
import stacks_project.Chap10.Lemma_10_52_6
import stacks_project.Chap10.Lemma_10_53_2

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped Pointwise

universe u v

section

/-
Domain triage:
* primary domain: one-dimensional local domains, primes lying over the closed point, and the
  induced residue-field extensions;
* source-facing owner data: the fiber index `P : 𝔪.primesOver S` for `𝔪 = maximalIdeal R`;
* core/canonical owners sampled for this refinement:
  `FiniteDimensional (FractionRing R) (FractionRing S)`,
  `Algebra (FractionRing R) (FractionRing S)`,
  `IsScalarTower R (FractionRing R) (FractionRing S)`,
  `Ideal.primesOver`,
  `finite_primesOver_and_primeHeight_eq_one_of_primeHeight_eq_one`,
  `Ideal.ResidueField.map`,
  `IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim`;
* layer: `source-facing`, since the textbook item is specifically about the closed fiber over the
  maximal ideal of a local domain, while `primesOver` and residue-field maps are the canonical
  ambient owners.

Primitive data are the rings `R`, `S`, the ring map `R → S`, the owner hypothesis that `Frac(S)`
is finite-dimensional over `Frac(R)`, and a prime `P : 𝔪.primesOver S`. The three
public theorems are derived API: maximality of `P`, finiteness of the closed fiber, and finiteness
of the residue-field extension `κ(𝔪) → κ(P)`. -/
variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
variable [IsLocalRing R] [IsNoetherianRing R] [Algebra R S]
variable [Algebra (FractionRing R) (FractionRing S)]
variable [IsScalarTower R (FractionRing R) (FractionRing S)]
variable [FiniteDimensional (FractionRing R) (FractionRing S)]

local notation "mR" => maximalIdeal R
local notation "kR" => Ideal.ResidueField mR

/-- Helper for Lemma 10.119.10: the ring quotient `S / mR S` agrees with the canonical module
quotient by `mR • ⊤`. -/
noncomputable def closedFiber_quotient_module_equiv :
    (S ⧸ Ideal.map (algebraMap R S) mR) ≃ₗ[R] (S ⧸ mR • (⊤ : Submodule R S)) := by
  -- Rewrite the ring-quotient owner as the quotient by the corresponding scalar-multiple
  -- submodule.
  refine Submodule.quotEquivOfEq
    ((Ideal.map (algebraMap R S) mR).restrictScalars R)
    (mR • (⊤ : Submodule R S)) ?_
  simpa using (Ideal.smul_top_eq_map (R := R) (S := S) (I := mR)).symm

/-- Helper for Lemma 10.119.10: a one-dimensional local domain has a nonzero element in its
maximal ideal. -/
lemma exists_nonzero_mem_maximalIdeal_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    ∃ x : R, x ∈ mR ∧ x ≠ 0 := by
  -- The maximal ideal cannot vanish, because a local ring with zero maximal ideal is a field.
  have hnotField : ¬ IsField R :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := R)).mp hdim |>.1
  have hm_ne_bot : mR ≠ ⊥ := by
    intro hm
    exact hnotField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).2 hm)
  exact (maximalIdeal R).ne_bot_iff.mp hm_ne_bot

/-- Helper for Lemma 10.119.10: the closed fiber `S / mR S` has finite `R`-module length. -/
lemma closedFiber_module_length_lt_top
    (hdim : ringKrullDim R = 1) :
    Module.length R (S ⧸ mR • (⊤ : Submodule R S)) < ⊤ := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  obtain ⟨x, hxmem, hx0⟩ :=
    exists_nonzero_mem_maximalIdeal_of_ringKrullDim_eq_one (R := R) hdim
  let n : ℕ := Module.finrank (FractionRing R) (FractionRing S)
  let eK : FractionRing S ≃ₗ[FractionRing R] (Fin n → FractionRing R) :=
    LinearEquiv.ofFinrankEq (FractionRing S) (Fin n → FractionRing R) (by simp [n])
  let eR : FractionRing S ≃ₗ[R] (Fin n → FractionRing R) := eK.restrictScalars R
  let f : S →ₗ[R] (Fin n → FractionRing R) :=
    eR.toLinearMap.comp ((Algebra.linearMap S (FractionRing S)).restrictScalars R)
  have hf : Function.Injective f := by
    intro a b hab
    have hfrac :
        algebraMap S (FractionRing S) a = algebraMap S (FractionRing S) b := by
      exact eR.injective (by simpa [f] using hab)
    apply IsFractionRing.injective S (FractionRing S)
    exact hfrac
  have hquot :
      Module.length R (QuotSMulTop x S) =
        Module.length R (QuotSMulTop x (LinearMap.range f)) := by
    -- Replace `S` by its single coordinate-model embedding into `K^n`.
    simpa using
      (LinearEquiv.length_eq
        (QuotSMulTop.congr x (LinearEquiv.ofInjective f hf)) :
          Module.length R (QuotSMulTop x S) =
            Module.length R (QuotSMulTop x (LinearMap.range f)))
  have hprincipal_finite :
      IsFiniteLength R (R ⧸ Ideal.span ({x} : Set R)) := by
    exact isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
  have hbound :
      Module.length R (QuotSMulTop x (LinearMap.range f)) ≤
        n * Module.length R (R ⧸ Ideal.span ({x} : Set R)) :=
    length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton
      (R := R) (K := FractionRing R) (M := LinearMap.range f)
  have hrange_lt_top :
      Module.length R (QuotSMulTop x (LinearMap.range f)) < ⊤ := by
    -- The source estimate from Lemma `10.119.9` has a finite right-hand side because `R / xR`
    -- has finite length in dimension one.
    have hprincipal_ne_top :
        Module.length R (R ⧸ Ideal.span ({x} : Set R)) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hprincipal_finite
    have hrhs_ne_top :
        n * Module.length R (R ⧸ Ideal.span ({x} : Set R)) ≠ ⊤ := by
      exact WithTop.mul_ne_top (ENat.coe_ne_top n) hprincipal_ne_top
    exact lt_top_iff_ne_top.mpr fun htop ↦
      hrhs_ne_top (top_unique (by simpa [htop] using hbound))
  have hx_lt_top :
      Module.length R (S ⧸ x • (⊤ : Submodule R S)) < ⊤ := by
    -- Route correction: transport the quotient length back along the direct embedding `S → K^n`,
    -- rather than through an intermediate image inside `FractionRing S`.
    simpa [QuotSMulTop] using (show Module.length R (QuotSMulTop x S) < ⊤ by
      rw [hquot]
      exact hrange_lt_top)
  have hxsmul_le : x • (⊤ : Submodule R S) ≤ mR • (⊤ : Submodule R S) := by
    -- Since `x ∈ mR`, the principal multiple `xS` is contained in `mR S`.
    calc
      x • (⊤ : Submodule R S) = Ideal.span ({x} : Set R) • (⊤ : Submodule R S) := by
        symm
        simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R S))
      _ ≤ mR • (⊤ : Submodule R S) := by
        refine Submodule.smul_mono ?_ le_rfl
        exact Ideal.span_le.mpr fun y hy ↦ by
          rcases Set.mem_singleton_iff.mp hy with rfl
          exact hxmem
  -- Descend from the principal quotient `S / xS` to the closed fiber quotient `S / mR S`.
  exact lt_of_le_of_lt
    (by
      simpa [QuotSMulTop] using
        (Module.length_le_of_surjective
          (g := Submodule.factor hxsmul_le)
          (Submodule.factor_surjective hxsmul_le)))
    hx_lt_top

/-- Helper for Lemma 10.119.10: the closed fiber `S / mR S` has finite `R`-module length. -/
lemma closedFiber_length_lt_top
    (hdim : ringKrullDim R = 1) :
    Module.length R (S ⧸ Ideal.map (algebraMap R S) mR) < ⊤ := by
  -- First prove finite length for the canonical module quotient, then rewrite to the ring quotient.
  rw [show Module.length R (S ⧸ Ideal.map (algebraMap R S) mR) =
      Module.length R (S ⧸ mR • (⊤ : Submodule R S)) by
    simpa using
      (LinearEquiv.length_eq (closedFiber_quotient_module_equiv (R := R) (S := S)) :
        Module.length R (S ⧸ Ideal.map (algebraMap R S) mR) =
          Module.length R (S ⧸ mR • (⊤ : Submodule R S)))]
  exact closedFiber_module_length_lt_top (R := R) (S := S) hdim

/-- Helper for Lemma 10.119.10: the canonical quotient `S / mR S`, viewed through the owner
module structure over `R ⧸ mR`, is finite. -/
lemma moduleFinite_closedFiber_quotient_over_residueField
    (hdim : ringKrullDim R = 1) :
    let hTors : Module.IsTorsionBySet R (S ⧸ mR • (⊤ : Submodule R S)) mR :=
      Module.isTorsionBySet_quotient_ideal_smul (R := R) (M := S) (I := mR)
    let _ : Module (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S)) := hTors.module
    Module.Finite (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S)) := by
  let hTors : Module.IsTorsionBySet R (S ⧸ mR • (⊤ : Submodule R S)) mR :=
    Module.isTorsionBySet_quotient_ideal_smul (R := R) (M := S) (I := mR)
  let _ : Module (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S)) := hTors.module
  have hlen :
      Module.length R (S ⧸ mR • (⊤ : Submodule R S)) < ⊤ := by
    -- Transport the finite-length statement from the ring quotient to the canonical module owner.
    rw [show Module.length R (S ⧸ mR • (⊤ : Submodule R S)) =
        Module.length R (S ⧸ Ideal.map (algebraMap R S) mR) by
      simpa using
        (LinearEquiv.length_eq (closedFiber_quotient_module_equiv (R := R) (S := S)).symm :
          Module.length R (S ⧸ mR • (⊤ : Submodule R S)) =
            Module.length R (S ⧸ Ideal.map (algebraMap R S) mR))]
    exact closedFiber_length_lt_top (R := R) (S := S) hdim
  have hfinite_length :
      IsFiniteLength R (S ⧸ mR • (⊤ : Submodule R S)) :=
    Module.length_ne_top_iff.mp (lt_top_iff_ne_top.mp hlen)
  have hfiniteR :
      Module.Finite R (S ⧸ mR • (⊤ : Submodule R S)) :=
    (isFiniteLength_iff_finite_of_isTorsionBySet
      (R := R) (M := S ⧸ mR • (⊤ : Submodule R S)) (m := mR) hTors).mp hfinite_length
  letI := hfiniteR
  -- Finite generation ascends from the restricted `R`-module to the quotient-ring action.
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ mR)
    (S ⧸ mR • (⊤ : Submodule R S))

/-- Helper for Lemma 10.119.10: the closed fiber `S / mR S` is an Artinian ring. -/
lemma isArtinianRing_closedFiber_over_maximalIdeal
    (hdim : ringKrullDim R = 1) :
    IsArtinianRing (S ⧸ Ideal.map (algebraMap R S) mR) := by
  letI : Field (R ⧸ mR) := Ideal.Quotient.field mR
  letI : Module (R ⧸ mR) (S ⧸ Ideal.map (algebraMap R S) mR) := inferInstance
  have hfinite_module :
      Module.Finite (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S)) :=
    moduleFinite_closedFiber_quotient_over_residueField (R := R) (S := S) hdim
  have hfinite_restrict :
      Module.Finite R (S ⧸ mR • (⊤ : Submodule R S)) :=
    Module.Finite.trans (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S))
  letI := hfinite_restrict
  have hfinite :
      Module.Finite (R ⧸ mR) (S ⧸ Ideal.map (algebraMap R S) mR) :=
    by
      letI : Module.Finite R (S ⧸ Ideal.map (algebraMap R S) mR) :=
        Module.Finite.equiv (closedFiber_quotient_module_equiv (R := R) (S := S)).symm
      exact Module.Finite.of_restrictScalars_finite R (R ⧸ mR)
        (S ⧸ Ideal.map (algebraMap R S) mR)
  -- A finite algebra over the residue field is Artinian.
  exact IsArtinianRing.of_finite (R ⧸ mR) (S ⧸ Ideal.map (algebraMap R S) mR)

-- Proof sketch: choose a nonzero element of `maximalIdeal R`, use Lemma `10.119.9` to show that
-- `S / maximalIdeal R • S` has finite length over `ResidueField R`, and hence is Artinian. Prime
-- ideals of `S` lying over `maximalIdeal R` correspond to prime ideals of this Artinian quotient,
-- so each such prime is maximal.
/-- Lemma 10.119.10 (1): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then each prime
ideal of `S` lying over `maximalIdeal R` is maximal. -/
theorem isMaximal_of_primeOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) (P : (mR).primesOver S) :
    P.1.IsMaximal := by
  let mS : Ideal S := Ideal.map (algebraMap R S) mR
  letI : IsArtinianRing (S ⧸ mS) :=
    isArtinianRing_closedFiber_over_maximalIdeal (R := R) (S := S) hdim
  have hmS_le : mS ≤ P.1 := by
    -- A prime lying over `mR` contains the extended ideal `mR S`.
    rw [Ideal.map_le_iff_le_comap]
    simpa [Ideal.under_def] using (le_of_eq P.2.2.over)
  let Q : Ideal (S ⧸ mS) := Ideal.map (Ideal.Quotient.mk mS) P.1
  have hQmax : Q.IsMaximal := by
    -- In the Artinian closed fiber, every prime ideal is maximal.
    exact (IsArtinianRing.isPrime_iff_isMaximal Q).mp inferInstance
  -- Pull maximality back along the surjective quotient map.
  simpa [Q, Ideal.comap_map_mk hmS_le] using
    (Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk mS)
      Ideal.Quotient.mk_surjective (K := Q))

-- Proof sketch: the same finite-length argument shows that `S / maximalIdeal R • S` is an
-- Artinian ring. Its prime spectrum is finite, and primes of `S` lying over `maximalIdeal R`
-- identify with primes of this quotient, giving finiteness of the fiber over `maximalIdeal R`.
/-- Lemma 10.119.10 (2): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then only finitely
many prime ideals of `S` lie over `maximalIdeal R`. -/
theorem finite_primesOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) :
    Finite ((mR).primesOver S) := by
  let mS : Ideal S := Ideal.map (algebraMap R S) mR
  letI : IsArtinianRing (S ⧸ mS) :=
    isArtinianRing_closedFiber_over_maximalIdeal (R := R) (S := S) hdim
  let f : (mR).primesOver S → PrimeSpectrum (S ⧸ mS) := fun P ↦
    ⟨Ideal.map (Ideal.Quotient.mk mS) P.1, inferInstance⟩
  have hf_inj : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    have hmS_le_P : mS ≤ P.1 := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [Ideal.under_def] using (le_of_eq P.2.2.over)
    have hmS_le_Q : mS ≤ Q.1 := by
      rw [Ideal.map_le_iff_le_comap]
      simpa [Ideal.under_def] using (le_of_eq Q.2.2.over)
    have hmap :
        Ideal.map (Ideal.Quotient.mk mS) P.1 =
          Ideal.map (Ideal.Quotient.mk mS) Q.1 := by
      simpa [f] using congrArg PrimeSpectrum.asIdeal hPQ
    have := congrArg (Ideal.comap (Ideal.Quotient.mk mS)) hmap
    simpa [Ideal.comap_map_mk hmS_le_P, Ideal.comap_map_mk hmS_le_Q] using this
  exact Finite.of_injective f hf_inj

/-- Helper for Lemma 10.119.10: quotienting the closed fiber further by a prime over `mR`
produces a finite `R`-module `S / P`. -/
lemma moduleFinite_quotient_of_primeOver_maximalIdeal
    (hdim : ringKrullDim R = 1) (P : (mR).primesOver S) :
    Module.Finite R (S ⧸ P.1) := by
  have hmS_le : Ideal.map (algebraMap R S) mR ≤ P.1 := by
    -- A prime lying over `mR` contains the closed-fiber ideal `mR S`.
    rw [Ideal.map_le_iff_le_comap]
    simpa [Ideal.under_def] using (le_of_eq P.2.2.over)
  have hclosed :
      Module.Finite (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S)) :=
    moduleFinite_closedFiber_quotient_over_residueField (R := R) (S := S) hdim
  have hclosed_restrict :
      Module.Finite R (S ⧸ mR • (⊤ : Submodule R S)) :=
    Module.Finite.trans (R ⧸ mR) (S ⧸ mR • (⊤ : Submodule R S))
  have hclosed_ring :
      Module.Finite R (S ⧸ Ideal.map (algebraMap R S) mR) := by
    letI : Module.Finite R (S ⧸ mR • (⊤ : Submodule R S)) := hclosed_restrict
    exact Module.Finite.equiv (closedFiber_quotient_module_equiv (R := R) (S := S)).symm
  -- The quotient map `(S / mR S) → (S / P)` is surjective because `mR S ⊆ P`.
  letI : Module.Finite R (S ⧸ Ideal.map (algebraMap R S) mR) := hclosed_ring
  exact Module.Finite.of_surjective
    ((Ideal.Quotient.factorₐ R hmS_le :
      S ⧸ Ideal.map (algebraMap R S) mR →ₐ[R] S ⧸ P.1).toLinearMap)
    (Ideal.Quotient.factor_surjective hmS_le)

-- Proof sketch: after proving that `S / maximalIdeal R • S` has finite length over
-- `ResidueField (Localization.AtPrime (maximalIdeal R)) = (maximalIdeal R).ResidueField`, each
-- quotient by a prime lying over `maximalIdeal R` is a finite module over the same residue field.
-- Identifying that quotient field with `P.ResidueField` gives the required finite residue-field
-- extension.
/-- Lemma 10.119.10 (3): if `R → S` is a homomorphism of domains, `R` is a one-dimensional
Noetherian local domain, and the induced extension of fraction rings is finite, then for each
prime ideal `𝔫` of `S` lying over `maximalIdeal R`, the residue field extension
`κ(𝔫) / κ(maximalIdeal R)` is finite. -/
theorem moduleFinite_residueField_of_primeOver_maximalIdeal_of_finite_fractionField_extension
    (hdim : ringKrullDim R = 1) (P : (mR).primesOver S) :
    Module.Finite kR P.1.ResidueField := by
  have hquot :
      Module.Finite R (S ⧸ P.1) :=
    moduleFinite_quotient_of_primeOver_maximalIdeal (R := R) (S := S) hdim P
  have hPmax : P.1.IsMaximal :=
    isMaximal_of_primeOver_maximalIdeal_of_finite_fractionField_extension
      (R := R) (S := S) hdim P
  letI : P.1.IsMaximal := hPmax
  let eResidue : (S ⧸ P.1) ≃ₐ[S ⧸ P.1] P.1.ResidueField :=
    AlgEquiv.ofBijective
      (Algebra.ofId (S ⧸ P.1) P.1.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField P.1)
  have hfinite_residue :
      Module.Finite R P.1.ResidueField := by
    letI : Module.Finite R (S ⧸ P.1) := hquot
    -- Maximality turns the quotient ring `S / P.1` into the residue field `κ(P)`.
    exact Module.Finite.equiv (eResidue.toLinearEquiv.restrictScalars R)
  letI : Module.Finite R P.1.ResidueField := hfinite_residue
  letI : Algebra.IsIntegral R P.1.ResidueField :=
    Algebra.IsIntegral.of_finite R P.1.ResidueField
  have hfinite_over_local_residue :
      Module.Finite (IsLocalRing.ResidueField R) P.1.ResidueField := by
    letI : Algebra (IsLocalRing.ResidueField R) P.1.ResidueField :=
      IsLocalRing.ResidueField.algebraOfIsIntegral (R := R) (k := P.1.ResidueField)
    letI : IsScalarTower R (IsLocalRing.ResidueField R) P.1.ResidueField :=
      IsLocalRing.ResidueField.isScalarTowerOfIsIntegral (R := R) (k := P.1.ResidueField)
    -- Over a local ring, finite generation over `R` descends along `R → κ(mR)`.
    have hcomap :
        Ideal.comap (algebraMap R P.1.ResidueField) (⊥ : Ideal P.1.ResidueField) =
          maximalIdeal R := by
      simpa [RingHom.ker] using
        (eq_maximalIdeal
          (Algebra.ker_algebraMap_isMaximal_of_isIntegral R P.1.ResidueField))
    exact Module.Finite.of_equiv_equiv
      (Ideal.quotEquivOfEq hcomap)
      (RingEquiv.quotientBot P.1.ResidueField)
      (by ext; rfl)
  letI : Module.Finite (IsLocalRing.ResidueField R) P.1.ResidueField :=
    hfinite_over_local_residue
  let eBase : (IsLocalRing.ResidueField R) ≃+* kR :=
    RingEquiv.ofBijective
      (algebraMap (IsLocalRing.ResidueField R) kR)
      (Ideal.bijective_algebraMap_quotient_residueField mR)
  have hcompat :
      RingHom.comp (algebraMap kR P.1.ResidueField) ↑eBase =
        RingHom.comp (RingEquiv.refl P.1.ResidueField)
          (algebraMap (IsLocalRing.ResidueField R) P.1.ResidueField) := by
    -- Both residue-field models send a residue class `residue R r` to the same element of `κ(P)`.
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := R) x
    change algebraMap kR P.1.ResidueField (algebraMap R kR r) =
      algebraMap R P.1.ResidueField r
    exact Ideal.ResidueField.map_algebraMap mR P.1 (algebraMap R S) (P.1.over_def mR) r
  -- Transport finite generation across the canonical equivalence between the two residue-field
  -- presentations of the closed point of `Spec R`.
  exact Module.Finite.of_equiv_equiv eBase (RingEquiv.refl P.1.ResidueField) hcompat

end
