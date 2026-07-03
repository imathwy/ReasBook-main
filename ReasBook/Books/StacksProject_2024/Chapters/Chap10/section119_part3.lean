import Mathlib
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_119_10 (from Chap10) -/
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

/-! ### Lemma_10_119_11 (from Chap10) -/
universe u v w

open scoped Pointwise

section

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Ring.KrullDimLE 1 R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

/-- Helper for Lemma 10.119.11: over a local one-dimensional Noetherian domain, quotienting an
`R`-submodule of a finite-dimensional fraction-field vector space by a nonzero scalar has finite
length. -/
lemma isFiniteLength_quotSMulTop_local_finiteDimensional
    {S : Type*} {L : Type*} {W : Type*}
    [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup W] [Module S W] [Module L W] [IsScalarTower S L W]
    [FiniteDimensional L W]
    (N : Submodule S W) {x : S} (hx : x ≠ 0) :
    IsFiniteLength S (QuotSMulTop x N) := by
  let s : ℕ := Module.finrank L W
  have hs :
      Module.finrank L W = Module.finrank L (Fin s → L) := by
    simp [s]
  let e : W ≃ₗ[L] (Fin s → L) := LinearEquiv.ofFinrankEq W (Fin s → L) hs
  let eS : W ≃ₗ[S] (Fin s → L) := e.restrictScalars S
  let eN : N ≃ₗ[S] N.map eS.toLinearMap :=
    Submodule.equivMapOfInjective eS.toLinearMap eS.injective N
  have hx_nonZeroDivisor : x ∈ nonZeroDivisors S := mem_nonZeroDivisors_iff_ne_zero.mpr hx
  have hquotient_finite :
      IsFiniteLength S (S ⧸ Ideal.span ({x} : Set S)) :=
    isFiniteLength_quotient_span_singleton S hx_nonZeroDivisor
  have hbound :
      Module.length S (QuotSMulTop x (N.map eS.toLinearMap)) ≤
        s * Module.length S (S ⧸ Ideal.span ({x} : Set S)) :=
    length_quotSMulTop_le_finrank_mul_length_quotient_span_singleton
      (R := S) (K := L) (M := N.map eS.toLinearMap)
  have hfinite_mapped :
      IsFiniteLength S (QuotSMulTop x (N.map eS.toLinearMap)) := by
    -- The coordinate-model bound from Lemma `10.119.9` has finite right-hand side because
    -- `S / xS` already has finite length.
    apply Module.length_ne_top_iff.mp
    have hquotient_ne_top :
        Module.length S (S ⧸ Ideal.span ({x} : Set S)) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hquotient_finite
    have hrhs_ne_top :
        s * Module.length S (S ⧸ Ideal.span ({x} : Set S)) ≠ ⊤ := by
      exact WithTop.mul_ne_top (ENat.coe_ne_top s) hquotient_ne_top
    exact fun htop ↦ hrhs_ne_top (top_unique (by simpa [htop] using hbound))
  -- Transport the finite-length result back from the coordinate model to the original submodule.
  exact (QuotSMulTop.congr x eN.symm).isFiniteLength hfinite_mapped

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.11: the quotient `QuotSMulTop x M` is naturally annihilated by the
principal ideal `(x)`, so it carries the canonical `R ⧸ (x)`-module structure. -/
private theorem quotSMulTop_isTorsionBySet_span_singleton
    (M : Submodule R V) (x : R) :
    Module.IsTorsionBySet R (QuotSMulTop x M) (Ideal.span ({x} : Set R)) := by
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span (R := R) (M := QuotSMulTop x M)
    ({x} : Set R)]
  rw [Module.isTorsionBySet_singleton_iff]
  change Module.IsTorsionBy R (↥M ⧸ x • (⊤ : Submodule R ↥M)) x
  simpa using (Module.isTorsionBy_quotient_element_smul (R := R) (M := ↥M) x)

/-- Helper for Lemma 10.119.11: after equipping `V` with a localized `R_p`-action, localizing the
quotient `M / xM` at `p` agrees with quotienting the localized submodule by the image of `x`. -/
private noncomputable def localized_quotSMulTop_atPrime_equiv_localized_submodule_quotient
    (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [Module (Localization.AtPrime p) V]
    [IsScalarTower R (Localization.AtPrime p) V]
    [IsLocalizedModule p.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) (x : R) :
    LocalizedModule.AtPrime p
        (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) ≃ₗ[Localization.AtPrime p]
      (↥(Submodule.localized' (Localization.AtPrime p) p.primeCompl
          (LinearMap.id : V →ₗ[R] V) M) ⧸
        Ideal.span ({algebraMap R (Localization.AtPrime p) x} :
          Set (Localization.AtPrime p)) •
          (⊤ : Submodule (Localization.AtPrime p)
            ↥(Submodule.localized' (Localization.AtPrime p) p.primeCompl
              (LinearMap.id : V →ₗ[R] V) M))) := by
  let S := Localization.AtPrime p
  let Mloc : Submodule S V :=
    Submodule.localized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  let IM : Submodule R ↥M := Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)
  let fM : ↥M →ₗ[R] Mloc :=
    Submodule.toLocalized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  have hlocalized :
      Submodule.localized' S p.primeCompl fM IM =
        Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc) := by
    -- Localizing the principal submodule `x • ⊤` inside `M` gives the principal submodule
    -- generated by `algebraMap R S x` inside the localized submodule.
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top]
    simpa [Set.image_singleton] using
      congrArg (fun J : Ideal S => J • (⊤ : Submodule S ↥Mloc))
        (Ideal.map_span (f := algebraMap R S) ({x} : Set R))
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e :
      (↥Mloc ⧸ Submodule.localized' S p.primeCompl fM IM) ≃ₗ[S]
        LocalizedModule.AtPrime p (↥M ⧸ IM) :=
    (IsLocalizedModule.linearEquiv p.primeCompl
      (IM.toLocalizedQuotient' S p.primeCompl fM)
      (LocalizedModule.mkLinearMap p.primeCompl (↥M ⧸ IM))).restrictScalars S
  exact
    e.symm.trans
      (Submodule.quotEquivOfEq _ _ hlocalized)

omit [Ring.KrullDimLE 1 R] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
/-- Helper for Lemma 10.119.11: every prime localization of `M / xM` has finite length over the
localized ring once the ambient finite-dimensional fraction-field action is localized onto `V`. -/
private theorem isFiniteLength_quotSMulTop_atPrime
    (p : Ideal R) [p.IsPrime]
    [Algebra (Localization.AtPrime p) K] [Module (Localization.AtPrime p) V]
    [IsScalarTower R (Localization.AtPrime p) V]
    [IsScalarTower (Localization.AtPrime p) K V]
    [Ring.KrullDimLE 1 (Localization.AtPrime p)]
    [IsFractionRing (Localization.AtPrime p) K]
    [IsLocalizedModule p.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) {x : R}
    (hx : algebraMap R (Localization.AtPrime p) x ≠ 0) :
    IsFiniteLength (Localization.AtPrime p)
      (LocalizedModule.AtPrime p (QuotSMulTop x M)) := by
  let S := Localization.AtPrime p
  let Mloc : Submodule S V :=
    Submodule.localized' S p.primeCompl (LinearMap.id : V →ₗ[R] V) M
  have hlocal :
      IsFiniteLength S (QuotSMulTop (algebraMap R S x) Mloc) :=
    isFiniteLength_quotSMulTop_local_finiteDimensional (S := S) (L := K) (W := V) Mloc hx
  have hsmul :
      Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc) =
        algebraMap R S x • (⊤ : Submodule S ↥Mloc) := by
    simpa using
      (Submodule.ideal_span_singleton_smul (algebraMap R S x) (⊤ : Submodule S ↥Mloc))
  let eLocal :
      QuotSMulTop (algebraMap R S x) Mloc ≃ₗ[S]
        (↥Mloc ⧸ Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc)) :=
    Submodule.quotEquivOfEq _ _ hsmul.symm
  have hlocal' :
      IsFiniteLength S
        (↥Mloc ⧸ Ideal.span ({algebraMap R S x} : Set S) • (⊤ : Submodule S ↥Mloc)) :=
    eLocal.isFiniteLength hlocal
  let e :=
    localized_quotSMulTop_atPrime_equiv_localized_submodule_quotient
      (R := R) (K := K) (V := V) p M x
  have hsource :
      IsFiniteLength S
        (LocalizedModule.AtPrime p
          (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M))) :=
    e.symm.isFiniteLength hlocal'
  have hsmul_source :
      Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M) = x • (⊤ : Submodule R ↥M) := by
    simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R ↥M))
  let eSource₀ : QuotSMulTop x M ≃ₗ[R]
      (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) :=
    Submodule.quotEquivOfEq _ _ hsmul_source.symm
  let eSource :
      LocalizedModule.AtPrime p (QuotSMulTop x M) ≃ₗ[S]
        LocalizedModule.AtPrime p
          (↥M ⧸ Ideal.span ({x} : Set R) • (⊤ : Submodule R ↥M)) :=
    LinearEquiv.ofBijective
      (LocalizedModule.map p.primeCompl eSource₀.toLinearMap)
      ⟨LocalizedModule.map_injective p.primeCompl eSource₀.toLinearMap eSource₀.injective,
        LocalizedModule.map_surjective p.primeCompl eSource₀.toLinearMap eSource₀.surjective⟩
  exact eSource.symm.isFiniteLength hsource

/-- Helper for Lemma 10.119.11: the principal quotient ring `R / (x)` is Artinian for nonzero
`x`, matching the source proof's ambient quotient-ring owner. -/
private theorem isArtinianRing_quotient_span_singleton_of_nonzero
    {x : R} (hx : x ≠ 0) :
    IsArtinianRing (R ⧸ Ideal.span ({x} : Set R)) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  letI : CommRing A := inferInstance
  have hfinite_R : IsFiniteLength R A :=
    isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  have hlength_eq : Module.length R A = Module.length A A := by
    simpa using
      (Module.length_eq_of_surjective
        (S := R)
        (R := A)
        (M := A)
        (Ideal.Quotient.mk_surjective (I := Ideal.span ({x} : Set R))))
  have hfinite_A : IsFiniteLength A A := by
    rw [← Module.length_ne_top_iff]
    simpa [hlength_eq] using (Module.length_ne_top_iff.mpr hfinite_R)
  exact (isArtinianRing_iff_isFiniteLength (R := A)).2 hfinite_A

/-- Helper for Lemma 10.119.11: once `M / xM` is finite over the Artinian quotient ring `R / (x)`,
it has finite length over that quotient ring. -/
private theorem isFiniteLength_quotSMulTop_over_quotient_of_finite
    (M : Submodule R V) {x : R} (hx : x ≠ 0)
    [Module.Finite (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    IsFiniteLength (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  letI : CommRing A := inferInstance
  let hTors : Module.IsTorsionBySet R (QuotSMulTop x M) (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := hTors.module
  letI : IsScalarTower R (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) :=
    Module.IsTorsionBySet.isScalarTower hTors
  letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
  exact (isFiniteLength_iff_isNoetherian_isArtinian).mpr ⟨inferInstance, inferInstance⟩

omit [Ring.KrullDimLE 1 R] [Algebra R K] [IsFractionRing R K] [IsScalarTower R K V] in
/-- Helper for Lemma 10.119.11: every maximal localization of `M / xM` is finite over the
corresponding local ring because the localized quotient already has finite length. -/
private theorem moduleFinite_localized_quotSMulTop_atMaximal
    (m : Ideal R) [m.IsMaximal]
    [Algebra (Localization.AtPrime m) K] [Module (Localization.AtPrime m) V]
    [IsScalarTower R (Localization.AtPrime m) V]
    [IsScalarTower (Localization.AtPrime m) K V]
    [Ring.KrullDimLE 1 (Localization.AtPrime m)]
    [IsFractionRing (Localization.AtPrime m) K]
    [IsLocalizedModule m.primeCompl (LinearMap.id : V →ₗ[R] V)]
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.Finite (Localization.AtPrime m)
      (LocalizedModule.AtPrime m (QuotSMulTop x M)) := by
  -- The local finite-length statement already gives the localized quotient a Noetherian module
  -- structure, and finitely generatedness is exactly the top submodule being finitely generated.
  have hfiniteLength :
      IsFiniteLength (Localization.AtPrime m)
        (LocalizedModule.AtPrime m (QuotSMulTop x M)) := by
    have hx_map : algebraMap R (Localization.AtPrime m) x ≠ 0 := by
      intro hx_map
      exact hx <| FaithfulSMul.algebraMap_injective R (Localization.AtPrime m) <| by
        simpa using hx_map
    exact isFiniteLength_quotSMulTop_atPrime (R := R) (K := K) (V := V) m M hx_map
  have hnoetherian :
      IsNoetherian (Localization.AtPrime m)
        (LocalizedModule.AtPrime m (QuotSMulTop x M)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfiniteLength).1
  rw [Module.finite_def]
  exact hnoetherian.noetherian _

omit [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 10.119.11: an element of a quotient ring outside a prime ideal lifts to an
element of the source ring outside the pulled-back prime ideal. -/
private theorem exists_lift_in_comap_prime_compl
    {I : Ideal R} (P : Ideal (R ⧸ I)) [P.IsPrime]
    (a : R ⧸ I) (ha : a ∈ P.primeCompl) :
    ∃ r : R, Ideal.Quotient.mk I r = a ∧
      r ∈ (Ideal.comap (algebraMap R (R ⧸ I)) P).primeCompl := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
  refine ⟨r, rfl, ?_⟩
  change Ideal.Quotient.mk I r ∉ P
  simpa using ha

/-- Helper for Lemma 10.119.11: after pulling a maximal ideal of `R ⧸ (x)` back to `R`, the
standard localization at that maximal ideal controls the quotient localization over `R ⧸ (x)`. -/
private theorem moduleFinite_localized_quotSMulTop_over_principal_quotient_atMaximal
    (M : Submodule R V) {x : R} (hx : x ≠ 0)
    (P : Ideal (R ⧸ Ideal.span ({x} : Set R))) [P.IsMaximal] :
    Module.Finite (Localization.AtPrime P)
      (LocalizedModule.AtPrime P (QuotSMulTop x M)) := by
  sorry

/-- Helper for Lemma 10.119.11: once the localizations of `M / xM` at maximal ideals of
`R ⧸ (x)` are controlled, the source proof globalizes finite generation over the quotient ring
`R ⧸ (x)`. -/
private theorem moduleFinite_quotSMulTop_over_principal_quotient
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  let N := QuotSMulTop x M
  let hTors : Module.IsTorsionBySet R N (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module A N := hTors.module
  letI : IsScalarTower R A N := Module.IsTorsionBySet.isScalarTower hTors
  letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
  letI : Finite (MaximalSpectrum A) := inferInstance
  -- The source proof globalizes from maximal localizations over the Artinian quotient ring.
  apply Module.Finite.of_localized_maximal (R := A) (M := N)
  intro P _hP
  simpa using
    moduleFinite_localized_quotSMulTop_over_principal_quotient_atMaximal
      M hx P

/-
Domain triage:
* primary domain: module length for principal quotients of `R`-submodules inside a finite-
  dimensional fraction-field vector space;
* sampled owner API: `QuotSMulTop`, `QuotSMulTop.congr`, `IsFiniteLength`,
  `Module.length_ne_top_iff`, and the finite-dimensional transport API
  `LinearEquiv.ofFinrankEq`;
* source/core/bridge split: Lemma `10.119.11` is `source-facing`, the quotient owner is
  `QuotSMulTop x M`, the finiteness owner is `IsFiniteLength R`, and the ambient owner abstraction
  is an `R`-submodule of a finite-dimensional `K`-vector space `V`;
* primitive data vs. derived API: the primitive inputs are the submodule `M`, the nonzero element
  `x`, and the ambient finite-dimensional `K`-space; any coordinate presentation
  `V ≃ₗ[K] Fin (finrank K V) → K` is derived from a basis and should not remain the public owner.
-/

-- Proof sketch: the support of `R / xR` is the finite set of maximal ideals containing `x`, since
-- a one-dimensional Noetherian domain has only maximal primes above a nonzero principal ideal.
-- Localize `M / xM` at those maximal ideals and, after choosing a `K`-basis of `V`, transport the
-- localized problem via `QuotSMulTop.congr` to the coordinate model `K^{\oplus r}` where the local
-- one-dimensional statement from Lemma `10.119.9` applies. Transporting back, the quotient has a
-- finite filtration with residue-field subquotients, so its `R`-length is finite.
/-- Lemma 10.119.11: if `R` is a Noetherian domain of Krull dimension at most `1`, `M` is an
`R`-submodule of a finite-dimensional `K`-vector space `V`, and `x ∈ R` is nonzero, then the
quotient `M / xM`, written canonically as `QuotSMulTop x M`, has finite length over `R`. -/
theorem isFiniteLength_quotSMulTop_submodule_of_nonzero
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := by
  let A : Type u := R ⧸ Ideal.span ({x} : Set R)
  let N := QuotSMulTop x M
  let hTors : Module.IsTorsionBySet R N (Ideal.span ({x} : Set R)) :=
    quotSMulTop_isTorsionBySet_span_singleton (R := R) (V := V) M x
  letI : Module A N := hTors.module
  letI : IsScalarTower R A N := Module.IsTorsionBySet.isScalarTower hTors
  letI : Module.Finite A N :=
    moduleFinite_quotSMulTop_over_principal_quotient M hx
  have hfiniteA : IsFiniteLength A N := by
    letI : IsArtinianRing A := isArtinianRing_quotient_span_singleton_of_nonzero (R := R) hx
    exact (isFiniteLength_iff_isNoetherian_isArtinian).mpr ⟨inferInstance, inferInstance⟩
  have hlength_eq : Module.length R N = Module.length A N := by
    simpa using
      (Module.length_eq_of_surjective
        (S := R)
        (R := A)
        (M := N)
        (Ideal.Quotient.mk_surjective (I := Ideal.span ({x} : Set R))))
  -- Transfer the finite-length statement back across the surjective quotient map `R → R / (x)`.
  exact Module.length_ne_top_iff.mp <| by
    intro htop
    rw [hlength_eq] at htop
    exact (Module.length_ne_top_iff.mpr hfiniteA) htop

/-- Source-facing numerical form of Lemma 10.119.11. -/
theorem length_submodule_quotient_by_nonzero_lt_top
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x M) < ⊤ := by
  exact lt_top_iff_ne_top.mpr <|
    Module.length_ne_top_iff.mpr <|
      isFiniteLength_quotSMulTop_submodule_of_nonzero M hx

end

/-! ### Lemma_10_119_12_Krull_Akizuki (from Chap10) -/
universe u v

open scoped Pointwise

section

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
variable [Algebra R L] [IsScalarTower R (FractionRing R) L]

/-
Domain triage:
* primary domain: intermediate `R`-subalgebras of a finite extension of `FractionRing R` over a
  one-dimensional Noetherian domain;
* sampled owner declarations in this domain:
  - `Ring.KrullDimLE 1 R`, the core dimension-at-most-one owner already used in nearby files;
  - `IsNoetherianRing.of_finite`, the canonical owner for deriving Noetherianity from
    module-finiteness when that stronger input is available;
  - `Subalgebra.isNoetherianRing_of_fg`, the owner-side API showing that Noetherianity of a
    subalgebra is derived data of the subalgebra object rather than separate packaged structure;
  - `FiniteDimensional.finiteDimensional_subalgebra`, the ambient finite-dimensional owner for
    subalgebras inside a finite-dimensional algebra.
* source/core/bridge split:
  - `source-facing`: the textbook Krull-Akizuki statement with explicit hypothesis
    `ringKrullDim R = 1`;
  - `core/canonical`: the intermediate owner `A : Subalgebra R L` together with the ambient owner
    hypothesis `[Ring.KrullDimLE 1 R]`;
  - `bridge/view`: the conversion from the explicit equality `ringKrullDim R = 1` to the
    canonical typeclass owner.
* primitive vs. derived:
  - primitive data are the ambient field-extension tower and the chosen intermediate subalgebra
    `A`;
  - `IsNoetherianRing A` is derived API and should live as owner-side output on `A`, not as a
    separate wrapper notion.
-/

namespace Subalgebra

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): a nonzero ideal of an intermediate
`R`-subalgebra contains a nonzero element coming from the base ring. -/
lemma exists_nonzero_base_mem_ideal [Ring.KrullDimLE 1 R]
    (A : Subalgebra R L) (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ x : R, x ≠ 0 ∧ algebraMap R A x ∈ I := by
  -- Contract the chosen nonzero ideal along `R → A` using algebraicity of the ambient field
  -- extension, then read a nonzero element from the contraction.
  have hAlgL : Algebra.IsAlgebraic R L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic (FractionRing R) L)
  have hAlgA' : A.IsAlgebraic := by
    intro y _hy
    exact Algebra.IsAlgebraic.isAlgebraic (R := R) (A := L) y
  have hAlgA : Algebra.IsAlgebraic R A :=
    (Subalgebra.isAlgebraic_iff (R := R) (A := L) A).mp hAlgA'
  have hcomap : I.comap (algebraMap R A) ≠ ⊥ := by
    -- A nonzero element of `I` is algebraic over `R`, so its contraction cannot vanish.
    obtain ⟨y, hyI, hy0⟩ := (Submodule.ne_bot_iff _).mp hI
    exact Ideal.comap_ne_bot_of_algebraic_mem hy0 hyI
      (hAlgA.isAlgebraic y)
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).mp hcomap
  exact ⟨x, hx0, hxI⟩

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): the `R`-submodule `xA` is the restriction of
scalars of the principal ideal generated by `x` inside the intermediate subalgebra. -/
lemma smul_top_eq_principal_ideal_restrictScalars
    (A : Subalgebra R L) (x : R) :
    x • (⊤ : Submodule R A) =
      ((Ideal.span ({algebraMap R A x} : Set A) : Ideal A) : Submodule A A).restrictScalars R := by
  -- Rewrite `xA` through the mapped principal ideal and then identify that ideal inside `A`.
  calc
    x • (⊤ : Submodule R A)
        = (Ideal.span ({x} : Set R) : Ideal R) • (⊤ : Submodule R A) := by
            simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R A)).symm
    _ = ((Ideal.span ({x} : Set R)).map (algebraMap R A)).restrictScalars R := by
          simpa using
            (Ideal.smul_top_eq_map (R := R) (S := A) (Ideal.span ({x} : Set R)))
    _ = ((Ideal.span ({algebraMap R A x} : Set A) : Ideal A) : Submodule A A).restrictScalars R := by
          congr 1
          simpa [Set.image_singleton] using
            (Ideal.map_span (f := algebraMap R A) ({x} : Set R))

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): quotienting the intermediate subalgebra by the
base scalar `x` agrees with quotienting by the principal ideal generated by `x` inside the
subalgebra. -/
def quotSMulTop_to_principal_quotient_equiv
    (A : Subalgebra R L) (x : R) :
    QuotSMulTop x A.toSubmodule ≃ₗ[R]
      (A ⧸ (Ideal.span ({algebraMap R A x} : Set A) : Submodule A A)) :=
  (QuotSMulTop.congr x (Subalgebra.toSubmoduleEquiv A)) ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (smul_top_eq_principal_ideal_restrictScalars (R := R) (L := L) A x))
      ≪≫ₗ
        (Submodule.Quotient.restrictScalarsEquiv R
          (Ideal.span ({algebraMap R A x} : Set A) : Submodule A A))

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): the quotient `A / (x)` coming from a nonzero
base scalar has finite length over `R`. -/
lemma isFiniteLength_quotient_span_base_scalar [Ring.KrullDimLE 1 R]
    (A : Subalgebra R L) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (A ⧸ Ideal.span ({algebraMap R A x} : Set A)) := by
  -- First apply Lemma `10.119.11` to the ambient `R`-submodule underlying `A`.
  have hquot :
      IsFiniteLength R (QuotSMulTop x A.toSubmodule) :=
    isFiniteLength_quotSMulTop_submodule_of_nonzero
      (R := R) (V := L) (M := A.toSubmodule) hx
  -- Then transport that finite-length statement to the principal ideal quotient of `A`.
  exact
    (quotSMulTop_to_principal_quotient_equiv (R := R) (L := L) A x).isFiniteLength hquot

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): inside a nonzero ideal `I`, the principal ideal
generated by a chosen element is represented by the corresponding singleton span. -/
lemma principal_comap_subtype_eq_span_singleton {A : Type*} [CommRing A]
    (I : Ideal A) {a : A} (ha : a ∈ I) :
    Submodule.comap I.subtype (Ideal.span ({a} : Set A) : Submodule A A) =
      Submodule.span A ({⟨a, ha⟩} : Set I) := by
  -- Both sides describe the same principal submodule of `I`.
  ext y
  constructor
  · intro hy
    change ((y : A) ∈ Ideal.span ({a} : Set A)) at hy
    rw [Submodule.mem_span_singleton]
    rw [Ideal.mem_span_singleton'] at hy
    rcases hy with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    simpa [smul_eq_mul] using hb
  · intro hy
    rw [Submodule.mem_span_singleton] at hy
    change ((y : A) ∈ Ideal.span ({a} : Set A))
    rw [Ideal.mem_span_singleton']
    rcases hy with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simpa [smul_eq_mul] using congrArg Subtype.val hb

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): the quotient of an ideal by a contained principal
subideal injects into the ambient principal quotient. -/
lemma ideal_quotient_to_ambient_quotient_injective {A : Type*} [CommRing A]
    (I J : Ideal A) (_hJI : J ≤ I) :
    Function.Injective
      (Submodule.mapQ
        (Submodule.comap I.subtype (J : Submodule A A))
        (J : Submodule A A)
        I.subtype
        (le_rfl : Submodule.comap I.subtype (J : Submodule A A) ≤
          Submodule.comap I.subtype (J : Submodule A A))) := by
  -- The induced quotient map has zero kernel because its defining submodule is exactly the
  -- pulled-back ambient ideal.
  intro z w hzw
  have hker :
      LinearMap.ker
          (Submodule.mapQ
            (Submodule.comap I.subtype (J : Submodule A A))
            (J : Submodule A A)
            I.subtype
            (le_rfl : Submodule.comap I.subtype (J : Submodule A A) ≤
              Submodule.comap I.subtype (J : Submodule A A))) =
        ⊥ := by
    rw [Submodule.ker_mapQ]
    simpa using
      (Submodule.mkQ_map_self (Submodule.comap I.subtype (J : Submodule A A)))
  exact LinearMap.ker_eq_bot.mp hker hzw

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): if the quotient of an ideal by the principal
subideal generated by a base scalar is finite over the base ring, then the ideal is finitely
generated over the ambient ring. -/
lemma fg_of_finite_quotient_by_base_scalar {S : Type*} [CommRing S] [Algebra R S]
    (I : Ideal S) {x : R} (hxI : algebraMap R S x ∈ I)
    [Module.Finite R
      (I ⧸ Submodule.comap I.subtype
        (Ideal.span ({algebraMap R S x} : Set S) : Submodule S S))] :
    I.FG := by
  let QI : Submodule S I :=
    Submodule.comap I.subtype
      (Ideal.span ({algebraMap R S x} : Set S) : Submodule S S)
  let N : Submodule S I :=
    Submodule.span S ({⟨algebraMap R S x, hxI⟩} : Set I)
  -- Route correction: replace the explicit quotient-lift reconstruction by the canonical
  -- submodule-plus-quotient finiteness argument inside `I`.
  have hQN : QI = N := by
    -- Normalize the pulled-back principal ideal to the singleton span generated inside `I`.
    simpa [QI, N] using
      (principal_comap_subtype_eq_span_singleton I (a := algebraMap R S x) hxI)
  haveI : Module.Finite R (I ⧸ N) := by
    -- Transport the given `R`-finite quotient across the canonical kernel identification.
    exact
      Module.Finite.equiv (R := R)
        ((Submodule.quotEquivOfEq QI N hQN).restrictScalars R)
  haveI : Module.Finite S (I ⧸ N) :=
    Module.Finite.of_restrictScalars_finite R S (I ⧸ N)
  haveI : Module.Finite S N := by
    -- The kernel is principal inside `I`, hence finite over `S`.
    exact Module.Finite.of_fg (Submodule.fg_span (Set.finite_singleton _))
  haveI : Module.Finite S I :=
    Module.Finite.of_submodule_quotient N
  -- Convert the finite `S`-module structure on the ideal back to finite generation.
  exact Module.Finite.iff_fg.mp inferInstance

/-- Helper for Lemma 10.119.12 (Krull-Akizuki): every nonzero ideal of an intermediate
subalgebra is finitely generated. -/
lemma ideal_fg_of_nonzero [Ring.KrullDimLE 1 R]
    (A : Subalgebra R L) (I : Ideal A) (hI : I ≠ ⊥) :
    I.FG := by
  obtain ⟨x, hx, hxI⟩ := exists_nonzero_base_mem_ideal (R := R) (L := L) A I hI
  let J : Ideal A := Ideal.span ({algebraMap R A x} : Set A)
  have hJI : J ≤ I := by
    -- The chosen base element already lies in `I`, so the principal ideal it generates does too.
    refine Ideal.span_le.2 ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxI
  have hambient :
      IsFiniteLength R (A ⧸ (J : Submodule A A)) := by
    simpa [J] using
      isFiniteLength_quotient_span_base_scalar (R := R) (L := L) A hx
  let QI : Submodule A I := Submodule.comap I.subtype (J : Submodule A A)
  let qmap : I ⧸ QI →ₗ[R] A ⧸ (J : Submodule A A) :=
    Submodule.mapQ QI (J : Submodule A A) I.subtype
      (le_rfl : QI ≤ Submodule.comap I.subtype (J : Submodule A A))
  have hqmap_injective : Function.Injective qmap := by
    -- This is the textbook injection `I / xA ↪ A / xA`.
    simpa [QI, qmap] using ideal_quotient_to_ambient_quotient_injective I J hJI
  have hquot : IsFiniteLength R (I ⧸ QI) :=
    IsFiniteLength.of_injective hambient hqmap_injective
  have hquot_noetherian_R : IsNoetherian R (I ⧸ QI) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hquot).1
  haveI : Module.Finite R (I ⧸ QI) := by
    -- Finite length gives a Noetherian `R`-module structure on the quotient.
    rw [Module.finite_def]
    exact hquot_noetherian_R.noetherian _
  -- Route correction: reduce the closing step to the pure finite-quotient reconstruction helper.
  simpa [QI, J] using
    fg_of_finite_quotient_by_base_scalar (R := R) (S := A) I hxI

-- Proof sketch: let `I` be a nonzero ideal of an intermediate `R`-subalgebra `A ⊆ L`. Since
-- `L` is algebraic over the fraction field of `R`, Lemma `10.30.8` gives a nonzero element
-- `x ∈ I ∩ R`. Realize `A` as an `R`-submodule of a finite-dimensional `FractionRing R`-vector
-- space and apply Lemma `10.119.11` to deduce that `A / xA`, hence also `I / xA`, has finite
-- length over `R`. A finite-length quotient yields finite generation of `I`, so every ideal of
-- `A` is finitely generated and `A` is Noetherian.
/-- Under the canonical dimension-at-most-one owner hypothesis, every intermediate `R`-subalgebra
of a finite extension of `FractionRing R` is Noetherian. -/
instance isNoetherianRing_of_krullDimLEOne_of_finiteDimensional [Ring.KrullDimLE 1 R]
    (A : Subalgebra R L) :
    IsNoetherianRing A := by
  -- Apply the ideal criterion, splitting off the zero ideal from the source proof's nonzero case.
  refine (isNoetherianRing_iff_ideal_fg A).2 fun I ↦ ?_
  by_cases hI : I = ⊥
  · simpa [hI] using (show (⊥ : Ideal A).FG from Submodule.fg_bot)
  · exact ideal_fg_of_nonzero (R := R) (L := L) A I hI

/-- Lemma 10.119.12 (Krull-Akizuki): if `R` is a Noetherian domain of Krull dimension `1` and
`L` is a finite extension of the fraction field of `R`, then every intermediate `R`-subalgebra
of `L` is a Noetherian ring. This source-facing form is a bridge to the canonical owner-side
instance above. -/
theorem isNoetherianRing_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {L : Type v} [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L]
    (A : Subalgebra R L) (hdim : ringKrullDim R = 1) :
    IsNoetherianRing A := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  exact isNoetherianRing_of_krullDimLEOne_of_finiteDimensional A

end Subalgebra

end

/-! ### Lemma_10_119_13 (from Chap10) -/
universe u v w

section

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
variable [Algebra.EssFiniteType K L]

/-
Domain triage:
* primary domain: valuation subrings of finitely generated field extensions dominating the image of
  a fixed Noetherian local domain;
* sampled owner declarations:
  - `LocalSubring.exists_le_valuationSubring` and `ValuationSubring.toLocalSubring` for the
    domination relation on local subrings of a field;
  - `ValuationSubring.comap` for contraction along `K → L`;
  - `exists_one_dimensional_dominating_essFiniteType_overring_of_not_isField` and
    `discreteValuationRing_iff_regularLocalRing_dim_one` for the chapter's one-dimensional and
    discrete-valuation owners.
* best owner abstraction:
  - `source-facing`: existence of a discrete valuation subring of `L` dominating the image of `R`;
  - `core/canonical`: domination as the order on `LocalSubring L`, together with the owner
    predicate `IsDiscreteValuationRing`.
* primitive vs. derived:
  - primitive data: the witness `V : ValuationSubring L` and the domination inequality
    `LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring`;
  - derived API: the local structure on `V.toLocalSubring`, the intermediate one-dimensional
    overring supplied by Lemma `10.119.1`, and the regular-local reformulation of the DVR
    condition from Lemma `10.119.7`.
-/

-- Proof sketch: if `L / K` is not finite, choose a finite transcendence basis and replace `R` by
-- the localization of the polynomial extension obtained by adjoining those generators, reducing to
-- the finite extension case. Then use Lemma `10.119.1` to replace `R` by a one-dimensional
-- dominating overring, take the integral closure in `L`, apply Krull-Akizuki to get Noetherianity,
-- choose a prime over the maximal ideal by lying over, and finally apply Lemma `10.119.7` to the
-- resulting localization.
/-- Lemma 10.119.13: if `R` is a Noetherian local domain with fraction field `K`, `R` is not a
field, and `L / K` is a finitely generated field extension, then there exists a discrete valuation
subring of `L` whose associated local subring dominates the image of `R` in `L`. -/
theorem exists_discreteValuationSubring_dominating_of_not_isField_of_essFiniteType
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := sorry

end
