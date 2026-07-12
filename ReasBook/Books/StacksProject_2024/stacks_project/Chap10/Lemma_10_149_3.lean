import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2

open Algebra
open Algebra.Extension
open Ideal.Quotient (eq_zero_iff_mem)

universe u

noncomputable section

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/- Domain-style sampling:
* primary domain: square-zero quotient thickenings of commutative rings and their conormal modules;
* sampled owner declarations:
  - `Ideal.Quotient.factorₐ`, the canonical quotient map `R ⧸ I² →ₐ[R] R ⧸ I`;
  - `Extension.ofSurjective`, the owner abstraction packaging a surjective algebra map as an
    extension;
  - `Extension.conormalModuleEquivCotangent`, the Chapter 10 bridge from a square-zero kernel ideal
    with its induced `R ⧸ I`-module structure to the owner cotangent module of a universal
    first-order thickening;
  - `Ideal.cotangentEquivIdeal`, the canonical bridge from `I / I²` to the square-zero kernel
    ideal inside `R ⧸ I²`.
* best owner abstraction: the source-facing quotient thickening should be expressed through the
  owner-level quotient map `Ideal.Quotient.factorₐ` and the extension it induces via
  `Extension.ofSurjective`; the conormal module statement should use the canonical linear
  equivalence to `I.Cotangent`, not a noncanonical type equality.
* primitive data vs. derived API:
  - primitive data: the ideal `I` and the canonical quotient map `R ⧸ I² →ₐ[R] R ⧸ I`;
  - derived API: the induced extension and the canonical equivalence from its conormal module to
    `I / I²`.
* layer triage:
  - `source-facing`: the quotient thickening `R ⧸ I² → R ⧸ I` and its conormal module;
  - `core/canonical`: `Ideal.Quotient.factorₐ`, `Extension.ofSurjective`, and `I.Cotangent`;
  - `bridge/view`: the identification of the kernel ideal of `R ⧸ I² → R ⧸ I` with
    `I.cotangentIdeal`. -/

-- Proof sketch: every class in `R ⧸ I` is represented by some `r : R`, and the class of the same
-- `r` in `R ⧸ I²` maps to it.
private theorem quotientIdealSquareFactor_surjective :
    Function.Surjective
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
        (R ⧸ I ^ 2) →ₐ[R] R ⧸ I) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

local notation "quotSqMap" =>
  (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
    (R ⧸ I ^ 2) →ₐ[R] R ⧸ I)

local notation "quotSqExt" =>
  Extension.ofSurjective quotSqMap (quotientIdealSquareFactor_surjective I)

-- Proof sketch: identify the canonical quotient extension `R ⧸ I² → R ⧸ I` with the
-- infinitesimal extension attached to `R → R ⧸ I`, then apply the universal square-zero lifting
-- property of that infinitesimal extension.
/-- Lemma 10.149.3 (1): the universal first-order thickening of `R ⧸ I` over `R` is the canonical
quotient extension `R ⧸ I² → R ⧸ I`. -/
theorem quotientIdealFirstOrderThickening_isUniversal :
    (quotSqExt : Extension R (R ⧸ I)).IsUniversalFirstOrderThickening :=
  sorry

-- Proof sketch: the conormal module of a universal first-order thickening is its cotangent module,
-- and for the quotient extension `R ⧸ I² → R ⧸ I` the kernel ideal is `I.cotangentIdeal`, whose
-- square is zero and whose underlying `R`-module is canonically `I/I²`.
/-- Lemma 10.149.3 (2): the conormal module of `R ⧸ I` over `R`, computed from the canonical
quotient thickening `R ⧸ I² → R ⧸ I`, is canonically isomorphic to `I / I²`. -/
noncomputable def quotientIdeal_conormalModuleEquiv :
    (quotSqExt : Extension R (R ⧸ I)).Cotangent ≃ₗ[R ⧸ I] I.Cotangent := by
  let P : Extension R (R ⧸ I) := quotSqExt
  let hP : P.IsUniversalFirstOrderThickening := quotientIdealFirstOrderThickening_isUniversal I
  have hker : P.ker = I.cotangentIdeal := by
    change RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero)).toRingHom =
      Submodule.map (Ideal.Quotient.mk (I ^ 2)).toSemilinearMap I
    have h :
        RingHom.ker (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero)).toRingHom =
          I.map (Ideal.Quotient.mk (I ^ 2)) := by
      simpa [Ideal.Quotient.factorₐ, Ideal.Quotient.factor, Ideal.mk_ker] using
        (Ideal.ker_quotient_lift
          (Ideal.Quotient.mk I)
          (fun x hx ↦ eq_zero_iff_mem.mpr (Ideal.pow_le_self two_ne_zero hx)))
    rw [Ideal.map_eq_submodule_map] at h
    exact h
  let eEq : I.cotangentIdeal ≃ₗ[R] ConormalModule P hP.square_zero :=
    ((LinearEquiv.ofEq I.cotangentIdeal P.ker hker.symm).restrictScalars R).trans <|
      kerEquivConormalModuleOfSquareZeroRestrictScalars P hP.square_zero
  let eR : I.Cotangent ≃ₗ[R] P.Cotangent :=
    (Ideal.cotangentEquivIdeal I).trans <|
      eEq.trans <|
        conormalModuleEquivCotangentRestrictScalars.{u, u, u, u} P hP
  have hquot : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa [Ideal.Quotient.algebraMap_eq] using (Ideal.Quotient.mk_surjective : _)
  let _ : IsScalarTower R (R ⧸ I) I.Cotangent :=
    Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)
  exact (eR.extendScalarsOfSurjective hquot).symm

end
