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

/-- Helper for Lemma 10.149.3: the kernel of the quotient map `R ⧸ I² → R ⧸ I` is the canonical
copy of `I / I²` inside `R ⧸ I²`. -/
lemma quotientIdealSquareFactor_ker_eq_cotangentIdeal :
    RingHom.ker
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
          (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom =
      I.cotangentIdeal := by
  -- Compute the kernel as the image ideal of `I` in the quotient by `I²`.
  have h :
      RingHom.ker
          (Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
            (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom =
        I.map (Ideal.Quotient.mk (I ^ 2)) := by
    simpa [Ideal.Quotient.factorₐ, Ideal.Quotient.factor, Ideal.mk_ker] using
      (Ideal.ker_quotient_lift
        (Ideal.Quotient.mk I)
        (fun x hx ↦ eq_zero_iff_mem.mpr (Ideal.pow_le_self two_ne_zero hx)))
  -- The quotient-side image ideal is exactly `I.cotangentIdeal`.
  rw [Ideal.map_eq_submodule_map] at h
  exact h

/-- Helper for Lemma 10.149.3: the structure map of the quotient extension is the canonical
quotient map `R ⧸ I² → R ⧸ I`. -/
lemma quotSqExt_toAlgHom_eq_factor :
    IsScalarTower.toAlgHom R (quotSqExt : Extension R (R ⧸ I)).Ring (R ⧸ I) = quotSqMap :=
  rfl

/-- Helper for Lemma 10.149.3: a map `R/I → A/J` into a square-zero quotient kills `I²` after
lifting representatives along `R → A`. -/
lemma algebraMap_zero_of_mem_square_of_square_zero_quotient
    {A : Type*} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (f : R ⧸ I →ₐ[R] A ⧸ J)
    {x : R} (hx : x ∈ I ^ 2) :
    algebraMap R A x = 0 := by
  -- First show that elements of `I` land inside `J`.
  have hIle : I ≤ J.comap (algebraMap R A) := by
    intro y hy
    change algebraMap R A y ∈ J
    have hy0 : (Ideal.Quotient.mk I y : R ⧸ I) = 0 := eq_zero_iff_mem.mpr hy
    have hleft : f (Ideal.Quotient.mk I y) = 0 := by
      simpa [hy0] using congrArg f hy0
    have hcomm := f.commutes y
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.alg_map_eq] at hcomm
    rw [hcomm] at hleft
    exact eq_zero_iff_mem.mp (by simpa [RingHom.comp_apply] using hleft)
  -- Then square-zero of `J` forces every element of `I²` to map to zero.
  have hcomap_sq :
      (J.comap (algebraMap R A)) ^ 2 ≤ RingHom.ker (algebraMap R A) := by
    intro z hz
    have hz' : z ∈ (J ^ 2).comap (algebraMap R A) :=
      (Ideal.le_comap_pow (f := algebraMap R A) (K := J) 2) hz
    have : algebraMap R A z ∈ (⊥ : Ideal A) := by
      simpa [hJ] using hz'
    simpa [RingHom.mem_ker] using this
  have hsq :
      I ^ 2 ≤ RingHom.ker (algebraMap R A) := by
    exact (Ideal.pow_right_mono hIle 2).trans hcomap_sq
  simpa [RingHom.mem_ker] using hsq hx

/-- Helper for Lemma 10.149.3: the descended map `R/I² → A` reduces modulo `J` to the original
map `R/I → A/J`. -/
lemma quotientIdealSquare_lift_comp_eq
    {A : Type*} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (f : R ⧸ I →ₐ[R] A ⧸ J) :
    let lift : R ⧸ I ^ 2 →ₐ[R] A :=
      Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
        (fun _ hx ↦
          algebraMap_zero_of_mem_square_of_square_zero_quotient
            (R := R) (I := I) J hJ f hx)
    (Ideal.Quotient.mkₐ R J).comp lift = f.comp quotSqMap := by
  intro lift
  -- Compare both maps after precomposing with the quotient map from `R`.
  refine Ideal.Quotient.algHom_ext (R₁ := R) <|
    AlgHom.ext fun x ↦ (f.commutes x).symm

-- Proof sketch: identify the canonical quotient extension `R ⧸ I² → R ⧸ I` with the
-- infinitesimal extension attached to `R → R ⧸ I`, then apply the universal square-zero lifting
-- property of that infinitesimal extension.
/-- Lemma 10.149.3 (1): the universal first-order thickening of `R ⧸ I` over `R` is the canonical
quotient extension `R ⧸ I² → R ⧸ I`. -/
theorem quotientIdealFirstOrderThickening_isUniversal :
    (quotSqExt : Extension R (R ⧸ I)).IsUniversalFirstOrderThickening :=
  by
    refine ⟨?_, ?_⟩
    · -- The kernel is `I/I²`, so its square vanishes by the cotangent-ideal calculation.
      have hker : (quotSqExt : Extension R (R ⧸ I)).ker = I.cotangentIdeal := by
        change RingHom.ker
            ((Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
                (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom) = I.cotangentIdeal
        exact quotientIdealSquareFactor_ker_eq_cotangentIdeal (R := R) (I := I)
      rw [hker]
      exact Ideal.cotangentIdeal_square I
    · intro A _ _ J hJ f
      rw [quotSqExt_toAlgHom_eq_factor (R := R) (I := I)]
      let lift : R ⧸ I ^ 2 →ₐ[R] A :=
        Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
          (fun _ hx ↦
            algebraMap_zero_of_mem_square_of_square_zero_quotient
              (R := R) (I := I) (A := A) J hJ f hx)
      refine ⟨lift, ?_, ?_⟩
      · -- The descended algebra map is the lift required by the universal square.
        exact quotientIdealSquare_lift_comp_eq (R := R) (I := I) J hJ f
      · intro g hg
        -- Any `R`-algebra map out of `R/I²` is determined by its values on representatives from `R`.
        refine Ideal.Quotient.algHom_ext (R₁ := R) <| by
          calc
            g.comp (Ideal.Quotient.mkₐ R (I ^ 2)) = Algebra.ofId R A := by
              exact AlgHom.ext fun x ↦ g.commutes x
            _ = lift.comp (Ideal.Quotient.mkₐ R (I ^ 2)) := by
              symm
              exact Ideal.Quotient.liftₐ_comp (I ^ 2) (Algebra.ofId R A)
                (fun _ hx ↦
                  algebraMap_zero_of_mem_square_of_square_zero_quotient
                    (R := R) (I := I) (A := A) J hJ f hx)

-- Proof sketch: the conormal module of a universal first-order thickening is its cotangent module,
-- and for the quotient extension `R ⧸ I² → R ⧸ I` the kernel ideal is `I.cotangentIdeal`, whose
-- square is zero and whose underlying `R`-module is canonically `I/I²`.
/-- Lemma 10.149.3 (2): the conormal module of `R ⧸ I` over `R`, computed from the canonical
quotient thickening `R ⧸ I² → R ⧸ I`, is canonically isomorphic to `I / I²`. -/
noncomputable def quotientIdeal_conormalModuleEquiv :
    (quotSqExt : Extension R (R ⧸ I)).Cotangent ≃ₗ[R ⧸ I] I.Cotangent := by
  let P : Extension R (R ⧸ I) := quotSqExt
  let hP : P.IsUniversalFirstOrderThickening := quotientIdealFirstOrderThickening_isUniversal I
  -- Reuse the quotient-kernel identification from the universal-thickening proof.
  have hker : P.ker = I.cotangentIdeal := by
    change RingHom.ker
        ((Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero) :
            (R ⧸ I ^ 2) →ₐ[R] R ⧸ I).toRingHom) = I.cotangentIdeal
    exact quotientIdealSquareFactor_ker_eq_cotangentIdeal (R := R) (I := I)
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
