import Mathlib
import stacks_project.Chap10.Definition_10_149_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Algebra
open Algebra.Extension
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x

namespace Algebra.Extension

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.149.4:
- primary domain: localization behavior of universal first-order thickenings and their conormal
  modules in the `Algebra.Extension` API;
- sampled owner declarations:
  `Extension.localization`,
  `Extension.toLocalization`,
  `Extension.Hom`,
  `Extension.Cotangent`,
  `Extension.Cotangent.map`;
- best owner abstraction: the ambient owner remains `Extension`; this file is a
  `source-facing` localization statement phrased on the canonical owner
  `Extension.localization`, and the canonical comparison map is the owner-level bridge
  `Extension.toLocalization`;
- primitive data vs. derived API:
  the primitive data are the extension `P` and the localization choices of the source or target
  algebra, while the comparison morphism `Extension.toLocalization` and the induced conormal-module
  maps are derived from the owner APIs `Extension.Hom` and `Extension.Cotangent.map`;
- source/core/bridge triage:
  `source-facing`: the two localization clauses of Lemma 10.149.4,
  `core/canonical`: `Extension.localization` and `Extension.Cotangent`,
  `bridge/view`: the canonical owner-level localization map `Extension.toLocalization`. -/

/-- The canonical hom from an extension to any localization of its target algebra. -/
noncomputable def toLocalization (P : Extension R S) (T : Submonoid S)
    {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [IsLocalization T S'] :
    P.Hom (P.localization T : Extension R S') where
  toRingHom := algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom x := congrArg (fun f : P.Ring →+* S' ↦ f x) (IsLocalization.map_comp le_rfl)

section

variable (P : Extension R S)

variable (M : Submonoid R)
variable {Sₘ : Type w} [CommRing Sₘ] [Algebra R Sₘ] [Algebra S Sₘ] [IsScalarTower R S Sₘ]
  [IsLocalization (M.map (algebraMap R S)) Sₘ]

variable (T : Submonoid S)
variable {Sₜ : Type x} [CommRing Sₜ] [Algebra R Sₜ] [Algebra S Sₜ] [IsScalarTower R S Sₜ]
  [IsLocalization T Sₜ]

local notation "Pₘ" => ((P.localization (M.map (algebraMap R S)) : Extension R Sₘ))
local notation "Pₜ" => ((P.localization T : Extension R Sₜ))
local notation "PₜR" => Localization (T.comap (algebraMap P.Ring S))

/-- Helper for Lemma 10.149.4: the localization tensor product carries the obvious left
`PₜR`-algebra structure. -/
local instance localizedTargetTensorLeftAlgebra : Algebra PₜR (PₜR ⊗[P.Ring] P.Ring) :=
  Algebra.TensorProduct.leftAlgebra

/-- Helper for Lemma 10.149.4: the localized target ring acts on the chosen target localization. -/
local instance localizedTargetRingToTargetAlgebra : Algebra PₜR Sₜ := by
  change Algebra ((P.localization T : Extension R Sₜ)).Ring Sₜ
  infer_instance

/-- Helper for Lemma 10.149.4: the localized target ring remains an `R`-algebra tower over the
chosen target localization. -/
local instance localizedTargetRingTower : IsScalarTower R PₜR Sₜ := by
  change IsScalarTower R ((P.localization T : Extension R Sₜ)).Ring Sₜ
  infer_instance

/-- Helper for Lemma 10.149.4: after localizing the source ring of `P` at the preimage of `T`,
mapping back to `S` recovers exactly the target multiplicative set `T`. -/
lemma map_comap_algebraMap_eq :
    Submonoid.map (algebraMap P.Ring S) (T.comap (algebraMap P.Ring S)) = T := by
  -- Surjectivity of `P.Ring → S` lets us represent every target denominator upstairs.
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hs
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective s
    exact ⟨x, hs, rfl⟩

/-- Helper for Lemma 10.149.4: localizing the extension identifies the new kernel with the
localized old kernel. -/
lemma ker_localization_eq_map :
    (Pₜ).ker =
      P.ker.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) := by
  -- This is the kernel-localization theorem for the defining map `P.Ring → S`.
  simpa [Extension.localization, Extension.ker, RingHom.algebraMap_toAlgebra] using
    (IsLocalization.ker_map (R := P.Ring)
      (S := Localization (T.comap (algebraMap P.Ring S)))
      (P := S) (Q := Sₜ) (g := algebraMap P.Ring S)
      (P.map_comap_algebraMap_eq (T := T)))

/-- Helper for Lemma 10.149.4: the target map of the localized extension agrees with the original
extension map on elements coming from `P.Ring`. -/
lemma toLocalization_algebraMap_apply (x : P.Ring) :
    algebraMap PₜR Sₜ (algebraMap P.Ring PₜR x) =
      algebraMap S Sₜ (algebraMap P.Ring S x) := by
  -- This is exactly the compatibility built into the canonical extension morphism to the
  -- localization.
  simpa [toLocalization] using (P.toLocalization T).algebraMap_toRingHom x

/-- Helper for Lemma 10.149.4: a chosen lift through a square-zero quotient localizes uniquely
once it is required to extend the original lift on `P.Ring`. -/
lemma existsUnique_lift_to_localization_of_square_zero
    {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (f : Sₜ →ₐ[R] A ⧸ I) (g : P.Ring →ₐ[R] A)
    (hg :
      (Ideal.Quotient.mkₐ R I).comp g =
        (f.comp (IsScalarTower.toAlgHom R S Sₜ)).comp (IsScalarTower.toAlgHom R P.Ring S)) :
    ∃! gₜ : PₜR →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp gₜ = f.comp (IsScalarTower.toAlgHom R PₜR Sₜ) ∧
        gₜ.comp (Algebra.algHom R P.Ring PₜR) = g := by
  let hnil : IsNilpotent I := ⟨2, hI⟩
  -- Every denominator already becomes a unit after passing to the quotient, hence is a unit in
  -- `A` because the quotient ideal is square-zero.
  have hunit : ∀ y : T.comap (algebraMap P.Ring S), IsUnit (g y) := by
    intro y
    have hyquot :
        IsUnit ((Ideal.Quotient.mkₐ R I) (g y)) := by
      have hyT : algebraMap P.Ring S y ∈ T := y.2
      have hyunit :
          IsUnit (f (algebraMap S Sₜ (algebraMap P.Ring S y))) :=
        (IsLocalization.map_units Sₜ ⟨algebraMap P.Ring S y, hyT⟩).map f.toRingHom
      have hyeq :
          (Ideal.Quotient.mkₐ R I) (g y) =
            f (algebraMap S Sₜ (algebraMap P.Ring S y)) := by
        simpa [AlgHom.comp_apply] using AlgHom.congr_fun hg y
      rwa [hyeq]
    exact (IsNilpotent.isUnit_quotient_mk_iff (I := I) hnil).mp <| by
      simpa [Ideal.Quotient.mkₐ_eq_mk] using hyquot
  let gₜ : PₜR →ₐ[R] A :=
    IsLocalization.liftAlgHom (M := T.comap (algebraMap P.Ring S)) (f := g) hunit
  have hgₜ_comp : gₜ.comp (Algebra.algHom R P.Ring PₜR) = g := by
    -- The localized lift agrees with `g` on the dense image of `P.Ring`.
    ext x
    change
      IsLocalization.lift (M := T.comap (algebraMap P.Ring S)) (g := g.toRingHom) hunit
          (algebraMap P.Ring PₜR x) =
        g x
    simpa using DFunLike.congr_fun
      (IsLocalization.lift_comp (M := T.comap (algebraMap P.Ring S))
        (S := PₜR) (g := g.toRingHom) hunit) x
  have hgₜ :
      (Ideal.Quotient.mkₐ R I).comp gₜ = f.comp (IsScalarTower.toAlgHom R PₜR Sₜ) := by
    -- It is enough to compare both maps on the image of `P.Ring`.
    apply IsLocalization.algHom_ext (W := T.comap (algebraMap P.Ring S))
    ext x
    have hgₜ_comp_apply : gₜ (Algebra.algHom R P.Ring PₜR x) = g x :=
      DFunLike.congr_fun hgₜ_comp x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgₜ_comp_apply]
    calc
      (Ideal.Quotient.mkₐ R I) (g x) = f (algebraMap S Sₜ (algebraMap P.Ring S x)) := by
        simpa [AlgHom.comp_apply] using AlgHom.congr_fun hg x
      _ = f (algebraMap PₜR Sₜ (Algebra.algHom R P.Ring PₜR x)) := by
        exact congrArg f (P.toLocalization_algebraMap_apply (T := T) (Sₜ := Sₜ) x).symm
  refine ⟨gₜ, ⟨hgₜ, hgₜ_comp⟩, ?_⟩
  intro gₜ' hgₜ'
  -- Once the extension on `P.Ring` is fixed, localization gives uniqueness.
  apply IsLocalization.algHom_ext (W := T.comap (algebraMap P.Ring S))
  exact hgₜ'.2.trans hgₜ_comp.symm

/-- Helper for Lemma 10.149.4: any lift from the localized extension restricts to a lift for the
original extension after precomposing with `P.Ring → PₜR`. -/
lemma comp_source_eq_of_localized_lift
    {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A)
    (f : Sₜ →ₐ[R] A ⧸ I) (gₜ : PₜR →ₐ[R] A)
    (hgₜ : (Ideal.Quotient.mkₐ R I).comp gₜ = f.comp (IsScalarTower.toAlgHom R PₜR Sₜ)) :
    (Ideal.Quotient.mkₐ R I).comp (gₜ.comp (Algebra.algHom R P.Ring PₜR)) =
      (f.comp (IsScalarTower.toAlgHom R S Sₜ)).comp (IsScalarTower.toAlgHom R P.Ring S) := by
  -- Compare the two source maps pointwise on `P.Ring`.
  ext x
  calc
    (Ideal.Quotient.mkₐ R I) (gₜ (Algebra.algHom R P.Ring PₜR x)) =
        f (algebraMap PₜR Sₜ (Algebra.algHom R P.Ring PₜR x)) := by
          simpa [AlgHom.comp_apply] using
            AlgHom.congr_fun hgₜ (Algebra.algHom R P.Ring PₜR x)
    _ = f (algebraMap S Sₜ (algebraMap P.Ring S x)) := by
          exact congrArg f (P.toLocalization_algebraMap_apply (T := T) (Sₜ := Sₜ) x)

/-- Helper for Lemma 10.149.4: quotienting by the image ideal in a `ULift` ring recovers the
original quotient ring. -/
noncomputable def ulift_quotient_algEquiv {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A) :
    ((ULift.{x} A) ⧸ I.map (algebraMap A (ULift.{x} A))) ≃ₐ[R] (A ⧸ I) := by
  let eu : ULift.{x} A ≃ₐ[R] A := ULift.algEquiv (R := R) (A := A)
  have hmap : I = (I.map (algebraMap A (ULift.{x} A))).map (eu : ULift.{x} A →+* A) := by
    -- The `ULift` algebra equivalence is inverse to the canonical lift `A → ULift A`.
    calc
      I = I.map (RingHom.id A) := by simp
      _ = I.map ((eu : ULift.{x} A →+* A).comp (algebraMap A (ULift.{x} A))) := by
        ext a
        rfl
      _ = (I.map (algebraMap A (ULift.{x} A))).map (eu : ULift.{x} A →+* A) := by
        rw [Ideal.map_map]
  exact Ideal.quotientEquivAlg _ _ eu hmap

/-- Helper for Lemma 10.149.4: mapping a square-zero ideal into a `ULift` target keeps it
square-zero. -/
lemma ulift_map_square_zero {A : Type w} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) :
    (I.map (algebraMap A (ULift.{x} A))) ^ 2 = ⊥ := by
  -- Localization of the proof route starts by transporting the square-zero quotient to the
  -- universe accepted by the universal property.
  calc
    (I.map (algebraMap A (ULift.{x} A))) ^ 2 =
        Ideal.map (algebraMap A (ULift.{x} A)) (I ^ 2) := by
          rw [Ideal.map_pow]
    _ = ⊥ := by
          simp [hI, Ideal.map_bot]

/-- Helper for Lemma 10.149.4: a universal first-order thickening lifts maps to `A` by first
lifting to a square-zero quotient of `ULift A`, then descending along the canonical equivalence. -/
theorem IsUniversalFirstOrderThickening.existsUnique_lift_uliftTarget
    {P : Extension R S}
    (hP : @IsUniversalFirstOrderThickening.{u, v, max w x, _} R _ S _ _ P)
    {A : Type w} [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥)
    (f : S →ₐ[R] A ⧸ I) :
    ∃! g : P.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp g = f.comp (IsScalarTower.toAlgHom R P.Ring S) := by
  let Iu : Ideal (ULift.{x} A) := I.map (algebraMap A (ULift.{x} A))
  let eQuot : ((ULift.{x} A) ⧸ Iu) ≃ₐ[R] (A ⧸ I) := ulift_quotient_algEquiv (R := R) I
  let fu : S →ₐ[R] ((ULift.{x} A) ⧸ Iu) := eQuot.symm.toAlgHom.comp f
  obtain ⟨gu, hgu, huniq⟩ := hP.2 Iu (ulift_map_square_zero (R := R) I hI) fu
  let eu : ULift.{x} A ≃ₐ[R] A := ULift.algEquiv (R := R) (A := A)
  let g : P.Ring →ₐ[R] A := eu.toAlgHom.comp gu
  refine ⟨g, ?_, ?_⟩
  · -- Descend the transported lift through the quotient equivalence back to `A`.
    ext s
    have hs := AlgHom.congr_fun hgu s
    simpa [g, fu, eu, eQuot, AlgHom.comp_apply] using congrArg eQuot hs
  · intro g' hg'
    let gu' : P.Ring →ₐ[R] ULift.{x} A := eu.symm.toAlgHom.comp g'
    have hgu' :
        (Ideal.Quotient.mkₐ R Iu).comp gu' = fu.comp (IsScalarTower.toAlgHom R P.Ring S) := by
      -- Re-encode any competing lift in the `ULift` target and compare after applying `eQuot`.
      ext s
      apply eQuot.injective
      have hs := AlgHom.congr_fun hg' s
      simpa [gu', fu, eu, eQuot, AlgHom.comp_apply] using hs
    have hEq : gu' = gu := huniq gu' hgu'
    -- Descending along `ULift.algEquiv` preserves the unique source lift.
    ext s
    exact congrArg eu <| AlgHom.congr_fun hEq s

/-- Helper for Lemma 10.149.4: localizing the target of a universal first-order thickening again
gives a universal first-order thickening. -/
theorem isUniversalFirstOrderThickening_localization
    (hP : @IsUniversalFirstOrderThickening.{u, v, max w x, _} R _ S _ _ P) :
    @IsUniversalFirstOrderThickening.{u, x, w, _} R _ Sₜ _ _ Pₜ := by
  classical
  refine ⟨?_, ?_⟩
  · -- The localized kernel is the image of the old kernel, so its square is still zero.
    have hmul :
        Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S))))
            (P.ker * P.ker) =
          Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) P.ker *
            Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) P.ker :=
      Ideal.map_mul
        (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) P.ker P.ker
    have hsq : P.ker * P.ker = ⊥ := by
      simpa [pow_two] using hP.square_zero
    rw [P.ker_localization_eq_map (T := T) (Sₜ := Sₜ), pow_two]
    calc
      Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) P.ker *
          Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))) P.ker
          =
            Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S))))
              (P.ker * P.ker) := hmul.symm
      _ = ⊥ := by
        simpa [Ideal.map_bot] using
          congrArg
            (Ideal.map (algebraMap P.Ring (Localization (T.comap (algebraMap P.Ring S)))))
            hsq
  · -- TODO for Lemma 10.149.4: the remaining step is to apply the source universal property to
    -- `f.comp (IsScalarTower.toAlgHom R S Sₜ)`, use
    -- `existsUnique_lift_to_localization_of_square_zero` for existence, and then feed
    -- `comp_source_eq_of_localized_lift` into source uniqueness for the final inverse-map check.
    -- Route correction: the source-faithful localization argument closes directly from the stored
    -- lifting clause of `hP`; no separate target-side recursion is needed here.
    intro A _ _ I hI f
    let f₀ : S →ₐ[R] A ⧸ I := f.comp (IsScalarTower.toAlgHom R S Sₜ)
    obtain ⟨g, hg, huniqg⟩ :=
      hP.existsUnique_lift_uliftTarget I hI f₀
    obtain ⟨gₜ, hgₜ, huniqₜ⟩ :=
      P.existsUnique_lift_to_localization_of_square_zero
        (T := T) (Sₜ := Sₜ) I hI f g <| by
          simpa [f₀, AlgHom.comp_assoc] using hg
    refine ⟨gₜ, hgₜ.1, ?_⟩
    intro gₜ' hgₜ'
    -- Precomposing a localized lift along `P.Ring → PₜR` produces a source lift.
    have hsource :
        (Ideal.Quotient.mkₐ R I).comp (gₜ'.comp (Algebra.algHom R P.Ring PₜR)) =
          f₀.comp (IsScalarTower.toAlgHom R P.Ring S) :=
      P.comp_source_eq_of_localized_lift (T := T) (Sₜ := Sₜ) I f gₜ' hgₜ'
    have hgcomp : gₜ'.comp (Algebra.algHom R P.Ring PₜR) = g := by
      -- The source universal property forces the precomposed lift to be the original one.
      exact huniqg _ <| by simpa [f₀, AlgHom.comp_assoc] using hsource
    -- Once the source restriction is fixed, localization gives uniqueness.
    exact huniqₜ gₜ' ⟨hgₜ', hgcomp⟩

-- Proof sketch: for localization from the source, lift maps out of the localized square-zero
-- quotient by composing with `B → S⁻¹B`, use universality of `P`, and then localize the resulting
-- lift because the image of `M` becomes invertible. For localization from the target, apply the
-- same argument directly to the multiplicative subset of `B`; the inverse maps are obtained by the
-- defining universal properties on the localized targets.
/-- Lemma 10.149.4 (1): the canonical localization of a universal first-order thickening at the
image of a multiplicative subset of the source ring is again a universal first-order thickening. -/
theorem universalFirstOrderThickening_sourceLocalization
    (hP : @IsUniversalFirstOrderThickening.{u, v, w, _} R _ S _ _ P) :
    @IsUniversalFirstOrderThickening.{u, w, w, _} R _ Sₘ _ _ Pₘ := by
  -- This is the source-localization specialization of the general target-localization theorem.
  simpa using
    (isUniversalFirstOrderThickening_localization
      (P := P) (T := M.map (algebraMap R S)) (Sₜ := Sₘ) hP)

/-- Lemma 10.149.4 (2): localizing a universal first-order thickening along a multiplicative
subset of the target ring again yields the universal first-order thickening of the corresponding
localized algebra. -/
theorem universalFirstOrderThickening_targetLocalization
    (hP : @IsUniversalFirstOrderThickening.{u, v, max w x, _} R _ S _ _ P) :
    @IsUniversalFirstOrderThickening.{u, x, w, _} R _ Sₜ _ _ Pₜ :=
  isUniversalFirstOrderThickening_localization (P := P) (T := T) (Sₜ := Sₜ) hP

-- Proof sketch: identify the cotangent module of a localization with the localization of the
-- original cotangent module by localizing the kernel ideal and checking that the canonical
-- comparison map on cotangent modules satisfies the module-localization universal property.
-- Proof sketch: localizing the extension at a multiplicative subset of the target localizes its
-- kernel ideal, so the canonical cotangent map is the localization map of the conormal module.
/-- The canonical map on conormal modules for target localization realizes the localized conormal
module. -/
theorem conormalModule_targetLocalization_isLocalizedModule :
    IsLocalizedModule T
      (Extension.Cotangent.map (P.toLocalization T : P.Hom Pₜ)) := by
  let W : Submonoid P.Ring := T.comap (algebraMap P.Ring S)
  letI : Algebra P.Ring (Pₜ).Ring := by
    change Algebra P.Ring PₜR
    infer_instance
  letI : Module (Pₜ).Ring (Pₜ).ker := inferInstance
  letI : Module PₜR (Pₜ).ker := by
    change Module (Pₜ).Ring ((Pₜ).ker : Type _)
    infer_instance
  letI : IsScalarTower P.Ring PₜR (Pₜ).ker := by
    change IsScalarTower P.Ring (Pₜ).Ring ((Pₜ).ker : Type _)
    infer_instance
  let F : P.ker →ₗ[P.Ring] (Pₜ).ker := (P.toLocalization T : P.Hom Pₜ).mapKer rfl
  have hF_localized : IsLocalizedModule W F := by
    let eLocalized :
        P.ker.localized₀ W (Algebra.linearMap P.Ring PₜR) ≃ₗ[P.Ring]
          (P.ker.map (algebraMap P.Ring PₜR)).restrictScalars P.Ring :=
      LinearEquiv.ofEq _ _ (Ideal.localized₀_eq_restrictScalars_map PₜR W P.ker)
    let eKer :
        (P.ker.map (algebraMap P.Ring PₜR)).restrictScalars P.Ring ≃ₗ[P.Ring]
          ((Pₜ).ker).restrictScalars P.Ring :=
      (LinearEquiv.ofEq _ _ (P.ker_localization_eq_map (T := T) (Sₜ := Sₜ)).symm).restrictScalars
        P.Ring
    let e :
        P.ker.localized₀ W (Algebra.linearMap P.Ring PₜR) ≃ₗ[P.Ring]
          ((Pₜ).ker).restrictScalars P.Ring :=
      eLocalized.trans eKer
    have hIdealMap :
        Algebra.idealMap PₜR P.ker =
          eLocalized.toLinearMap ∘ₗ P.ker.toLocalized₀ W (Algebra.linearMap P.Ring PₜR) := by
      simpa [W] using Algebra.idealMap_eq_ofEq_comp_toLocalized₀ (S := PₜR) (p := W) (I := P.ker)
    have hF :
        F = e.toLinearMap ∘ₗ P.ker.toLocalized₀ W (Algebra.linearMap P.Ring PₜR) := by
      rw [show e.toLinearMap = eKer.toLinearMap ∘ₗ eLocalized.toLinearMap by rfl]
      rw [LinearMap.comp_assoc, ← hIdealMap]
      ext x
      rfl
    rw [hF]
    exact IsLocalizedModule.of_linearEquiv W
      (P.ker.toLocalized₀ W (Algebra.linearMap P.Ring PₜR)) e
  have hF_bijective : Function.Bijective (F.liftBaseChange PₜR) := by
    have hF_baseChange : IsBaseChange PₜR F :=
      (isLocalizedModule_iff_isBaseChange W PₜR F).mp hF_localized
    have hLift :
        hF_baseChange.equiv.toLinearMap = F.liftBaseChange PₜR := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul a b =>
          simp [IsBaseChange.equiv_tmul, LinearMap.liftBaseChange_tmul]
      | add x y hx hy =>
          calc
            hF_baseChange.equiv (x + y) = hF_baseChange.equiv x + hF_baseChange.equiv y := by
              exact map_add _ _ _
            _ = F.liftBaseChange PₜR x + F.liftBaseChange PₜR y := by
              simpa using congrArg₂ (· + ·) hx hy
            _ = F.liftBaseChange PₜR (x + y) := by
              symm
              exact LinearMap.map_add _ _ _
    rw [← hLift]
    exact hF_baseChange.equiv.bijective
  rw [isLocalizedModule_iff_isBaseChange T Sₜ]
  change Function.Bijective ((Extension.Cotangent.map (P.toLocalization T : P.Hom Pₜ)).liftBaseChange Sₜ)
  let e := Extension.tensorCotangent (f := (P.toLocalization T : P.Hom Pₜ)) rfl hF_bijective
  change Function.Bijective e.toLinearMap
  simpa [e] using e.bijective

/-- The canonical map on conormal modules for source localization realizes the localized conormal
module. -/
theorem conormalModule_sourceLocalization_isLocalizedModule :
    IsLocalizedModule (M.map (algebraMap R S))
      (Extension.Cotangent.map (P.toLocalization (M.map (algebraMap R S)) : P.Hom Pₘ)) := by
  -- The source-localization statement is the target-localization statement for the image
  -- multiplicative subset in `S`.
  simpa using
    (conormalModule_targetLocalization_isLocalizedModule
      (P := P) (T := M.map (algebraMap R S)) (Sₜ := Sₘ))

end

end Algebra.Extension
