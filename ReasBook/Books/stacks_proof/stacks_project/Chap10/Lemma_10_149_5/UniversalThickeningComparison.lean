import Mathlib
import StacksProject_2024.Chap10.Definition_10_149_2
import StacksProject_2024.Chap10.Lemma_10_131_9
import StacksProject_2024.Chap10.Lemma_10_148_3
import StacksProject_2024.Chap10.Lemma_10_138_9
import StacksProject_2024.Chap10.Lemma_10_149_1
import StacksProject_2024.Chap10.Lemma_10_149_4
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

open scoped TensorProduct
open Algebra TensorProduct
open Algebra.Extension
open TensorProduct.AlgebraTensorModule

universe u v w x y

namespace Algebra.Extension

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable (R) (P : Extension A B)

variable {R} {P}

/-- Helper for Lemma 10.149.5: the canonical self-presentation quotient from Lemma 10.149.1 is a
universal first-order thickening of a formally unramified algebra. -/
theorem selfPresentation_section_quotient_isUniversal
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    (selfPresentation_section_quotient (R := A) (S := B) l).IsUniversalFirstOrderThickening := by
  let P0 : Extension A B := (Generators.self A B).toExtension
  let P : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
  have hsq : P.ker ^ 2 = ⊥ := by
    -- The section-image quotient inherits the square-zero kernel of the infinitesimal presentation.
    simpa [P] using selfPresentation_section_quotient_square_zero (R := A) (S := B) l
  refine ⟨hsq, ?_⟩
  intro C _ _ I hI f
  -- First lift through the polynomial self-presentation before correcting the cotangent defect.
  obtain ⟨β, hβ⟩ :=
    selfPresentation_exists_polynomial_lift
      (R := A) (S := B) (A := C) I hI f
  let _ : Algebra B (C ⧸ I) := f.toAlgebra
  let Q : Extension A (C ⧸ I) :=
    Extension.ofSurjective (Ideal.Quotient.mkₐ A I) (Ideal.Quotient.mkₐ_surjective A I)
  obtain ⟨φ, rfl⟩ :=
    selfPresentation_polynomial_lift_to_extension_hom
      (R := A) (S := B) I f β hβ
  have hQsq : Q.ker ^ 2 = ⊥ := by
    -- The quotient extension `C → C/I` is square-zero by hypothesis on `I`.
    simpa [Q] using squareZeroQuotient_extension_square_zero (R := A) (I := I) hI
  obtain ⟨φu, hφu⟩ :=
    selfPresentation_corrected_extension_hom_cotangent_vanish
      (R := A) (S := B) Q hQsq φ l hl
  let φInf := selfPresentation_infinitesimal_lift (R := A) (S := B) Q hQsq φu
  have hφInf :
      (Ideal.Quotient.mkₐ A I).comp φInf =
        f.comp (IsScalarTower.toAlgHom A P0.infinitesimal.Ring B) := by
    -- After the cotangent correction, the lift already factors through the infinitesimal quotient.
    simpa [φInf, Q] using
      selfPresentation_infinitesimal_lift_comp_eq (R := A) (S := B) Q hQsq φu
  have hφInf_zero :
      ∀ x : P0.CotangentSpace,
        φInf
            (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
              P0.ker.cotangentIdeal)).1 = 0 := by
    -- The corrected lift annihilates exactly the section-image generators cut out in the quotient.
    intro x
    exact selfPresentation_section_generator_image_eq_zero_of_cotangent_vanish
      (R := A) (S := B) Q hQsq φu l hφu x
  obtain ⟨g, hg⟩ :=
    selfPresentation_factor_through_section_quotient_of_cotangent_vanish
      (R := A) (S := B) (A := C) I f l φInf hφInf hφInf_zero
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  -- Uniqueness is the same quotient-factor uniqueness proved in Lemma 10.149.1.
  exact (selfPresentation_factored_lift_unique
    (R := A) (S := B) (A := C) I f l hl hI g g' hg hg').symm

/-- Helper for Lemma 10.149.5: a lift against the quotient-by-kernel presentation of `Q`
automatically commutes with the structure maps to `B`. -/
lemma quotientKer_lift_comp_eq
    {P Q : Extension A B}
    (f : P.Ring →ₐ[A] Q.Ring)
    (hf :
      (Ideal.Quotient.mkₐ A Q.ker).comp f =
        ((Ideal.quotientKerAlgEquivOfSurjective
            (f := IsScalarTower.toAlgHom A Q.Ring B) Q.algebraMap_surjective).symm.toAlgHom).comp
          (IsScalarTower.toAlgHom A P.Ring B)) :
    (IsScalarTower.toAlgHom A Q.Ring B).comp f =
      IsScalarTower.toAlgHom A P.Ring B := by
  let qMap : Q.Ring →ₐ[A] B := IsScalarTower.toAlgHom A Q.Ring B
  let eQ : (Q.Ring ⧸ Q.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := qMap) Q.algebraMap_surjective
  -- Compare the given lift equation after applying the canonical quotient-kernel equivalence.
  ext x
  calc
    qMap (f x) = eQ ((Ideal.Quotient.mkₐ A Q.ker) (f x)) := by
      symm
      exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := qMap) Q.algebraMap_surjective (f x)
    _ = eQ (((eQ.symm.toAlgHom).comp (IsScalarTower.toAlgHom A P.Ring B)) x) := by
      exact congrArg eQ (AlgHom.congr_fun hf x)
    _ = IsScalarTower.toAlgHom A P.Ring B x := by
      simpa [AlgHom.comp_apply] using eQ.apply_symm_apply (IsScalarTower.toAlgHom A P.Ring B x)

/-- Helper for Lemma 10.149.5: once a map to an extension ring commutes with the structure maps to
`B`, its quotient-by-kernel reduction is forced to be the canonical quotient lift. -/
lemma quotientKer_comp_eq_of_lift_comp
    {P Q : Extension A B}
    (f : P.Ring →ₐ[A] Q.Ring)
    (hf :
      (IsScalarTower.toAlgHom A Q.Ring B).comp f =
        IsScalarTower.toAlgHom A P.Ring B) :
    (Ideal.Quotient.mkₐ A Q.ker).comp f =
      ((Ideal.quotientKerAlgEquivOfSurjective
          (f := IsScalarTower.toAlgHom A Q.Ring B) Q.algebraMap_surjective).symm.toAlgHom).comp
        (IsScalarTower.toAlgHom A P.Ring B) := by
  let qMap : Q.Ring →ₐ[A] B := IsScalarTower.toAlgHom A Q.Ring B
  let eQ : (Q.Ring ⧸ Q.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := qMap) Q.algebraMap_surjective
  -- Compare both quotient lifts after applying the canonical quotient-kernel equivalence.
  ext x
  apply eQ.injective
  calc
    eQ (((Ideal.Quotient.mkₐ A Q.ker).comp f) x) = qMap (f x) := by
      exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := qMap) Q.algebraMap_surjective (f x)
    _ = IsScalarTower.toAlgHom A P.Ring B x := by
      exact AlgHom.congr_fun hf x
    _ = eQ ((((eQ.symm.toAlgHom).comp (IsScalarTower.toAlgHom A P.Ring B)) x) : Q.Ring ⧸ Q.ker) := by
      symm
      simpa [AlgHom.comp_apply] using eQ.apply_symm_apply (IsScalarTower.toAlgHom A P.Ring B x)

/-- Helper for Lemma 10.149.5: the identity on a universal thickening is one of the canonical
quotient lifts of the structure map to `B`. -/
lemma quotientKer_id_comp
    (P : Extension A B) :
    (Ideal.Quotient.mkₐ A P.ker).comp (AlgHom.id A P.Ring) =
      ((Ideal.quotientKerAlgEquivOfSurjective
          (f := IsScalarTower.toAlgHom A P.Ring B) P.algebraMap_surjective).symm.toAlgHom).comp
        (IsScalarTower.toAlgHom A P.Ring B) := by
  let pMap : P.Ring →ₐ[A] B := IsScalarTower.toAlgHom A P.Ring B
  let eP : (P.Ring ⧸ P.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := pMap) P.algebraMap_surjective
  -- Both quotient maps become the same structure map after applying the canonical equivalence.
  ext x
  apply eP.injective
  calc
    eP ((Ideal.Quotient.mkₐ A P.ker) x) = pMap x := by
      exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := pMap) P.algebraMap_surjective x
    _ = eP (((eP.symm.toAlgHom).comp pMap) x) := by
      symm
      simpa [AlgHom.comp_apply] using eP.apply_symm_apply (pMap x)

/-- Helper for Lemma 10.149.5: an algebra equivalence over `A` that commutes with the maps to `B`
identifies the kernel ideals after mapping along the equivalence. -/
lemma extension_ker_map_eq_of_sourceAlgEquiv
    {P P' : Extension A B}
    (e : P'.Ring ≃ₐ[A] P.Ring)
    (he :
      (IsScalarTower.toAlgHom A P.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P'.Ring B) :
    Ideal.map e.toRingHom P'.ker = P.ker := by
  let pMap : P.Ring →ₐ[A] B := IsScalarTower.toAlgHom A P.Ring B
  let pMap' : P'.Ring →ₐ[A] B := IsScalarTower.toAlgHom A P'.Ring B
  -- The commuting square turns membership in the mapped kernel into the defining kernel equation.
  ext y
  change y ∈ Ideal.map e.toRingHom P'.ker ↔ y ∈ P.ker
  constructor
  · intro hy
    rcases (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hy with ⟨x, hx, rfl⟩
    have hcomm := AlgHom.congr_fun he x
    change pMap (e x) = 0
    simpa [pMap', AlgHom.comp_apply] using hcomm.trans hx
  · intro hy
    refine (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mpr ⟨e.symm y, ?_, by simp⟩
    have hcomm := AlgHom.congr_fun he (e.symm y)
    change pMap' (e.symm y) = 0
    change pMap y = 0 at hy
    have hcomm' : pMap' (e.symm y) = pMap y := by
      simpa [pMap', AlgHom.comp_apply] using hcomm.symm
    exact hcomm'.trans hy

/-- Helper for Lemma 10.149.5: square-zero kernels transport across a source-ring algebra
equivalence that commutes with the maps to `B`. -/
lemma extension_square_zero_of_sourceAlgEquiv
    {P P' : Extension A B}
    (e : P'.Ring ≃ₐ[A] P.Ring)
    (he :
      (IsScalarTower.toAlgHom A P.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P'.Ring B)
    (hsq : P.ker ^ 2 = ⊥) :
    P'.ker ^ 2 = ⊥ := by
  have hmapker : Ideal.map e.toRingHom P'.ker = P.ker :=
    extension_ker_map_eq_of_sourceAlgEquiv (P := P) (P' := P') e he
  have hmap_sq : Ideal.map e.toRingHom (P'.ker ^ 2) = ⊥ := by
    -- Mapping the squared kernel across the equivalence reduces directly to the known square-zero
    -- relation on `P`.
    calc
      Ideal.map e.toRingHom (P'.ker ^ 2)
          = (Ideal.map e.toRingHom P'.ker) ^ 2 := by rw [Ideal.map_pow]
      _ = P.ker ^ 2 := by rw [hmapker]
      _ = ⊥ := hsq
  rw [_root_.eq_bot_iff]
  intro x hx
  have hxmap : e x ∈ Ideal.map e.toRingHom (P'.ker ^ 2) :=
    Ideal.mem_map_of_mem e.toRingHom hx
  have hxbot : e x ∈ (⊥ : Ideal P.Ring) := by
    rw [hmap_sq] at hxmap
    simpa using hxmap
  have hzero : e x = 0 := Ideal.mem_bot.mp hxbot
  simpa using e.injective (show e x = e 0 by simpa using hzero)

/-- Helper for Lemma 10.149.5: any two universal first-order thickenings of `B` over `A` are
canonically isomorphic as `A`-algebras over `B`. -/
theorem universalFirstOrderThickening_hom_equiv
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x y, _} A _ B _ _ P)
    (hQ : @IsUniversalFirstOrderThickening.{v, w, max x y, _} A _ B _ _ Q) :
    ∃ e : P.Ring ≃ₐ[A] Q.Ring,
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B := by
  let pMap : P.Ring →ₐ[A] B := IsScalarTower.toAlgHom A P.Ring B
  let qMap : Q.Ring →ₐ[A] B := IsScalarTower.toAlgHom A Q.Ring B
  let eP : (P.Ring ⧸ P.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := pMap) P.algebraMap_surjective
  let eQ : (Q.Ring ⧸ Q.ker) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := qMap) Q.algebraMap_surjective
  -- Route correction: compare the two universal thickenings directly through their quotient-kernel
  -- presentations over `B`, instead of normalizing both sides through ULift.
  obtain ⟨f, hf, hfuniq⟩ :=
    hP.existsUnique_lift_uliftTarget (A := Q.Ring) Q.ker hQ.square_zero eQ.symm.toAlgHom
  obtain ⟨g, hg, hguniq⟩ :=
    hQ.existsUnique_lift_uliftTarget (A := P.Ring) P.ker hP.square_zero eP.symm.toAlgHom
  have hf_comp :
      qMap.comp f = pMap :=
    quotientKer_lift_comp_eq (P := P) (Q := Q) f hf
  have hg_comp :
      pMap.comp g = qMap :=
    quotientKer_lift_comp_eq (P := Q) (Q := P) g hg
  have hgf_lift :
      (Ideal.Quotient.mkₐ A P.ker).comp (g.comp f) =
        eP.symm.toAlgHom.comp pMap := by
    -- Compose the `Q → P` lift relation with `f` and rewrite back over `B`.
    ext x
    have hgx := AlgHom.congr_fun hg (f x)
    change (Ideal.Quotient.mkₐ A P.ker) (g (f x)) = eP.symm (pMap x)
    calc
      (Ideal.Quotient.mkₐ A P.ker) (g (f x)) = eP.symm (qMap (f x)) := by
        simpa [AlgHom.comp_apply] using hgx
      _ = eP.symm (pMap x) := by
        exact congrArg eP.symm (AlgHom.congr_fun hf_comp x)
  have hfg_lift :
      (Ideal.Quotient.mkₐ A Q.ker).comp (f.comp g) =
        eQ.symm.toAlgHom.comp qMap := by
    -- The symmetric composite is again a lift of the canonical quotient map for `Q`.
    ext x
    have hfx := AlgHom.congr_fun hf (g x)
    change (Ideal.Quotient.mkₐ A Q.ker) (f (g x)) = eQ.symm (qMap x)
    calc
      (Ideal.Quotient.mkₐ A Q.ker) (f (g x)) = eQ.symm (pMap (g x)) := by
        simpa [AlgHom.comp_apply] using hfx
      _ = eQ.symm (qMap x) := by
        exact congrArg eQ.symm (AlgHom.congr_fun hg_comp x)
  obtain ⟨uP, huP, huPuniq⟩ :=
    hP.existsUnique_lift_uliftTarget (A := P.Ring) P.ker hP.square_zero eP.symm.toAlgHom
  obtain ⟨uQ, huQ, huQuniq⟩ :=
    hQ.existsUnique_lift_uliftTarget (A := Q.Ring) Q.ker hQ.square_zero eQ.symm.toAlgHom
  have hgf : g.comp f = AlgHom.id A P.Ring := by
    -- Uniqueness for the `P`-lifting problem forces the composite to be the identity.
    calc
      g.comp f = uP := huPuniq _ hgf_lift
      _ = AlgHom.id A P.Ring := by
        symm
        exact huPuniq _ (quotientKer_id_comp (P := P))
  have hfg : f.comp g = AlgHom.id A Q.Ring := by
    -- The same uniqueness argument on `Q` identifies the opposite composite with the identity.
    calc
      f.comp g = uQ := huQuniq _ hfg_lift
      _ = AlgHom.id A Q.Ring := by
        symm
        exact huQuniq _ (quotientKer_id_comp (P := Q))
  have hLeft : Function.LeftInverse g f := by
    intro x
    simpa [AlgHom.comp_apply] using AlgHom.congr_fun hgf x
  have hRight : Function.RightInverse g f := by
    intro x
    simpa [AlgHom.comp_apply] using AlgHom.congr_fun hfg x
  refine ⟨AlgEquiv.ofBijective f ⟨hLeft.injective, hRight.surjective⟩, ?_⟩
  -- The equivalence commutes with the maps to `B` because its underlying map is the lifted `f`.
  simpa using hf_comp

/-- Helper for Lemma 10.149.5: any universal first-order thickening is isomorphic over `B` to the
canonical self-presentation quotient from Lemma 10.149.1. -/
theorem universalFirstOrderThickening_selfPresentation_equiv
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    ∃ e : P.Ring ≃ₐ[A] (selfPresentation_section_quotient (R := A) (S := B) l).Ring,
      (IsScalarTower.toAlgHom A
          (selfPresentation_section_quotient (R := A) (S := B) l).Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B := by
  -- Route correction: specialize the direct comparison theorem to the canonical quotient from
  -- Lemma 10.149.1 instead of passing through any ULift-normalized intermediary.
  let Q : Extension.{max v w} A B := selfPresentation_section_quotient (R := A) (S := B) l
  have hQ_same :
      @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ Q := by
    simpa [Q] using selfPresentation_section_quotient_isUniversal (A := A) (B := B) l hl
  exact universalFirstOrderThickening_hom_equiv
    (P := P)
    (Q := Q)
    hP
    hQ_same

end Algebra.Extension
