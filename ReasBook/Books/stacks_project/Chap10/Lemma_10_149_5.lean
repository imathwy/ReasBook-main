import Mathlib
import stacks_project.Chap10.Definition_10_149_2
import stacks_project.Chap10.Lemma_10_131_9
import stacks_project.Chap10.Lemma_10_148_3
import stacks_project.Chap10.Lemma_10_149_1
import stacks_project.Chap10.Lemma_10_149_4
import stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

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

/- Domain-style sampling:
- primary domain: universal first-order thickenings, formal unramifiedness, and the
  Jacobi-Zariski/transitivity sequence for Kähler differentials over a tower `R → A → P.Ring → B`;
- sampled owner declarations:
  `Algebra.FormallyUnramified`,
  `Algebra.FormallyUnramified.iff_comp_injective`,
  `KaehlerDifferential.mapBaseChange`,
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`;
- best owner abstraction:
  part (1) is governed by the canonical owner predicate `FormallyUnramified A _`,
  while part (2) is governed by the owner map `KaehlerDifferential.mapBaseChange R A P.Ring`,
  further base changed along `P.Ring → B`;
- primitive data vs. derived API:
  the primitive data are the extension `P : Extension A B` and the universal first-order
  thickening hypothesis, while the tensor-reassociated comparison used below is only a thin
  auxiliary bridge/view of the owner `KaehlerDifferential.mapBaseChange`;
- source/core/bridge triage:
  `source-facing`: the formal-unramified consequence and the textbook isomorphism on the
    base-changed differential modules;
  `core/canonical`: `FormallyUnramified` and `KaehlerDifferential.mapBaseChange`;
  `bridge/view`: the tensor-order identification
    `B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`.

The previous local map definition rebuilt this bridge by hand with `rid`/`assoc`/`map`.
The canonical owner-level construction is the standard further base change of
`KaehlerDifferential.mapBaseChange` using `lTensor` and `cancelBaseChange`.
-/

/-- Lemma 10.149.5 (2), source-facing canonical map: after identifying the displayed textbook
comparison with the further base change of `KaehlerDifferential.mapBaseChange R A P.Ring` along
`P.Ring → B`, we obtain the canonical `B`-linear map
`B ⊗[A] Ω[A⁄R] → B ⊗[P.Ring] Ω[P.Ring⁄R]`. -/
noncomputable def universalFirstOrderThickening_kaehlerBaseChangeLinearMap
    : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  lTensor B B (KaehlerDifferential.mapBaseChange R A P.Ring) ∘ₗ
    (cancelBaseChange A P.Ring B B Ω[A⁄R]).symm.toLinearMap

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

/-- Helper for Lemma 10.149.5: the `A`-relative quotient from the infinitesimal self-presentation
to the canonical section quotient has kernel exactly the section-image ideal `J' / J²`. -/
lemma selfPresentation_section_quotient_a_relative_ker_eq
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)) = Jbar := by
  intro P0 Jbar
  -- Proof comment: after unfolding the canonical quotient extension, the source algebra map is
  -- the quotient map `P0.infinitesimal.Ring → P0.infinitesimal.Ring ⧸ Jbar`.
  change RingHom.ker
      (Ideal.Quotient.mkₐ A Jbar :
        P0.infinitesimal.Ring →+* P0.infinitesimal.Ring ⧸ Jbar) = Jbar
  simpa using (Ideal.Quotient.mkₐ_ker A Jbar)

/-- Helper for Lemma 10.149.5: the canonical quotient map from the infinitesimal self-presentation
to the section quotient is surjective. -/
lemma selfPresentation_section_quotient_a_relative_surjective
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Surjective (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)) := by
  intro P0 Jbar
  -- Proof comment: once the quotient ring is exposed, surjectivity is the standard quotient-map
  -- surjectivity.
  change Function.Surjective
      (Ideal.Quotient.mkₐ A Jbar :
        P0.infinitesimal.Ring →ₐ[A] P0.infinitesimal.Ring ⧸ Jbar)
  simpa using (Ideal.Quotient.mkₐ_surjective A Jbar)

/-- Helper for Lemma 10.149.5: the `A`-relative conormal sequence for the canonical section
quotient is the standard conormal sequence for the quotient by the section-image ideal. -/
theorem selfPresentation_section_quotient_a_relative_exact
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    Function.Exact
        ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap)
        (KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) ∧
      Function.Surjective
        (KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)) := by
  intro P0 Jbar
  -- Proof comment: this is Lemma 10.131.9 specialized to the quotient by the explicit
  -- section-image ideal.
  exact kaehlerDifferential_exact_cotangent_tensor_of_surjective
    (R := A)
    (S := P0.infinitesimal.Ring)
    (S' := P0.infinitesimal.Ring ⧸ Jbar)
    Jbar
    (selfPresentation_section_quotient_a_relative_ker_eq (A := A) (B := B) l)
    (selfPresentation_section_quotient_a_relative_surjective (A := A) (B := B) l)

/-- Helper for Lemma 10.149.5: each explicit section generator maps, under the `A`-relative
conormal map for the canonical quotient, to the corresponding differential class. -/
theorem selfPresentation_section_quotient_a_relative_generator_toCotangent
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let sectionGenerator :
        P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
        (P0.infinitesimal.Ring ⧸ Jbar)).comp
      (Ideal.Cotangent.equivOfEq Jbar
        (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
        (selfPresentation_section_quotient_a_relative_ker_eq
          (A := A) (B := B) l).symm).toLinearMap)
      (Ideal.toCotangent Jbar ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩) =
      1 ⊗ₜ[P0.infinitesimal.Ring] KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator := by
  intro P0 Jbar sectionGenerator
  -- Proof comment: this is exactly the concrete generator formula from Lemma 10.131.9, applied to
  -- the quotient ideal `Jbar`.
  simpa [sectionGenerator] using
    kerCotangentToTensorOfKerEq_toCotangent
      (R := A)
      (S := P0.infinitesimal.Ring)
      (S' := P0.infinitesimal.Ring ⧸ Jbar)
      Jbar
      (selfPresentation_section_quotient_a_relative_ker_eq (A := A) (B := B) l)
      ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩

/-- Helper for Lemma 10.149.5: each chosen section generator already lies in the image of the
`A`-relative conormal map for the canonical quotient. -/
theorem selfPresentation_section_quotient_a_relative_generator_mem_range
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (x : (Generators.self A B).toExtension.CotangentSpace) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let sectionGenerator :
        P0.infinitesimal.Ring :=
      (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
        P0.ker.cotangentIdeal)).1
    1 ⊗ₜ[P0.infinitesimal.Ring] KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator ∈
      LinearMap.range
        ((KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
            (P0.infinitesimal.Ring ⧸ Jbar)).comp
          (Ideal.Cotangent.equivOfEq Jbar
            (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
            (selfPresentation_section_quotient_a_relative_ker_eq
              (A := A) (B := B) l).symm).toLinearMap) := by
  intro P0 Jbar sectionGenerator
  -- Proof comment: witness the target element by the corresponding cotangent class of the chosen
  -- section generator.
  refine ⟨Ideal.toCotangent Jbar ⟨sectionGenerator, Ideal.subset_span ⟨x, rfl⟩⟩, ?_⟩
  simpa [sectionGenerator] using
    selfPresentation_section_quotient_a_relative_generator_toCotangent
      (A := A) (B := B) l x

/-- Helper for Lemma 10.149.5: the identity range on the cotangent space of the self-presentation
already spans the whole module over the canonical quotient ring. -/
theorem selfPresentation_section_quotient_cotangentSpace_identity_span_top
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Q : Extension A B := selfPresentation_section_quotient (R := A) (S := B) l
    Submodule.span Q.Ring
      (Set.range (fun x : P0.CotangentSpace ↦ x)) = ⊤ := by
  intro P0 Q
  -- Proof comment: the identity map is surjective, so its range spans the whole module.
  simpa using
    (LinearMap.range_eq_top.2
      (show Function.Surjective
          (LinearMap.id : P0.CotangentSpace →ₗ[Q.Ring] P0.CotangentSpace) from
          fun x ↦ ⟨x, rfl⟩))

/-- Helper for Lemma 10.149.5: a surjective family spans the whole target module. -/
lemma submodule_span_range_eq_top_of_surjective
    {R₀ : Type*} {M₀ : Type*} [Semiring R₀] [AddCommMonoid M₀] [Module R₀ M₀]
    {ι : Type*} (v : ι → M₀) (hv : Function.Surjective v) :
    Submodule.span R₀ (Set.range v) = ⊤ := by
  -- Proof comment: surjectivity identifies the range with the whole ambient set, whose span is
  -- tautologically all of `M₀`.
  rw [Set.range_eq_univ.2 hv]
  simp

/-- Helper for Lemma 10.149.5: after passing to the quotient by the square-zero kernel action,
the canonical section-generator family still surjects onto the `A`-relative middle term. -/
theorem selfPresentation_section_quotient_a_relative_generator_mod_nilpotent_surjective
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let K : Ideal (P0.infinitesimal.Ring ⧸ Jbar) :=
      (selfPresentation_section_quotient (R := A) (S := B) l).ker
    let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]
    let qgen : P0.CotangentSpace → M ⧸ (K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)) :=
      fun x ↦
        let sectionGenerator :
            P0.infinitesimal.Ring :=
          (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
            P0.ker.cotangentIdeal)).1
        ((K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)).mkQ)
          ((1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
            KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator)
    Function.Surjective qgen := by
  intro P0 Jbar K M qgen
  -- Route correction: the source-faithful next step is to build the explicit quotient-middle
  -- comparison with `P0.CotangentSpace`, then read this surjectivity off from the generator
  -- formula on that comparison.
  -- TODO: define the quotient-middle comparison
  -- `(M ⧸ (K • ⊤)) → B ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]`
  -- by composing `quotTensorEquivQuotSMul`, `cancelBaseChange`, and the quotient-kernel algebra
  -- equivalence `((P0.infinitesimal.Ring ⧸ Jbar) ⧸ K) ≃ₐ[A] B`; then prove that it sends
  -- `qgen x` to `Extension.CotangentSpace.map P0.toInfinitesimal x`, and conclude surjectivity
  -- from `Extension.CotangentSpace.map_toInfinitesimal_bijective`.
  sorry

theorem selfPresentation_section_quotient_a_relative_generator_mod_nilpotent_span
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let K : Ideal (P0.infinitesimal.Ring ⧸ Jbar) :=
      (selfPresentation_section_quotient (R := A) (S := B) l).ker
    let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]
    let s : Set M :=
      Set.range fun x : P0.CotangentSpace ↦
        let sectionGenerator :
            P0.infinitesimal.Ring :=
          (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
            P0.ker.cotangentIdeal)).1
        (1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
          KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator
    Submodule.span (P0.infinitesimal.Ring ⧸ Jbar)
      (((K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)).mkQ) '' s) = ⊤ := by
  intro P0 Jbar K M s
  -- Route correction: the intended proof transports this span through an explicit quotient-middle
  -- comparison to the identity range on `P0.CotangentSpace`, whose span is already `⊤` by
  -- `selfPresentation_section_quotient_cotangentSpace_identity_span_top`.
  let qgen : P0.CotangentSpace → M ⧸ (K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)) :=
    fun x ↦
      let sectionGenerator :
          P0.infinitesimal.Ring :=
        (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
          P0.ker.cotangentIdeal)).1
      ((K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)).mkQ)
        ((1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
          KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator)
  have hsurj : Function.Surjective qgen :=
    selfPresentation_section_quotient_a_relative_generator_mod_nilpotent_surjective
      (A := A) (B := B) l hl
  -- The displayed image family is exactly the range of the quotient generator map.
  have hspanRange :
      Submodule.span (P0.infinitesimal.Ring ⧸ Jbar) (Set.range qgen) = ⊤ :=
    submodule_span_range_eq_top_of_surjective
      (R₀ := P0.infinitesimal.Ring ⧸ Jbar)
      qgen
      hsurj
  have hsEq : ((K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)).mkQ) '' s = Set.range qgen := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [hsEq]
  exact hspanRange

/-- Helper for Lemma 10.149.5: once the section-generator classes span modulo the square-zero
kernel, they already span the `A`-relative middle term over the infinitesimal source ring. -/
theorem selfPresentation_section_quotient_a_relative_generator_span_source
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]
    let s : Set M :=
      Set.range fun x : P0.CotangentSpace ↦
        let sectionGenerator :
            P0.infinitesimal.Ring :=
          (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
            P0.ker.cotangentIdeal)).1
        (1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
          KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator
    Submodule.span P0.infinitesimal.Ring s = ⊤ := by
  intro P0 Jbar M s
  let K : Ideal (P0.infinitesimal.Ring ⧸ Jbar) :=
    (selfPresentation_section_quotient (R := A) (S := B) l).ker
  let _ : Module (P0.infinitesimal.Ring ⧸ Jbar) M := inferInstance
  have hquotSpan :
      Submodule.span (P0.infinitesimal.Ring ⧸ Jbar)
        (((K • (⊤ : Submodule (P0.infinitesimal.Ring ⧸ Jbar) M)).mkQ) '' s) = ⊤ :=
    selfPresentation_section_quotient_a_relative_generator_mod_nilpotent_span
      (A := A) (B := B) l hl
  have hnil : IsNilpotent K := by
    -- The kernel of the canonical section quotient is square-zero, hence nilpotent.
    refine ⟨2, ?_⟩
    simpa [K] using selfPresentation_section_quotient_square_zero (R := A) (S := B) l
  have hspan : Submodule.span (P0.infinitesimal.Ring ⧸ Jbar) s = ⊤ := by
    -- Nakayama upgrades generation modulo the square-zero kernel to generation upstairs.
    exact span_eq_top_of_quotient_span_eq_top_of_isNilpotent
      (R := P0.infinitesimal.Ring ⧸ Jbar)
      (M := M)
      (I := K)
      s
      hquotSpan
      hnil
  -- Forgetting scalars from the quotient ring to the source ring preserves this top span.
  rw [← Submodule.restrictScalars_span P0.infinitesimal.Ring
    (P0.infinitesimal.Ring ⧸ Jbar) Ideal.Quotient.mk_surjective, hspan,
    Submodule.restrictScalars_eq_top_iff]

/-- Helper for Lemma 10.149.5: the `A`-relative conormal map for the canonical section quotient
has full range once the chosen section generators span modulo the square-zero kernel. -/
theorem selfPresentation_section_quotient_a_relative_range_eq_top
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    let P0 : Extension A B := (Generators.self A B).toExtension
    let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
    let f :
        Jbar.Cotangent →ₗ[P0.infinitesimal.Ring]
          (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A] :=
      (KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
          (P0.infinitesimal.Ring ⧸ Jbar)).comp
        (Ideal.Cotangent.equivOfEq Jbar
          (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
          (selfPresentation_section_quotient_a_relative_ker_eq
            (A := A) (B := B) l).symm).toLinearMap
    LinearMap.range f = ⊤ := by
  intro P0 Jbar f
  let M := (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A]
  let s : Set M :=
    Set.range fun x : P0.CotangentSpace ↦
      let sectionGenerator :
          P0.infinitesimal.Ring :=
        (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
          P0.ker.cotangentIdeal)).1
      (1 : P0.infinitesimal.Ring ⧸ Jbar) ⊗ₜ[P0.infinitesimal.Ring]
        KaehlerDifferential.D A P0.infinitesimal.Ring sectionGenerator
  have hspan :
      Submodule.span P0.infinitesimal.Ring s = ⊤ :=
    selfPresentation_section_quotient_a_relative_generator_span_source
      (A := A) (B := B) l hl
  have hspan_le_range : Submodule.span P0.infinitesimal.Ring s ≤ LinearMap.range f := by
    -- Each textbook generator already comes from the conormal map, so the whole span does as well.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    change
      1 ⊗ₜ[P0.infinitesimal.Ring] KaehlerDifferential.D A P0.infinitesimal.Ring
          (((Ideal.cotangentEquivIdeal P0.ker) (P0.cotangentEquivCotangentKer (l x)) :
            P0.ker.cotangentIdeal)).1 ∈
        LinearMap.range f
    exact selfPresentation_section_quotient_a_relative_generator_mem_range
      (A := A) (B := B) l x
  -- The spanning family lies in the range, so the range is everything.
  exact top_unique <| by
    rw [← hspan]
    exact hspan_le_range

/-- Helper for Lemma 10.149.5: the canonical self-presentation quotient is formally unramified
over `A`. -/
theorem selfPresentation_section_quotient_formallyUnramified
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    FormallyUnramified A (selfPresentation_section_quotient (R := A) (S := B) l).Ring := by
  refine ⟨?_⟩
  let P0 : Extension A B := (Generators.self A B).toExtension
  let Jbar := selfPresentation_section_image_ideal (R := A) (S := B) l
  change Subsingleton Ω[(P0.infinitesimal.Ring ⧸ Jbar)⁄A]
  let f :
      Jbar.Cotangent →ₗ[P0.infinitesimal.Ring]
        (P0.infinitesimal.Ring ⧸ Jbar) ⊗[P0.infinitesimal.Ring] Ω[P0.infinitesimal.Ring⁄A] :=
    (KaehlerDifferential.kerCotangentToTensor A P0.infinitesimal.Ring
        (P0.infinitesimal.Ring ⧸ Jbar)).comp
      (Ideal.Cotangent.equivOfEq Jbar
        (RingHom.ker (algebraMap P0.infinitesimal.Ring (P0.infinitesimal.Ring ⧸ Jbar)))
        (selfPresentation_section_quotient_a_relative_ker_eq
          (A := A) (B := B) l).symm).toLinearMap
  let g :=
    KaehlerDifferential.mapBaseChange A P0.infinitesimal.Ring
      (P0.infinitesimal.Ring ⧸ Jbar)
  have hExact : Function.Exact f g :=
    (selfPresentation_section_quotient_a_relative_exact
      (A := A) (B := B) l).1
  have hRange : LinearMap.range f = ⊤ :=
    selfPresentation_section_quotient_a_relative_range_eq_top
      (A := A) (B := B) l hl
  have hz : ∀ z, g (f z) = 0 := congr_fun hExact.comp_eq_zero
  have hSurj : Function.Surjective g :=
    (selfPresentation_section_quotient_a_relative_exact
      (A := A) (B := B) l).2
  have hzero : ∀ x : Ω[(P0.infinitesimal.Ring ⧸ Jbar)⁄A], x = 0 := by
    intro x
    obtain ⟨x', rfl⟩ := hSurj x
    have hx' : x' ∈ LinearMap.range f := by
      simpa [hRange]
    rcases hx' with ⟨z, rfl⟩
    -- Exactness kills the image of the conormal map, and `range f = ⊤` puts every source element
    -- in that image.
    exact hz z
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

-- Proof sketch: the universal lifting property gives uniqueness of lifts from `P.Ring` after
-- precomposing with `P.Ring → B`, so `Algebra.FormallyUnramified.iff_comp_injective` yields
-- `FormallyUnramified A P.Ring`.
/-- Lemma 10.149.5 (1): a universal first-order thickening `B'` of a formally unramified
`A`-algebra `B` is itself formally unramified over `A`. -/
theorem universalFirstOrderThickening_formallyUnramified
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    FormallyUnramified A P.Ring := by
  let P0 : Extension A B := (Generators.self A B).toExtension
  -- Compare the given universal thickening with the canonical quotient from Lemma 10.149.1.
  obtain ⟨l, hl⟩ := selfPresentation_cotangentComplex_has_section (R := A) (S := B)
  obtain ⟨e, -⟩ :=
    universalFirstOrderThickening_selfPresentation_equiv
      (P := P) hP l hl
  have hQfu :
      FormallyUnramified A (selfPresentation_section_quotient (R := A) (S := B) l).Ring :=
    selfPresentation_section_quotient_formallyUnramified (A := A) (B := B) l hl
  let _ :
      FormallyUnramified A (selfPresentation_section_quotient (R := A) (S := B) l).Ring := hQfu
  -- Transport formal unramifiedness across the unique comparison equivalence.
  exact Algebra.FormallyUnramified.of_equiv e.symm

/-- Helper for Lemma 10.149.5: if an `A`-algebra equivalence of extension rings commutes with the
structure maps to `B`, then its inverse satisfies the symmetric commutative square as well. -/
lemma sourceAlgEquiv_symm_comp_eq
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    (IsScalarTower.toAlgHom A P.Ring B).comp e.symm.toAlgHom =
      IsScalarTower.toAlgHom A Q.Ring B := by
  ext x
  -- Evaluate the given commutative square at `e.symm x` and rewrite the composite.
  have hx := AlgHom.congr_fun he (e.symm x)
  simpa [AlgHom.comp_apply] using hx.symm

/-- Helper for Lemma 10.149.5: an `A`-algebra equivalence of extension rings also commutes with
the induced maps from any further base ring `R₀` along the tower `R₀ → A → P.Ring, Q.Ring`. -/
lemma sourceAlgEquiv_commutes_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (x : R₀) :
    e (algebraMap R₀ P.Ring x) = algebraMap R₀ Q.Ring x := by
  -- Proof comment: `e` is already an `A`-algebra equivalence, so we only need to rewrite the
  -- `R₀`-structure maps through `A`.
  rw [IsScalarTower.algebraMap_eq R₀ A P.Ring, IsScalarTower.algebraMap_eq R₀ A Q.Ring]
  exact e.commutes (algebraMap R₀ A x)

/-- Helper for Lemma 10.149.5: the inverse comparison equivalence satisfies the symmetric base-map
compatibility over any further base ring `R₀`. -/
lemma sourceAlgEquiv_symm_commutes_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P Q : Extension A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (x : R₀) :
    e.symm (algebraMap R₀ Q.Ring x) = algebraMap R₀ P.Ring x := by
  -- Proof comment: this is the same `A`-algebra compatibility for the inverse equivalence.
  rw [IsScalarTower.algebraMap_eq R₀ A Q.Ring, IsScalarTower.algebraMap_eq R₀ A P.Ring]
  exact e.symm.commutes (algebraMap R₀ A x)

/-- Helper for Lemma 10.149.5: the `Q.Ring`-module of differentials is naturally a scalar tower
over any compatible map `P.Ring → Q.Ring`. -/
lemma sourceAlgEquiv_kaehler_isScalarTower
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] :
    IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] := by
  -- Proof comment: the `P.Ring`-action on `Ω[Q.Ring⁄R₀]` is exactly the one obtained by
  -- restricting scalars along `P.Ring → Q.Ring`.
  exact IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simpa

/-- Helper for Lemma 10.149.5: changing the tensor base from `P.Ring` to `Q.Ring` along a
compatible scalar tower `P.Ring → Q.Ring → B` is the canonical scalar-descent equivalence. -/
noncomputable def sourceAlgEquiv_tensorKaehler_desc
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] [IsScalarTower P.Ring Q.Ring B]
    (hPQ : Function.Surjective (algebraMap P.Ring Q.Ring)) :
    B ⊗[P.Ring] Ω[Q.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀] :=
  letI : IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_kaehler_isScalarTower (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
  letI : CompatibleSMul P.Ring Q.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    CompatibleSMul.of_algebraMap_surjective
      (R := P.Ring) (A := Q.Ring) (M := Q.Ring) (N := Ω[Q.Ring⁄R₀]) hPQ
  -- Proof comment: first reinsert the missing `Q.Ring` tensor factor via `cancelBaseChange`,
  -- then collapse `Q.Ring ⊗[P.Ring] Ω[Q.Ring⁄R₀]` back to `Ω[Q.Ring⁄R₀]` by the left-unit tensor
  -- equivalence.
  (cancelBaseChange P.Ring Q.Ring B B Ω[Q.Ring⁄R₀]).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl B B)
      (_root_.TensorProduct.lidOfCompatibleSMul P.Ring Q.Ring Ω[Q.Ring⁄R₀])

/-- Helper for Lemma 10.149.5: the scalar-descent equivalence sends a pure tensor `b ⊗ m` to the
same pure tensor after changing the tensor base to `Q.Ring`. -/
theorem sourceAlgEquiv_tensorKaehler_desc_tmul
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    [Algebra P.Ring Q.Ring] [IsScalarTower R₀ P.Ring Q.Ring] [IsScalarTower P.Ring Q.Ring B]
    (hPQ : Function.Surjective (algebraMap P.Ring Q.Ring))
    (b : B) (m : Ω[Q.Ring⁄R₀]) :
    sourceAlgEquiv_tensorKaehler_desc (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q) hPQ
        (b ⊗ₜ[P.Ring] m) =
      b ⊗ₜ[Q.Ring] m := by
  let _ : IsScalarTower P.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_kaehler_isScalarTower (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
  let _ : CompatibleSMul P.Ring Q.Ring Q.Ring Ω[Q.Ring⁄R₀] :=
    CompatibleSMul.of_algebraMap_surjective
      (R := P.Ring) (A := Q.Ring) (M := Q.Ring) (N := Ω[Q.Ring⁄R₀]) hPQ
  -- Proof comment: both constituent equivalences have explicit pure-tensor formulas, so the
  -- composite reduces immediately to the same tensor over the smaller base ring.
  simp only [sourceAlgEquiv_tensorKaehler_desc, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, _root_.TensorProduct.lidOfCompatibleSMul_tmul, one_smul]

/-- Helper for Lemma 10.149.5: after installing the `P.Ring`-algebra structure on `Q.Ring`
coming from the comparison equivalence, the maps `R₀ → P.Ring → Q.Ring` form a scalar tower. -/
lemma sourceAlgEquiv_isScalarTower_base
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    IsScalarTower R₀ P.Ring Q.Ring := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  -- Proof comment: the comparison equivalence carries the `R₀`-structure map of `P.Ring` to that
  -- of `Q.Ring`.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  simpa using (sourceAlgEquiv_commutes_base (A := A) (B := B) (R₀ := R₀) e x).symm

/-- Helper for Lemma 10.149.5: after installing the `P.Ring`-algebra structure on `Q.Ring`
coming from the comparison equivalence, the compatibility square with `B` gives the scalar tower
`P.Ring → Q.Ring → B`. -/
lemma sourceAlgEquiv_isScalarTower_target
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    IsScalarTower P.Ring Q.Ring B := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  -- Proof comment: the commuting square says exactly that the two maps `P.Ring → B` agree.
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  simpa using (AlgHom.congr_fun he x).symm

/-- Helper for Lemma 10.149.5: the owner Kähler map induced by an `A`-algebra equivalence of
extension rings is bijective. -/
lemma sourceAlgEquiv_kaehler_map_bijective
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring) :
    let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
    let _ : IsScalarTower R₀ P.Ring Q.Ring :=
      sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
    Function.Bijective (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring) := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ P.Ring Q.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
  let _ : Algebra Q.Ring P.Ring := e.symm.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ Q.Ring P.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e.symm
  let _ : IsScalarTower P.Ring Q.Ring P.Ring := by
    -- Proof comment: with the source and target algebra structures coming from `e` and `e.symm`,
    -- the two-step action `P.Ring → Q.Ring → P.Ring` is literally the identity.
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change x = e.symm (e x)
    simp
  let f : Ω[P.Ring⁄R₀] →ₗ[P.Ring] Ω[Q.Ring⁄R₀] :=
    KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring
  let g : Ω[Q.Ring⁄R₀] →ₗ[Q.Ring] Ω[P.Ring⁄R₀] :=
    KaehlerDifferential.map R₀ R₀ Q.Ring P.Ring
  have hleftMap : (g.restrictScalars P.Ring).comp f = LinearMap.id := by
    -- Proof comment: both endomorphisms of `Ω[P.Ring⁄R₀]` have the same composite with the
    -- universal derivation, so uniqueness of lifts from Kähler differentials identifies them.
    apply Derivation.liftKaehlerDifferential_unique
    ext x
    simpa [LinearMap.comp_apply, f, g, KaehlerDifferential.map_D] using
      congrArg (KaehlerDifferential.D R₀ P.Ring) (by
        change (algebraMap Q.Ring P.Ring) ((algebraMap P.Ring Q.Ring) x) = x
        change e.symm (e x) = x
        simp)
  have hleft : Function.LeftInverse (g.restrictScalars P.Ring) f := by
    intro x
    exact LinearMap.congr_fun hleftMap x
  -- Proof comment: surjectivity is the standard surjective-algebra-map statement because the
  -- installed `P.Ring → Q.Ring` algebra map is exactly the equivalence `e`.
  refine ⟨hleft.injective, ?_⟩
  simpa [f] using
    (KaehlerDifferential.map_surjective_of_surjective R₀ R₀ P.Ring Q.Ring
      (show Function.Surjective (algebraMap P.Ring Q.Ring) from e.surjective))

/-- Helper for Lemma 10.149.5: two `B`-linear maps out of the base-changed module
`B ⊗[A] Ω[A⁄R₀]` agree once they agree on the generators `1 ⊗ d a`. -/
lemma tensorBaseChange_currying_ext
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [Module R₀ M]
    [IsScalarTower A B M] [IsScalarTower R₀ A M]
    {f g : B ⊗[A] Ω[A⁄R₀] →ₗ[B] M}
    (h : ∀ a : A,
      f (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a) =
        g (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a)) :
    f = g := by
  let f₁ : Ω[A⁄R₀] →ₗ[A] M :=
    TensorProduct.AlgebraTensorModule.curry f 1
  let g₁ : Ω[A⁄R₀] →ₗ[A] M :=
    TensorProduct.AlgebraTensorModule.curry g 1
  have h₁ : f₁ = g₁ := by
    -- Proof comment: after currying, Kähler differentials are generated by the classes `d a`, so
    -- equality on those generators forces equality of the two `A`-linear maps.
    have hcomp :
        f₁.compDer (KaehlerDifferential.D R₀ A) =
          g₁.compDer (KaehlerDifferential.D R₀ A) := by
      ext a
      simpa [f₁, g₁, TensorProduct.AlgebraTensorModule.curry_apply] using h a
    exact Derivation.liftKaehlerDifferential_unique _ _ hcomp
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      -- Proof comment: both maps are linear, so they agree at `0`.
      simp
  | add z w hz hw =>
      -- Proof comment: additivity reduces the sum case to the induction hypotheses.
      simp [hz, hw]
  | tmul b η =>
      have hη : f ((1 : B) ⊗ₜ[A] η) = g ((1 : B) ⊗ₜ[A] η) := by
        simpa [f₁, g₁, TensorProduct.AlgebraTensorModule.curry_apply] using
          LinearMap.congr_fun h₁ η
      -- Proof comment: every pure tensor is a `B`-multiple of a generator `1 ⊗ η`, so the
      -- curried equality at `1` upgrades to equality on all pure tensors.
      calc
        f (b ⊗ₜ[A] η) = f (b • ((1 : B) ⊗ₜ[A] η)) := by
          rw [TensorProduct.tmul_eq_smul_one_tmul]
        _ = b • f ((1 : B) ⊗ₜ[A] η) := by rw [LinearMap.map_smul]
        _ = b • g ((1 : B) ⊗ₜ[A] η) := by rw [hη]
        _ = g (b • ((1 : B) ⊗ₜ[A] η)) := by rw [LinearMap.map_smul]
        _ = g (b ⊗ₜ[A] η) := by
          rw [← TensorProduct.tmul_eq_smul_one_tmul (R := A) b η]

/-- Helper for Lemma 10.149.5: an `A`-algebra equivalence of extension rings over `B` induces the
corresponding `B`-linear equivalence on the base-changed `R`-relative Kähler modules, and this
equivalence intertwines the canonical maps from `Ω[A⁄R]`. -/
theorem universalFirstOrderThickening_kaehlerBaseChange_codomain_transport
    (R₀ : Type u) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ B] [IsScalarTower R₀ A B]
    {P : Extension.{x} A B} {Q : Extension.{y} A B}
    (e : P.Ring ≃ₐ[A] Q.Ring)
    (he :
      (IsScalarTower.toAlgHom A Q.Ring B).comp e.toAlgHom =
        IsScalarTower.toAlgHom A P.Ring B) :
    ∃ E : B ⊗[P.Ring] Ω[P.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀],
      E.toLinearMap ∘ₗ universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P =
        universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q := by
  let _ : Algebra P.Ring Q.Ring := e.toAlgHom.toAlgebra
  let _ : IsScalarTower R₀ P.Ring Q.Ring :=
    sourceAlgEquiv_isScalarTower_base (A := A) (B := B) (R₀ := R₀) e
  let _ : IsScalarTower P.Ring Q.Ring B :=
    sourceAlgEquiv_isScalarTower_target (A := A) (B := B) e he
  let eΩ : Ω[P.Ring⁄R₀] ≃ₗ[P.Ring] Ω[Q.Ring⁄R₀] :=
    LinearEquiv.ofBijective
      (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring)
      (sourceAlgEquiv_kaehler_map_bijective (A := A) (B := B) (R₀ := R₀) e)
  let E₀ : B ⊗[P.Ring] Ω[P.Ring⁄R₀] ≃ₗ[B] B ⊗[P.Ring] Ω[Q.Ring⁄R₀] :=
    AlgebraTensorModule.congr (.refl B B) eΩ
  let E₁ : B ⊗[P.Ring] Ω[Q.Ring⁄R₀] ≃ₗ[B] B ⊗[Q.Ring] Ω[Q.Ring⁄R₀] :=
    sourceAlgEquiv_tensorKaehler_desc (A := A) (B := B) (R₀ := R₀) (P := P) (Q := Q)
      (by simpa using e.surjective)
  refine ⟨E₀.trans E₁, ?_⟩
  -- Route correction: after packaging the owner equivalence on Kähler differentials, the
  -- conjugation check reduces to the universal generators `1 ⊗ d a`.
  apply tensorBaseChange_currying_ext (A := A) (B := B) (R₀ := R₀)
  intro a
  have hmap :
      eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) =
        KaehlerDifferential.D R₀ Q.Ring
          ((algebraMap P.Ring Q.Ring) (algebraMap A P.Ring a)) := by
    -- The owner equivalence is defined by the Kähler map induced from `e`.
    change (KaehlerDifferential.map R₀ R₀ P.Ring Q.Ring)
        (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) = _
    simpa using (KaehlerDifferential.map_D R₀ R₀ P.Ring Q.Ring (algebraMap A P.Ring a))
  calc
    (E₀.trans E₁)
        (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ P
          (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a))
        = E₁ (E₀ (1 ⊗ₜ[P.Ring]
            KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a))) := by
              simp [E₀, E₁, universalFirstOrderThickening_kaehlerBaseChangeLinearMap]
    _ = E₁ (1 ⊗ₜ[P.Ring]
          eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a))) := by
            simp [E₀, AlgebraTensorModule.congr_tmul]
    _ = 1 ⊗ₜ[Q.Ring]
          eΩ (KaehlerDifferential.D R₀ P.Ring (algebraMap A P.Ring a)) := by
            simp [E₁, sourceAlgEquiv_tensorKaehler_desc_tmul]
    _ = 1 ⊗ₜ[Q.Ring]
          KaehlerDifferential.D R₀ Q.Ring
            ((algebraMap P.Ring Q.Ring) (algebraMap A P.Ring a)) := by
              rw [hmap]
    _ = 1 ⊗ₜ[Q.Ring]
          KaehlerDifferential.D R₀ Q.Ring (algebraMap A Q.Ring a) := by
            congr 2
            exact sourceAlgEquiv_commutes_base (A := A) (B := B) (R₀ := A) e a
    _ = universalFirstOrderThickening_kaehlerBaseChangeLinearMap R₀ Q
          (1 ⊗ₜ[A] KaehlerDifferential.D R₀ A a) := by
            simp [universalFirstOrderThickening_kaehlerBaseChangeLinearMap]

/-- Helper for Lemma 10.149.5: the canonical self-presentation quotient satisfies the textbook
base-changed Kähler-differential isomorphism. -/
theorem selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective
    (R : Type u) [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
    [FormallyUnramified A B]
    (l : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A B).toExtension.Cotangent)
    (hl : (Generators.self A B).toExtension.cotangentComplex ∘ₗ l = LinearMap.id) :
    Function.Bijective
      (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R
        (selfPresentation_section_quotient (R := A) (S := B) l)) := by
  -- Route correction: the remaining source-faithful work is the literal quotient-ring computation
  -- from the textbook, namely that after tensoring the `R`-relative conormal sequence with `B`,
  -- the section-generator image fills the polynomial `dx`-summand and the residual `J²`-piece dies.
  sorry

variable (R) (P)

-- Proof sketch: use the canonical Jacobi-Zariski/transitivity maps for `R → A → P.Ring → B`.
-- Route correction: the owner-level route through `KaehlerDifferential.mapBaseChange R A P.Ring`
-- alone is too strong. The remaining proof has to follow the Stacks presentation argument on the
-- canonical self-presentation quotient, then transport bijectivity back to `P`.
/-- Lemma 10.149.5 (2), companion owner-level statement: the canonical base-changed comparison map
on Kähler differentials attached to a universal first-order thickening is bijective. -/
theorem universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    Function.Bijective (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P) := by
  obtain ⟨l, hl⟩ := selfPresentation_cotangentComplex_has_section (R := A) (S := B)
  obtain ⟨e, he⟩ :=
    universalFirstOrderThickening_selfPresentation_equiv
      (P := P) hP l hl
  have hQ :
      Function.Bijective
        (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R
          (selfPresentation_section_quotient (R := A) (S := B) l)) :=
    selfPresentation_section_quotient_kaehlerBaseChangeLinearMap_bijective
      (R := R) (A := A) (B := B) l hl
  obtain ⟨E, hE⟩ :=
    universalFirstOrderThickening_kaehlerBaseChange_codomain_transport
      (A := A) (B := B) (R₀ := R) e he
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hQ.1
    calc
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap R
          (selfPresentation_section_quotient (R := A) (S := B) l) x =
        E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P x) := by
          symm
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hE x
      _ = E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P y) := by
          rw [hxy]
      _ =
        universalFirstOrderThickening_kaehlerBaseChangeLinearMap R
          (selfPresentation_section_quotient (R := A) (S := B) l) y := by
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hE y
  · intro z
    obtain ⟨x, hx⟩ := hQ.2 (E z)
    refine ⟨x, E.injective ?_⟩
    calc
      E (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P x) =
        universalFirstOrderThickening_kaehlerBaseChangeLinearMap R
          (selfPresentation_section_quotient (R := A) (S := B) l) x := by
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun hE x
      _ = E z := hx

/-- Lemma 10.149.5 (2): in the library-facing tensor order, the canonical base-changed map
`B ⊗[A] Ω[A⁄R] → B ⊗[B'] Ω[B'⁄R]` attached to a universal first-order thickening `B'`
induces a `B`-linear isomorphism. -/
noncomputable def universalFirstOrderThickening_kaehlerBaseChange
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  LinearEquiv.ofBijective
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P)
    (universalFirstOrderThickening_kaehlerBaseChangeLinearMap_bijective
      (R := R) (P := P) hP)

@[simp] theorem universalFirstOrderThickening_kaehlerBaseChange_toLinearMap
    {P : Extension.{x} A B}
    (hP : @IsUniversalFirstOrderThickening.{v, w, max x (max v w), _} A _ B _ _ P)
    [FormallyUnramified A B] :
    (universalFirstOrderThickening_kaehlerBaseChange (R := R) (P := P) hP).toLinearMap =
      universalFirstOrderThickening_kaehlerBaseChangeLinearMap R P :=
  by
    ext x
    rfl

end Algebra.Extension
