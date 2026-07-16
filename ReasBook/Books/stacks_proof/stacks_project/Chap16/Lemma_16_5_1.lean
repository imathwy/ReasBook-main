import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_126_9
import stacks_proof.stacks_project.Chap10.Lemma_10_147_5
import stacks_proof.stacks_project.Chap15.Lemma_15_94_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- Helper for Lemma 16.5.1: a smooth `CommRingCat` stage is finitely presentable as a morphism
for the categorical owner used by `MorphismProperty.ind`. -/
lemma commRingCatIsFinitelyPresentableHom_of_smooth
    {X Y : CommRingCat.{max u v w}} (f : X ⟶ Y)
    (hf : (RingHom.toMorphismProperty RingHom.Smooth) f) :
    CategoryTheory.MorphismProperty.isFinitelyPresentable.{max (max u v) w,
      max (max u v) w, max (max u v) w + 1} CommRingCat f := by
  -- Proof comment: smooth ring maps are finitely presented, and `CommRingCat` already packages
  -- finitely presented ring maps as finitely presentable arrows in the under-category.
  exact CommRingCat.isFinitelyPresentable_hom f hf.finitePresentation

/-- Helper for Lemma 16.5.1: any ideal contained in the extension of a square-zero ideal is again
square-zero. -/
lemma idealSquareZero_of_le_map_of_squareZero {B : Type*} [CommRing B] [Algebra R B]
    (I : Ideal R) (J : Ideal B) (hSq : I ^ 2 = ⊥) (hJ : J ≤ I.map (algebraMap R B)) :
    J ^ 2 = ⊥ := by
  -- Proof comment: compare the square of `J` with the square of the extended ideal `IB`.
  refine le_antisymm ?_ bot_le
  calc
    J ^ 2 ≤ (I.map (algebraMap R B)) ^ 2 := Ideal.pow_right_mono hJ 2
    _ = Ideal.map (algebraMap R B) (I ^ 2) := by
      rw [Ideal.map_pow]
    _ = ⊥ := by
      rw [hSq, Ideal.map_bot]

/-- Helper for Lemma 16.5.1: factor the reduced map through one smooth stage of the filtered
colimit presentation of `Λ ⧸ IΛ`. -/
lemma quotientStageFactorization
    (I : Ideal R)
    [FinitePresentation (R ⧸ I) (A ⧸ I.map (algebraMap R A))]
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ₀ : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ)) :
    ∃ (Bbar : Type (max u v w)) (_ : CommRing Bbar) (_ : Algebra (R ⧸ I) Bbar)
      (_ : Smooth (R ⧸ I) Bbar)
      (fbar : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] Bbar)
      (gbar : Bbar →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ)),
      gbar.comp fbar = φ₀ := by
  -- TODO(Chap16 Lemma 16 5 1): follow the existing `ULift` + `MorphismProperty.ind_iff_exists`
  -- descent pattern from `Lemma_16_4_6` / `Lemma_16_14_1`.
  -- Route correction: the current blocker is a universe-level transport failure when packaging
  -- the reduced arrow inside `CommRingCat.ofHom`. The filtered-colimit witness for
  -- `algebraMap (R ⧸ I) (Λ ⧸ IΛ)` lives over smaller lifted source/target rings than the larger
  -- ambient `CommRingCat` universe needed to mention `A ⧸ IA`. A reusable bridge lemma should
  -- transport `MorphismProperty.ind` across the canonical `ULift` ring equivalences before
  -- applying `ind_iff_exists`.
  sorry

/-- Helper for Lemma 16.5.1: finite presentation survives passage to the quotient by `I`. -/
lemma quotientFinitePresentation
    (I : Ideal R) [FinitePresentation R A] :
    FinitePresentation (R ⧸ I) (A ⧸ I.map (algebraMap R A)) := by
  -- Proof comment: identify `A / IA` with the base change `(R / I) ⊗[R] A`, then reuse the
  -- canonical base-change stability of finite presentation.
  let e :
      (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] A :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := R) (B := A) I
  exact Algebra.FinitePresentation.equiv e.symm

/-- Helper for Chap16 Lemma 16 5 1: the extension of `I` to the source algebra always maps into
the pullback ideal coming from the target extension `I S'`. -/
lemma extendedIdeal_le_comap_extendedIdeal
    {S : Type*} {S' : Type*} [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S']
    (I : Ideal R) (f : S →ₐ[R] S') :
    Ideal.map (algebraMap R S) I ≤ Ideal.comap f.toRingHom (Ideal.map (algebraMap R S') I) := by
  -- Proof comment: after restricting along `R → S`, the target containment is just the algebra-map
  -- compatibility of `f`.
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f ((algebraMap R S) x) ∈ Ideal.map (algebraMap R S') I
  simpa using Ideal.mem_map_of_mem (algebraMap R S') hx

/-- Helper for Chap16 Lemma 16 5 1: once a map is surjective after quotienting by a square-zero
extended ideal, it is already surjective upstairs. -/
lemma surjectiveOfReducedSurjectiveForSquareZeroLift
    {S : Type*} {S' : Type*} [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] [FiniteType R S']
    (I : Ideal R) (hSq : I ^ 2 = ⊥) (f : S →ₐ[R] S')
    (hquot :
      Function.Surjective ((Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)).comp f)) :
    Function.Surjective f := by
  -- Proof comment: square-zero implies local nilpotence, so the Chapter 10 quotient-surjectivity
  -- upgrade applies directly to `f`.
  have hIloc : I.IsLocallyNilpotent :=
    ideal_isLocallyNilpotent_of_sq_eq_bot I hSq
  exact surjective_of_surjective_quotient_of_finiteType_of_locallyNilpotent hIloc f hquot

/-- Helper for Chap16 Lemma 16 5 1: if the reduced quotient map attached to `f` is injective, then
every element of `ker f` already lies in the source extension `I S`. -/
lemma ker_le_mappedIdeal_of_reducedInjective
    {S : Type*} {S' : Type*} [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S']
    (I : Ideal R) (f : S →ₐ[R] S')
    (hquotInj :
      Function.Injective
        (Ideal.quotientMapₐ (R₁ := R) (J := Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal (R := R) I f))) :
    RingHom.ker f.toRingHom ≤ Ideal.map (algebraMap R S) I := by
  intro x hx
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hquotInj
  -- Proof comment: apply injectivity after identifying the quotient map on the class of `x`
  -- with the class of `f x`, which vanishes because `x ∈ ker f`.
  have hmap :
      (Ideal.quotientMapₐ (R₁ := R) (J := Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal (R := R) I f))
          (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S) I) x)
        =
      (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S') I)) (f x) := by
    simpa using
      congrArg
        (fun g : S →ₐ[R] S' ⧸ Ideal.map (algebraMap R S') I ↦ g x)
        (Ideal.quotient_map_comp_mkₐ
          (R₁ := R) (I := Ideal.map (algebraMap R S) I)
          (J := Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal (R := R) I f))
  change
    (Ideal.quotientMapₐ (R₁ := R) (J := Ideal.map (algebraMap R S') I) f
        (extendedIdeal_le_comap_extendedIdeal (R := R) I f))
        (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R S) I) x)
      =
    (Ideal.quotientMapₐ (R₁ := R) (J := Ideal.map (algebraMap R S') I) f
        (extendedIdeal_le_comap_extendedIdeal (R := R) I f))
        0
  rw [hmap]
  rw [RingHom.mem_ker] at hx
  have hfx : f x = 0 := hx
  simpa [hfx]

/- Domain-style sampling for smooth quotient factorizations over a square-zero ideal:
* primary domain: commutative algebra of smooth `R`-algebras, quotient algebras, and finite
  presentation factorization through filtered colimits of smooth quotients;
* sampled owner declarations:
  `Smooth R B`,
  `RingHom.IsFilteredColimitOfSmooth`,
  `exists_smooth_factorization_of_singularIdeal_map_eq_top`,
  `exists_smooth_lift_of_quotient`;
* best owner abstraction: this item is not a new packaged object; its canonical public surface is
  the direct existence of a smooth `R`-algebra `B`, an ideal `J : Ideal B`, and the quotient
  factorization `A →ₐ[R] B ⧸ J →ₐ[R] Λ`.

Source/core/bridge triage:
* `source-facing`: the existence theorem below, matching Lemma `16.5.1`;
* `core/canonical`: `Smooth`, `Ideal`, quotient algebras `B ⧸ J`, and
  `RingHom.IsFilteredColimitOfSmooth`;
* `bridge/view`: the explicit quotient-stage factorization maps into and out of `B ⧸ J`.

Primitive output data are exactly `B`, `J`, the canonical owner hypotheses on `B` and `J`, and
the two algebra maps exhibiting the factorization. A separate wrapper structure would only
repackage those primitives without adding mathematical content, so the theorem exposes the direct
existential data instead.
-/

-- Proof sketch: factor the induced map `A ⧸ IA → Λ ⧸ IΛ` through a smooth `(R ⧸ I)`-algebra using
-- the filtered-colimit hypothesis and finite presentation. Lift that smooth quotient algebra to a
-- smooth `R`-algebra, then use formal smoothness across the square-zero extension `I² = 0` to map
-- the lift into a polynomial enlargement of `Λ`. Finally, rewrite the resulting surjection as a
-- quotient `B ⧸ J` with `J ⊆ IB` finitely generated via Nakayama and finite presentation.
/-- Lemma 16.5.1: if `I ⊂ R` is square-zero, if the quotient map
`R ⧸ I → Λ ⧸ IΛ` is a filtered colimit of smooth `(R ⧸ I)`-algebras, and if `φ : A → Λ` is an
`R`-algebra map with `A` of finite presentation over `R`, then `φ` factors as
`A → B ⧸ J → Λ` with `B` smooth over `R` and `J ⊆ IB` finitely generated. -/
@[stacks 07CK]
theorem exists_smooth_quotient_factorization_of_square_zero
    (I : Ideal R) [FinitePresentation R A] (hSq : I ^ 2 = ⊥)
    (hcolim : (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IsFilteredColimitOfSmooth)
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (J : Ideal B) (_ : J ≤ I.map (algebraMap R B)) (_ : J.FG)
      (f : A →ₐ[R] B ⧸ J) (g : B ⧸ J →ₐ[R] Λ),
      g.comp f = φ := by
  -- Proof comment: first work modulo `I` and isolate one smooth quotient stage of the target.
  let A₀ := A ⧸ I.map (algebraMap R A)
  let Λ₀ := Λ ⧸ I.map (algebraMap R Λ)
  have hIA :
      I.map (algebraMap R A) ≤ Ideal.comap φ.toRingHom (I.map (algebraMap R Λ)) := by
    intro x hx
    have hx' : φ x ∈ Ideal.map φ.toRingHom (I.map (algebraMap R A)) :=
      Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_map] at hx'
    simpa [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hx'
  let φ₀ : A₀ →ₐ[R] Λ₀ :=
    Ideal.quotientMapₐ (R₁ := R) (J := I.map (algebraMap R Λ)) φ hIA
  have hφ₀ :
      φ₀.comp (Ideal.Quotient.mkₐ R (I.map (algebraMap R A))) =
        (Ideal.Quotient.mkₐ R (I.map (algebraMap R Λ))).comp φ := by
    -- Proof comment: this is the defining computation rule for the quotient map attached to `φ`.
    simpa [A₀, Λ₀, φ₀] using
      (Ideal.quotient_map_comp_mkₐ (R₁ := R) (J := I.map (algebraMap R Λ)) φ hIA)
  -- Route correction: the reduced quotient map is now explicit. The first remaining blocker is
  -- the reduced finite-presentation bridge `FinitePresentation (R ⧸ I) A₀`. The reduced map
  -- itself can already be packaged as an `(R ⧸ I)`-algebra map, which is the first setup fact
  -- needed before `quotientStageFactorization` can be applied.
  let φ₀Red : A₀ →ₐ[R ⧸ I] Λ₀ :=
    { toRingHom := φ₀.toRingHom
      commutes' := by
        intro r
        refine Quotient.inductionOn' r ?_
        intro r
        change φ₀ ((algebraMap R A₀) r) = (algebraMap R Λ₀) r
        simpa using φ₀.commutes r }
  -- Route correction: the reduced quotient map is now packaged as an `(R ⧸ I)`-algebra map.
  -- The first stable prefix is now to extract one smooth reduced stage before constructing the
  -- source-style correction algebra directly from a finite presentation over `A₀`.
  let _ : FinitePresentation (R ⧸ I) A₀ := quotientFinitePresentation (R := R) (A := A) I
  obtain ⟨Bbar, _, _, hBbarSmooth, fbar, gbar, hgbar⟩ :=
    quotientStageFactorization (R := R) (A := A) (Λ := Λ) (I := I) hcolim φ₀Red
  let _ : Smooth (R ⧸ I) Bbar := hBbarSmooth
  -- Route correction: the reduced stage `A₀ → Bbar → Λ₀` is now fixed.
  -- The remaining blocker is the correction algebra `A'` over `A`. The stable route is to take a
  -- pullback-style intermediary over `gbar : Bbar →ₐ[R ⧸ I] Λ₀` and `Λ →ₐ[R] Λ₀`, then prove that
  -- this ring is finitely presented over `R` and that its reduction is exactly `Bbar`.
  let _ := fbar
  let _ := gbar
  let _ := hgbar
  -- TODO(Lemma 16.5.1): construct a finitely presented correction algebra
  -- `A' = Bbar ×_{Λ₀} Λ` together with `A →ₐ[R] A' →ₐ[R] Λ`, prove `(A' ⧸ I A') ≃ₐ[R ⧸ I] Bbar`,
  -- lift `A' / I A'` to a smooth `R`-algebra `B`, and then apply
  -- `surjectiveOfReducedSurjectiveForSquareZeroLift` together with
  -- `ker_le_mappedIdeal_of_reducedInjective` to finish the quotient-by-kernel package.
  sorry

end

end Algebra
