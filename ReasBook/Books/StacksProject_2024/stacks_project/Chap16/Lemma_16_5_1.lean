import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_147_5

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
  let R0u := ULift.{max u v w, u} (R ⧸ I)
  let A0u := ULift.{max u v w, v} (A ⧸ I.map (algebraMap R A))
  let Λ0u := ULift.{max u v w, w} (Λ ⧸ I.map (algebraMap R Λ))
  let _ : Algebra (A ⧸ I.map (algebraMap R A)) (Λ ⧸ I.map (algebraMap R Λ)) := φ₀.toAlgebra
  let _ : Algebra A0u Λ0u := ULift.algebra' (A ⧸ I.map (algebraMap R A)) Λ0u
  let _ : Algebra (R ⧸ I) A0u := ULift.algebra
  let _ : Algebra R0u A0u := ULift.algebra' (R ⧸ I) A0u
  let _ : Algebra (R ⧸ I) Λ0u := ULift.algebra
  let _ : Algebra R0u Λ0u := ULift.algebra' (R ⧸ I) Λ0u
  have hp :
      CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat
        (CommRingCat.ofHom
          (algebraMap R0u A0u)) := by
    -- Proof comment: finite presentation of the reduced source algebra is exactly the
    -- finite-presentability condition needed by `MorphismProperty.ind_iff_exists`.
    simpa using
      (CommRingCat.isFinitelyPresentable_hom
        (CommRingCat.ofHom (algebraMap R0u A0u))
        (by infer_instance))
  have hpg :
      CommRingCat.ofHom
          (algebraMap R0u A0u) ≫
        CommRingCat.ofHom
          (algebraMap A0u Λ0u) =
      CommRingCat.ofHom
        (algebraMap R0u Λ0u) := by
    -- Proof comment: the lifted reduced quotient map is an `(R ⧸ I)`-algebra map, so the two
    -- structure maps compose exactly to the lifted target algebra map.
    apply CommRingCat.hom_ext_iff.mpr
    intro x
    rfl
  have huliftColim :
      CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom
          (algebraMap R0u Λ0u)) := by
    -- Proof comment: unwrap the source-facing filtered-colimit hypothesis once so the
    -- factorization criterion can be applied to the lifted reduced source map.
    simpa [RingHom.IsFilteredColimitOfSmooth] using hcolim
  obtain ⟨B, u, v, huv, hSmoothStage⟩ :=
    ((CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.Smooth)
      (H := commRingCatIsFinitelyPresentableHom_of_smooth)
      (CommRingCat.ofHom
        (algebraMap R0u Λ0u))).1 huliftColim)
      (CommRingCat.ofHom
        (algebraMap R0u A0u))
      (CommRingCat.ofHom
        (algebraMap A0u Λ0u))
      hp hpg
  let sourceToB : R0u →+* B :=
    u.hom.comp (algebraMap R0u A0u)
  have hsourceToBSmooth : sourceToB.Smooth := by
    -- Proof comment: the stage extracted from `ind_iff_exists` is smooth over the lifted base.
    simpa [sourceToB, RingHom.toMorphismProperty, CommRingCat.hom_comp] using hSmoothStage
  let fR : (R ⧸ I) →+* R0u :=
    (ULift.ringEquiv.symm : (R ⧸ I) ≃+* R0u).toRingHom
  let _ : Algebra (R ⧸ I) B := (sourceToB.comp fR).toAlgebra
  have hsourceSmooth : (algebraMap (R ⧸ I) B).Smooth := by
    -- Proof comment: smoothness is preserved when we descend along the bijective source
    -- equivalence `(R ⧸ I) ≃ ULift (R ⧸ I)`.
    let hbase : fR.Smooth :=
      RingHom.Smooth.of_bijective
        (ULift.ringEquiv.symm : (R ⧸ I) ≃+* R0u).bijective
    simpa [sourceToB, fR, RingHom.algebraMap_toAlgebra] using
      RingHom.Smooth.comp hbase hsourceToBSmooth
  have hBSmooth : Smooth (R ⧸ I) B := by
    simpa [RingHom.smooth_algebraMap] using hsourceSmooth
  let fA : A ⧸ I.map (algebraMap R A) →+* A0u :=
    (ULift.ringEquiv.symm : (A ⧸ I.map (algebraMap R A)) ≃+* A0u).toRingHom
  have hAlphaComm :
      ∀ r : R ⧸ I,
        (u.hom.comp fA) (algebraMap (R ⧸ I) (A ⧸ I.map (algebraMap R A)) r) =
          algebraMap (R ⧸ I) B r := by
    -- Proof comment: the descended source map `fbar` respects the transported base-algebra
    -- structure because `u` lies over the lifted base map.
    intro r
    simp [sourceToB, fR, fA, RingHom.algebraMap_toAlgebra]
  let fbar : A ⧸ I.map (algebraMap R A) →ₐ[R ⧸ I] B :=
    { toRingHom := u.hom.comp fA
      commutes' := hAlphaComm }
  let betaDown :
      Λ0u →+*
        Λ ⧸ I.map (algebraMap R Λ) :=
    (ULift.ringEquiv : Λ0u ≃+*
      Λ ⧸ I.map (algebraMap R Λ)).toRingHom
  have hsourceComp :
      v.hom.comp sourceToB =
        algebraMap R0u Λ0u := by
    -- Proof comment: the extracted stage still maps to the lifted quotient target through the
    -- original lifted reduced map.
    ext r
    have huvr :=
      congrArg
        (fun ψ :
          CommRingCat.of A0u ⟶ CommRingCat.of Λ0u ↦
          ψ.hom ((algebraMap R0u A0u) r))
        huv
    have hpgr :=
      congrArg
        (fun ψ :
          CommRingCat.of R0u ⟶ CommRingCat.of Λ0u ↦
          ψ.hom r)
        hpg
    calc
      v.hom (sourceToB r) =
          (algebraMap A0u Λ0u) ((algebraMap R0u A0u) r) := by
              simpa [sourceToB, CommRingCat.hom_comp] using huvr
      _ = (algebraMap R0u Λ0u) r := by
            simpa [CommRingCat.hom_comp] using hpgr
  have hBetaComm :
      ∀ r : R ⧸ I,
        (betaDown.comp v.hom) (algebraMap (R ⧸ I) B r) =
          algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) r := by
    -- Proof comment: the descended target map `gbar` remains an `(R ⧸ I)`-algebra map because
    -- the lifted source map still composes to the canonical lifted quotient map.
    intro r
    have hcompR := DFunLike.congr_fun hsourceComp (ULift.up r)
    simpa [sourceToB, fR, RingHom.algebraMap_toAlgebra] using congrArg ULift.down hcompR
  let gbar : B →ₐ[R ⧸ I] Λ ⧸ I.map (algebraMap R Λ) :=
    { toRingHom := betaDown.comp v.hom
      commutes' := hBetaComm }
  have hgf : gbar.comp fbar = φ₀ := by
    -- Proof comment: evaluate the lifted factorization on each reduced source element, then erase
    -- the `ULift` wrappers on source and target.
    ext x
    have huvx :=
      congrArg
        (fun ψ :
          CommRingCat.of A0u ⟶ CommRingCat.of Λ0u ↦
          ψ.hom (ULift.up x))
        huv
    simpa [fbar, gbar, fA, betaDown, CommRingCat.hom_comp] using congrArg ULift.down huvx
  exact ⟨B, inferInstance, inferInstance, hBSmooth, fbar, gbar, hgf⟩

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
  -- The remaining blocker is the explicit correction algebra `A'` that should lift `fbar` and
  -- map to `Λ`; once `A' / IA' ≃ Bbar` is built, the source proof can choose a standard smooth
  -- lift `B` directly from a lifted Jacobian presentation, without depending on broken imports.
  let _ := fbar
  let _ := gbar
  let _ := hgbar
  -- TODO(Lemma 16.5.1): build the correction algebra `A'` from a finite presentation of the
  -- reduced smooth stage over `A₀`, produce `A →ₐ[R] A' →ₐ[R] Λ` reducing to `fbar` and `gbar`,
  -- choose a standard smooth lift `B` of `A' / IA'`, and finish with the quotient-by-kernel
  -- argument.
  sorry

end

end Algebra
