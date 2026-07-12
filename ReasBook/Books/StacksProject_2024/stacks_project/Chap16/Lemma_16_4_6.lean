import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_127_1
import StacksProject_2024.Chap10.Lemma_10_127_4
import StacksProject_2024.Chap10.Lemma_10_147_5
import StacksProject_2024.Chap10.Lemma_10_140_9
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap16.Situation_16_4_1
import StacksProject_2024.Chap16.Lemma_16_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open IsLocalRing

universe u

namespace Algebra

section

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
variable [Algebra R Λ] [_root_.IsExtensionOfDiscreteValuationRings R Λ]

/-- Helper for Lemma 16.4.6: a smooth stage over the target is automatically finitely presented
over the base DVR. -/
lemma finitePresentation_of_smoothOverTarget
    (A : Over (CommAlgCat.of R Λ))
    (hA : Smooth R A.left) :
    Algebra.FinitePresentation R A.left := by
  -- Proof comment: smoothness already carries the finite-presentation owner instance.
  letI : Smooth R A.left := hA
  infer_instance

/-- Helper for Lemma 16.4.6: quotienting an algebra map by its kernel gives the canonical
injective comparison into the target DVR. -/
lemma quotientKerLift_injective
    {A : Type u} [CommRing A] [Algebra R A] (φ : A →ₐ[R] Λ) :
    Function.Injective (Ideal.kerLiftAlg φ) := by
  -- Proof comment: the quotient-by-kernel comparison is exactly `Ideal.kerLiftAlg`.
  simpa using (Ideal.kerLiftAlg_injective φ)

/-- Helper for Lemma 16.4.6: the quotient-by-kernel comparison agrees with the original map on
representatives. -/
@[simp] lemma quotientKerLift_mk
    {A : Type u} [CommRing A] [Algebra R A] (φ : A →ₐ[R] Λ) (x : A) :
    Ideal.kerLiftAlg φ (Ideal.Quotient.mk _ x) = φ x := by
  -- Proof comment: this is the defining computation rule for `Ideal.kerLiftAlg`.
  simpa using (Ideal.kerLiftAlg_mk φ x)

/-- Helper for Lemma 16.4.6: quotienting a finitely presented `R`-algebra by the kernel of a map
to `Λ` preserves finite presentation over the base DVR. -/
lemma finitePresentation_quotientKer
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    Algebra.FinitePresentation R (A ⧸ RingHom.ker φ.toRingHom) := by
  -- Proof comment: finite presentation implies finite type, hence the target ring is Noetherian;
  -- once the kernel ideal is finitely generated, the standard quotient lemma applies.
  letI : Algebra.FiniteType R A := inferInstance
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact Algebra.FinitePresentation.quotient (Ideal.FG.of_isNoetherianRing (RingHom.ker φ.toRingHom))

/-- Helper for Lemma 16.4.6: the induced `R`-algebra map into the kernel quotient is injective as
soon as the quotient still maps to the target DVR `Λ`. -/
lemma algebraMap_injective_quotientKer
    {A : Type u} [CommRing A] [Algebra R A] (φ : A →ₐ[R] Λ) :
    Function.Injective (algebraMap R (A ⧸ RingHom.ker φ.toRingHom)) := by
  -- Proof comment: compose with the injective quotient-to-`Λ` map and use injectivity of
  -- `algebraMap R Λ`.
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective R Λ
  simpa using congrArg (Ideal.kerLiftAlg φ) hxy

/-- Helper for Lemma 16.4.6: over an injective finite-type map of domains, separability of the
induced fraction-field extension gives smoothness at the generic point. -/
lemma smoothAtPrime_zero_of_fractionFieldSeparable
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (hinj : Function.Injective (algebraMap R A))
    (hsep : Algebra.fractionRingIsSeparableOver (R := R) (S := A) hinj) :
    Algebra.SmoothAtPrime R A ⟨⊥, inferInstance⟩ := by
  -- Proof comment: Lemma `10.140.9` rewrites generic-point smoothness as separability of the
  -- induced fraction-field extension.
  letI : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hsmooth : IsSmoothAt R (⊥ : Ideal A) :=
    (Algebra.isSmoothAt_zero_iff_isSeparableOver_fractionRing (R := R) (S := A) hinj).2 hsep
  exact
    (Algebra.smoothAtPrime_iff_isSmoothAt (R := R) (S := A) ⟨⊥, inferInstance⟩).2 hsmooth

/-- Helper for Lemma 16.4.6: separability of the target fraction field descends to any injective
finite-type `R`-subalgebra of the target DVR. -/
lemma fractionRingIsSeparableOver_of_injective_toDvrTarget
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (j : A →ₐ[R] Λ)
    (hinjR : Function.Injective (algebraMap R A))
    (hj : Function.Injective j) :
    Algebra.fractionRingIsSeparableOver (R := R) (S := A) hinjR := by
  let _ : Algebra A Λ := j.toAlgebra
  let _ : IsScalarTower R A Λ := IsScalarTower.of_algebraMap_eq' <| by
    ext x
    exact (j.commutes x).symm
  let _ : FaithfulSMul A Λ := (faithfulSMul_iff_algebraMap_injective A Λ).mpr hj
  let _ : Algebra (FractionRing A) (FractionRing Λ) :=
    FractionRing.liftAlgebra A (FractionRing Λ)
  let _ : IsScalarTower (FractionRing R) (FractionRing A) (FractionRing Λ) :=
    FractionRing.isScalarTower_liftAlgebra
  -- Proof comment: once the fraction fields form a tower
  -- `FractionRing R ⟶ FractionRing A ⟶ FractionRing Λ`, separability descends to the middle
  -- field extension.
  exact Algebra.isSeparable_tower_bot_of_isSeparable
    (FractionRing R) (FractionRing A) (FractionRing Λ)

/-- Helper for Lemma 16.4.6: a smooth `CommRingCat` stage is finitely presentable as a morphism
in the categorical owner used by `MorphismProperty.ind`. -/
lemma commRingCatIsFinitelyPresentableHom_of_smooth
    {X Y : CommRingCat} (f : X ⟶ Y)
    (hf : (RingHom.toMorphismProperty RingHom.Smooth) f) :
    CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat f := by
  -- Proof comment: smooth ring maps are finitely presented, and `CommRingCat` already packages
  -- finitely presented ring maps as finitely presentable arrows in the under-category.
  exact CommRingCat.isFinitelyPresentable_hom f hf.finitePresentation

/-- Helper for Lemma 16.4.6: any finitely presentable arrow `p : ULift R ⟶ Z` together with a map
`g : Z ⟶ ULift Λ` factors through one concrete finitely presented `ULift R`-algebra over
`ULift Λ`. -/
lemma existsFinitePresentationStageFactorization
    {Z : CommRingCat} (p : CommRingCat.of (ULift R) ⟶ Z)
    (g : Z ⟶ CommRingCat.of (ULift Λ))
    (hp : MorphismProperty.isFinitelyPresentable CommRingCat p)
    (hpg : p ≫ g = CommRingCat.ofHom (algebraMap (ULift R) (ULift Λ))) :
    ∃ A : Over (CommAlgCat.of (ULift R) (ULift Λ)),
      Algebra.FinitePresentation (ULift R) A.left ∧
        ∃ u : Z ⟶ CommRingCat.of A.left,
          u ≫ (forget₂ (CommAlgCat (ULift R)) CommRingCat).map A.hom = g ∧
            p ≫ u = CommRingCat.ofHom (algebraMap (ULift R) A.left) := by
  let _ : Algebra (ULift R) Z := p.hom.toAlgebra
  let E := commAlgCatEquivUnder (CommRingCat.of (ULift R))
  let F :=
    selectedAlgebrasOverTargetDiagram
      (finitelyPresentedAlgebrasOverProperty (ULift R) (ULift Λ))
  let G : finitelyPresentedAlgebrasOver (ULift R) (ULift Λ) ⥤ Under (CommRingCat.of (ULift R)) :=
    F ⋙ E.functor
  let cOver := finitelyPresentedAlgebrasOverCocone (ULift R) (ULift Λ)
  let cUnder : Cocone G := E.functor.mapCocone cOver
  have hcUnder : IsColimit cUnder := by
    -- Proof comment: use the canonical filtered-colimit presentation by finitely presented stages.
    exact isColimitOfPreserves E.functor
      (finitelyPresentedAlgebrasOverCoconeIsColimit (ULift R) (ULift Λ))
  have hpres :
      PreservesFilteredColimits
        (coyoneda.obj (.op (CommRingCat.mkUnder (CommRingCat.of (ULift R)) Z))) := by
    -- Proof comment: finite presentability of `p` is exactly the coyoneda preservation
    -- hypothesis needed to factor through one stage of the canonical colimit.
    simpa using
      (CommRingCat.preservesFilteredColimits_coyoneda
        (CommRingCat.of (ULift R))
        (CommRingCat.mkUnder (CommRingCat.of (ULift R)) Z)
        hp)
  let gAlg : Z →ₐ[ULift R] ULift Λ :=
    { toRingHom := g.hom
      commutes' := by
        intro x
        have hw := CommRingCat.hom_ext_iff.mp hpg
        change (g.hom.comp p.hom) x = (algebraMap (ULift R) (ULift Λ)) x
        simpa [CommRingCat.hom_comp] using DFunLike.congr_fun hw x }
  let gToAmbient : CommRingCat.mkUnder (CommRingCat.of (ULift R)) Z ⟶ cUnder.pt := gAlg.toUnder
  obtain ⟨j, gStageRaw, hgStageRaw⟩ :=
    factorsThroughStage_of_preservesFilteredColimits_coyoneda
      (algebraMap (ULift R) Z) hpres G cUnder hcUnder gToAmbient
  have gStage :
      CommRingCat.mkUnder (CommRingCat.of (ULift R)) Z ⟶
        E.functor.obj (F.obj j) := by
    simpa [G, E, F] using gStageRaw
  have ιj : E.functor.obj (F.obj j) ⟶ cUnder.pt := by
    simpa [G, E, F] using cUnder.ι.app j
  have hgStage : gToAmbient = gStage ≫ ιj := by
    -- Proof comment: the abstract stage factorization becomes concrete after simplifying the
    -- diagram and cocone spellings.
    dsimp [gStage, ιj]
    simpa [gToAmbient, G, E, F] using hgStageRaw
  refine ⟨j.1, j.2, gStage.right, ?_, ?_⟩
  · -- Proof comment: read off the right component of the under-category factorization to recover
    -- the desired map `Z ⟶ A ⟶ ULift Λ`.
    have hw := congrArg (fun f ↦ f.right) hgStage
    simpa [gToAmbient, G, E, F, ιj, CommRingCat.hom_comp] using hw
  · -- Proof comment: the under-morphism condition on `gStage` says exactly that the induced map
    -- `Z ⟶ A` is compatible with the chosen `ULift R`-algebra structures.
    apply CommRingCat.hom_ext_iff.mpr
    intro x
    have hw := CommRingCat.hom_ext_iff.mp (Under.w gStage)
    change ((CommRingCat.Hom.hom gStage.right).comp p.hom) x =
      (algebraMap (ULift R) j.1.left) x
    simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x

/-- Helper for Lemma 16.4.6: an irreducible parameter identifies the special fibers with the
residue fields, so the residue-field separability hypothesis transfers to the quotient-by-parameter
extension required by Lemma `16.4.5`. -/
lemma specialFiberSeparable_of_irreducibleParameter
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    [Algebra.IsSeparable (ResidueField R) (ResidueField Λ)]
    {π : R} (hπ : Irreducible π) :
    Algebra.IsSeparable
      (R ⧸ Ideal.span ({π} : Set R))
      (Λ ⧸ Ideal.span ({algebraMap R Λ π} : Set Λ)) := by
  -- Proof comment: rewrite the two special-fiber quotients as the residue fields of the source
  -- and target DVRs using the irreducible parameter and the weakly unramified maximal-ideal
  -- identity.
  have hπR : maximalIdeal R = Ideal.span ({π} : Set R) :=
    (maximalIdeal_eq_span_singleton_iff_irreducible π).mpr hπ
  have hπL : maximalIdeal Λ = Ideal.span ({algebraMap R Λ π} : Set Λ) := by
    calc
      maximalIdeal Λ = Ideal.map (algebraMap R Λ) (maximalIdeal R) := by
        symm
        exact (weaklyUnramified_iff_map_maximalIdeal R Λ).mp hweak
      _ = Ideal.map (algebraMap R Λ) (Ideal.span ({π} : Set R)) := by
        rw [hπR]
      _ = Ideal.span ({algebraMap R Λ π} : Set Λ) := by
        rw [Ideal.map_span]
        simp
  simpa [ResidueField, hπR, hπL] using
    (inferInstance : Algebra.IsSeparable (ResidueField R) (ResidueField Λ))

/-- Helper for Lemma 16.4.6: any smooth factorization of the kernel-quotient comparison
`Ideal.kerLiftAlg φ` lifts to a smooth factorization of the original map `φ` by precomposing with
the quotient map. -/
lemma liftSmoothFactorizationAlongQuotientKer
    {A : Type u} [CommRing A] [Algebra R A] (φ : A →ₐ[R] Λ)
    (hquot :
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
        (f : (A ⧸ RingHom.ker φ.toRingHom) →ₐ[R] B) (β : B →ₐ[R] Λ),
        β.comp f = Ideal.kerLiftAlg φ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (f : A →ₐ[R] B) (β : B →ₐ[R] Λ),
      β.comp f = φ := by
  rcases hquot with ⟨B, hB, hAlgB, hSmoothB, fbar, β, hβfbar⟩
  let _ : CommRing B := hB
  let _ : Algebra R B := hAlgB
  let _ : Smooth R B := hSmoothB
  refine
    ⟨B, hB, hAlgB, hSmoothB,
      fbar.comp (Ideal.Quotient.mkₐ R (RingHom.ker φ.toRingHom)),
      β, ?_⟩
  ext x
  -- Proof comment: evaluate the quotient-stage factorization on the class of `x` and use the
  -- defining computation rule for `Ideal.kerLiftAlg`.
  have hEval :=
    congrArg
      (fun ψ : (A ⧸ RingHom.ker φ.toRingHom) →ₐ[R] Λ =>
        ψ (Ideal.Quotient.mk (RingHom.ker φ.toRingHom) x))
      hβfbar
  simpa [quotientKerLift_mk (R := R) (Λ := Λ) φ x] using hEval

/-- Helper for Lemma 16.4.6: if a stage in the affine Néron blowup tower is smooth at its center
prime, then some localization away from that center is a smooth algebra over the base DVR and
still maps to the target DVR. -/
lemma terminalStageSmoothLocalization
    (S : RamificationOneDvrFactorizationSituation)
    (hsmooth : Algebra.SmoothAtPrime S.R S.A S.pPoint) :
    ∃ a : S.A, a ∉ S.p ∧
      ∃ (_ : Smooth S.R (Localization.Away a)) (β : Localization.Away a →ₐ[S.R] S.L), True := by
  letI : Algebra.FinitePresentation S.R S.A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rcases smoothAtPrime_exists_not_mem_isElementaryStandard
      (R := S.R) (A := S.A) S.pPoint hsmooth with
    ⟨a, ha, haElementary⟩
  letI : IsStandardSmooth S.R (Localization.Away a) :=
    isElementaryStandard_implies_standardSmoothAway (R := S.R) (A := S.A) a haElementary
  let hsmoothAway : Smooth S.R (Localization.Away a) := inferInstance
  refine ⟨a, ha, hsmoothAway, ?_, trivial⟩
  -- Proof comment: restrict scalars on the canonical localization map `A_a →ₐ[A] Λ`.
  exact (neronBlowupLocalizationFactorization (S := S) a ha).restrictScalars S.R

/-- Helper for Lemma 16.4.6: the localization factorization agrees with the original stage map on
source elements. -/
@[simp] lemma neronBlowupLocalizationFactorization_algebraMap
    (S : RamificationOneDvrFactorizationSituation)
    (a : S.A) (ha : a ∉ S.p) (x : S.A) :
    neronBlowupLocalizationFactorization (S := S) a ha (algebraMap S.A (Localization.Away a) x) =
      S.phi x := by
  -- Proof comment: `IsLocalization.liftAlgHom` extends the original `A`-algebra map.
  rw [neronBlowupLocalizationFactorization, IsLocalization.liftAlgHom_apply]
  rfl

/-- Helper for Lemma 16.4.6: composing the terminal localization factorization with the canonical
source map recovers the stage map `φ`. -/
@[simp] lemma neronBlowupLocalizationFactorization_comp_algebraMap
    (S : RamificationOneDvrFactorizationSituation)
    (a : S.A) (ha : a ∉ S.p) :
    (neronBlowupLocalizationFactorization (S := S) a ha).toRingHom.comp
        (algebraMap S.A (Localization.Away a)) =
      S.phi.toRingHom := by
  -- Proof comment: extensionality reduces the ring-hom identity to the computation on source
  -- elements proved just above.
  ext x
  simp

/-- Helper for Lemma 16.4.6: once a compatible intermediate algebra map to `Λ` is smooth at its
closed-point center, localizing away from that center yields the required smooth factorization. -/
lemma smoothFactorizationOfCenterSmoothMap
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Flat R B] [Algebra.FiniteType R B]
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    (φ : A →ₐ[R] Λ) (ψ : B →ₐ[R] Λ)
    (hsmooth :
      Algebra.SmoothAtPrime R B
        ⟨Ideal.comap ψ.toRingHom (maximalIdeal Λ), inferInstance⟩)
    (f : A →ₐ[R] B)
    (hcompat : ψ.comp f = φ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (_ : Smooth R C)
      (g : A →ₐ[R] C) (β : C →ₐ[R] Λ),
      β.comp g = φ := by
  let T : RamificationOneDvrFactorizationSituation where
    R := R
    L := Λ
    A := B
    instCommRingR := inferInstance
    instIsDomainR := inferInstance
    instIsDiscreteValuationRingR := inferInstance
    instCommRingL := inferInstance
    instIsDomainL := inferInstance
    instIsDiscreteValuationRingL := inferInstance
    instCommRingA := inferInstance
    instAlgebraRL := inferInstance
    dvrExtension := inferInstance
    weaklyUnramified := hweak
    instAlgebraRA := inferInstance
    phi := ψ
    flat_toA := inferInstance
    finiteType_toA := inferInstance
  have hTp :
      Algebra.SmoothAtPrime T.R T.A T.pPoint := by
    -- Proof comment: after unfolding the packaged center prime, this is exactly the input
    -- smoothness hypothesis for `ψ : B →ₐ[R] Λ`.
    simpa [T, RamificationOneDvrFactorizationSituation.pPoint,
      RamificationOneDvrFactorizationSituation.p]
      using hsmooth
  rcases terminalStageSmoothLocalization T hTp with ⟨a, ha, hCa, _, _⟩
  let gB : B →ₐ[R] Localization.Away a := IsScalarTower.toAlgHom R B (Localization.Away a)
  let β : Localization.Away a →ₐ[R] Λ :=
    (neronBlowupLocalizationFactorization (S := T) a ha).restrictScalars R
  refine ⟨Localization.Away a, inferInstance, inferInstance, hCa, gB.comp f, β, ?_⟩
  ext x
  -- Proof comment: the localized terminal map agrees with `ψ` on source elements, so the new
  -- factorization is the old compatible map `A → B → Λ`.
  change
    (neronBlowupLocalizationFactorization (S := T) a ha)
        (algebraMap B (Localization.Away a) (f x)) = φ x
  rw [neronBlowupLocalizationFactorization_algebraMap (S := T) a ha]
  simpa using congrArg (fun η : A →ₐ[R] Λ ↦ η x) hcompat

/-- Helper for Lemma 16.4.6: a finitely presented `R`-algebra map into the target DVR should
factor through a smooth `R`-algebra. -/
lemma existsSmoothFactorizationOfFinitePresentationMap
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    [Algebra.IsSeparable (ResidueField R) (ResidueField Λ)]
    [IsSeparableOver (FractionRing R) (FractionRing Λ)]
    (φ : A →ₐ[R] Λ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Smooth R B)
      (f : A →ₐ[R] B) (β : B →ₐ[R] Λ),
      β.comp f = φ := by
  -- Proof comment: the intended route is now isolated in one theorem-local helper. Quotient by
  -- `ker φ`, use `fractionRingIsSeparableOver_of_injective_toDvrTarget` and
  -- `smoothAtPrime_zero_of_fractionFieldSeparable` for generic smoothness, apply
  -- `exists_finite_affine_neron_blowup_tower_with_smooth_center`, and then consume the resulting
  -- finite tower by composing the canonical blowup maps and one terminal localization.
  let Abar := A ⧸ RingHom.ker φ.toRingHom
  let j : Abar →ₐ[R] Λ := Ideal.kerLiftAlg φ
  have hj : Function.Injective j := quotientKerLift_injective (R := R) (Λ := Λ) φ
  let _ : IsDomain Abar := Function.Injective.isDomain j.toRingHom hj
  let _ : Algebra.FinitePresentation R Abar := by
    simpa [Abar] using finitePresentation_quotientKer (R := R) (Λ := Λ) φ
  let _ : Algebra.FiniteType R Abar := inferInstance
  -- Proof comment: the image quotient is torsion free because it embeds into the target DVR.
  let _ : Module.IsTorsionFree R Λ := Module.IsTorsionFree.trans_faithfulSMul R Λ Λ
  let _ : Module.IsTorsionFree R Abar :=
    Function.Injective.moduleIsTorsionFree j.toLinearMap hj (fun r x ↦ by simp)
  let _ : Module.Flat R Abar :=
    (flat_iff_isTorsionFree_of_valuationRing (A := R) (M := Abar)).2 inferInstance
  have hinjR : Function.Injective (algebraMap R Abar) := by
    simpa [Abar] using algebraMap_injective_quotientKer (R := R) (Λ := Λ) φ
  -- Proof comment: the generic point of the image quotient is smooth by separability of the
  -- induced fraction-field extension.
  have hsepFrac :
      Algebra.fractionRingIsSeparableOver (R := R) (S := Abar) hinjR :=
    fractionRingIsSeparableOver_of_injective_toDvrTarget
      (R := R) (Λ := Λ) (A := Abar) j hinjR hj
  have hsmooth_generic : Algebra.SmoothAtPrime R Abar ⟨⊥, inferInstance⟩ :=
    smoothAtPrime_zero_of_fractionFieldSeparable
      (R := R) (A := Abar) hinjR hsepFrac
  let Sbar : RamificationOneDvrFactorizationSituation where
    R := R
    L := Λ
    A := Abar
    instCommRingR := inferInstance
    instIsDomainR := inferInstance
    instIsDiscreteValuationRingR := inferInstance
    instCommRingL := inferInstance
    instIsDomainL := inferInstance
    instIsDiscreteValuationRingL := inferInstance
    instCommRingA := inferInstance
    instAlgebraRL := inferInstance
    dvrExtension := inferInstance
    weaklyUnramified := hweak
    instAlgebraRA := inferInstance
    phi := j
    flat_toA := inferInstance
    finiteType_toA := inferInstance
  have hkerj : RingHom.ker j.toRingHom = ⊥ := RingHom.ker_eq_bot.mpr hj
  have hsmooth_qbar : Algebra.SmoothAtPrime Sbar.R Sbar.A Sbar.qPoint := by
    -- Proof comment: injectivity of `j` identifies the distinguished generic prime `q` with
    -- `(0)`, so the generic smoothness statement applies directly to `Sbar.qPoint`.
    change Algebra.SmoothAtPrime R Abar ⟨RingHom.ker j.toRingHom, inferInstance⟩
    cases hkerj
    simpa using hsmooth_generic
  -- Route correction: the quotient-image setup and the generic smoothness input are complete.
  -- The remaining work is now isolated to one precise missing premise from Lemma `16.4.5`:
  -- construct a compatible center-smooth intermediate map `ψ : B →ₐ[R] Λ` together with
  -- `f : Abar →ₐ[R] B` and `ψ.comp f = j`. Once that exists, the proved helper
  -- `smoothFactorizationOfCenterSmoothMap` finishes the theorem by localizing away from the
  -- terminal center.
  -- TODO: derive such a compatible center-smooth stage from the finite affine Néron blowup tower
  -- for `Sbar`; the current blocker is the missing owner-level compatibility theorem relating the
  -- transported stage maps along `AffineNeronBlowupStepWitness`.
  sorry

-- Proof sketch: by Lemma `10.127.4`, it is enough to factor every finite-presentation
-- `R`-algebra map `A → Λ` through a smooth `R`-algebra. Replace `A` by its image in `Λ` so that
-- `A` is a domain inside `FractionRing Λ`; the assumed separability of `FractionRing Λ` over
-- `FractionRing R` and Lemma `10.140.9` make `R → A` smooth at the generic point. Lemma `16.4.5`
-- then yields, after finitely many Néron blowups, a stage smooth at the center over the closed
-- point, and localizing away from that center gives the required smooth factorization through
-- `Λ`.
/-- Lemma 16.4.6: let `R ⊂ Λ` be an extension of discrete valuation rings with ramification index
`1`. If the induced extension of residue fields is separable and the induced extension of
fraction fields is separable in the Stacks Project sense, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_ramificationIndexOne_dvrExtension
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    [Algebra.IsSeparable (ResidueField R) (ResidueField Λ)]
    [IsSeparableOver (FractionRing R) (FractionRing Λ)] :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := by
  let _ : Algebra R Λ := (algebraMap R Λ).toAlgebra
  let _ : Algebra R (ULift Λ) := ULift.algebra
  let _ : Algebra (ULift R) (ULift Λ) := ULift.algebra' R (ULift Λ)
  -- Route correction: unfold the owner once and reduce to the categorical factorization criterion
  -- `MorphismProperty.ind_iff_exists`.
  dsimp [RingHom.IsFilteredColimitOfSmooth]
  refine
    (CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.Smooth)
      (H := commRingCatIsFinitelyPresentableHom_of_smooth)
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift Λ)))).2 ?_
  intro Z p g hp hpg
  obtain ⟨A, hAfp, uA, huA, hpA⟩ :=
    existsFinitePresentationStageFactorization (R := R) (Λ := Λ) p g hp hpg
  let _ : Algebra.FinitePresentation (ULift R) A.left := hAfp
  let fR : R →+* ULift R := (ULift.ringEquiv.symm : R ≃+* ULift R).toRingHom
  let _ : Algebra R A.left := ((algebraMap (ULift R) A.left).comp fR).toAlgebra
  have hAfpR : (algebraMap R A.left).FinitePresentation := by
    -- Proof comment: finite presentation over `ULift R` transports across the bijective base-ring
    -- equivalence `R ≃ ULift R`.
    let hfR : fR.FinitePresentation := RingHom.FinitePresentation.of_bijective
      (ULift.ringEquiv.symm : R ≃+* ULift R).bijective
    simpa [fR, RingHom.algebraMap_toAlgebra] using RingHom.FinitePresentation.comp hAfp hfR
  let _ : Algebra.FinitePresentation R A.left := by
    simpa [RingHom.finitePresentation_algebraMap] using hAfpR
  let φ : A.left →ₐ[R] Λ :=
    { toRingHom := (ULift.ringEquiv : ULift Λ ≃+* Λ).toRingHom.comp A.hom.toRingHom
      commutes' := by
        intro r
        change
          (ULift.ringEquiv : ULift Λ ≃+* Λ) (A.hom (algebraMap R A.left r)) =
            algebraMap R Λ r
        change
          (ULift.ringEquiv : ULift Λ ≃+* Λ)
              (A.hom ((algebraMap (ULift R) A.left) (ULift.up r))) =
            algebraMap R Λ r
        simpa [fR, RingHom.algebraMap_toAlgebra] using
          congrArg ULift.down (A.hom.commutes (ULift.up r)) }
  obtain ⟨B', _, _, hB'smooth, f, β, hβf⟩ :=
    existsSmoothFactorizationOfFinitePresentationMap
      (R := R) (Λ := Λ) (A := A.left) hweak φ
  let βup : B' →+* ULift Λ :=
    (ULift.ringEquiv.symm : Λ ≃+* ULift Λ).toRingHom.comp β.toRingHom
  have hβupf :
      βup.comp f.toRingHom = A.hom.toRingHom := by
    -- Proof comment: transporting the target across `ULift Λ ≃ Λ` recovers the original stage
    -- map `A.left → ULift Λ`.
    ext a
    change ULift.up (β (f a)) = A.hom a
    have hEq : β (f a) = φ a := by
      simpa using congrArg (fun ψ : A.left →ₐ[R] Λ => ψ a) hβf
    cases hA : A.hom a with
    | up x =>
        change ULift.up (β (f a)) = ULift.up x
        apply congrArg ULift.up
        simpa [φ, hA] using hEq
  let sourceToB' : ULift R →+* B' :=
    (algebraMap R B').comp (ULift.ringEquiv : ULift R ≃+* R).toRingHom
  have hsourceSmooth : sourceToB'.Smooth := by
    -- Proof comment: smoothness over `R` stays smooth after precomposing with the bijective
    -- source-ring equivalence `ULift R ≃ R`.
    let hbase : ((ULift.ringEquiv : ULift R ≃+* R).toRingHom).Smooth :=
      RingHom.Smooth.of_bijective (ULift.ringEquiv : ULift R ≃+* R).bijective
    have htarget : (algebraMap R B').Smooth := by
      simpa [RingHom.smooth_algebraMap] using hB'smooth
    simpa [sourceToB'] using RingHom.Smooth.comp hbase htarget
  refine ⟨CommRingCat.of B', CommRingCat.ofHom (uA.hom.comp f.toRingHom),
    CommRingCat.ofHom βup, hsourceSmooth, ?_, ?_⟩
  · -- Proof comment: the target factorization is the stage map `Z → A.left`, followed by the
    -- concrete smooth factorization `A.left → B' → ULift Λ`.
    apply CommRingCat.hom_ext_iff.mpr
    intro z
    change βup (f (uA.hom z)) = g.hom z
    have hu := CommRingCat.hom_ext_iff.mp huA z
    change A.hom (uA.hom z) = g.hom z at hu
    have hstage : βup (f (uA.hom z)) = A.hom (uA.hom z) := by
      change (βup.comp f.toRingHom) (uA.hom z) = A.hom (uA.hom z)
      rw [hβupf]
    exact hstage.trans hu
  · -- Proof comment: compatibility with the source arrow is exactly the algebra-map identity for
    -- the transported factorization source `ULift R → B'`.
    apply CommRingCat.hom_ext_iff.mpr
    intro r
    have hpAr := CommRingCat.hom_ext_iff.mp hpA r
    change f (uA.hom (p.hom r)) = sourceToB' r
    change f ((algebraMap (ULift R) A.left) r) = sourceToB' r at hpAr ⊢
    cases r
    simpa [sourceToB', fR, RingHom.algebraMap_toAlgebra] using
      congrArg f hpAr

end

end Algebra
