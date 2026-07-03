import Mathlib
import StacksProject_2024.Chap15.Definition_15_83_1
import StacksProject_2024.Chap15.Lemma_15_65_6
import StacksProject_2024.Chap15.Lemma_15_65_11
import StacksProject_2024.Chap15.Lemma_15_82_15

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [(algebraMap R A).IsPseudoCoherentRingMap]

/- Domain-style sampling for Lemma 15.83.7:
- primary domain: comparison between relative pseudo-coherence over `R` and absolute
  pseudo-coherence in `D(A)` under a pseudo-coherent ring map `R → A`;
- sampled owner declarations:
  `RingHom.IsPseudoCoherentRingMap`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_restrictScalars`,
  `isPseudoCoherent_iff_forall_isMPseudoCoherent`;
- best owner abstraction: this file stays `source-facing`, while the chapter owner for changing the
  base along an intermediate algebra is
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`;
- primitive vs. derived: primitive data are the ring-map class field asserting relative
  pseudo-coherence of the regular `A`-module over `R`; derived API is the resulting equivalence
  between relative and absolute pseudo-coherence on derived `A`-complexes, with the self-base
  comparison kept internal as bridge data.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems
  `isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap` and
  `isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap`;
- `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherent`, and `DerivedCategory.IsMPseudoCoherent`;
- `bridge/view`: the internal self-base comparison together with
  `isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`.
 -/

private theorem regularModule_restrictScalars_isPseudoCoherent
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] A) (hα : Function.Surjective α) :
    ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)).IsPseudoCoherent := by
  let P : Type u := MvPolynomial (Fin n) A
  let M : ModuleCat P := (ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of A A)
  let hId : (RingHom.id A).IsPseudoCoherentRingMap := inferInstance
  have hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo A := hId.isPseudoCoherentRelativeTo
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent]
  intro m
  let F : ModuleCat A ⥤ ModuleCat P := ModuleCat.restrictScalars α.toRingHom
  let e₀ :
      (((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (ModuleCat.of A A)).polynomialPresentationRestriction α) ≅
        (CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M :=
    (Functor.mapCochainComplexSingleFunctor F (0 : ℤ)).app (ModuleCat.of A A)
  let e :
      (ModuleCat.single0Functor : ModuleCat P ⥤ DerivedCategory (ModuleCat P)).obj M ≅
        DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat P) (0 : ℤ)).app M
  let Qprop : ObjectProperty (DerivedCategory (ModuleCat P)) := fun K ↦ K.IsMPseudoCoherent m
  have hsource :
      DerivedCategory.IsMPseudoCoherent
        (DerivedCategory.Q.obj
          ((((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
            (ModuleCat.of A A)).polynomialPresentationRestriction α))) m := by
    simpa [CochainComplex.IsMPseudoCoherent] using hA m n α hα
  have htarget :
      Qprop (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat P) (0 : ℤ)).obj M)) :=
    Qprop.prop_of_iso (DerivedCategory.Q.mapIso e₀) hsource
  exact
    Qprop.prop_of_iso e.symm htarget

omit [Algebra R A] [(algebraMap R A).IsPseudoCoherentRingMap] in
private theorem moduleCat_isPseudoCoherentRelativeTo_congr_algebra
    (M : ModuleCat A)
    {alg₁ alg₂ : Algebra R A}
    {ft₁ : @Algebra.FiniteType R A _ _ alg₁}
    {ft₂ : @Algebra.FiniteType R A _ _ alg₂}
    (h : alg₁ = alg₂) :
    @ModuleCat.IsPseudoCoherentRelativeTo R _ A _ alg₁ ft₁ M ↔
      @ModuleCat.IsPseudoCoherentRelativeTo R _ A _ alg₂ ft₂ M := by
  subst h
  have hft : ft₁ = ft₂ := Subsingleton.elim _ _
  subst hft
  rfl

private theorem regularModule_isPseudoCoherentRelativeTo_base :
    (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := by
  let hRing : (algebraMap R A).IsPseudoCoherentRingMap := inferInstance
  let hAlg : (algebraMap R A).toAlgebra = (inferInstance : Algebra R A) := by
    ext r x
    change @SMul.smul R A ((algebraMap R A).toAlgebra).toSMul r x = r • x
    rw [show @SMul.smul R A ((algebraMap R A).toAlgebra).toSMul r x =
        (algebraMap R A) r * x by
      rfl]
    rw [Algebra.smul_def]
  letI : Algebra R A := (algebraMap R A).toAlgebra
  letI : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hRing.finiteType
  have hbase : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R := hRing.isPseudoCoherentRelativeTo
  exact (moduleCat_isPseudoCoherentRelativeTo_congr_algebra (ModuleCat.of A A) hAlg).1 hbase

private theorem isMPseudoCoherentRelativeTo_self_iff
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherent m := by
  constructor
  · intro hK
    rcases
      Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType A A)
      with ⟨n, α, hα⟩
    exact
      (isMPseudoCoherent_iff_restrictScalars α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent α hα)).2 (hK n α hα)
  · intro hK n α hα
    exact
      (isMPseudoCoherent_iff_restrictScalars α.toRingHom K m
        (regularModule_restrictScalars_isPseudoCoherent α hα)).1 hK

-- Proof sketch: first compare relative pseudo-coherence over `R` with relative pseudo-coherence
-- over the intermediate algebra `A` by Lemma `15.82.15`, using the pseudo-coherent ring map
-- hypothesis to supply pseudo-coherence of the regular `A`-module relative to `R`. Then identify
-- relative pseudo-coherence over `A` with the absolute notion by the previous theorem.
/-- Lemma 15.83.7 (1): if `R → A` is a pseudo-coherent ring map, then a derived `A`-complex is
`m`-pseudo-coherent relative to `R` if and only if it is `m`-pseudo-coherent in `D(A)`. -/
theorem isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherent m := by
  calc
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherentRelativeTo A m := by
      simpa using
        (isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo K m
          regularModule_isPseudoCoherentRelativeTo_base).symm
    _ ↔ K.IsMPseudoCoherent m := isMPseudoCoherentRelativeTo_self_iff K m

-- Proof sketch: combine Lemma `15.82.15 (2)` with the self-base comparison above.
/-- Lemma 15.83.7 (2): if `R → A` is a pseudo-coherent ring map, then a derived `A`-complex is
pseudo-coherent relative to `R` if and only if it is pseudo-coherent in `D(A)`. -/
theorem isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
    (K : DerivedCategory.{u + 1, u, u + 1} (ModuleCat A)) :
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherent := by
  calc
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherentRelativeTo A := by
      simpa using
        (isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo K
          regularModule_isPseudoCoherentRelativeTo_base).symm
    _ ↔ K.IsPseudoCoherent := by
      rw [DerivedCategory.IsPseudoCoherentRelativeTo, isPseudoCoherent_iff_forall_isMPseudoCoherent]
      constructor
      · intro hK m
        exact (isMPseudoCoherentRelativeTo_self_iff K m).1 (hK m)
      · intro hK m
        exact (isMPseudoCoherentRelativeTo_self_iff K m).2 (hK m)

end

end CategoryTheory
