import Mathlib
import StacksProject_2024.Chap10.Lemma_10_46_8
import StacksProject_2024.Chap10.Lemma_10_116_5
import StacksProject_2024.Chap10.Definition_10_136_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Algebra.TensorProduct.leftAlgebra

universe u v w

section

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/-- Helper for Chap10 Lemma 10 136 3: the tensor-product identification of a base-changed
principal localization respects the left scalar algebra structure. -/
private theorem tensorLocalizationAwayAlgEquivIncludeRight_commutes
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {K : Type w} [CommRing K] [Algebra k K] (g : A) (x : K) :
    let F := K ⊗[k] A
    let e₁ : K ⊗[k] Localization.Away g ≃ₐ[K] F ⊗[A] Localization.Away g :=
      (Algebra.IsPushout.cancelBaseChangeAlg k K A F (Localization.Away g)).symm
    let e₂ : F ⊗[A] Localization.Away g ≃ₐ[F] Localization.Away g ⊗[A] F :=
      Algebra.TensorProduct.commRight A F (Localization.Away g)
    let e₃ : Localization.Away g ⊗[A] F ≃ₐ[F]
        Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g) :=
      IsLocalization.Away.tensorRightEquiv F g (Localization.Away g)
    e₃ (e₂ (e₁ (algebraMap K (K ⊗[k] Localization.Away g) x))) =
      algebraMap K
        (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g)) x := by
  dsimp only
  let F := K ⊗[k] A
  let e₁ : K ⊗[k] Localization.Away g ≃ₐ[K] F ⊗[A] Localization.Away g :=
    (Algebra.IsPushout.cancelBaseChangeAlg k K A F (Localization.Away g)).symm
  let e₂ : F ⊗[A] Localization.Away g ≃ₐ[F] Localization.Away g ⊗[A] F :=
    Algebra.TensorProduct.commRight A F (Localization.Away g)
  let e₃ : Localization.Away g ⊗[A] F ≃ₐ[F]
      Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g) :=
    IsLocalization.Away.tensorRightEquiv F g (Localization.Away g)
  calc
    e₃ (e₂ (e₁ (algebraMap K (K ⊗[k] Localization.Away g) x)))
        = e₃ (e₂ (algebraMap K (F ⊗[A] Localization.Away g) x)) := by
            rw [e₁.commutes]
    _ = e₃ (e₂ (algebraMap F (F ⊗[A] Localization.Away g) (algebraMap K F x))) := by
          rw [IsScalarTower.algebraMap_apply K F (F ⊗[A] Localization.Away g)]
    _ = e₃ (algebraMap F (Localization.Away g ⊗[A] F) (algebraMap K F x)) := by
          rw [e₂.commutes]
    _ = algebraMap F
          (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g))
          (algebraMap K F x) := by
          rw [e₃.commutes]
    _ = algebraMap K
          (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g)) x := by
          rw [IsScalarTower.algebraMap_apply K F
            (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g))]

/-- Helper for Chap10 Lemma 10 136 3: base changing a principal localization along a field
extension identifies it with the corresponding principal localization of the tensor product. -/
private noncomputable def tensorLocalizationAwayAlgEquivIncludeRight
    {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Algebra k A]
    {K : Type w} [CommRing K] [Algebra k K] (g : A) :
    K ⊗[k] Localization.Away g ≃ₐ[K]
      Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) g) :=
  let F := K ⊗[k] A
  let e₁ : K ⊗[k] Localization.Away g ≃ₐ[K] F ⊗[A] Localization.Away g :=
    (Algebra.IsPushout.cancelBaseChangeAlg k K A F (Localization.Away g)).symm
  let e₂ : F ⊗[A] Localization.Away g ≃ₐ[F] Localization.Away g ⊗[A] F :=
    Algebra.TensorProduct.commRight A F (Localization.Away g)
  let e₃ : Localization.Away g ⊗[A] F ≃ₐ[F]
      Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] F) g) :=
    IsLocalization.Away.tensorRightEquiv F g (Localization.Away g)
  { __ := e₁.toRingEquiv.trans e₂.toRingEquiv |>.trans e₃.toRingEquiv
    commutes' := tensorLocalizationAwayAlgEquivIncludeRight_commutes g }

/-- Helper for Chap10 Lemma 10 136 3: global complete intersections over a field remain global
complete intersections after extension of scalars. -/
private theorem isGlobalCompleteIntersection_tensorProduct_fieldExtension
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    {K : Type w} [Field K] [Algebra k K]
    (hA : IsGlobalCompleteIntersection k A) :
    IsGlobalCompleteIntersection K (K ⊗[k] A) where
  presentation_or_subsingleton := by
    rcases hA.presentation_or_subsingleton with hsub | ⟨n, c, P, hdim⟩
    · left
      letI : Subsingleton A := hsub
      infer_instance
    · right
      haveI : Algebra.FinitePresentation k A := P.finitePresentation_of_isFinite
      haveI : Algebra.FiniteType k A := inferInstance
      refine ⟨n, c, P.baseChange K, ?_⟩
      calc
        ringKrullDim (K ⊗[k] A) = ringKrullDim A := by
          exact (ringKrullDim_tensorProduct_eq_of_fieldExtension
            (k := k) (K := K) (S := A)).symm
        _ = P.dimension := hdim
        _ = (P.baseChange K).dimension := by simp [Algebra.Presentation.dimension]

/-- Helper for Chap10 Lemma 10 136 3: principal global complete-intersection charts remain
global complete-intersection charts after field extension. -/
private theorem isGlobalCompleteIntersection_tensorLocalizationAway_includeRight
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    {K : Type w} [Field K] [Algebra k K] (g : A)
    (hA : IsGlobalCompleteIntersection k (Localization.Away g)) :
    IsGlobalCompleteIntersection K
      (Localization.Away ((Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) g)) :=
  IsGlobalCompleteIntersection.of_algEquiv
    (isGlobalCompleteIntersection_tensorProduct_fieldExtension hA)
    (tensorLocalizationAwayAlgEquivIncludeRight g)

/-- Helper for Chap10 Lemma 10 136 3: local complete intersections over a field remain local
complete intersections after extension of scalars. -/
private theorem isLocalCompleteIntersection_tensorProduct_fieldExtension
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    {K : Type w} [Field K] [Algebra k K]
    (hA : IsLocalCompleteIntersection k A) :
    IsLocalCompleteIntersection K (K ⊗[k] A) := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  let i : A →+* K ⊗[k] A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom
  refine ⟨s.image i, ?_, ?_⟩
  · -- The images of the original basic-open generators still generate the unit ideal.
    calc
      Ideal.span ((s.image i : Finset (K ⊗[k] A)) : Set (K ⊗[k] A))
          = Ideal.map i (Ideal.span (s : Set A)) := by
            simp [i, Ideal.map_span]
      _ = Ideal.map i ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- Each localized chart is the base change of the corresponding downstairs global chart.
    simpa [i] using
      isGlobalCompleteIntersection_tensorLocalizationAway_includeRight
        (K := K) a (hglobal a ha)

/-- Helper for Chap10 Lemma 10 136 3: local complete intersections are preserved by an algebra
equivalence over the base field. -/
private theorem isLocalCompleteIntersection_of_algEquiv
    {k : Type u} [Field k]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image e, ?_, ?_⟩
  · -- Transport the principal-open cover through the algebra equivalence.
    calc
      Ideal.span ((s.image e : Finset B) : Set B)
          = Ideal.map (e : A →+* B) (Ideal.span (s : Set A)) := by
              simp [Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (e : A →+* B) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- The corresponding away localizations are algebra equivalent, so the global chart
    -- condition transports to the image basic open.
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal a ha) <|
      IsLocalization.algEquivOfAlgEquiv
        (A := k)
        (S := Localization.Away a)
        (Q := Localization.Away (e a))
        e
        (Submonoid.map_powers e a)

/-- Helper for Chap10 Lemma 10 136 3: after identifying an upstairs fiber with the residue-field
base change of the contracted downstairs fiber, the local-complete-intersection condition ascends
to the upstairs fiber. -/
private theorem baseChangeFiber_isLocalCompleteIntersection
    (p' : PrimeSpectrum R')
    (hfiber : IsLocalCompleteIntersection
      (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.ResidueField
      ((PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S)) :
    IsLocalCompleteIntersection p'.asIdeal.ResidueField
      (p'.asIdeal.Fiber (R' ⊗[R] S)) := by
  letI : Algebra p'.asIdeal.ResidueField
      (p'.asIdeal.ResidueField ⊗[
        (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.ResidueField]
        (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S) :=
    Algebra.TensorProduct.leftAlgebra
  have e :
      p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
        p'.asIdeal.ResidueField ⊗[
          (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.ResidueField]
          (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S :=
    baseChange_fiber_algEquiv (R := R) (S := S) p'
  -- First pass the downstairs fiber to the residue-field extension, then transport across the
  -- canonical comparison equivalence for base-changed fibers.
  have htensor :
      IsLocalCompleteIntersection p'.asIdeal.ResidueField
        (p'.asIdeal.ResidueField ⊗[
          (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.ResidueField]
          (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S) :=
    isLocalCompleteIntersection_tensorProduct_fieldExtension hfiber
  exact
    isLocalCompleteIntersection_of_algEquiv
      (k := p'.asIdeal.ResidueField)
      (A := p'.asIdeal.ResidueField ⊗[
        (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.ResidueField]
        (PrimeSpectrum.comap (algebraMap R R') p').asIdeal.Fiber S)
      (B := p'.asIdeal.Fiber (R' ⊗[R] S))
      htensor
      e.symm

/-- Helper for Chap10 Lemma 10 136 3: local-complete-intersection fibers are preserved by
tensor-product base change. -/
private theorem hasLocalCompleteIntersectionFibers_baseChange
    (h : (algebraMap R S).HasLocalCompleteIntersectionFibers) :
    (algebraMap R' (R' ⊗[R] S)).HasLocalCompleteIntersectionFibers := by
  -- Test the target condition at a prime upstairs and compare that fiber with the scalar
  -- extension of the fiber over its contraction.
  rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at h ⊢
  intro p'
  exact
    baseChangeFiber_isLocalCompleteIntersection
      (R := R) (S := S) (R' := R') p'
      (h (PrimeSpectrum.comap (algebraMap R R') p'))

/- Domain-style sampling:
- primary domain: syntomic ring maps under tensor-product base change in commutative algebra;
- inspected owner declarations:
  `RingHom.Syntomic`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.Smooth.baseChange`;
- best owner abstraction:
  `RingHom.Syntomic` is the owner predicate, while the tensor-product base change
  `R' → R' ⊗[R] S` is the canonical bridge/view on which the stability theorem should live;
- primitive vs. derived:
  flatness, finite presentation, and local-complete-intersection fibers are derived projections of
  `RingHom.Syntomic`, so this file should expose only the owner-namespace base-change theorem
  rather than a parallel freestanding wrapper.
-/

namespace Syntomic

-- Proof sketch: unpack `hf` into flatness, finite presentation, and local complete-intersection
-- fibers. The first two properties are preserved by base change by the canonical base-change
-- results, and each fiber of `R' → R' ⊗[R] S` is a residue-field extension of a fiber of
-- `R → S`, so the field-extension helper transports the local complete-intersection condition.
/-- Chap10 Lemma 10 136 3: any base change of a syntomic ring map is syntomic. -/
@[stacks 00SN]
theorem baseChange (hf : (algebraMap R S).Syntomic) :
    (algebraMap R' (R' ⊗[R] S)).Syntomic := by
  -- Prove the three defining syntomic components separately: flatness and finite presentation
  -- by standard base-change stability, and the fiber condition by the comparison above.
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    letI : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hf.flat
    exact Module.Flat.baseChange (R := R) (S := R') (M := S)
  · rw [RingHom.finitePresentation_algebraMap]
    letI : Algebra.FinitePresentation R S :=
      (RingHom.finitePresentation_algebraMap).mp hf.finitePresentation
    infer_instance
  · exact hasLocalCompleteIntersectionFibers_baseChange hf.hasLocalCompleteIntersectionFibers

end Syntomic

end RingHom

end
