import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section AlgebraHelpers

namespace Algebra

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {B : Type w} [CommRing B] [Algebra k B]

namespace IsLocalCompleteIntersection

/-- Helper for Lemma 10.136.4: local complete intersections are invariant under `k`-algebra
equivalence. -/
theorem of_algEquiv (hA : IsLocalCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsLocalCompleteIntersection k B := by
  classical
  rcases hA.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  refine ⟨s.image e, ?_, ?_⟩
  · -- Transport the unit-ideal condition along the algebra equivalence.
    calc
      Ideal.span ((s.image e : Finset B) : Set B)
          = Ideal.map (e : A →+* B) (Ideal.span (s : Set A)) := by
              simp [Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (e : A →+* B) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    -- Rewrite the localized chart along the induced equivalence of away localizations.
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal a ha) <|
      IsLocalization.algEquivOfAlgEquiv
        (A := k)
        (S := Localization.Away a)
        (Q := Localization.Away (e a))
        e
        (Submonoid.map_powers e a)

/-- Helper for Lemma 10.136.4: if a finite principal-open cover of `Spec A` consists of local
complete intersections, then `A` is a local complete intersection. -/
theorem of_span_eq_top_target (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤)
    (hloc : ∀ g : s, IsLocalCompleteIntersection k (Localization.Away (g : A))) :
    IsLocalCompleteIntersection k A := by
  classical
  choose t htone ht using fun g : s => (hloc g).exists_basicOpen_cover
  let u : Finset A :=
    (Finset.univ.sigma fun g ↦ (t g).attach).image
      (fun x ↦ (x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
  refine ⟨u, ?_, ?_⟩
  · -- Clear denominators in the localized covers to obtain a finite cover of `Spec A`.
    have hu :
        (u : Set A) =
          Set.range
            (IsLocalization.Away.mulNumerator
              (s : Set A)
              (fun g : (s : Set A) ↦ (t ⟨g.1, g.2⟩ : Set (Localization.Away g.1)))) := by
      ext a
      constructor
      · intro ha
        rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
        exact ⟨⟨⟨(x.1 : A), x.1.2⟩, ⟨x.2.1, by simpa using x.2.2⟩⟩, rfl⟩
      · rintro ⟨⟨g, y⟩, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨⟨g.1, g.2⟩, ⟨y.1, by simpa using y.2⟩⟩, ?_, rfl⟩
        simp
    rw [hu]
    exact IsLocalization.Away.span_range_mulNumerator_eq_top
      (s := (s : Set A))
      hs
      (fun g ↦ by simpa using htone ⟨g.1, g.2⟩)
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
    have hsec :
        Associated x.2.1
          (algebraMap A (Localization.Away (x.1 : A))
            (IsLocalization.Away.sec (x.1 : A) x.2.1).1) := by
      simpa using (IsLocalization.Away.associated_sec_fst (x.1 : A) x.2.1).symm
    letI :
        IsLocalization.Away
          (algebraMap A (Localization.Away (x.1 : A))
            (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
          (Localization.Away x.2.1) :=
      IsLocalization.Away.of_associated hsec
    letI :
        IsLocalization.Away
          ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1)
          (Localization.Away x.2.1) :=
      IsLocalization.Away.mul'
        (Localization.Away (x.1 : A))
        (Localization.Away x.2.1)
        (x.1 : A)
        (IsLocalization.Away.sec (x.1 : A) x.2.1).1
    -- View the final chart directly as an away localization of `A`.
    exact IsGlobalCompleteIntersection.of_algEquiv (ht x.1 x.2.1 x.2.2) <|
      (IsLocalization.algEquiv
        (Submonoid.powers ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1))
        (Localization.Away x.2.1)
        (Localization.Away ((x.1 : A) * (IsLocalization.Away.sec (x.1 : A) x.2.1).1))).restrictScalars k

end IsLocalCompleteIntersection

end Algebra

end AlgebraHelpers

section

namespace RingHom

open Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
Source/core/bridge triage:
* source-facing: syntomicity is local on the target for a finite principal-open cover;
* core/canonical: `RingHom.OfLocalizationSpanTarget` for the owner predicate `RingHom.Syntomic`;
* bridge/view: any explicit finite family `g : Fin n → S` generating the unit ideal.

The primitive data are already in `RingHom.Syntomic` from Definition `10.136.1`. This file adds
only the canonical locality theorem for that owner predicate rather than a parallel free-standing
restatement specialized to one chosen cover.
-/

/-- Helper for Chap10 Lemma 10 136 4: an away localization over an algebra inherits the
composite scalar tower from the base algebra. -/
theorem localizationAway_isScalarTower_base [Algebra R S] (g : S) :
    IsScalarTower R S (Localization.Away g) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Helper for Chap10 Lemma 10 136 4: the underlying ring equivalence between the fiber of
`R → S_g` and the away localization of the fiber ring. -/
noncomputable def fiberLocalizationAwayRingEquiv
    [Algebra R S] (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S) :
    p.asIdeal.Fiber (Localization.Away g) ≃+*
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g) :=
  let F := p.asIdeal.Fiber S
  let Sg := Localization.Away g
  letI : Algebra S Sg := inferInstance
  letI : Algebra R Sg := inferInstance
  letI : IsScalarTower R S Sg := localizationAway_isScalarTower_base (R := R) g
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S F := inferInstance
  letI : Algebra F (Sg ⊗[S] F) := Algebra.TensorProduct.rightAlgebra
  let e₁ : p.asIdeal.Fiber Sg ≃ₐ[p.asIdeal.ResidueField] F ⊗[S] Sg :=
    (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField S F Sg).symm
  let e₂ : F ⊗[S] Sg ≃ₐ[F] Sg ⊗[S] F :=
    Algebra.TensorProduct.commRight S F Sg
  let e₃ : Sg ⊗[S] F ≃ₐ[F]
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] F) g) :=
    IsLocalization.Away.tensorRightEquiv F g Sg
  e₁.toRingEquiv.trans e₂.toRingEquiv |>.trans e₃.toRingEquiv

/-- Helper for Chap10 Lemma 10 136 4: the fiber/localization ring equivalence is linear over the
residue field. -/
theorem fiberLocalizationAwayRingEquiv_algebraMap
    [Algebra R S] (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S)
    (x : p.asIdeal.ResidueField) :
    fiberLocalizationAwayRingEquiv (R := R) (S := S) p g
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber (Localization.Away g)) x) =
      algebraMap p.asIdeal.ResidueField
        (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g))
        x := by
  let F := p.asIdeal.Fiber S
  let Sg := Localization.Away g
  letI : Algebra S Sg := inferInstance
  letI : Algebra R Sg := inferInstance
  letI : IsScalarTower R S Sg := localizationAway_isScalarTower_base (R := R) g
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R S F := inferInstance
  letI : Algebra F (Sg ⊗[S] F) := Algebra.TensorProduct.rightAlgebra
  let e₁ : p.asIdeal.Fiber Sg ≃ₐ[p.asIdeal.ResidueField] F ⊗[S] Sg :=
    (Algebra.IsPushout.cancelBaseChangeAlg R p.asIdeal.ResidueField S F Sg).symm
  let e₂ : F ⊗[S] Sg ≃ₐ[F] Sg ⊗[S] F :=
    Algebra.TensorProduct.commRight S F Sg
  let e₃ : Sg ⊗[S] F ≃ₐ[F]
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] F) g) :=
    IsLocalization.Away.tensorRightEquiv F g Sg
  calc
    fiberLocalizationAwayRingEquiv (R := R) (S := S) p g
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber (Localization.Away g)) x)
        = e₃ (e₂ (e₁ (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber Sg) x))) := by
            rfl
    _ = e₃ (e₂ (algebraMap p.asIdeal.ResidueField (F ⊗[S] Sg) x)) := by
            rw [e₁.commutes]
    _ = e₃ (e₂
          (algebraMap F (F ⊗[S] Sg) (algebraMap p.asIdeal.ResidueField F x))) := by
          rw [IsScalarTower.algebraMap_apply p.asIdeal.ResidueField F (F ⊗[S] Sg)]
    _ = e₃ (algebraMap F (Sg ⊗[S] F) (algebraMap p.asIdeal.ResidueField F x)) := by
          rw [e₂.commutes]
    _ = algebraMap F
          (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] F) g))
          (algebraMap p.asIdeal.ResidueField F x) := by
          rw [e₃.commutes]
    _ = algebraMap p.asIdeal.ResidueField
          (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] F) g)) x := by
          rw [IsScalarTower.algebraMap_apply p.asIdeal.ResidueField F
            (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] F) g))]

/-- Chap10 Lemma 10 136 4: the fiber of `R → S_g` identifies with the localization of the
fiber ring of `R → S` away from the image of `g`. -/
noncomputable def fiber_localizationAway_algEquiv
    [Algebra R S] (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S) :
    p.asIdeal.Fiber (Localization.Away g) ≃ₐ[p.asIdeal.ResidueField]
      Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g) :=
  { __ := fiberLocalizationAwayRingEquiv (R := R) (S := S) p g
    commutes' := fiberLocalizationAwayRingEquiv_algebraMap (R := R) (S := S) p g }

/-- Helper for Lemma 10.136.4: syntomicity of `R → S_g` yields a local complete intersection
chart on every fiber over `R`. -/
theorem fiber_localizationAway_isLocalCompleteIntersection_of_syntomic
    [Algebra R S] (p : PrimeSpectrum R) [p.asIdeal.IsPrime] (g : S)
    (hg : IsLocalCompleteIntersection p.asIdeal.ResidueField
      (p.asIdeal.Fiber (Localization.Away g))) :
    IsLocalCompleteIntersection p.asIdeal.ResidueField
      (Localization.Away ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g)) := by
  -- Route correction: the source-faithful fiber argument closes once the fiber of `S_g` is
  -- rewritten as the localization of the fiber of `S`; no new global locality argument is needed.
  -- Transport the localized fiber property across the canonical fiber/localization equivalence.
  exact Algebra.IsLocalCompleteIntersection.of_algEquiv hg <|
    fiber_localizationAway_algEquiv (R := R) (S := S) p g

/-- Helper for Lemma 10.136.4: the local-complete-intersection fiber condition is local on the
target. -/
theorem HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget :
    OfLocalizationSpanTarget HasLocalCompleteIntersectionFibers := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  intro R S _ _ f s hs hloc
  let _ : Algebra R S := f.toAlgebra
  intro p
  classical
  let _ : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let sp : Finset (p.asIdeal.Fiber S) := s.image (algebraMap S (p.asIdeal.Fiber S))
  have hsp : Ideal.span (sp : Set (p.asIdeal.Fiber S)) = ⊤ := by
    -- The target generators still span after mapping into the fiber ring.
    calc
      Ideal.span ((sp : Finset (p.asIdeal.Fiber S)) : Set (p.asIdeal.Fiber S))
          = Ideal.map (algebraMap S (p.asIdeal.Fiber S)) (Ideal.span (s : Set S)) := by
              simp [sp, Finset.coe_image, Ideal.map_span]
      _ = Ideal.map (algebraMap S (p.asIdeal.Fiber S)) ⊤ := by rw [hs]
      _ = ⊤ := Ideal.map_top _
  refine Algebra.IsLocalCompleteIntersection.of_span_eq_top_target sp hsp ?_
  intro g
  rcases Finset.mem_image.mp g.2 with ⟨x, hx, hxg⟩
  -- Each fiber chart comes from the corresponding syntomic target localization.
  rw [← hxg]
  have hxFiber :
      IsLocalCompleteIntersection p.asIdeal.ResidueField
        (p.asIdeal.Fiber (Localization.Away x)) := by
    have hcomp :
        (algebraMap S (Localization.Away x)).comp f =
          algebraMap R (Localization.Away x) := by
      ext r
      exact IsScalarTower.algebraMap_apply R S (Localization.Away x) r
    have hlocx : (algebraMap R (Localization.Away x)).HasLocalCompleteIntersectionFibers := by
      simpa [hcomp] using hloc ⟨x, hx⟩
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap] at hlocx
    exact hlocx p
  exact
    fiber_localizationAway_isLocalCompleteIntersection_of_syntomic
      (R := R)
      (S := S)
      p
      x
      hxFiber

-- Proof sketch: combine the canonical target-locality results for flatness and finite
-- presentation with the fiberwise local-complete-intersection criterion. For a source prime `p`,
-- the induced principal-open cover on the fiber ring `κ(p) ⊗[R] S` is generated by the images of
-- the chosen target generators, and each localized fiber is a local complete intersection by the
-- syntomic hypotheses on the corresponding target localizations.
/-- Consequence for Chap10 Lemma 10 136 4: syntomicity is local on the target for finite
principal-open covers. -/
@[stacks 00SO]
theorem Syntomic.ofLocalizationSpanTarget : OfLocalizationSpanTarget Syntomic := by
  rw [RingHom.ofLocalizationSpanTarget_iff_finite]
  intro R S _ _ f s hs hloc
  refine ⟨?_, ?_, ?_⟩
  · -- Flatness is already known to be local on the target.
    exact RingHom.Flat.ofLocalizationSpanTarget f s hs fun r ↦ (hloc r).flat
  · -- Finite presentation is also known to be local on the target.
    exact RingHom.finitePresentation_ofLocalizationSpanTarget f s hs
      fun r ↦ (hloc r).finitePresentation
  · -- Reassemble the fiberwise local complete intersection condition from the localized charts.
    exact HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget f s hs
      fun r ↦ (hloc r).hasLocalCompleteIntersectionFibers

end RingHom

end
