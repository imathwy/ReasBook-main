import StacksProject_2024.Chap10.Definition_10_136_5
import StacksProject_2024.Chap10.Lemma_10_116_5
import StacksProject_2024.Chap10.Lemma_10_135_2
import StacksProject_2024.Chap10.Lemma_10_136_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

namespace Algebra

variable {R : Type u} {R' : Type v} {Rf : Type v} {S : Type w}
variable [CommRing R] [CommRing R'] [CommRing Rf] [CommRing S]
variable [Algebra R S] [Algebra R R'] [Algebra R Rf]

namespace Presentation

/-- Helper for Lemma 10.136.9: relative-global-complete-intersection presentations remain such
after arbitrary base change. -/
theorem IsRelativeGlobalCompleteIntersection.baseChange
    {n c : ℕ} {P : Algebra.Presentation R S (Fin n) (Fin c)}
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    (P.baseChange R').IsRelativeGlobalCompleteIntersection := by
  intro p' hp'
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R R') p'
  let Pp : Algebra.Presentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) (Fin n) (Fin c) :=
    P.baseChange p.asIdeal.ResidueField
  let e : p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
      p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    -- Transport one prime of the new fiber to the scalar-extended old fiber, then contract it.
    rcases hp' with ⟨q'⟩
    let j :
        p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.includeRight
    let qTensor :
        PrimeSpectrum
          (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv) q'
    exact ⟨PrimeSpectrum.comap j.toRingHom qTensor⟩
  haveI : Algebra.FinitePresentation p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    simpa [Pp] using Pp.finitePresentation_of_isFinite
  haveI : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
  -- Compare the new fiber with the old one after extending scalars between residue fields.
  calc
    ringKrullDim (p'.asIdeal.Fiber (R' ⊗[R] S))
        = ringKrullDim (p'.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] (p.asIdeal.Fiber S)) := by
          rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    _ = ringKrullDim (p.asIdeal.Fiber S) := by
          symm
          exact ringKrullDim_tensorProduct_eq_of_fieldExtension
    _ = P.dimension := hP p hp_nonempty
    _ = (P.baseChange R').dimension := by
          simp [Algebra.Presentation.dimension]

/-- Helper for Lemma 10.136.9: transporting a relative global complete intersection across an
algebra equivalence preserves the property. -/
theorem IsRelativeGlobalCompleteIntersection.of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (hA : Algebra.IsRelativeGlobalCompleteIntersection R A) (e : A ≃ₐ[R] B) :
    Algebra.IsRelativeGlobalCompleteIntersection R B := by
  rcases hA.exists_presentation with ⟨n, c, P, hP⟩
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P.ofAlgEquiv e) ?_
  intro p hp
  let ep : p.asIdeal.Fiber B ≃ₐ[R] p.asIdeal.Fiber A :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] p.asIdeal.ResidueField)
      e.symm
  have hpA : Nonempty (PrimeSpectrum (p.asIdeal.Fiber A)) := by
    -- Fiber nonemptiness is invariant under the induced tensor-product equivalence.
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber B) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber B) := hp_nontrivial
    have hpA_nontrivial : Nontrivial (p.asIdeal.Fiber A) :=
      RingHom.domain_nontrivial ep.symm.toRingHom
    exact PrimeSpectrum.nonempty_iff_nontrivial.mpr hpA_nontrivial
  -- The source and target fibers are canonically tensor-congruent over the same residue field.
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim (p.asIdeal.Fiber A) := by
      simpa [ep] using (ringKrullDim_eq_of_ringEquiv ep.toRingEquiv)
    _ = P.dimension := hP p hpA
    _ = (P.ofAlgEquiv e).dimension := by
      exact_mod_cast P.dimension_ofAlgEquiv e

end Presentation

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose a finite presentation witness for `S` over `R`, base change that
-- presentation along `R → R'` using `Algebra.Presentation.baseChange`, and identify the fibers of
-- the new presentation with the base changes of the original fibers to transport the dimension
-- condition via Lemma 10.116.5.
/-- Lemma 10.136.9 (1): relative global complete intersections are stable under base change. -/
theorem baseChange (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection R' (R' ⊗[R] S) := by
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  -- Package the source presentation-level base-change witness back into the intrinsic owner.
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection
    (Algebra.Presentation.IsRelativeGlobalCompleteIntersection.baseChange
      (R' := R') hP)

-- Proof sketch: write `Localization.Away g` as a localization of the chosen presentation of `S`,
-- realized by adjoining one generator and one relation `h * X - 1`, and then check that each
-- fiber is the corresponding localization of the original fiber, so the presentation dimension is
-- unchanged.
/-- Lemma 10.136.9 (2): localizing away from an element of a relative global complete
intersection again yields a relative global complete intersection over the same base. -/
theorem localizationAway (hS : IsRelativeGlobalCompleteIntersection R S) (g : S) :
    IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  rcases hS.exists_presentation with ⟨n, c, P, hP⟩
  let Q : Algebra.Presentation R (Localization.Away g)
      (Fin (Fintype.card (Unit ⊕ Fin n))) (Fin (Fintype.card (Unit ⊕ Fin c))) :=
    ((Algebra.Presentation.localizationAway (Localization.Away g) g).comp P).reindex
      (Fintype.equivFin (Unit ⊕ Fin n)).symm
      (Fintype.equivFin (Unit ⊕ Fin c)).symm
  refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := Q) ?_
  intro p hp
  let _ : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let e : p.asIdeal.Fiber (Localization.Away g) ≃ₐ[p.asIdeal.ResidueField]
      Localization.Away (algebraMap S (p.asIdeal.Fiber S) g) :=
    RingHom.fiber_localizationAway_algEquiv (R := R) (S := S) p g
  have hp_nonempty : Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    -- Transport one prime of the localized fiber through the canonical equivalence and contract it.
    rcases hp with ⟨q⟩
    let qLoc : PrimeSpectrum (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) :=
      (PrimeSpectrum.comapEquiv e.toRingEquiv) q
    exact ⟨PrimeSpectrum.comap
      (algebraMap (p.asIdeal.Fiber S) (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)))
      qLoc⟩
  have hloc_nontrivial :
      Nontrivial (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := by
    have hp_nontrivial : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mp hp
    let _ : Nontrivial (p.asIdeal.Fiber (Localization.Away g)) := hp_nontrivial
    exact RingHom.domain_nontrivial e.symm.toRingHom
  let _ : Nontrivial (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := hloc_nontrivial
  -- Reindex the localized presentation and reuse the field-valued localization bound on each
  -- fiber.
  calc
    ringKrullDim (p.asIdeal.Fiber (Localization.Away g))
        = ringKrullDim (Localization.Away (algebraMap S (p.asIdeal.Fiber S) g)) := by
          rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    _ =
        (IsGlobalCompleteIntersection.localized_comp_presentation
          (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
          (algebraMap S (p.asIdeal.Fiber S) g)
          (P.baseChange p.asIdeal.ResidueField)).dimension := by
            exact
              IsGlobalCompleteIntersection.ringKrullDim_localized_comp_presentation
                (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
                (algebraMap S (p.asIdeal.Fiber S) g)
                (P.baseChange p.asIdeal.ResidueField)
                (by
                  simpa [Algebra.Presentation.dimension] using hP p hp_nonempty)
    _ = (P.baseChange p.asIdeal.ResidueField).dimension := by
          simpa [Algebra.Presentation.dimension] using
            IsGlobalCompleteIntersection.localized_comp_presentation_dimension
              (Sg := Localization.Away (algebraMap S (p.asIdeal.Fiber S) g))
              (algebraMap S (p.asIdeal.Fiber S) g)
              (P.baseChange p.asIdeal.ResidueField)
    _ = P.dimension := by
          simp [Algebra.Presentation.dimension]
    _ = Q.dimension := by
          rw [show Q =
            ((Algebra.Presentation.localizationAway (Localization.Away g) g).comp P).reindex
              (Fintype.equivFin (Unit ⊕ Fin n)).symm
              (Fintype.equivFin (Unit ⊕ Fin c)).symm by
                rfl]
          rw [Algebra.Presentation.dimension_reindex]
          simp [Algebra.Presentation.dimension]
          omega

variable [Algebra Rf S] [IsScalarTower R Rf S]

-- Proof sketch: identify `S` with the base change `Rf ⊗[R] S` coming from the factorization
-- `R → Rf → S`, apply the base-change statement to `hS`, and transport the result across the
-- canonical localization tensor-product equivalence.
/-- Lemma 10.136.9 (3): if `R → S` factors through a localization `R_f`, then `S` is a relative
global complete intersection over `R_f`. -/
theorem of_isLocalizationAway (f : R) [IsLocalization.Away f Rf]
    (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection Rf S := by
  have hbase : IsRelativeGlobalCompleteIntersection Rf (Rf ⊗[R] S) :=
    baseChange (R := R) (R' := Rf) hS
  let hu : IsUnit (algebraMap R S f) := by
    rw [show algebraMap R S f = algebraMap Rf S (algebraMap R Rf f) by
      rw [IsScalarTower.algebraMap_apply R Rf S]]
    exact (IsLocalization.Away.algebraMap_isUnit f).map (algebraMap Rf S)
  letI : IsLocalization.Away (algebraMap R S f) S :=
    IsLocalization.away_of_isUnit_of_bijective S hu Function.bijective_id
  letI : Algebra S (Rf ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let eu : S ≃ₐ[S] Localization.Away (algebraMap R S f) :=
    IsLocalization.atUnit S (Localization.Away (algebraMap R S f)) (algebraMap R S f) hu
  let eS : Rf ⊗[R] S ≃ₐ[S] S :=
    (IsLocalization.Away.tensorRightEquiv S f Rf).trans eu.symm
  have hcomm :
      (eS : Rf ⊗[R] S →+* S).comp (algebraMap Rf (Rf ⊗[R] S)) = algebraMap Rf S := by
    -- Route correction: this is the same tensor-versus-localization compatibility used in the
    -- standard smooth localization argument, now only to transport the relative GCI owner.
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    change eS (algebraMap Rf (Rf ⊗[R] S) (algebraMap R Rf r)) = algebraMap Rf S (algebraMap R Rf r)
    rw [← IsScalarTower.algebraMap_apply R Rf (Rf ⊗[R] S)]
    rw [← IsScalarTower.algebraMap_apply R Rf S]
    have hmap : algebraMap R (Rf ⊗[R] S) r = algebraMap S (Rf ⊗[R] S) (algebraMap R S r) :=
      IsScalarTower.algebraMap_apply R S (Rf ⊗[R] S) r
    rw [hmap]
    exact eS.commutes _
  let e : Rf ⊗[R] S ≃ₐ[Rf] S :=
    { __ := eS.toRingEquiv
      commutes' := by
        intro x
        exact RingHom.ext_iff.mp hcomm x }
  -- Transport the base-changed owner along the canonical tensor/localization equivalence.
  exact Algebra.Presentation.IsRelativeGlobalCompleteIntersection.of_algEquiv hbase e

end IsRelativeGlobalCompleteIntersection

end Algebra

end
