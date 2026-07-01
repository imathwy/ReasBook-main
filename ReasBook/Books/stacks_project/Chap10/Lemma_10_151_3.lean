import Mathlib
import stacks_project.Chap10.Definition_10_112_5
import stacks_project.Chap10.Definition_10_151_1
import stacks_project.Chap10.Lemma_10_126_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w x

namespace Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: unramified commutative algebra via Kähler differentials, the unramified locus,
  and basic-open neighborhood criteria;
- sampled owner declarations:
  `Algebra.Unramified`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.Unramified.comp`,
  `Algebra.basicOpen_subset_unramifiedLocus_iff`,
  `Algebra.unramifiedAt_iff_isUnramifiedAt`,
  `Algebra.gUnramifiedAt_iff_isUnramifiedAt`;
- best owner abstraction:
  `Algebra.Unramified` for the global notion and `Algebra.IsUnramifiedAt` for the canonical local
  owner, with the chapter's `UnramifiedAt` / `GUnramifiedAt` retained as the source-facing
  basic-open neighborhood predicates;
- primitive data: the algebra map `R → S` and, for the source-facing local notions, a principal
  open `D(g)` carrying the unramified or G-unramified structure;
- derived API: the finite type / finite presentation bridges
  `unramifiedAt_iff_isUnramifiedAt` and `gUnramifiedAt_iff_isUnramifiedAt`.

The finite-presentation clauses in this file are `source-facing`, so they should land in
`GUnramifiedAt`; any `IsUnramifiedAt` reformulation belongs only to the bridge layer.
-/

/- Lemma 10.151.3 (1): the base change of an unramified ring map is unramified. -/
example {R' : Type w} [CommRing R'] [Algebra R R'] [Unramified R S] :
    Unramified R' (R' ⊗[R] S) :=
  inferInstance

-- Proof sketch: combine base change for the owner predicate `Algebra.Unramified` with base change
-- for finite presentation.
/-- Lemma 10.151.3 (2): the base change of a G-unramified ring map is G-unramified. -/
theorem gUnramified_baseChange {R' : Type w} [CommRing R'] [Algebra R R'] [GUnramified R S] :
    GUnramified R' (R' ⊗[R] S) := by
  infer_instance

/- Lemma 10.151.3 (3): the composition of unramified ring maps is unramified. -/
example {T : Type x} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Unramified R S] [Unramified S T] :
    Unramified R T :=
  Unramified.comp R S T

-- Proof sketch: compose the owner predicate `Algebra.Unramified` via `Algebra.Unramified.comp`,
-- compose finite presentation via `Algebra.FinitePresentation.trans`, and package the two facts.
/-- Lemma 10.151.3 (4): the composition of G-unramified ring maps is G-unramified. -/
theorem gUnramified_comp {T : Type x} [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [GUnramified R S] [GUnramified S T] :
    GUnramified R T := by
  letI : Unramified R T := Unramified.comp R S T
  letI : FinitePresentation R T := FinitePresentation.trans R S T
  infer_instance

/- Lemma 10.151.3 (5): any principal localization `R → R_f` is unramified. -/
example (f : R) :
    Unramified R (Localization.Away f) :=
  Unramified.of_isLocalization_Away f

-- Proof sketch: principal localization is unramified by the canonical localization theorem, and
-- `IsLocalization.Away.finitePresentation` supplies finite presentation.
/-- Lemma 10.151.3 (6): any principal localization `R → R_f` is G-unramified. -/
theorem localizationAway_gUnramified (f : R) :
    GUnramified R (Localization.Away f) := by
  infer_instance

-- Proof sketch: the quotient map is surjective, hence formally unramified by the quotient
-- instance, and quotients are finitely generated as algebras over the source.
/-- Lemma 10.151.3 (7): for any ideal `I ⊆ R`, the quotient map `R → R/I` is unramified. -/
theorem quotient_unramified (I : Ideal R) :
    Unramified R (R ⧸ I) := by
  letI : FormallyUnramified R (R ⧸ I) := by infer_instance
  letI : FiniteType R (R ⧸ I) := by infer_instance
  exact {}

-- Proof sketch: combine the quotient unramified map with finite presentation of the quotient map
-- for finitely generated ideals.
/-- Lemma 10.151.3 (8): for any finitely generated ideal `I ⊆ R`, the quotient map `R → R/I` is
G-unramified. -/
theorem quotient_gUnramified_of_fg (I : Ideal R) (hI : I.FG) :
    GUnramified R (R ⧸ I) := by
  letI : Unramified R (R ⧸ I) := quotient_unramified I
  letI : FinitePresentation R R := by infer_instance
  letI : FinitePresentation R (R ⧸ I) := FinitePresentation.quotient hI
  infer_instance

/- Lemma 10.151.3 (9): an étale ring map is unramified. -/
example [Etale R S] :
    Unramified R S :=
  inferInstance

-- Proof sketch: an étale algebra is unramified, and étale algebras are finitely presented.
/-- Lemma 10.151.3 (10): an étale ring map is G-unramified. -/
theorem etale_gUnramified [Etale R S] :
    GUnramified R S := by
  infer_instance

-- Bridge sketch: if the localization of `Ω[S⁄R]` at `q` is zero, then `q` lies in the unramified
-- locus by `Algebra.unramifiedLocus_eq_compl_support`, which is exactly the owner predicate
-- `Algebra.IsUnramifiedAt R q.asIdeal`.
/-- Bridge theorem: vanishing of the localized Kähler differentials gives the canonical local owner
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_kaehlerLocalized
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    IsUnramifiedAt R q.asIdeal := by
  -- The owner predicate is exactly membership in the unramified locus.
  have hq : q ∈ unramifiedLocus R S := by
    -- The unramified locus is the complement of the support of `Ω[S⁄R]`.
    rw [unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.notMem_support_iff]
    exact hOmega
  simpa [unramifiedLocus] using hq

-- Proof sketch: under finite type, translate the owner-level conclusion above to the chapter's
-- source-facing local predicate via `Algebra.unramifiedAt_iff_isUnramifiedAt`.
/-- Lemma 10.151.3 (11): if the localization `(Ω[S⁄R])_q` is zero, then `R → S` is unramified at
`q`. -/
theorem unramifiedAt_of_subsingleton_kaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerLocalized q hOmega)

-- Proof sketch: first obtain the source-facing unramified-at statement from clause (11); under
-- finite presentation, that same basic-open neighborhood is automatically G-unramified.
/-- Lemma 10.151.3 (12): if `R → S` is of finite presentation and the localization
`(Ω[S⁄R])_q` is zero, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_kaehlerLocalized
    [FinitePresentation R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerLocalized q hOmega)

-- Bridge sketch: by Nakayama over the local ring `S_q`, vanishing of
-- `Ω[S⁄R] ⊗[S] κ(q)` is equivalent to vanishing of the localized differential module, so the
-- localized owner-level criterion applies.
/-- Bridge theorem: under finite type, vanishing of `Ω[S⁄R] ⊗[S] κ(q)` gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_kaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    IsUnramifiedAt R q.asIdeal := by
  -- The finite-type hypothesis makes `Ω[S⁄R]` finite, so residue-field vanishing detects
  -- support at `q`.
  have hq : q ∈ unramifiedLocus R S := by
    rw [unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct
        (R := S) (M := Ω[S⁄R]) q]
    exact not_nontrivial_iff_subsingleton.mpr hOmega
  simpa [unramifiedLocus] using hq

-- Proof sketch: after passing to the canonical owner-level criterion above, translate back to the
-- chapter's source-facing local predicate.
/-- Lemma 10.151.3 (13): if `R → S` is of finite type and
`Ω[S⁄R] ⊗[S] κ(q)` is zero, then `R → S` is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_kaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q hOmega)

-- Proof sketch: reduce to the source-facing unramified-at criterion from clause (13); finite
-- presentation then upgrades that basic-open witness to a G-unramified one.
/-- Lemma 10.151.3 (14): if `R → S` is of finite presentation and
`Ω[S⁄R] ⊗[S] κ(q)` is zero, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_kaehlerResidueTensor
    [FinitePresentation R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q hOmega)

/-- Helper for Lemma 10.151.3: the fiber prime corresponding to `q` contracts back to `q` along
the canonical map `S → κ(q ∩ R) ⊗[R] S`. -/
theorem comap_fiberPrimeAt_eq
    (q : PrimeSpectrum S) :
    PrimeSpectrum.comap (algebraMap S ((q.asIdeal.under R).Fiber S)) (fiberPrimeAt R S q) = q := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  have hleft :
      ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) = q := by
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber R S p).symm_apply_apply ⟨q, rfl⟩)
  calc
    PrimeSpectrum.comap (algebraMap S (p.asIdeal.Fiber S)) (fiberPrimeAt R S q)
        = ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q)) := by
            change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                (fiberPrimeAt R S q) =
              ↑((PrimeSpectrum.preimageEquivFiber R S p).symm (fiberPrimeAt R S q))
            rfl
    _ = q := hleft

/-- Helper for Lemma 10.151.3: the ideal of the fiber prime contracts back to `q.asIdeal`. -/
theorem comap_fiberPrimeAt_asIdeal
    (q : PrimeSpectrum S) :
    Ideal.comap (algebraMap S ((q.asIdeal.under R).Fiber S)) (fiberPrimeAt R S q).asIdeal =
      q.asIdeal := by
  simpa using congrArg PrimeSpectrum.asIdeal (comap_fiberPrimeAt_eq (R := R) (S := S) q)

/-- Helper for Lemma 10.151.3: the canonical map `κ(q) → κ(\bar q)` is bijective. -/
theorem fiberPrime_residueField_map_bijective
    (q : PrimeSpectrum S) :
    Function.Bijective
      (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt R S q).asIdeal
        (Algebra.ofId S ((q.asIdeal.under R).Fiber S))
        (comap_fiberPrimeAt_asIdeal (R := R) (S := S) q).symm) := by
  -- The residue-field map is exactly the base change of `κ(q ∩ R)` along `S`.
  simpa using
    RingHom.SurjectiveOnStalks.residueFieldMap_bijective
      ((Ideal.surjectiveOnStalks_residueField (R := R) (q.asIdeal.under R)).baseChange')
      q.asIdeal (fiberPrimeAt R S q).asIdeal
      (comap_fiberPrimeAt_asIdeal (R := R) (S := S) q).symm

/-- Helper for Lemma 10.151.3: the residue fields at `q` and its fiber prime are canonically
identified as `S`-algebras. -/
noncomputable def fiberPrime_residueField_equiv
    (q : PrimeSpectrum S) :
    (fiberPrimeAt R S q).asIdeal.ResidueField ≃ₐ[S] q.asIdeal.ResidueField :=
  (AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt R S q).asIdeal
      (Algebra.ofId S ((q.asIdeal.under R).Fiber S))
      (comap_fiberPrimeAt_asIdeal (R := R) (S := S) q).symm)
    (fiberPrime_residueField_map_bijective (R := R) (S := S) q)).symm

-- Proof sketch: work entirely over the fiber ring `κ(q ∩ R) ⊗[R] S`; finite type makes its
-- Kähler differentials a finite module, so the usual support criterion upgrades vanishing after
-- localizing at `fiberPrimeAt q` to vanishing after tensoring with the residue field of that prime.
/-- Helper for Lemma 10.151.3: vanishing of the localized fiber differential module forces
vanishing of its tensor with the residue field at `fiberPrimeAt q`. -/
theorem subsingleton_fiberKaehlerResidueTensor_of_subsingleton_fiberKaehlerLocalized
    [FiniteType R S] (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Subsingleton
      (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) := by
  letI : FiniteType (q.asIdeal.under R).ResidueField ((q.asIdeal.under R).Fiber S) := by
    infer_instance
  -- The localized fiber vanishing says exactly that the fiber prime is outside the support.
  have hnotSupport :
      fiberPrimeAt R S q ∉
        Module.support ((q.asIdeal.under R).Fiber S)
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField] := by
    rw [Module.notMem_support_iff]
    exact hOmega
  -- The finite-type support criterion over the fiber ring converts that into residue-field
  -- tensor vanishing.
  refine not_nontrivial_iff_subsingleton.mp ?_
  intro hnontrivial
  exact hnotSupport <|
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct
      (R := (q.asIdeal.under R).Fiber S)
      (M := Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])
      (p := fiberPrimeAt R S q)).2 hnontrivial

/-- Helper for Lemma 10.151.3: the Kähler differentials of the fiber ring identify with the base
change of `Ω[S⁄R]`. -/
noncomputable def fiber_kaehlerEquiv_baseChange
    (q : PrimeSpectrum S) :
    Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField] ≃ₗ[(q.asIdeal.under R).Fiber S]
      (((q.asIdeal.under R).Fiber S) ⊗[S] Ω[S⁄R]) :=
  (KaehlerDifferential.tensorKaehlerEquiv R (q.asIdeal.under R).ResidueField S
    ((q.asIdeal.under R).Fiber S)).symm

/-- Helper for Lemma 10.151.3: after the fiber Kähler differential is rewritten as a base change,
the outer residue-field tensor collapses to the ordinary `S`-tensor. -/
noncomputable def fiber_residueTensor_cancelBaseChange
    (q : PrimeSpectrum S) :
    (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
      (((q.asIdeal.under R).Fiber S) ⊗[S] Ω[S⁄R])) ≃ₗ[S]
      (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[S] Ω[S⁄R]) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange S ((q.asIdeal.under R).Fiber S)
    ((q.asIdeal.under R).Fiber S) ((fiberPrimeAt R S q).asIdeal.ResidueField) Ω[S⁄R]).restrictScalars S

/-- Helper for Lemma 10.151.3: tensoring the fiber Kähler comparison with the residue field and
then canceling the base change identifies the fiber criterion with the `κ(\bar q)`-tensor over
`S`. -/
noncomputable def fiber_kaehlerResidueTensor_equiv_residueTensorAtFiber
    (q : PrimeSpectrum S) :
    (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
      Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) ≃ₗ[S]
      (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[S] Ω[S⁄R]) :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ((q.asIdeal.under R).Fiber S)
        ((fiberPrimeAt R S q).asIdeal.ResidueField))
      (fiber_kaehlerEquiv_baseChange (R := R) (S := S) q)).restrictScalars S ≪≫ₗ
    fiber_residueTensor_cancelBaseChange (R := R) (S := S) q

/-- Helper for Lemma 10.151.3: vanishing of the fiber-residue tensor forces vanishing of the
ordinary residue tensor `κ(q) ⊗[S] Ω[S⁄R]`. -/
theorem subsingleton_residueTensor_of_subsingleton_fiberKaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R]) := by
  -- Route correction: fix the source-proof intermediate tensor
  -- `κ(\bar q) ⊗[fiber] (fiber ⊗[S] Ω[S⁄R])` before transporting to `κ(q)`.
  let eFiber :
      (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) ≃ₗ[S]
        (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[S] Ω[S⁄R]) :=
    fiber_kaehlerResidueTensor_equiv_residueTensorAtFiber (R := R) (S := S) q
  -- First transfer vanishing across the source-faithful fiber-to-base-change equivalence.
  have hFiberBase :
      Subsingleton (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[S] Ω[S⁄R]) :=
    (eFiber.toEquiv.subsingleton_congr).mp hOmega
  let eResidue :
      (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[S] Ω[S⁄R]) ≃ₗ[S]
        (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R]) :=
    TensorProduct.AlgebraTensorModule.congr
      (fiberPrime_residueField_equiv (R := R) (S := S) q).toLinearEquiv
      (LinearEquiv.refl S Ω[S⁄R])
  -- Then replace the fiber-prime residue field `κ(\bar q)` by `κ(q)`.
  exact (eResidue.toEquiv.subsingleton_congr).mp hFiberBase

-- Bridge sketch: identify the Kähler differentials of the canonical fiber ring
-- `(q.asIdeal.under R).Fiber S` with the base change of `Ω[S⁄R]`, localize at the canonical fiber
-- prime `fiberPrimeAt R S q`, and reduce to the localized owner-level criterion above.
/-- Bridge theorem: under finite type, the fiber-localized differential criterion gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    IsUnramifiedAt R q.asIdeal := by
  -- Route correction: stay on the source proof route by first applying Nakayama on the fiber
  -- ring, and postpone the residue-field identification `κ(\bar q) ≃ κ(q)` to the next bridge.
  have hFiber :
      Subsingleton
        (((fiberPrimeAt R S q).asIdeal.ResidueField) ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField]) :=
    subsingleton_fiberKaehlerResidueTensor_of_subsingleton_fiberKaehlerLocalized
      (R := R) (S := S) q hOmega
  -- The fiber criterion becomes the ordinary residue-field criterion after the canonical
  -- residue-field and Kähler base-change identifications.
  exact isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q
    (subsingleton_residueTensor_of_subsingleton_fiberKaehlerResidueTensor
      (R := R) (S := S) q hFiber)

-- Proof sketch: translate the owner-level fiber criterion above to the source-facing local
-- predicate `UnramifiedAt`.
/-- Lemma 10.151.3 (15): if `R → S` is of finite type and the localization of
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)]` at the canonical fiber prime corresponding to `q` is zero, then the
map is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_fiberKaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized q hOmega)

-- Proof sketch: the source-facing unramified-at criterion from clause (15) becomes
-- G-unramified-at after adding finite presentation.
/-- Lemma 10.151.3 (16): if `R → S` is of finite presentation and the localization of
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)]` at the canonical fiber prime corresponding to `q` is zero, then
`R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_fiberKaehlerLocalized
    [FinitePresentation R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized q hOmega)

-- Bridge sketch: over the local fiber ring, Nakayama identifies vanishing of the residue-field
-- tensor of the fiber differential with vanishing of its localization, so the previous owner-level
-- fiber criterion applies.
/-- Bridge theorem: under finite type, the fiber-residue differential criterion gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    IsUnramifiedAt R q.asIdeal := by
  -- The source-proof fiber tensor is equivalent to the ordinary residue tensor criterion.
  exact isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q
    (subsingleton_residueTensor_of_subsingleton_fiberKaehlerResidueTensor
      (R := R) (S := S) q hOmega)

-- Proof sketch: convert the owner-level fiber-residue criterion above to the chapter's
-- source-facing `UnramifiedAt` predicate.
/-- Lemma 10.151.3 (17): if `R → S` is of finite type and
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)] ⊗ κ(\bar q)` is zero at the canonical fiber prime corresponding to
`q`, then the map is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_fiberKaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor q hOmega)

-- Proof sketch: the source-facing fiber-residue criterion from clause (17) upgrades to the
-- G-unramified-at statement once finite presentation is available.
/-- Lemma 10.151.3 (18): if `R → S` is of finite presentation and
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)] ⊗ κ(\bar q)` is zero at the canonical fiber prime corresponding to
`q`, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor
    [FinitePresentation R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor q hOmega)

-- Proof sketch: each localization `S_f` is unramified on the corresponding basic open `D(f)`;
-- if the chosen elements generate the unit ideal, these basic opens cover `Spec S`, so
-- unramifiedness descends from the cover.
/-- Lemma 10.151.3 (19): if finitely many principal localizations `S_{g_j}` are unramified and the
elements `g_j` generate the unit ideal, then `R → S` is unramified. -/
theorem unramified_of_localizationAway_cover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, Unramified R (Localization.Away f.1)) :
    Unramified R S := by
  -- Formal unramifiedness is local on the principal-open cover coming from `s`.
  have hform : FormallyUnramified R S := by
    rw [← unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro q
    obtain ⟨r, hr, hrq⟩ : ∃ r ∈ (↑s : Set S), q ∈ PrimeSpectrum.basicOpen r := by
      simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
        (TopologicalSpace.Opens.mem_top q)
    have hsubset : ↑(PrimeSpectrum.basicOpen r) ⊆ unramifiedLocus R S := by
      rw [basicOpen_subset_unramifiedLocus_iff]
      letI : Unramified R (Localization.Away r) := hlocal ⟨r, hr⟩
      infer_instance
    exact hsubset hrq
  -- Finite type is also local on the same target cover.
  have hft : FiniteType R S :=
    FiniteType.of_span_eq_top_target (s := (↑s : Set S)) hs fun g hg ↦ by
      letI : Unramified R (Localization.Away g) := hlocal ⟨g, hg⟩
      infer_instance
  letI : FormallyUnramified R S := hform
  letI : FiniteType R S := hft
  exact {}

-- Proof sketch: finite presentation is local on a principal-open cover, and formal unramifiedness
-- is detected by vanishing of the differential on that same cover, so G-unramifiedness descends.
/-- Lemma 10.151.3 (20): if finitely many principal localizations `S_{g_j}` are G-unramified and
the elements `g_j` generate the unit ideal, then `R → S` is G-unramified. -/
theorem gUnramified_of_localizationAway_cover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, GUnramified R (Localization.Away f.1)) :
    GUnramified R S := by
  -- First descend the unramified owner on the principal-open cover.
  letI : Unramified R S :=
    unramified_of_localizationAway_cover (R := R) (S := S) s hs fun f ↦ by
      letI : GUnramified R (Localization.Away f.1) := hlocal f
      infer_instance
  -- Finite presentation is local on the same target cover.
  have hfp : FinitePresentation R S :=
    FinitePresentation.of_span_eq_top_target (s := (↑s : Set S)) hs fun g hg ↦ by
      letI : GUnramified R (Localization.Away g) := hlocal ⟨g, hg⟩
      infer_instance
  letI : FinitePresentation R S := hfp
  infer_instance

-- Proof sketch: every prime admits an unramified basic-open neighborhood, so by quasi-compactness
-- of `Spec S` finitely many such opens cover and clause (19) applies.
/-- Lemma 10.151.3 (21): if `R → S` is unramified at every prime of `S`, then `R → S` is
unramified. -/
theorem unramified_of_unramifiedAt
    (hlocal : ∀ q : PrimeSpectrum S, UnramifiedAt R S q) :
    Unramified R S := by
  let s : Set S := { g | Unramified R (Localization.Away g) }
  -- The primewise neighborhoods cover `Spec S`.
  have hscover : (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ g ∈ s, PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    rcases hlocal q with ⟨g, hgq, hg⟩
    have hgmem : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    exact
      (show (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) ≤
          ⨆ h ∈ s, PrimeSpectrum.basicOpen h from
        le_iSup_of_le g <| le_iSup_of_le hg le_rfl) hgmem
  have hsone : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hscover
  -- Formal unramifiedness and finite type both descend from this cover.
  have hform : FormallyUnramified R S := by
    rw [← unramifiedLocus_eq_univ_iff]
    exact Set.eq_univ_iff_forall.mpr fun q ↦ by
      obtain ⟨g, hgq, hg⟩ := hlocal q
      have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ unramifiedLocus R S := by
        rw [basicOpen_subset_unramifiedLocus_iff]
        letI : Unramified R (Localization.Away g) := hg
        infer_instance
      exact hsubset (by simpa [PrimeSpectrum.mem_basicOpen] using hgq)
  have hft : FiniteType R S :=
    FiniteType.of_span_eq_top_target s hsone fun g hg ↦ by
      letI : Unramified R (Localization.Away g) := hg
      infer_instance
  letI : FormallyUnramified R S := hform
  letI : FiniteType R S := hft
  exact {}

-- Proof sketch: under finite type, the source-facing and owner-level local predicates are
-- equivalent at every prime, so clause (21) applies after translating the hypothesis through
-- `Algebra.unramifiedAt_iff_isUnramifiedAt`.
/-- Bridge theorem: for finite type algebras, pointwise `Algebra.IsUnramifiedAt` implies global
`Algebra.Unramified`. -/
theorem unramified_of_isUnramifiedAt [FiniteType R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    Unramified R S := by
  exact unramified_of_unramifiedAt
    (fun q ↦ (unramifiedAt_iff_isUnramifiedAt R S q).2 (hlocal q))

-- Proof sketch: the same quasi-compactness argument reduces the pointwise G-unramified
-- neighborhoods to a finite principal-open cover, then clause (20) gives the global result.
/-- Lemma 10.151.3 (22): if `R → S` is G-unramified at every prime of `S`, then `R → S` is
G-unramified. -/
theorem gUnramified_of_gUnramifiedAt
    (hlocal : ∀ q : PrimeSpectrum S, GUnramifiedAt R S q) :
    GUnramified R S := by
  let s : Set S := { g | GUnramified R (Localization.Away g) }
  -- The G-unramified neighborhoods cover `Spec S`.
  have hscover : (⨆ g ∈ s, PrimeSpectrum.basicOpen g) = ⊤ := by
    apply SetLike.ext'
    change (↑(⨆ g ∈ s, PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) = Set.univ
    rw [Set.eq_univ_iff_forall]
    intro q
    rcases hlocal q with ⟨g, hgq, hg⟩
    have hgmem : q ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      simpa [PrimeSpectrum.mem_basicOpen] using hgq
    exact
      (show (PrimeSpectrum.basicOpen g : TopologicalSpace.Opens (PrimeSpectrum S)) ≤
          ⨆ h ∈ s, PrimeSpectrum.basicOpen h from
        le_iSup_of_le g <| le_iSup_of_le hg le_rfl) hgmem
  have hsone : Ideal.span s = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hscover
  -- Route correction: descend the owner facts directly from the cover instead of extracting an
  -- explicit finite subcover first.
  have hform : FormallyUnramified R S := by
    rw [← unramifiedLocus_eq_univ_iff]
    exact Set.eq_univ_iff_forall.mpr fun q ↦ by
      rcases hlocal q with ⟨g, hgq, hg⟩
      have hsubset : ↑(PrimeSpectrum.basicOpen g) ⊆ unramifiedLocus R S := by
        rw [basicOpen_subset_unramifiedLocus_iff]
        letI : GUnramified R (Localization.Away g) := hg
        infer_instance
      exact hsubset (by simpa [PrimeSpectrum.mem_basicOpen] using hgq)
  have hfp : FinitePresentation R S :=
    FinitePresentation.of_span_eq_top_target s hsone fun g hg ↦ by
      letI : GUnramified R (Localization.Away g) := hg
      infer_instance
  letI : FormallyUnramified R S := hform
  letI : FinitePresentation R S := hfp
  infer_instance

-- Proof sketch: for finitely presented algebras, the source-facing `GUnramifiedAt` predicate and
-- the canonical owner `Algebra.IsUnramifiedAt` are equivalent primewise, so clause (22) applies.
/-- Bridge theorem: for finitely presented algebras, pointwise `Algebra.IsUnramifiedAt` implies
global `Algebra.GUnramified`. -/
theorem gUnramified_of_isUnramifiedAt [FinitePresentation R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    GUnramified R S := by
  exact gUnramified_of_gUnramifiedAt
    (fun q ↦ (gUnramifiedAt_iff_isUnramifiedAt R S q).2 (hlocal q))

/-- Helper for Lemma 10.151.3: for a fixed finite presentation, vanishing of `Ω[S⁄R]` makes the
cotangent complex map onto the cotangent space. -/
theorem ofFinitePresentation_cotangentComplex_surjective_of_formallyUnramified
    [FinitePresentation R S] [FormallyUnramified R S] :
    Function.Surjective
      ((Algebra.Presentation.ofFinitePresentation R S).toExtension.cotangentComplex) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  -- Exactness identifies the cotangent-complex range with the kernel of `toKaehler`.
  have hExact :
      LinearMap.ker P.toExtension.toKaehler =
        LinearMap.range P.toExtension.cotangentComplex := by
    exact (LinearMap.exact_iff).mp P.toExtension.exact_cotangentComplex_toKaehler
  -- Formal unramifiedness says the Kähler differentials are trivial, so the kernel is all of the
  -- cotangent space.
  have hKer :
      LinearMap.ker P.toExtension.toKaehler = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  exact LinearMap.range_eq_top.mp <| hExact.symm.trans hKer

/-- Helper for Lemma 10.151.3: the cotangent-complex image of one relation is the sum of its
evaluated partial derivatives in the canonical cotangent-space basis. -/
theorem presentation_relation_cotangentComplex_eq_sum_pderiv
    {R' : Type*} [CommRing R']
    {S' : Type*} [CommRing S'] [Algebra R' S']
    {ι σ : Type*} [Fintype ι]
    (P : Algebra.Presentation R' S' ι σ) (r : σ) :
    P.toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation r, P.relation_mem_ker r⟩) =
      ∑ i, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation r)) •
        P.cotangentSpaceBasis i := by
  -- Expand the cotangent-space element in the canonical basis.
  calc
    P.toExtension.cotangentComplex
        (Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation r, P.relation_mem_ker r⟩)
        =
      ∑ i,
        P.cotangentSpaceBasis.repr
            (P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) i •
          P.cotangentSpaceBasis i := by
          symm
          exact P.cotangentSpaceBasis.sum_repr _
    _ =
      ∑ i, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation r)) •
        P.cotangentSpaceBasis i := by
          -- The `i`-th coordinate is exactly the evaluated `i`-th partial derivative.
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Algebra.Extension.cotangentComplex_mk, P.cotangentSpaceBasis_repr_one_tmul]

/-- Helper for Lemma 10.151.3: for a fixed finite presentation of a formally unramified algebra,
each basis vector of the cotangent space is a finite `S`-linear combination of the relation
classes. -/
theorem finitePresentation_formallyUnramified_basis_in_range_data
    [FinitePresentation R S] [FormallyUnramified R S] :
    let P := Algebra.Presentation.ofFinitePresentation R S
    ∃ h : Fin (Algebra.Presentation.ofFinitePresentationVars R S) →
        Fin (Algebra.Presentation.ofFinitePresentationRels R S) → P.Ring,
      ∀ i,
        P.cotangentSpaceBasis i =
          ∑ r,
            MvPolynomial.aeval P.val (h i r) •
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have hsurj :
      Function.Surjective P.toExtension.cotangentComplex :=
    ofFinitePresentation_cotangentComplex_surjective_of_formallyUnramified (R := R) (S := S)
  have hCotSpan :
      Submodule.span S
          (Set.range fun r :
            Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
              Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩) = ⊤ := by
    -- The relation classes generate the cotangent module because the relations generate `ker`.
    exact Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension)
      P.relation P.span_range_relation_eq_ker
  have hRangeSpan :
      Submodule.span S
          (Set.range fun r :
            Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) = ⊤ := by
    -- Mapping the spanning relation classes through the surjective cotangent complex still spans
    -- the whole cotangent space.
    have hRangeEq :
        P.toExtension.cotangentComplex ''
            Set.range
              (fun r : Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
                Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩) =
          Set.range
            (fun r : Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) := by
      ext y
      constructor
      · rintro ⟨x, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨_, ⟨r, rfl⟩, rfl⟩
    calc
      Submodule.span S
          (Set.range fun r :
            Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩))
          =
        Submodule.map P.toExtension.cotangentComplex
          (Submodule.span S
            (Set.range fun r :
              Fin (Algebra.Presentation.ofFinitePresentationRels R S) ↦
                Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) := by
            rw [Submodule.map_span, hRangeEq]
      _ = ⊤ := by
            rw [hCotSpan, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  choose c hc using
    fun i : Fin (Algebra.Presentation.ofFinitePresentationVars R S) ↦
      (Submodule.mem_span_range_iff_exists_fun S).mp <| by
        rw [hRangeSpan]
        exact Submodule.mem_top
  refine ⟨fun i r ↦ P.σ (c i r), ?_⟩
  intro i
  -- Replace the `S`-coefficients by chosen polynomial representatives.
  calc
    P.cotangentSpaceBasis i
        = ∑ r,
            c i r •
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩) := (hc i).symm
    _ =
      ∑ r,
        MvPolynomial.aeval P.val (P.σ (c i r)) •
          P.toExtension.cotangentComplex
            (Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [P.aeval_val_σ]

/-- Helper for Lemma 10.151.3: for a fixed finite presentation of a formally unramified algebra,
the cotangent-basis surjectivity data can be rewritten as explicit polynomial coordinate-error
identities in the presentation ring. -/
theorem finitePresentation_formallyUnramified_coordinate_error_data
    [FinitePresentation R S] [FormallyUnramified R S] :
    let P := Algebra.Presentation.ofFinitePresentation R S
    ∃ h : Fin (Algebra.Presentation.ofFinitePresentationVars R S) →
        Fin (Algebra.Presentation.ofFinitePresentationRels R S) → P.Ring,
      ∃ a : Fin (Algebra.Presentation.ofFinitePresentationVars R S) →
          Fin (Algebra.Presentation.ofFinitePresentationVars R S) →
            Fin (Algebra.Presentation.ofFinitePresentationRels R S) → P.Ring,
        ∀ i j,
          (if i = j then 1 else 0 : P.Ring) -
              ∑ r, h i r * MvPolynomial.pderiv j (P.relation r) =
            ∑ r, a i j r * P.relation r := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R S
  obtain ⟨h, hh⟩ :=
    finitePresentation_formallyUnramified_basis_in_range_data (R := R) (S := S)
  have hrelation_coord :
      ∀ r j,
        P.cotangentSpaceBasis.repr
            (P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) j =
          MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
    intro r j
    -- Read the relation image in the cotangent-space basis.
    calc
      P.cotangentSpaceBasis.repr
          (P.toExtension.cotangentComplex
            (Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩)) j
          =
        P.cotangentSpaceBasis.repr
          (∑ i, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation r)) •
            P.cotangentSpaceBasis i) j := by
              rw [presentation_relation_cotangentComplex_eq_sum_pderiv (P := P) r]
      _ = MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
            rw [P.cotangentSpaceBasis.repr_sum_self]
  have hcoord_eval :
      ∀ i j,
        (if i = j then 1 else 0 : S) =
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
    intro i j
    -- Compare the `j`-th cotangent-space coordinate of the chosen basis expansion for `dxᵢ`.
    have hij :=
      congrArg (fun z ↦ P.cotangentSpaceBasis.repr z j) (hh i)
    calc
      (if i = j then 1 else 0 : S) = P.cotangentSpaceBasis.repr (P.cotangentSpaceBasis i) j := by
        simpa using (P.cotangentSpaceBasis.repr_self_apply (i := i) j).symm
      _ =
          P.cotangentSpaceBasis.repr
            (∑ r,
              MvPolynomial.aeval P.val (h i r) •
                P.toExtension.cotangentComplex
                  (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                    ⟨P.relation r, P.relation_mem_ker r⟩)) j := by
            exact hij
      _ =
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              P.cotangentSpaceBasis.repr
                (P.toExtension.cotangentComplex
                  (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                    ⟨P.relation r, P.relation_mem_ker r⟩)) j := by
            simp
      _ =
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [hrelation_coord r j]
  have hcoord_mem :
      ∀ i j,
        (if i = j then 1 else 0 : P.Ring) -
            ∑ r, h i r * MvPolynomial.pderiv j (P.relation r) ∈
          Ideal.span (Set.range P.relation) := by
    intro i j
    -- The coordinate defect evaluates to zero in `S`, hence lies in the relation ideal.
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    calc
      MvPolynomial.aeval P.val
          ((if i = j then 1 else 0 : P.Ring) -
            ∑ r, h i r * MvPolynomial.pderiv j (P.relation r))
          =
        (if i = j then 1 else 0 : S) -
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
              simp [map_sub, map_sum, map_mul]
      _ = 0 := by
            exact sub_eq_zero.mpr (hcoord_eval i j)
  choose a ha using
    fun i j ↦
      (Ideal.mem_span_range_iff_exists_fun (α := Fin (Algebra.Presentation.ofFinitePresentationRels R S))
        (x := (if i = j then 1 else 0 : P.Ring) -
          ∑ r, h i r * MvPolynomial.pderiv j (P.relation r))
        (v := P.relation)).mp (hcoord_mem i j)
  refine ⟨h, a, ?_⟩
  intro i j
  -- Repackage the ideal-membership witness in the source-facing equality form.
  exact (ha i j).symm

/-- Helper for Lemma 10.151.3: coordinate-error identities for a finite presentation force the
Kähler differentials to vanish, hence the algebra is formally unramified. -/
theorem presentation_formallyUnramified_of_coordinate_error_data
    {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (P : Algebra.Presentation R S ι σ)
    (h : ι → σ → P.Ring)
    (a : ι → ι → σ → P.Ring)
    (hcoord :
      ∀ i j,
        (if i = j then 1 else 0 : P.Ring) -
            ∑ r, h i r * MvPolynomial.pderiv j (P.relation r) =
          ∑ r, a i j r * P.relation r) :
    FormallyUnramified R S := by
  have hrelation_coord :
      ∀ r j,
        P.cotangentSpaceBasis.repr
            (P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) j =
          MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
    intro r j
    -- Read the relation image in coordinates using the canonical cotangent-space basis.
    calc
      P.cotangentSpaceBasis.repr
          (P.toExtension.cotangentComplex
            (Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩)) j
          =
        P.cotangentSpaceBasis.repr
          (∑ i, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation r)) •
            P.cotangentSpaceBasis i) j := by
              rw [presentation_relation_cotangentComplex_eq_sum_pderiv (P := P) r]
      _ = MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
            rw [P.cotangentSpaceBasis.repr_sum_self]
  have hcoord_eval :
      ∀ i j,
        (if i = j then 1 else 0 : S) =
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
    intro i j
    -- Apply `aeval` to the coordinate-error identity; the relation-error term vanishes in `S`.
    have hvanish :
        MvPolynomial.aeval P.val
          ((if i = j then 1 else 0 : P.Ring) -
              ∑ r, h i r * MvPolynomial.pderiv j (P.relation r)) = 0 := by
      rw [hcoord i j, map_sum]
      simp [map_mul]
    apply sub_eq_zero.mp
    calc
      (if i = j then 1 else 0 : S) -
          ∑ r,
            MvPolynomial.aeval P.val (h i r) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))
          =
        MvPolynomial.aeval P.val
          ((if i = j then 1 else 0 : P.Ring) -
            ∑ r, h i r * MvPolynomial.pderiv j (P.relation r)) := by
              simp [map_sub, map_sum, map_mul]
      _ = 0 := hvanish
  have hbasis_mem :
      ∀ i, P.cotangentSpaceBasis i ∈ LinearMap.range P.toExtension.cotangentComplex := by
    intro i
    refine ⟨∑ r,
      MvPolynomial.aeval P.val (h i r) •
        Algebra.Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation r, P.relation_mem_ker r⟩, ?_⟩
    -- The coordinate identities make the chosen cotangent-class sum map to `dxᵢ`.
    apply P.cotangentSpaceBasis.repr.injective
    ext j
    calc
      P.cotangentSpaceBasis.repr
          (P.toExtension.cotangentComplex
            (∑ r,
              MvPolynomial.aeval P.val (h i r) •
                Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) j
          =
        ∑ r,
          MvPolynomial.aeval P.val (h i r) *
            P.cotangentSpaceBasis.repr
              (P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) j := by
            simp
      _ =
        ∑ r,
          MvPolynomial.aeval P.val (h i r) *
            MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [hrelation_coord r j]
      _ = (if i = j then 1 else 0 : S) := (hcoord_eval i j).symm
      _ = P.cotangentSpaceBasis.repr (P.cotangentSpaceBasis i) j := by
            simpa using (P.cotangentSpaceBasis.repr_self_apply (i := i) j).symm
  have hRangeTop :
      LinearMap.range P.toExtension.cotangentComplex = ⊤ := by
    -- Once every basis vector lies in the range, the range is the whole cotangent space.
    exact (Submodule.eq_top_iff_forall_basis_mem (b := P.cotangentSpaceBasis)).2 hbasis_mem
  have hExact :
      LinearMap.ker P.toExtension.toKaehler =
        LinearMap.range P.toExtension.cotangentComplex := by
    exact (LinearMap.exact_iff).mp P.toExtension.exact_cotangentComplex_toKaehler
  have hzero :
      P.toExtension.toKaehler = 0 := by
    -- Exactness and the surjective cotangent complex force the Kähler map to vanish.
    exact LinearMap.ker_eq_top.mp (hExact.trans hRangeTop)
  refine (Algebra.formallyUnramified_iff R S).2 ?_
  refine ⟨?_⟩
  intro x y
  -- Surjectivity of `toKaehler` reduces equality in `Ω[S⁄R]` to the vanishing of the map.
  rcases P.toExtension.toKaehler_surjective x with ⟨x', rfl⟩
  rcases P.toExtension.toKaehler_surjective y with ⟨y', rfl⟩
  simp [hzero]

/-- Helper for Lemma 10.151.3: if the coefficient ring contains the coefficients of the
presentation and of one coordinate-error witness, then that witness descends to the model cut out
by `relationOfHasCoeffs`. -/
theorem coordinate_error_data_modelOfHasCoeffs
    {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (P : Algebra.Presentation R S ι σ)
    {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    [FaithfulSMul R₀ R]
    [P.HasCoeffs R₀]
    (h : ι → σ → P.Ring)
    (a : ι → ι → σ → P.Ring)
    (hhcoeffs : ∀ i r, ((h i r).coeffs : Set R) ⊆ Set.range (algebraMap R₀ R))
    (haccoeffs : ∀ i j r, ((a i j r).coeffs : Set R) ⊆ Set.range (algebraMap R₀ R))
    (hcoord :
      ∀ i j,
        (if i = j then 1 else 0 : P.Ring) -
            ∑ r, h i r * MvPolynomial.pderiv j (P.relation r) =
          ∑ r, a i j r * P.relation r) :
    ∃ h₀ : ι → σ → MvPolynomial ι R₀,
      ∃ a₀ : ι → ι → σ → MvPolynomial ι R₀,
        ∀ i j,
          (if i = j then 1 else 0 : MvPolynomial ι R₀) -
              ∑ r, h₀ i r * MvPolynomial.pderiv j (P.relationOfHasCoeffs R₀ r) =
            ∑ r, a₀ i j r * P.relationOfHasCoeffs R₀ r := by
  classical
  choose h₀ hh₀ using
    fun i r ↦ (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (hhcoeffs i r))
  choose a₀ ha₀ using
    fun i j r ↦ (MvPolynomial.mem_range_map_iff_coeffs_subset.mpr (haccoeffs i j r))
  refine ⟨h₀, a₀, ?_⟩
  intro i j
  -- Compare the descended identity after mapping it back to the original coefficient ring.
  apply MvPolynomial.map_injective (algebraMap R₀ R)
    (FaithfulSMul.algebraMap_injective R₀ R)
  -- The lifted witness maps to the original coordinate-error identity term-by-term.
  calc
    MvPolynomial.map (algebraMap R₀ R)
        ((if i = j then 1 else 0 : MvPolynomial ι R₀) -
          ∑ r, h₀ i r * MvPolynomial.pderiv j (P.relationOfHasCoeffs R₀ r))
        =
      (if i = j then 1 else 0 : P.Ring) -
        ∑ r, h i r * MvPolynomial.pderiv j (P.relation r) := by
          simp [hh₀, P.map_relationOfHasCoeffs, ← MvPolynomial.pderiv_map]
    _ = ∑ r, a i j r * P.relation r := hcoord i j
    _ =
      MvPolynomial.map (algebraMap R₀ R)
        (∑ r, a₀ i j r * P.relationOfHasCoeffs R₀ r) := by
          symm
          simp [ha₀, P.map_relationOfHasCoeffs]

-- Proof sketch: choose a finite presentation of `S` over `R`; the relations expressing the
-- vanishing of `Ω[S⁄R]` involve only finitely many coefficients, so they descend to a finitely
-- generated `ℤ`-subalgebra `R₀ ⊆ R` and a finitely presented formally unramified `R₀`-algebra
-- `S₀` whose base change recovers `S`.
/-- Helper for Lemma 10.151.3: descend a finitely presented formally unramified algebra to a
finite type `ℤ`-model whose base change recovers the original algebra. -/
theorem exists_formallyUnramified_model_over_Z_of_finitePresentation
    [FinitePresentation R S] [FormallyUnramified R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : FinitePresentation R₀ S₀)
      (_ : FormallyUnramified R₀ S₀) (_ : Algebra R₀ R),
      Nonempty ((R ⊗[R₀] S₀) ≃ₐ[R] S) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation R S
  obtain ⟨h, a, hcoord⟩ :=
    finitePresentation_formallyUnramified_coordinate_error_data (R := R) (S := S)
  let hCoeffSet : Set R := ⋃ i, ⋃ r, ((h i r).coeffs : Set R)
  let aCoeffSet : Set R := ⋃ i, ⋃ j, ⋃ r, ((a i j r).coeffs : Set R)
  let coeffSet : Set R := P.coeffs ∪ hCoeffSet ∪ aCoeffSet
  let A₀ : Subalgebra ℤ R := Algebra.adjoin ℤ coeffSet
  have hPcoeffs : P.HasCoeffs A₀ := by
    refine ⟨?_⟩
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin <| by
      exact Or.inl <| Or.inl hx⟩, rfl⟩
  letI : P.HasCoeffs A₀ := hPcoeffs
  have hCoeffSet_finite : hCoeffSet.Finite := by
    refine Set.finite_iUnion ?_
    intro i
    refine Set.finite_iUnion ?_
    intro r
    exact Finset.finite_toSet (h i r).coeffs
  have haCoeffSet_finite : aCoeffSet.Finite := by
    refine Set.finite_iUnion ?_
    intro i
    refine Set.finite_iUnion ?_
    intro j
    refine Set.finite_iUnion ?_
    intro r
    exact Finset.finite_toSet (a i j r).coeffs
  have hcoeffSet_finite : coeffSet.Finite := by
    simpa [coeffSet, Set.union_assoc] using
      P.finite_coeffs.union (hCoeffSet_finite.union haCoeffSet_finite)
  have hA₀FiniteType : FiniteType ℤ A₀ := by
    exact Algebra.FiniteType.adjoin_of_finite (R := ℤ) (A := R) hcoeffSet_finite
  letI : FiniteType ℤ A₀ := hA₀FiniteType
  have hhcoeffs :
      ∀ i r, ((h i r).coeffs : Set R) ⊆ Set.range (algebraMap A₀ R) := by
    intro i r x hx
    exact ⟨⟨x, Algebra.subset_adjoin <| by
      exact Or.inl <| Or.inr <| Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨r, hx⟩⟩⟩, rfl⟩
  have haccoeffs :
      ∀ i j r, ((a i j r).coeffs : Set R) ⊆ Set.range (algebraMap A₀ R) := by
    intro i j r x hx
    exact ⟨⟨x, Algebra.subset_adjoin <| by
      exact Or.inr <| Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨r, hx⟩⟩⟩⟩,
      rfl⟩
  let S₀ := P.ModelOfHasCoeffs A₀
  letI : CommRing S₀ := inferInstance
  letI : Algebra A₀ S₀ := inferInstance
  letI : FinitePresentation A₀ S₀ := inferInstance
  obtain ⟨h₀, a₀, h₀coord⟩ :=
    coordinate_error_data_modelOfHasCoeffs
      (P := P) (R₀ := A₀) h a hhcoeffs haccoeffs hcoord
  have hS₀FormallyUnramified : FormallyUnramified A₀ S₀ := by
    let P₀ : Algebra.Presentation A₀ S₀
        (Fin (Algebra.Presentation.ofFinitePresentationVars R S))
        (Fin (Algebra.Presentation.ofFinitePresentationRels R S)) :=
      Algebra.Presentation.naive (v := P.relationOfHasCoeffs A₀)
    -- Re-run the coordinate-error argument on the descended naive presentation over `A₀`.
    simpa [P₀] using
      presentation_formallyUnramified_of_coordinate_error_data
        (R := A₀) (S := S₀) (P := P₀) h₀ a₀ h₀coord
  letI : FormallyUnramified A₀ S₀ := hS₀FormallyUnramified
  refine ⟨A₀, inferInstance, inferInstance, inferInstance, S₀, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  -- The tensor model over `A₀` is already the source-faithful descended witness.
  exact ⟨P.tensorModelOfHasCoeffsEquiv A₀⟩

/-- Lemma 10.151.3 (23): a G-unramified ring map is obtained by base change from a G-unramified
map of finite type `ℤ`-algebras. -/
theorem exists_gUnramified_approximation_over_Z [GUnramified R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : GUnramified R₀ S₀)
      (_ : Algebra R₀ R), Nonempty ((R ⊗[R₀] S₀) ≃ₐ[R] S) := by
  letI : FormallyUnramified R S := inferInstance
  letI : FinitePresentation R S := inferInstance
  -- Route correction: reduce the G-unramified statement to the source-faithful formally
  -- unramified finite-presentation descent package, then rebuild `GUnramified` from the
  -- descended finite presentation.
  obtain ⟨R₀, hR₀Comm, hR₀Alg, hR₀FiniteType, S₀, hS₀Comm, hS₀Alg, hS₀FinitePresentation,
      hS₀FormallyUnramified, hRAlg, hbase⟩ :=
    exists_formallyUnramified_model_over_Z_of_finitePresentation (R := R) (S := S)
  letI : CommRing R₀ := hR₀Comm
  letI : Algebra ℤ R₀ := hR₀Alg
  letI : FiniteType ℤ R₀ := hR₀FiniteType
  letI : CommRing S₀ := hS₀Comm
  letI : Algebra R₀ S₀ := hS₀Alg
  letI : FinitePresentation R₀ S₀ := hS₀FinitePresentation
  letI : FormallyUnramified R₀ S₀ := hS₀FormallyUnramified
  letI : Algebra R₀ R := hRAlg
  letI : GUnramified R₀ S₀ := inferInstance
  exact ⟨R₀, hR₀Comm, hR₀Alg, hR₀FiniteType, S₀, hS₀Comm, hS₀Alg, inferInstance, hRAlg, hbase⟩

-- Proof sketch: descend a finite type presentation together with the relations forcing the module
-- of Kähler differentials to vanish to finitely many coefficients over a finite type `ℤ`-subalgebra
-- `R₀`; the descended algebra `S₀` is unramified over `R₀`, and the original `S` is recovered as
-- a quotient of its base change to `R`.
/-- Helper for Lemma 10.151.3: if a surjective polynomial map kills a finite family of relations,
then it factors through the corresponding quotient, and the induced quotient map is still
surjective. -/
theorem quotient_mvPolynomial_span_surjective
    {n : ℕ} {ι : Type*} (f : MvPolynomial (Fin n) R →ₐ[R] S) (hf : Function.Surjective f)
    (v : ι → MvPolynomial (Fin n) R) (hv : ∀ j, f (v j) = 0) :
    ∃ φ : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) →ₐ[R] S, Function.Surjective φ := by
  have hspan_le :
      Ideal.span (Set.range v) ≤ RingHom.ker f.toRingHom := by
    -- Each chosen relation already vanishes under `f`, so their span lands in the kernel.
    refine Ideal.span_le.2 ?_
    intro y hy
    rcases hy with ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hv j)
  have hspan :
      ∀ x : MvPolynomial (Fin n) R, x ∈ Ideal.span (Set.range v) → f x = 0 := by
    -- Repackage the kernel containment in the form expected by `Ideal.Quotient.liftₐ`.
    intro x hx
    exact RingHom.mem_ker.mp (hspan_le hx)
  refine ⟨Ideal.Quotient.liftₐ (Ideal.span (Set.range v)) f hspan, ?_⟩
  intro s
  rcases hf s with ⟨x, rfl⟩
  refine ⟨Ideal.Quotient.mkₐ R (Ideal.span (Set.range v)) x, ?_⟩
  -- The quotient lift agrees with the original polynomial map on quotient classes.
  simpa using
    DFunLike.congr_fun
      (Ideal.Quotient.liftₐ_comp (I := Ideal.span (Set.range v)) (f := f) hspan) x

/-- Helper for Lemma 10.151.3: a surjective polynomial presentation of a formally unramified
algebra admits kernel-indexed coordinate-error identities with finitely supported coefficients. -/
theorem surjective_mvPolynomial_coordinate_error_finsupp_data
    {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] S) (hf : Function.Surjective f)
    [FormallyUnramified R S] :
    ∃ h : Fin n → (RingHom.ker f.toRingHom →₀ MvPolynomial (Fin n) R),
      ∃ a : Fin n → Fin n → (RingHom.ker f.toRingHom →₀ MvPolynomial (Fin n) R),
        ∀ i j,
          (if i = j then 1 else 0 : MvPolynomial (Fin n) R) -
              (h i).sum (fun r c ↦ c * MvPolynomial.pderiv j r.1) =
            (a i j).sum (fun r c ↦ c * r.1) := by
  classical
  let P : Algebra.Presentation R S (Fin n) (RingHom.ker f.toRingHom) :=
    { toGenerators := Algebra.Generators.ofAlgHom f hf
      relation := fun r : RingHom.ker f.toRingHom ↦ r.1
      span_range_relation_eq_ker := by
        change
          Ideal.span (Set.range (Subtype.val : RingHom.ker f.toRingHom → MvPolynomial (Fin n) R)) =
            (Algebra.Generators.ofAlgHom f hf).ker
        rw [Algebra.Generators.ker_eq_ker_aeval_val]
        change
          Ideal.span (Set.range (Subtype.val : RingHom.ker f.toRingHom → MvPolynomial (Fin n) R)) =
            RingHom.ker (MvPolynomial.aeval (f ∘ MvPolynomial.X))
        rw [show MvPolynomial.aeval (f ∘ MvPolynomial.X) = f by
          ext x
          simp]
        rw [Subtype.range_coe_subtype]
        exact Ideal.span_eq (RingHom.ker f.toRingHom) }
  have hsurj :
      Function.Surjective P.toExtension.cotangentComplex := by
    -- Formal unramifiedness kills `Ω[S⁄R]`, so exactness makes the cotangent complex surjective.
    have hrange : LinearMap.range P.toExtension.cotangentComplex = ⊤ := by
      have hExact :
          LinearMap.range P.toExtension.cotangentComplex =
            LinearMap.ker P.toExtension.toKaehler :=
        (LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler).symm
      rw [hExact]
      ext x
      constructor
      · intro hx
        simp
      · intro hx
        change P.toExtension.toKaehler x = 0
        exact Subsingleton.elim _ _
    exact LinearMap.range_eq_top.mp hrange
  have hCotSpan :
      Submodule.span S
          (Set.range fun r : RingHom.ker f.toRingHom ↦
            Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩) = ⊤ := by
    -- The chosen kernel elements generate the cotangent module because they generate `ker f`.
    exact Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension)
      P.relation P.span_range_relation_eq_ker
  have hRangeSpan :
      Submodule.span S
          (Set.range fun r : RingHom.ker f.toRingHom ↦
            P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) = ⊤ := by
    -- Mapping the spanning relation classes through the surjective cotangent complex still spans
    -- the whole cotangent space.
    have hRangeEq :
        P.toExtension.cotangentComplex ''
            Set.range
              (fun r : RingHom.ker f.toRingHom ↦
                Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩) =
          Set.range
            (fun r : RingHom.ker f.toRingHom ↦
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) := by
      ext y
      constructor
      · rintro ⟨x, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, rfl⟩
      · rintro ⟨r, rfl⟩
        exact ⟨_, ⟨r, rfl⟩, rfl⟩
    calc
      Submodule.span S
          (Set.range fun r : RingHom.ker f.toRingHom ↦
            P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩))
          =
        Submodule.map P.toExtension.cotangentComplex
          (Submodule.span S
            (Set.range fun r : RingHom.ker f.toRingHom ↦
              Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) := by
            rw [Submodule.map_span, hRangeEq]
      _ = ⊤ := by
            rw [hCotSpan, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  have hbasis_mem :
      ∀ i : Fin n,
        P.cotangentSpaceBasis i ∈
          Submodule.span S
            (Set.range fun r : RingHom.ker f.toRingHom ↦
              P.toExtension.cotangentComplex
                (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                  ⟨P.relation r, P.relation_mem_ker r⟩)) := by
    intro i
    rw [hRangeSpan]
    exact Submodule.mem_top
  choose c hc using
    fun i : Fin n ↦
      (Finsupp.mem_span_range_iff_exists_finsupp
        (R := S)
        (v := fun r : RingHom.ker f.toRingHom ↦
          P.toExtension.cotangentComplex
            (Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩))
        (x := P.cotangentSpaceBasis i)).mp (hbasis_mem i)
  let liftCoeff : S → MvPolynomial (Fin n) R :=
    fun s ↦ if hs : s = 0 then 0 else P.σ s
  have hliftCoeff_zero : liftCoeff 0 = 0 := by
    simp [liftCoeff]
  have hliftCoeff_spec : ∀ s, MvPolynomial.aeval P.val (liftCoeff s) = s := by
    intro s
    by_cases hs : s = 0
    · simp [liftCoeff, hs]
    · simp [liftCoeff, hs, P.aeval_val_σ]
  let h : Fin n → (RingHom.ker f.toRingHom →₀ MvPolynomial (Fin n) R) :=
    fun i ↦ Finsupp.mapRange liftCoeff hliftCoeff_zero (c i)
  have hrelation_coord :
      ∀ r j,
        P.cotangentSpaceBasis.repr
            (P.toExtension.cotangentComplex
              (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                ⟨P.relation r, P.relation_mem_ker r⟩)) j =
          MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
    intro r j
    -- Read the relation image in the cotangent-space basis.
    calc
      P.cotangentSpaceBasis.repr
          (P.toExtension.cotangentComplex
            (Algebra.Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation r, P.relation_mem_ker r⟩)) j
          =
        P.cotangentSpaceBasis.repr
          (∑ i, MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation r)) •
            P.cotangentSpaceBasis i) j := by
              rw [presentation_relation_cotangentComplex_eq_sum_pderiv (P := P) r]
      _ = MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r)) := by
            rw [P.cotangentSpaceBasis.repr_sum_self]
  have hcoord_eval :
      ∀ i j,
        (if i = j then 1 else 0 : S) =
          (h i).sum (fun r p ↦
            MvPolynomial.aeval P.val p *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))) := by
    intro i j
    -- Compare the `j`-th cotangent-space coordinate of the chosen basis expansion for `dxᵢ`.
    have hij :=
      congrArg (fun z ↦ P.cotangentSpaceBasis.repr z j) (hc i)
    calc
      (if i = j then 1 else 0 : S) = P.cotangentSpaceBasis.repr (P.cotangentSpaceBasis i) j := by
        simpa using (P.cotangentSpaceBasis.repr_self_apply (i := i) j).symm
      _ =
          P.cotangentSpaceBasis.repr
            ((c i).sum fun r s ↦
              s •
                P.toExtension.cotangentComplex
                  (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                    ⟨P.relation r, P.relation_mem_ker r⟩)) j := by
            simpa using hij.symm
      _ =
          ((c i).sum fun r s ↦
            P.cotangentSpaceBasis.repr
              (s •
                P.toExtension.cotangentComplex
                  (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                    ⟨P.relation r, P.relation_mem_ker r⟩))) j := by
            rw [map_finsuppSum]
      _ =
          (c i).sum (fun r s ↦
            s *
              P.cotangentSpaceBasis.repr
                (P.toExtension.cotangentComplex
                  (Algebra.Extension.Cotangent.mk (P := P.toExtension)
                    ⟨P.relation r, P.relation_mem_ker r⟩)) j) := by
            simp
      _ =
          (c i).sum (fun r s ↦
            s * MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))) := by
            apply Finsupp.sum_congr
            intro r hr
            rw [hrelation_coord]
      _ =
          (c i).sum (fun r s ↦
            MvPolynomial.aeval P.val (liftCoeff s) *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))) := by
            apply Finsupp.sum_congr
            intro r hr
            have hs : c i r ≠ 0 := Finsupp.mem_support_iff.mp hr
            have hlift : liftCoeff (c i r) = P.σ (c i r) := by
              unfold liftCoeff
              split_ifs with hzero
              · exact (hs hzero).elim
              · rfl
            rw [hlift]
            rw [P.aeval_val_σ]
      _ =
          (h i).sum (fun r p ↦
            MvPolynomial.aeval P.val p *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))) := by
            simp [h, liftCoeff, Finsupp.sum_mapRange_index]
  have hcoord_mem :
      ∀ i j,
        (if i = j then 1 else 0 : P.Ring) -
            (h i).sum (fun r p ↦ p * MvPolynomial.pderiv j (P.relation r)) ∈
          Ideal.span (Set.range P.relation) := by
    intro i j
    -- The coordinate defect evaluates to zero in `S`, hence lies in the relation ideal.
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker]
    calc
      MvPolynomial.aeval P.val
          ((if i = j then 1 else 0 : P.Ring) -
            (h i).sum (fun r p ↦ p * MvPolynomial.pderiv j (P.relation r)))
          =
        (if i = j then 1 else 0 : S) -
          (h i).sum (fun r p ↦
            MvPolynomial.aeval P.val p *
              MvPolynomial.aeval P.val (MvPolynomial.pderiv j (P.relation r))) := by
              rw [map_sub, map_finsuppSum]
              simp [map_mul]
      _ = 0 := by
            exact sub_eq_zero.mpr (hcoord_eval i j)
  choose a ha using
    fun i j ↦
      (Finsupp.mem_ideal_span_range_iff_exists_finsupp
        (x := (if i = j then 1 else 0 : P.Ring) -
          (h i).sum (fun r p ↦ p * MvPolynomial.pderiv j (P.relation r)))
        (v := P.relation)).mp (hcoord_mem i j)
  refine ⟨h, a, ?_⟩
  intro i j
  -- Repackage the ideal-membership witness in the source-facing equality form.
  exact (ha i j).symm

/-- Helper for Lemma 10.151.3: replace an unramified finite type algebra by a G-unramified
finite quotient which still surjects onto the original algebra. -/
theorem exists_gUnramified_finite_quotient_of_unramified [Unramified R S] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : GUnramified R A),
      ∃ φ : A →ₐ[R] S, Function.Surjective φ := by
  classical
  letI : FormallyUnramified R S := inferInstance
  letI : FiniteType R S := inferInstance
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S)).mp
    inferInstance
  obtain ⟨h, a, hcoord⟩ :=
    surjective_mvPolynomial_coordinate_error_finsupp_data (R := R) (S := S) f hf
  letI : DecidableEq (RingHom.ker f.toRingHom) := Classical.decEq _
  let K : Finset (RingHom.ker f.toRingHom) :=
    Finset.univ.biUnion fun i ↦
      (h i).support ∪ Finset.univ.biUnion fun j ↦ (a i j).support
  let v : { r : RingHom.ker f.toRingHom // r ∈ K } → MvPolynomial (Fin n) R :=
    fun r ↦ r.1.1
  let hK : Fin n → { r : RingHom.ker f.toRingHom // r ∈ K } → MvPolynomial (Fin n) R :=
    fun i r ↦ ((h i).subtypeDomain fun s ↦ s ∈ K) r
  let aK : Fin n → Fin n → { r : RingHom.ker f.toRingHom // r ∈ K } → MvPolynomial (Fin n) R :=
    fun i j r ↦ ((a i j).subtypeDomain fun s ↦ s ∈ K) r
  letI : Fintype { r : RingHom.ker f.toRingHom // r ∈ K } := K.fintypeCoeSort
  have hKsupport_h :
      ∀ i, ∀ r ∈ (h i).support, r ∈ K := by
    intro i r hr
    exact Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, Finset.mem_union.2 <| Or.inl hr⟩
  have hKsupport_a :
      ∀ i j, ∀ r ∈ (a i j).support, r ∈ K := by
    intro i j r hr
    exact Finset.mem_biUnion.2
      ⟨i, Finset.mem_univ i, Finset.mem_union.2 <| Or.inr <|
        Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hr⟩⟩
  have hcoordK :
      ∀ i j,
        (if i = j then 1 else 0 : MvPolynomial (Fin n) R) -
            ∑ r : { s : RingHom.ker f.toRingHom // s ∈ K },
              hK i r * MvPolynomial.pderiv j (v r) =
          ∑ r : { s : RingHom.ker f.toRingHom // s ∈ K },
            aK i j r * v r := by
    intro i j
    have hsum_hK :
        ((h i).subtypeDomain fun s ↦ s ∈ K).sum (fun r p ↦ p * MvPolynomial.pderiv j r.1) =
          (h i).sum (fun r p ↦ p * MvPolynomial.pderiv j r.1) := by
      simpa using
        (Finsupp.sum_subtypeDomain_index
          (v := h i) (p := fun s ↦ s ∈ K)
          (h := fun r p ↦ p * MvPolynomial.pderiv j r.1)
          (hKsupport_h i))
    have hsum_aK :
        ((a i j).subtypeDomain fun s ↦ s ∈ K).sum (fun r p ↦ p * r.1) =
          (a i j).sum (fun r p ↦ p * r.1) := by
      simpa using
        (Finsupp.sum_subtypeDomain_index
          (v := a i j) (p := fun s ↦ s ∈ K)
          (h := fun r p ↦ p * r.1)
          (hKsupport_a i j))
    -- Route correction: compress the kernel-indexed Finsupp witnesses directly to the finite
    -- support subtype, rather than introducing a second `Fin m` enumeration layer.
    calc
      (if i = j then 1 else 0 : MvPolynomial (Fin n) R) -
          ∑ r : { s : RingHom.ker f.toRingHom // s ∈ K },
            hK i r * MvPolynomial.pderiv j (v r)
          =
        (if i = j then 1 else 0 : MvPolynomial (Fin n) R) -
          ((h i).subtypeDomain fun s ↦ s ∈ K).sum
            (fun r p ↦ p * MvPolynomial.pderiv j r.1) := by
              rw [Finsupp.sum_fintype]
              simp [hK, v]
      _ =
        (if i = j then 1 else 0 : MvPolynomial (Fin n) R) -
          (h i).sum (fun r p ↦ p * MvPolynomial.pderiv j r.1) := by
            rw [hsum_hK]
      _ = (a i j).sum (fun r p ↦ p * r.1) := hcoord i j
      _ =
        ((a i j).subtypeDomain fun s ↦ s ∈ K).sum (fun r p ↦ p * r.1) := by
            exact hsum_aK.symm
      _ =
        ∑ r : { s : RingHom.ker f.toRingHom // s ∈ K },
          aK i j r * v r := by
            rw [Finsupp.sum_fintype]
            simp [aK, v]
  let A : Type u := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)
  letI : CommRing A := inferInstance
  letI : Algebra R A := inferInstance
  let P₀ : Algebra.Presentation R A (Fin n) { r : RingHom.ker f.toRingHom // r ∈ K } :=
    Algebra.Presentation.naive (v := v)
  have hA_formallyUnramified : FormallyUnramified R A := by
    -- The finite support subtype now gives a genuine finite presentation with the descended
    -- coordinate-error identities required by the source proof.
    simpa [P₀, hK, aK, v] using
      presentation_formallyUnramified_of_coordinate_error_data
        (R := R) (S := A) (P := P₀) hK aK hcoordK
  letI : FormallyUnramified R A := hA_formallyUnramified
  letI : FinitePresentation R A := P₀.finitePresentation_of_isFinite
  letI : GUnramified R A := inferInstance
  have hv : ∀ r : { s : RingHom.ker f.toRingHom // s ∈ K }, f (v r) = 0 := by
    intro r
    exact RingHom.mem_ker.mp r.1.2
  obtain ⟨φ, hφ⟩ :=
    quotient_mvPolynomial_span_surjective (R := R) (S := S) f hf v hv
  refine ⟨A, inferInstance, inferInstance, inferInstance, φ, hφ⟩

/-- Lemma 10.151.3 (24): an unramified ring map is a quotient of a base change of an unramified map
of finite type `ℤ`-algebras. -/
theorem exists_unramified_approximation_over_Z [Unramified R S] :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Unramified R₀ S₀)
      (_ : Algebra R₀ R), ∃ φ : R ⊗[R₀] S₀ →ₐ[R] S, Function.Surjective φ := by
  -- Route correction: first compress the unramified finite-type algebra to a G-unramified finite
  -- quotient, then apply clause (23) to that quotient and compose the resulting maps.
  obtain ⟨A, hAComm, hAAlg, hAGUnramified, φ, hφ⟩ :=
    exists_gUnramified_finite_quotient_of_unramified (R := R) (S := S)
  letI : CommRing A := hAComm
  letI : Algebra R A := hAAlg
  letI : GUnramified R A := hAGUnramified
  obtain ⟨R₀, hR₀Comm, hR₀Alg, hR₀FiniteType, S₀, hS₀Comm, hS₀Alg, hS₀GUnramified, hRAlg,
      hbase⟩ :=
    exists_gUnramified_approximation_over_Z (R := R) (S := A)
  letI : CommRing R₀ := hR₀Comm
  letI : Algebra ℤ R₀ := hR₀Alg
  letI : FiniteType ℤ R₀ := hR₀FiniteType
  letI : CommRing S₀ := hS₀Comm
  letI : Algebra R₀ S₀ := hS₀Alg
  letI : GUnramified R₀ S₀ := hS₀GUnramified
  letI : Unramified R₀ S₀ := inferInstance
  letI : Algebra R₀ R := hRAlg
  obtain ⟨e⟩ := hbase
  refine ⟨R₀, hR₀Comm, hR₀Alg, hR₀FiniteType, S₀, hS₀Comm, hS₀Alg, inferInstance, hRAlg, ?_⟩
  refine ⟨φ.comp e.toAlgHom, ?_⟩
  intro s
  rcases hφ s with ⟨a, rfl⟩
  refine ⟨e.symm a, ?_⟩
  simp

end Algebra
