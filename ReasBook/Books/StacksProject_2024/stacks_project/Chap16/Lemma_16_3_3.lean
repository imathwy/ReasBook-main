import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_136_17
import StacksProject_2024.stacks_project.Chap10.Lemma_10_137_9
import StacksProject_2024.stacks_project.Chap10.Lemma_10_149_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_33_5
import StacksProject_2024.stacks_project.Chap16.Lemma_16_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Helper for Lemma 16.3.3: over a field base, every residue field is canonically identified with
the base field itself. -/
private noncomputable def fieldPrimeResidueFieldAlgEquivSelf
    {k : Type*} [Field k] (p : PrimeSpectrum k) :
    p.asIdeal.ResidueField ≃ₐ[k] k := by
  let φ : k →ₐ[k] p.asIdeal.ResidueField := IsScalarTower.toAlgHom k k p.asIdeal.ResidueField
  have hκ : Function.Bijective φ := by
    constructor
    · exact RingHom.injective _
    · simpa using (Ideal.algebraMap_residueField_surjective p.asIdeal)
  exact (AlgEquiv.ofBijective φ hκ).symm

/-- Helper for Lemma 16.3.3: over a field base, every fiber is canonically another copy of the
target algebra. -/
private noncomputable def fieldPrimeFiberAlgEquivSelf
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    (p : PrimeSpectrum k) :
    p.asIdeal.Fiber B ≃ₐ[k] B :=
  (Algebra.TensorProduct.congr
      (fieldPrimeResidueFieldAlgEquivSelf p)
      (AlgEquiv.refl : B ≃ₐ[k] B)).trans
    (Algebra.TensorProduct.lid k B)

/-- Helper for Lemma 16.3.3: over a field base, every fiber has the same Krull dimension as the
ambient algebra. -/
private theorem ringKrullDim_fieldFiber_eq
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    (p : PrimeSpectrum k) :
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim B := by
  -- Proof comment: compare the fiber with the original algebra before invoking any complete-
  -- intersection owner.
  simpa using
    ringKrullDim_eq_of_ringEquiv (fieldPrimeFiberAlgEquivSelf (B := B) p).toRingEquiv

/-- Helper for Lemma 16.3.3: over a field base, a presentation whose displayed dimension already
matches the algebra's Krull dimension is automatically a relative global complete intersection
presentation. -/
private lemma presentationIsRelativeGlobalCompleteIntersectionOfField
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    {n c : ℕ} (P : Algebra.Presentation k B (Fin n) (Fin c))
    (hP : ringKrullDim B = P.dimension) :
    P.IsRelativeGlobalCompleteIntersection := by
  intro p _hp
  -- Proof comment: over a field base, the only fiber is another copy of the same algebra.
  calc
    ringKrullDim (p.asIdeal.Fiber B) = ringKrullDim B :=
      ringKrullDim_fieldFiber_eq (B := B) p
    _ = P.dimension := hP

/-- Helper for Lemma 16.3.3: every prime localization of a syntomic fiber is a complete
intersection over the corresponding residue field. -/
private lemma fiberCompleteIntersectionOver_atPrime
    {C : Type*} [CommRing C] [Algebra R C]
    (hC : (algebraMap R C).Syntomic) (p : PrimeSpectrum R) :
    ∀ q : PrimeSpectrum (p.asIdeal.Fiber C),
      Algebra.IsCompleteIntersectionOver p.asIdeal.ResidueField
        (Localization.AtPrime q.asIdeal) := by
  let k := p.asIdeal.ResidueField
  let B := p.asIdeal.Fiber C
  have hlocal : IsLocalCompleteIntersection k B := by
    -- Proof comment: syntomicity packages the field-fiber local-complete-intersection owner.
    simpa [k, B] using hC.hasLocalCompleteIntersectionFibers p
  -- Proof comment: unfold the local-complete-intersection owner into the primewise complete-
  -- intersection localizations supplied by the Chapter 10 TFAE.
  exact
    ((isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
      (k := k) (S := B)).out 0 1 rfl rfl).mp hlocal

/-- Helper for Lemma 16.3.3: base changing the chosen presentation to a residue field preserves
its displayed dimension. -/
private lemma presentationBaseChange_dimension_eq
    {C : Type*} [CommRing C] [Algebra R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c)) (p : PrimeSpectrum R) :
    (P.baseChange p.asIdeal.ResidueField).dimension = P.dimension := by
  -- Proof comment: base change keeps the same generator and relation counts, so the presentation
  -- dimension `n - c` is unchanged.
  rfl

/-- Helper for Lemma 16.3.3: primewise complete-intersection fibers package into the field-level
local-complete-intersection owner on the whole fiber. -/
private lemma fiberIsLocalCompleteIntersection_of_completeIntersectionOver_atPrime
    {C : Type*} [CommRing C] [Algebra R C]
    (hci :
      ∀ p : PrimeSpectrum R,
        ∀ q : PrimeSpectrum (p.asIdeal.Fiber C),
          Algebra.IsCompleteIntersectionOver p.asIdeal.ResidueField
            (Localization.AtPrime q.asIdeal))
    (p : PrimeSpectrum R) :
    IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber C) := by
  -- Proof comment: the Chapter 10 TFAE turns the primewise complete-intersection local rings into
  -- the intrinsic fiberwise local-complete-intersection owner.
  exact
    ((isLocalCompleteIntersection_tfae_completeIntersectionOver_localRings
      (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber C)).out 1 0 rfl rfl).mp (hci p)

/-- Helper for Lemma 16.3.3: once the fiber-dimension formula is known primewise, it is exactly
the presentation-level relative-global-complete-intersection condition. -/
private lemma presentation_relativeGlobalCompleteIntersection_of_fiberDimension
    {C : Type*} [CommRing C] [Algebra R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c))
    (hP :
      ∀ p : PrimeSpectrum R,
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber C)) →
          ringKrullDim (p.asIdeal.Fiber C) = P.dimension) :
    P.IsRelativeGlobalCompleteIntersection := by
  -- Proof comment: `Presentation.IsRelativeGlobalCompleteIntersection` is defined by this exact
  -- primewise fiber-dimension equality.
  intro p hp
  exact hP p hp

/-- Helper for Lemma 16.3.3: localizing a free conormal module preserves its finite rank. -/
private lemma targetLocalization_cotangent_finrank_eq
    {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S]
    (P : Algebra.Extension k S) {c : ℕ}
    (b : Module.Basis (Fin c) S P.Cotangent)
    (q : PrimeSpectrum S) :
    Module.finrank (Localization.AtPrime q.asIdeal)
      ((P.localization q.asIdeal.primeCompl : Algebra.Extension k
        (Localization.AtPrime q.asIdeal)).Cotangent) = c := by
  let Ploc : Algebra.Extension k (Localization.AtPrime q.asIdeal) :=
    P.localization q.asIdeal.primeCompl
  let f : P.Cotangent →ₗ[S] Ploc.Cotangent :=
    Algebra.Extension.Cotangent.map
      (P.toLocalization q.asIdeal.primeCompl : P.Hom Ploc)
  let _ : Module.Free S P.Cotangent := Module.Free.of_basis b
  let _ : IsLocalizedModule q.asIdeal.primeCompl f :=
    Algebra.Extension.conormalModule_targetLocalization_isLocalizedModule
      (P := P) (T := q.asIdeal.primeCompl)
  -- Proof comment: the owner-level localization theorem turns the target cotangent map into a
  -- localized module, so finrank is unchanged under localization of the free source module.
  calc
    Module.finrank (Localization.AtPrime q.asIdeal)
        ((P.localization q.asIdeal.primeCompl : Algebra.Extension k
          (Localization.AtPrime q.asIdeal)).Cotangent) =
      Module.finrank S P.Cotangent := by
        simpa [f] using
          (Module.finrank_of_isLocalizedModule_of_free
            (Rₛ := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl f)
    _ = c := by simpa using Module.finrank_eq_card_basis b

/-- Helper for Lemma 16.3.3: a presentation whose residue-field fibers are locally complete
intersections and whose base-changed cotangent modules stay free has the expected fiber dimension.
-/
private lemma fiberDimension_eq_presentationDimension_of_fiberCompleteIntersection_and_cotangentFree
    {C : Type*} [CommRing C] [Algebra R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c))
    (b : Module.Basis (Fin c) C P.toExtension.Cotangent)
    (hci :
      ∀ p : PrimeSpectrum R,
        ∀ q : PrimeSpectrum (p.asIdeal.Fiber C),
          Algebra.IsCompleteIntersectionOver p.asIdeal.ResidueField
            (Localization.AtPrime q.asIdeal)) :
    ∀ p : PrimeSpectrum R,
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber C)) →
        ringKrullDim (p.asIdeal.Fiber C) = P.dimension := by
  intro p hp
  let k := p.asIdeal.ResidueField
  let B := p.asIdeal.Fiber C
  let Pp := P.baseChange k
  have hlocal : IsLocalCompleteIntersection k B :=
    fiberIsLocalCompleteIntersection_of_completeIntersectionOver_atPrime
      (R := R) (C := C) hci p
  -- Proof comment: the only remaining work is the local dimension-drop comparison on the fiber,
  -- now phrased on the canonical base-changed presentation itself and the basis produced by
  -- `exists_presentation_of_free_cotangent`.
  let _ := hlocal
  let _ := hp
  -- Route correction: the old route incorrectly treated an arbitrary base-changed presentation as
  -- having free cotangent of rank equal to its displayed number of relations. The corrected route
  -- uses the actual cotangent basis `b`; the remaining blocker is transporting the localized
  -- finrank statement coming from `targetLocalization_cotangent_finrank_eq` to the
  -- `PolynomialPresentationAtPrime` local quotient model used by the Chapter 10 complete-
  -- intersection TFAE and regular-local dimension-drop theorem.
  -- TODO: compare `(Pp.toExtension.localization q.asIdeal.primeCompl).Cotangent` with
  -- `PolynomialPresentationAtPrime.localizedConormalModule Pp.toAlgHom q`, using the localized
  -- finrank equality supplied by `targetLocalization_cotangent_finrank_eq (P := Pp.toExtension)`;
  -- then feed the resulting rank `c` into `PolynomialPresentationAtPrime.tfae` and globalize the
  -- maximal-local
  -- dimension equality to `ringKrullDim B = P.dimension`.
  sorry

/-- Helper for Lemma 16.3.3: the `a = 1` chart from Lemma `16.3.1` transports the localized
smooth structure and free-cotangent generators back to the original algebra `C`. -/
lemma smoothAndGeneratorsOfAwayOne
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    {n : ℕ}
    (hSmoothAway : Smooth (Localization.Away (1 : A)) (Localization.Away (1 : C)))
    (Paway : Generators R (Localization.Away (1 : C)) (Fin n))
    (hfreeAway : Module.Free (Localization.Away (1 : C)) Paway.toExtension.Cotangent) :
    Smooth A C ∧ ∃ P : Generators R C (Fin n), Module.Free C P.toExtension.Cotangent := by
  constructor
  · -- Proof comment: compose the smooth map `A → A[1]` with the away-one smooth chart
    -- `A[1] → C[1]`, then transport back along the canonical `C[1] ≃ C` equivalence.
    letI : Smooth A (Localization.Away (1 : A)) :=
      Algebra.Smooth.of_isLocalization_Away (R := A) (A := Localization.Away (1 : A)) 1
    letI : Smooth (Localization.Away (1 : A)) (Localization.Away (1 : C)) := hSmoothAway
    letI : Smooth A (Localization.Away (1 : C)) :=
      Algebra.Smooth.comp
        (R := A) (A := Localization.Away (1 : A)) (B := Localization.Away (1 : C))
    exact
      Algebra.Smooth.of_equiv
        (((IsLocalization.atOne C (Localization.Away (1 : C))).restrictScalars A).symm)
  · -- Proof comment: the away-one localization of `C` is canonically `C`, so the localized
    -- generators and their free cotangent module transport directly across that equivalence.
    let eC : Localization.Away (1 : C) ≃ₐ[R] C :=
      ((IsLocalization.atOne C (Localization.Away (1 : C))).restrictScalars R).symm
    refine ⟨Paway.ofAlgEquiv eC, ?_⟩
    simpa [eC] using hfreeAway

/-- Helper for Lemma 16.3.3: a syntomic algebra equipped with a finite generator family whose
cotangent module is free admits a presentation witnessing the relative global complete
intersection property. -/
lemma exists_relativeGlobalCompleteIntersectionPresentation_of_syntomic_of_freeCotangent
    {C : Type*} [CommRing C] [Algebra R C]
    {n : ℕ} (P : Generators R C (Fin n))
    (hfree : Module.Free C P.toExtension.Cotangent)
    (hC : (algebraMap R C).Syntomic) :
    ∃ (c : ℕ) (P' : Algebra.Presentation R C (Fin n) (Fin c)),
      P'.IsRelativeGlobalCompleteIntersection := by
  -- Proof comment: upgrade the free-cotangent generator family to a presentation whose displayed
  -- relations generate the cotangent module, then close the relative-global-complete-intersection
  -- condition fiberwise using the syntomic local-complete-intersection fibers.
  obtain ⟨P', b, _hP', _hb⟩ := Algebra.Generators.exists_presentation_of_free_cotangent P
  have hfiberCompleteIntersection :
      ∀ p : PrimeSpectrum R,
        ∀ q : PrimeSpectrum (p.asIdeal.Fiber C),
          Algebra.IsCompleteIntersectionOver p.asIdeal.ResidueField
            (Localization.AtPrime q.asIdeal) :=
    fiberCompleteIntersectionOver_atPrime (R := R) (C := C) hC
  have hfiberDimension :
      ∀ p : PrimeSpectrum R,
        Nonempty (PrimeSpectrum (p.asIdeal.Fiber C)) →
          ringKrullDim (p.asIdeal.Fiber C) = P'.dimension :=
    fiberDimension_eq_presentationDimension_of_fiberCompleteIntersection_and_cotangentFree
      (R := R) (C := C) P' b hfiberCompleteIntersection
  refine ⟨_, P', ?_⟩
  -- Proof comment: the main theorem now reduces to the single primewise fiber-dimension formula
  -- isolated in the helper above.
  exact
    presentation_relativeGlobalCompleteIntersection_of_fiberDimension
      (R := R) (C := C) P' hfiberDimension

/- Domain-style sampling:
- primary domain: syntomic ring maps, smooth retractions, and relative global complete
  intersections;
- sampled owner declarations:
  `RingHom.Syntomic`,
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `exists_finiteType_retraction_with_smoothing_localizations`,
  `Algebra.Generators.exists_presentation_of_free_cotangent`;
- best owner abstraction:
  the ambient canonical owners are `RingHom.Syntomic` for `R → A` and
  `Algebra.IsRelativeGlobalCompleteIntersection R C` for the output algebra `C`; the localized
  free-cotangent presentations from Lemma `16.3.1` are bridge data used to construct the global
  complete-intersection owner and should not survive here as a parallel public wrapper;
- primitive vs. derived:
  this lemma exports only the smooth `A`-algebra retract and the canonical relative-global-complete
  intersection owner; finite presentation and local presentation data are derived API coming from
  those owners.

Source/core/bridge triage:
- `source-facing`: the existence of a smooth `A`-algebra retract `C` that is a relative global
  complete intersection over `R`;
- `core/canonical`: `RingHom.Syntomic` and `Algebra.IsRelativeGlobalCompleteIntersection`;
- `bridge/view`: `exists_finiteType_retraction_with_smoothing_localizations`, whose localized free
  cotangent presentations are converted into the source-facing owner below.
-/
-- Proof sketch: apply
-- `exists_finiteType_retraction_with_smoothing_localizations` to the syntomic map `R → A` to
-- obtain an `A`-algebra `C` with an `A`-algebra retraction such that `A → C` is smooth and the
-- localizations `C_a` admit free cotangent presentations over `R`. Then use
-- `Algebra.Generators.exists_presentation_of_free_cotangent` to replace those local presentations
-- by finite presentations whose defining equations map to bases of the corresponding conormal
-- modules, and apply Lemma `10.135.4` fiberwise to identify the fiber dimensions with the
-- presentation dimension.
/-- Lemma 16.3.3: if `R → A` is syntomic, then there exists an `A`-algebra `C` with an `A`-algebra
retraction `C → A` such that `A → C` is smooth and `C` is a relative global complete intersection
over `R`. The presentation-theoretic form of the last condition is packaged by the owner
`IsRelativeGlobalCompleteIntersection R C`, rather than by a separate local wrapper in this file. -/
theorem exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic
    (hA : (algebraMap R A).Syntomic) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra A C)
      (_ : IsScalarTower R A C) (_ : Smooth A C) (r : C →ₐ[A] A),
      IsRelativeGlobalCompleteIntersection R C := by
  letI : FinitePresentation R A :=
    RingHom.finitePresentation_algebraMap.mp hA.finitePresentation
  -- Proof comment: first pass from the syntomic input to the local-complete-intersection owner
  -- required by Lemma `16.3.1`.
  have hciA : RingHom.IsLocalCompleteIntersection (algebraMap R A) :=
    (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection (algebraMap R A)).mp hA |>.2
  obtain ⟨C, _hC, _hRC, _hAC, _hTower, _hftAC, r, hlocal, _homega⟩ :=
    exists_finiteType_retraction_with_smoothing_localizations (R := R) (A := A)
  -- Proof comment: specialize the localized retraction theorem to the trivial chart `D(1)`.
  have hA1Syntomic : (algebraMap R (Localization.Away (1 : A))).Syntomic := by
    letI : Smooth A (Localization.Away (1 : A)) :=
      Algebra.Smooth.of_isLocalization_Away (R := A) (A := Localization.Away (1 : A)) 1
    have hloc :
        (algebraMap A (Localization.Away (1 : A))).Syntomic := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (Algebra.smooth_syntomic (R := A) (S := Localization.Away (1 : A)))
    have hcomp :
        (algebraMap A (Localization.Away (1 : A))).comp (algebraMap R A) =
          algebraMap R (Localization.Away (1 : A)) := by
      ext x
      rfl
    exact hcomp ▸ RingHom.Syntomic.comp hA hloc
  have hciA1 : RingHom.IsLocalCompleteIntersection (algebraMap R (Localization.Away (1 : A))) :=
    (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection
      (algebraMap R (Localization.Away (1 : A)))).mp hA1Syntomic |>.2
  obtain ⟨hSmoothAway, n, Paway, hfreeAway⟩ := hlocal 1 hciA1
  -- Proof comment: the trivial chart `D(1)` already identifies the localized output of Lemma
  -- `16.3.1` with a global smooth algebra and a global free-cotangent generator family.
  obtain ⟨hSmoothC, P, hfree⟩ :=
    smoothAndGeneratorsOfAwayOne (R := R) (A := A) hSmoothAway Paway hfreeAway
  -- Proof comment: once `A → C` is smooth, the composite `R → C` is syntomic.
  have hCSyntomic : (algebraMap R C).Syntomic := by
    letI : Smooth A C := hSmoothC
    have hACSyntomic : (algebraMap A C).Syntomic := by
      simpa [RingHom.algebraMap_toAlgebra] using (Algebra.smooth_syntomic (R := A) (S := C))
    have hcomp : (algebraMap A C).comp (algebraMap R A) = algebraMap R C := by
      ext x
      rfl
    exact hcomp ▸ RingHom.Syntomic.comp hA hACSyntomic
  letI : FinitePresentation R C :=
    RingHom.finitePresentation_algebraMap.mp hCSyntomic.finitePresentation
  obtain ⟨c, P', hP'⟩ :=
    exists_relativeGlobalCompleteIntersectionPresentation_of_syntomic_of_freeCotangent
      (R := R) (C := C) P hfree hCSyntomic
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, hSmoothC, r, ?_⟩
  -- Proof comment: the helper theorem isolates the remaining presentation-level bridge from the
  -- free-cotangent presentation to the intrinsic relative-global-complete-intersection owner.
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P') hP'

end

end Algebra
