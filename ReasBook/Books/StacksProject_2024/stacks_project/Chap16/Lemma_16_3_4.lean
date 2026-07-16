import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_137_12
import StacksProject_2024.stacks_project.Chap10.Lemma_10_137_15
import StacksProject_2024.stacks_project.Chap10.Lemma_10_137_9
import StacksProject_2024.stacks_project.Chap16.Lemma_16_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/- Domain-style sampling for smooth retractions with standard smooth targets:
* primary domain: smooth commutative algebra, syntomic factorization, and standard smooth
  presentations;
* sampled owner declarations:
  `Smooth R A`,
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic`,
  `Algebra.IsStandardSmooth`;
* best owner abstraction:
  the ambient owners are `Smooth R A` for the input algebra, the Chapter 16 retraction theorem
  `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` for the retract data,
  and `Algebra.IsStandardSmooth R B` for the strengthened target conclusion;
* primitive vs. derived:
  the primitive public output is only the smooth `A`-algebra retract together with the standard
  smooth owner on the target. The syntomic upgrade and the relative-global-complete-intersection
  witness are bridge data from upstream owners and should not be repackaged here as a parallel
  local wrapper.

Source/core/bridge triage:
* `source-facing`: the existence of a smooth `A`-algebra retract `B` that is standard smooth over
  `R`;
* `core/canonical`: `Smooth`, `RingHom.Syntomic`, `Algebra.IsStandardSmooth`, and the Chapter 16
  retraction owner theorem;
* `bridge/view`: the intermediate relative-global-complete-intersection presentation obtained from
  syntomicity, together with the bridge theorem `smooth_syntomic` converting the input smoothness
  hypothesis into the syntomic hypothesis needed for that retraction theorem.
-/

-- Proof sketch: first apply the bridge theorem `smooth_syntomic` to view the smooth map `R → A`
-- as syntomic. Then invoke the Chapter 16 retraction theorem
-- `exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic` to obtain a smooth
-- `A`-algebra retraction `A → B → A` with `B` a relative global complete intersection over `R`.
-- Finally apply the Stacks Jacobian argument to that retract presentation to promote the target to
-- the canonical owner `IsStandardSmooth R B`, while preserving the same retract shape over `A`.
/-- Helper for Lemma 16.3.4: an `A`-algebra retraction sends a target-spanning family in `C` to a
family spanning the unit ideal in `A`. -/
lemma ideal_span_image_retraction_eq_top
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (r : C →ₐ[A] A) {s : Set C} (hs : Ideal.span s = ⊤) :
    Ideal.span (r '' s) = ⊤ := by
  -- Proof comment: mapping the spanning ideal along the retraction preserves the top ideal, and
  -- the image of a span is the span of the image family.
  calc
    Ideal.span (r '' s) = Ideal.map r.toRingHom (Ideal.span s) := by
      rw [Ideal.map_span]
    _ = ⊤ := by
      simpa [hs]

/-- Helper for Lemma 16.3.4: localizing a retract stage away from an element whose image under the
retraction is a unit extends the retraction over the same base ring. -/
noncomputable lemma localizationAway_retraction_of_isUnit
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (r : C →ₐ[A] A) (c : C) (hc : IsUnit (r c)) :
    ∃ r' : Localization.Away c →ₐ[A] A,
      r'.comp (algebraMap C (Localization.Away c)) = r := by
  let r' : Localization.Away c →ₐ[A] A :=
    IsLocalization.liftAlgHom (A := A) (R := C) (M := Submonoid.powers c)
      (S := Localization.Away c) (P := A) (f := r) (fun y ↦ by
        rcases y.2 with ⟨n, rfl⟩
        simpa using IsUnit.map (powMonoidHom n : A →* A) hc)
  refine ⟨r', ?_⟩
  -- Proof comment: the localization lift agrees with the original retraction on the image of `C`.
  ext x
  simp [r', IsLocalization.liftAlgHom]

/-- Helper for Lemma 16.3.4: a smooth relative-global-complete-intersection retract stage admits
one fixed polynomial presentation together with a section modulo the square of the presentation
kernel. -/
lemma existsPresentationWithKerSquareSection
    {C : Type*} [CommRing C] [Algebra R C] [Smooth R C]
    (hrel : IsRelativeGlobalCompleteIntersection R C) :
    ∃ (n c : ℕ) (P : Algebra.Presentation R C (Fin n) (Fin c))
      (σ : C →ₐ[R] MvPolynomial (Fin n) R ⧸ (RingHom.ker P.toAlgHom.toRingHom) ^ 2),
      P.IsRelativeGlobalCompleteIntersection ∧
        P.toAlgHom.kerSquareLift.comp σ = AlgHom.id R C := by
  -- Proof comment: freeze one relative-GCI presentation of `C`, then apply the canonical
  -- polynomial-presentation criterion for formal smoothness to that fixed surjection.
  obtain ⟨n, c, P, hP⟩ := hrel.exists_presentation
  have hform : Algebra.FormallySmooth R C :=
    Algebra.Smooth.formallySmooth (R := R) (A := C)
  obtain ⟨σ, hσ⟩ :=
    (formallySmooth_iff_exists_polynomial_presentation_section_mod_ker_sq
      (R := R) (ι := Fin n) (S := C) P.toAlgHom P.algebraMap_surjective).mp hform
  exact ⟨n, c, P, σ, hP, hσ⟩

/-- Helper for Lemma 16.3.4: once a standard-smooth localization of the retract stage maps to a
unit in `A`, that localization already provides the desired smooth retract target. -/
noncomputable lemma smooth_retraction_of_standardSmooth_localization
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [Smooth A C] (r : C →ₐ[A] A) (c : C) (hc : IsUnit (r c))
    (hstd : IsStandardSmooth R (Localization.Away c)) :
    ∃ (_ : Smooth A (Localization.Away c)) (r' : Localization.Away c →ₐ[A] A),
      IsStandardSmooth R (Localization.Away c) := by
  obtain ⟨r', _hr'⟩ := localizationAway_retraction_of_isUnit (R := R) (A := A) r c hc
  -- Proof comment: localization is smooth over `C`, so smoothness over `A` composes to the
  -- localized retract stage.
  letI : Smooth C (Localization.Away c) :=
    Algebra.Smooth.of_isLocalization_Away (R := C) (A := Localization.Away c) c
  letI : Smooth A (Localization.Away c) :=
    Algebra.Smooth.comp (R := A) (A := C) (B := Localization.Away c)
  exact ⟨inferInstance, r', hstd⟩

/-- Helper for Lemma 16.3.4: formal smoothness of a fixed polynomial presentation gives a
retraction of the conormal map in the exact Kähler-differential sequence. -/
lemma presentationConormalRetraction_of_formallySmooth
    {C : Type*} [CommRing C] [Algebra R C] [Smooth R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c)) :
    ∃ τ : C ⊗[P.Ring] Ω[P.Ring⁄R] →ₗ[P.Ring] (RingHom.ker (algebraMap P.Ring C)).Cotangent,
      τ ∘ₗ KaehlerDifferential.kerCotangentToTensor R P.Ring C = LinearMap.id := by
  -- Proof comment: specialize the polynomial conormal-splitting criterion to the fixed
  -- presentation ring `P.Ring = MvPolynomial (Fin n) R`.
  have hform : Algebra.FormallySmooth R C :=
    Algebra.Smooth.formallySmooth (R := R) (A := C)
  simpa using
    (formallySmooth_iff_polynomial_conormal_has_retraction
      (R := R) (ι := Fin n) (S := C) P.algebraMap_surjective).mp hform

/-- Helper for Lemma 16.3.4: if `s` spans the unit ideal in the retract stage `C`, then some
linear combination of elements of `s` maps to `1` under the retraction. -/
lemma exists_span_element_with_retraction_eq_one
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (r : C →ₐ[A] A) {s : Set C} (hs : Ideal.span s = ⊤) :
    ∃ c : C, c ∈ Ideal.span s ∧ r c = 1 := by
  classical
  -- Proof comment: first push the spanning family through the retraction, then choose an explicit
  -- finite linear combination in `A` whose value is `1`, and lift that combination back to `C`.
  have himage : Ideal.span (r '' s) = ⊤ :=
    ideal_span_image_retraction_eq_top (R := R) (A := A) r hs
  obtain ⟨t, htt, htspan⟩ := (Ideal.span_eq_top_iff_finite (r '' s)).mp himage
  have hone : (1 : A) ∈ Ideal.span (↑t : Set A) := by
    rw [htspan]
    exact Submodule.mem_top
  obtain ⟨μ, hμsupport, hμsum⟩ :=
    (Submodule.mem_span_finset (R := A) (s := t) (x := (1 : A))).mp hone
  have hpreimage : ∀ a : t, ∃ x : C, x ∈ s ∧ r x = a := by
    intro a
    rcases htt a.property with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  choose pre hpre_mem hpre_eq using hpreimage
  let c : C := Finset.univ.sum fun a : t ↦ algebraMap A C (μ a) * pre a
  refine ⟨c, ?_, ?_⟩
  · -- Each summand uses one element of `s`, so the whole combination still lies in `Ideal.span s`.
    refine Ideal.sum_mem ?_
    intro a ha
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (hpre_mem a))
  · -- Applying the retraction collapses the lifted combination back to the chosen relation in `A`.
    calc
      r c = ∑ a : t, μ a * a := by
        simp [c, hpre_eq, mul_comm, mul_left_comm, mul_assoc]
      _ = Finset.sum t (fun a ↦ μ a * a) := by
        simpa using (t.sum_attach fun a : A ↦ μ a * a)
      _ = 1 := by
        simpa [smul_eq_mul] using hμsum

/-- Helper for Lemma 16.3.4: if `c` already lies in the ideal generated by `s`, then after
localizing away from `c` the images of `s` generate the unit ideal. -/
lemma ideal_span_localizationAway_image_eq_top_of_mem_span
    {C : Type*} [CommRing C] {s : Set C} {c : C}
    (hc : c ∈ Ideal.span s) :
    Ideal.span ((algebraMap C (Localization.Away c)) '' s) = ⊤ := by
  have hmem :
      algebraMap C (Localization.Away c) c ∈
        Ideal.span ((algebraMap C (Localization.Away c)) '' s) := by
    -- Proof comment: membership in the span localizes term-by-term because the span is an ideal.
    refine Ideal.span_induction hc ?_ ?_ ?_ ?_
    · intro x hx
      exact Ideal.subset_span ⟨x, hx, rfl⟩
    · intro x y hx hy
      exact Ideal.add_mem _ hx hy
    · intro a x hx
      exact Ideal.mul_mem_left _ _ hx
    · exact Ideal.zero_mem _
  have hunit : IsUnit (algebraMap C (Localization.Away c) c) := by
    -- Proof comment: the distinguished denominator becomes invertible in its own localization.
    simpa using IsLocalization.map_units (Localization.Away c)
      (⟨c, 1, by simp⟩ : Submonoid.powers c)
  rw [Ideal.eq_top_iff_one]
  rcases hunit with ⟨u, hu⟩
  -- Proof comment: multiply the localized span element by the inverse of the denominator.
  calc
    (1 : Localization.Away c) = ↑u⁻¹ * algebraMap C (Localization.Away c) c := by
      rw [hu]
      simp
    _ ∈ Ideal.span ((algebraMap C (Localization.Away c)) '' s) :=
      Ideal.mul_mem_left _ _ hmem

/-- Helper for Lemma 16.3.4: for one fixed relative-global-complete-intersection presentation of a
smooth algebra, the evaluated Jacobian column minors already span the unit ideal in the target
algebra. -/
private lemma presentationJacobianMinorSpan_eq_top
    {C : Type*} [CommRing C] [Algebra R C] [Smooth R C]
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    Ideal.span
        (Set.range fun I : Set.powersetCard (Fin n) c ↦
          algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I)) = ⊤ := by
  classical
  let T := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation)
  let e : T ≃ₐ[R] C :=
    (Ideal.quotientEquivAlgOfEq (R₁ := R) (A := P.Ring) P.span_range_relation_eq_ker).trans
      (P.quotientEquiv.restrictScalars R)
  let J : Ideal C :=
    Ideal.span
      (Set.range fun I : Set.powersetCard (Fin n) c ↦
        algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I))
  by_contra hJ
  obtain ⟨m, hmmax, hJm⟩ := Ideal.exists_le_maximal J hJ
  let q : PrimeSpectrum C := ⟨m, inferInstance⟩
  let qT : PrimeSpectrum T := PrimeSpectrum.comap e.toRingHom q
  letI : Smooth R T := Algebra.Smooth.of_equiv e
  have hqT :
      SmoothAtPrime R T qT :=
    (smooth_iff_forall_smoothAtPrime (R := R) (S := T)).mp inferInstance qT
  have hnaive :
      (Algebra.Presentation.naive : Algebra.Presentation R T (Fin n) (Fin c)).IsRelativeGlobalCompleteIntersection :=
    naivePresentation_isRelativeGlobalCompleteIntersection_of_presentation P hP
  obtain ⟨I, hI⟩ :=
    (smoothAtPrime_iff_exists_jacobian_minor_not_mem
      (R := R) (f := P.relation) le_rfl hnaive qT).mp hqT
  have hminor_mem :
      algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I) ∈ q.asIdeal := by
    exact hJm (Ideal.subset_span ⟨I, rfl⟩)
  have hminor_not_mem :
      algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I) ∉ q.asIdeal := by
    simpa [qT, e, P.algebraMap_apply] using hI
  exact hminor_not_mem hminor_mem

/-- Helper for Lemma 16.3.4: a retraction of the target algebra carries some explicit linear
combination of the Jacobian column minors of a fixed relative-global-complete-intersection
presentation to `1`. -/
private lemma existsJacobianMinorCombination_with_retraction_eq_one
    {C : Type*} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [Smooth R C] (r : C →ₐ[A] A)
    {n c : ℕ} (P : Algebra.Presentation R C (Fin n) (Fin c))
    (hP : P.IsRelativeGlobalCompleteIntersection) :
    ∃ d : C,
      d ∈ Ideal.span
          (Set.range fun I : Set.powersetCard (Fin n) c ↦
            algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I)) ∧
      r d = 1 := by
  -- Proof comment: first use the Jacobian criterion to show the minors span the unit ideal, then
  -- choose one explicit spanning combination whose retraction is `1`.
  have hminorTop :
      Ideal.span
          (Set.range fun I : Set.powersetCard (Fin n) c ↦
            algebraMap P.Ring C (P.jacobianColumnMinor le_rfl I)) = ⊤ :=
    presentationJacobianMinorSpan_eq_top (R := R) P hP
  exact exists_span_element_with_retraction_eq_one (R := R) (A := A) r hminorTop

/-- Helper for Lemma 16.3.4: after localizing a standard-smooth chart `C[1 / g]` once more away
from `c`, the resulting iterated localization identifies with the corresponding localization of
`C[1 / c]`, and hence remains standard smooth over `R`. -/
noncomputable lemma isStandardSmooth_iteratedLocalizationAway
    {C : Type*} [CommRing C] [Algebra R C] (g c : C)
    (hstd : IsStandardSmooth R (Localization.Away g)) :
    IsStandardSmooth R (Localization.Away (algebraMap C (Localization.Away c) g)) := by
  let T₁ := Localization.Away (algebraMap C (Localization.Away g) c)
  let T₂ := Localization.Away (algebraMap C (Localization.Away c) g)
  let e : T₁ ≃ₐ[R] T₂ :=
    (IsLocalization.algEquiv (Submonoid.powers (g * c)) T₁ T₂).restrictScalars R
  -- Proof comment: first localize the standard-smooth chart `C[1 / g]` away from `c`.
  letI : IsStandardSmooth R (Localization.Away g) := hstd
  letI : IsStandardSmooth (Localization.Away g) T₁ :=
    Algebra.IsStandardSmooth.localization_away (algebraMap C (Localization.Away g) c)
  letI : IsStandardSmooth R T₁ :=
    Algebra.IsStandardSmooth.trans R (Localization.Away g) T₁
  -- Proof comment: then transport that owner across the canonical iterated-localization
  -- equivalence.
  exact IsStandardSmooth.of_algEquiv e

/-- Helper for Lemma 16.3.4: a smooth `A`-algebra retract stage which is a relative global
complete intersection over `R` can be refined to a standard-smooth retract stage over `R`. -/
noncomputable lemma
    exists_standardSmooth_retract_of_relativeGlobalCompleteIntersection_retract
    {C : Type (max u v)} [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [Smooth R C] [Smooth A C] (r : C →ₐ[A] A)
    (hrel : IsRelativeGlobalCompleteIntersection R C) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : IsScalarTower R A B) (_ : Smooth A B) (r' : B →ₐ[A] A),
      IsStandardSmooth R B := by
  obtain ⟨s, hsone, hsstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R C
  obtain ⟨d, hd, hrd⟩ :=
    exists_span_element_with_retraction_eq_one (R := R) (A := A) (C := C) r hsone
  have hdunit : IsUnit (r d) := hrd ▸ isUnit_one
  let B := Localization.Away d
  have hspanBImage : Ideal.span ((algebraMap C B) '' s) = ⊤ :=
    ideal_span_localizationAway_image_eq_top_of_mem_span hd
  have hspanB :
      Ideal.span (Set.range fun y : { g // g ∈ s } ↦ algebraMap C B y.1) = ⊤ := by
    simpa [Set.image_eq_range] using hspanBImage
  -- Route correction: use the canonical smooth basic-open cover of `C`, then descend it to the
  -- chosen localization `C[1 / d]` whose denominator already retracts to a unit in `A`.
  have hloc :
      RingHom.Locally RingHom.IsStandardSmooth (algebraMap R B) := by
    refine RingHom.locally_of_exists RingHom.IsStandardSmooth.respectsIso (algebraMap R B)
      (fun y : { g // g ∈ s } ↦ algebraMap C B y.1) hspanB
      (fun y : { g // g ∈ s } ↦ Localization.Away (algebraMap C B y.1)) ?_
    intro y
    -- Each chart of the smooth cover of `C` stays standard smooth after localizing away from `d`.
    have hstdChart :
        IsStandardSmooth R (Localization.Away (algebraMap C B y.1)) :=
      isStandardSmooth_iteratedLocalizationAway (R := R) (C := C) y.1 d (hsstd y.1 y.2)
    exact RingHom.isStandardSmooth_algebraMap.mpr hstdChart
  have hstdBhom : (algebraMap R B).IsStandardSmooth :=
    (RingHom.locally_iff_of_localizationSpanTarget RingHom.IsStandardSmooth.respectsIso
      RingHom.IsStandardSmooth.ofLocalizationSpanTarget (algebraMap R B)).mp hloc
  have hstdB : IsStandardSmooth R B :=
    RingHom.isStandardSmooth_algebraMap.mp hstdBhom
  exact
    smooth_retraction_of_standardSmooth_localization
      (R := R) (A := A) (C := C) r d hdunit hstdB

/-- Lemma 16.3.4: if `R → A` is smooth, then there exists a smooth `R`-algebra map `A → B` with
an `A`-algebra retraction such that `B` is standard smooth over `R`. The presentation-theoretic
Jacobian data are carried canonically by the owner `IsStandardSmooth R B`, so they are not
repackaged here as separate public output. -/
theorem exists_smooth_retraction_standardSmooth_of_smooth [Smooth R A] :
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : IsScalarTower R A B) (_ : Smooth A B) (r : B →ₐ[A] A),
      IsStandardSmooth R B := by
  -- Proof comment: first convert the smooth map `R → A` into the syntomic hypothesis required by
  -- Lemma `16.3.3`.
  have hA : (algebraMap R A).Syntomic := Algebra.smooth_syntomic (R := R) (S := A)
  -- Proof comment: unpack the Chapter 16 retract theorem to obtain a smooth `A`-algebra retract
  -- that is a relative global complete intersection over `R`.
  obtain ⟨C, _hC, _hRC, _hAC, _hTower, hSmoothAC, r, hrel⟩ :=
    exists_smooth_retraction_relativeGlobalCompleteIntersection_of_syntomic
      (R := R) (A := A) hA
  -- Proof comment: the composite `R → A → C` is smooth, so the remaining work is exactly the
  -- relative-GCI-to-standard-smooth refinement at this fixed retract stage.
  letI : Smooth R C := Algebra.Smooth.comp (R := R) (A := A) (B := C)
  letI : Smooth A C := hSmoothAC
  exact
    exists_standardSmooth_retract_of_relativeGlobalCompleteIntersection_retract
      (R := R) (A := A) (C := C) r hrel

end

end Algebra
