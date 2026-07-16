import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_25_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18
import stacks_proof.stacks_project.Chap10.Lemma_10_72_9
import stacks_proof.stacks_project.Chap10.Lemma_10_106_2
import stacks_proof.stacks_project.Chap10.Lemma_10_140_3
import stacks_proof.stacks_project.Chap10.Lemma_10_157_2
import stacks_proof.stacks_project.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import stacks_proof.stacks_project.Chap10.Lemma_10_163_4
import stacks_proof.stacks_project.Chap10.Lemma_10_163_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsReduced R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth ring maps and ascent of reducedness;
* sampled owner declarations of the same kind:
  - `Algebra.Smooth`, the ambient owner of the source hypothesis;
  - `Algebra.Smooth.flat`, the canonical flatness consequence used downstream;
  - `isReduced_of_flat_of_fiber`, the chapter owner for reducedness ascent from reduced fibers;
  - `Algebra.IsGeometricallyReduced`, the field-valued owner underlying the fiberwise reducedness
    step in the proof sketch.

Best owner abstraction:
* the source-facing owner here is already `isReduced_of_smooth`; the smooth structure
  `[Algebra.Smooth R S]` is primitive data, while flatness and fiberwise reducedness are derived
  API that should be supplied by canonical owners rather than by a local wrapper.

Primitive data vs. derived API:
* primitive data: the smooth `R`-algebra structure on `S` and the reducedness owner `[IsReduced R]`;
* derived API: flatness of `R → S`, smoothness or geometric reducedness of the residue-field
  fibers, and the final ascent step through `isReduced_of_flat_of_fiber`.

Source/core/bridge triage:
* `source-facing`: `isReduced_of_smooth`, the textbook reducedness ascent statement for smooth
  algebras;
* `core/canonical`: `Algebra.Smooth`, `IsReduced`, and the field-level owner
  `Algebra.IsGeometricallyReduced`;
* `bridge/view`: the canonical fiberwise reducedness consequences of smoothness together with the
  reducedness-ascent theorem `isReduced_of_flat_of_fiber`.
-/
-- Proof sketch: smooth algebras are flat by `Algebra.Smooth.flat`, and smoothness is preserved
-- under base change to residue fields. A smooth algebra over a field is geometrically reduced, so
-- every fiber `κ(𝔭) ⊗[R] S` is reduced; then Lemma `10.163.6` gives the result.
omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: localizing the self-module of a ring at a prime identifies with the
localized ring. -/
noncomputable abbrev localized_self_linearEquiv_entry
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    LocalizedModule.AtPrime p A ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl A).trans
    (Algebra.TensorProduct.rid A (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: a reduced Noetherian local ring of positive Krull dimension cannot
have its maximal ideal as an associated prime of the self-module. -/
lemma reduced_local_ring_maximalIdeal_not_associated_of_positive_krullDim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A ≠ 0) :
    maximalIdeal A ∉ associatedPrimes A A := by
  -- Proof comment: an associated closed point would annihilate a nonunit element, forcing a
  -- square-zero element in the reduced ring and collapsing the maximal ideal.
  intro hmax
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hmax
  rcases hmax with ⟨_, x, hx⟩
  have hnot_field : ¬ IsField A := by
    intro hfield
    letI : Field A := hfield.toField
    exact hdim (ringKrullDim_eq_zero_of_field A)
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hbot
    exact hnot_field ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  have hx_not_unit : ¬ IsUnit x := by
    intro hx_unit
    have hbot : maximalIdeal A = ⊥ := by
      rw [hx]
      ext a
      constructor
      · intro ha
        have ha_zero : a * x = 0 := by
          simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using ha
        rcases hx_unit with ⟨u, rfl⟩
        apply_fun fun y => y * ↑u⁻¹ at ha_zero
        simpa [mul_assoc] using ha_zero
      · intro ha
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
        have ha_zero : a = 0 := by
          simpa using ha
        simp [ha_zero]
    exact hmax_ne_bot hbot
  have hx_mem : x ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hx_not_unit
  have hx_sq_zero : x * x = 0 := by
    have hx_colon : x ∈ Submodule.colon (⊥ : Submodule A A) ({x} : Set A) := by
      simpa [hx] using hx_mem
    simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using hx_colon
  have hx_zero : x = 0 := by
    exact IsNilpotent.eq_zero ⟨2, by simpa [pow_two] using hx_sq_zero⟩
  have htop : maximalIdeal A = ⊤ := by
    rw [hx, hx_zero]
    ext a
    simp [Submodule.mem_colon_singleton, smul_eq_mul]
  exact (IsLocalRing.maximalIdeal.isMaximal A).1.1 htop

omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: a reduced Noetherian ring satisfies Serre's conditions `(R₀)` and
`(S₁)`. -/
lemma serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsReduced A] :
    SerreConditionR A 0 ∧ SerreConditionS A 1 := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: localizing at a height-zero prime gives the localization at a minimal prime,
    -- hence a field in the reduced case.
    refine
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := ?_ }
    intro p hp
    have hp_zero : p.asIdeal.primeHeight = 0 := le_antisymm hp bot_le
    have hp_min : p.asIdeal ∈ minimalPrimes A := Ideal.primeHeight_eq_zero_iff.mp hp_zero
    let pmin : minimalPrimes A := ⟨p.asIdeal, hp_min⟩
    letI : Field (Localization.AtPrime p.asIdeal) :=
      (isField_localizationAtPrime_of_minimalPrime (R := A) pmin).toField
    infer_instance
  · -- Proof comment: positive-dimensional localizations have positive depth because reducedness
    -- rules out the maximal ideal as an associated prime.
    refine
      { toIsNoetherian := inferInstance
        toSerreConditionS := ?_ }
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    let Ap := Localization.AtPrime p.asIdeal
    let e := localized_self_linearEquiv_entry p.asIdeal
    have hsupport :
        Module.supportDim Ap (LocalizedModule.AtPrime p.asIdeal A) = ringKrullDim Ap := by
      simpa [Ap, Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
    have hdepth :
        moduleDepth Ap (LocalizedModule.AtPrime p.asIdeal A) = moduleDepth Ap Ap := by
      simpa [Ap] using moduleDepth_eq_of_equiv e
    by_cases hdim : ringKrullDim Ap = 0
    · -- Proof comment: if the localized ring has dimension zero, the required bound is automatic.
      rw [hdepth, hsupport, hdim]
      simp
    · have hdepth_ne_zero : moduleDepth Ap Ap ≠ 0 := by
        intro hdepth_zero
        have hmax :
            maximalIdeal Ap ∈ associatedPrimes Ap Ap :=
          Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
            (A := Ap) hdepth_zero
        exact
          reduced_local_ring_maximalIdeal_not_associated_of_positive_krullDim
            (A := Ap) hdim hmax
      have hdepth_ge_one : (1 : ℕ∞) ≤ moduleDepth Ap Ap :=
        ENat.one_le_iff_ne_zero.2 hdepth_ne_zero
      have hdepth_ge_one' :
          (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth Ap Ap : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_ge_one)
      rw [hdepth, hsupport]
      exact le_trans (min_le_left _ _) hdepth_ge_one'

omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: in the Noetherian flat setting, reduced fibers force the target to
be reduced. -/
lemma isReduced_of_flat_of_fiber_entry
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsReduced R]
    (hfiber : ∀ p : PrimeSpectrum R, IsReduced (p.asIdeal.Fiber S)) :
    IsReduced S := by
  have hbase :
      SerreConditionR R 0 ∧ SerreConditionS R 1 :=
    serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring (A := R)
  have hfiberSerre (p : PrimeSpectrum R) :
      SerreConditionR (p.asIdeal.Fiber S) 0 ∧ SerreConditionS (p.asIdeal.Fiber S) 1 := by
    -- Proof comment: each fiber is Noetherian via its tensor-product presentation over `S`, so
    -- the reduced-to-Serre bridge applies fiberwise.
    let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
    let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
      Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
    let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
      isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
        (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm
    let _ : IsReduced (p.asIdeal.Fiber S) := hfiber p
    exact
      serreConditionR_zero_and_serreConditionS_one_of_isReduced_noetherian_ring
        (A := p.asIdeal.Fiber S)
  letI : SerreConditionR R 0 := hbase.1
  letI : SerreConditionS R 1 := hbase.2
  -- Proof comment: ascend `(R₀)` and `(S₁)` separately from the base and the fibers, then use the
  -- compiled reducedness converse from Serre's criterion.
  have hSR : SerreConditionR S 0 :=
    serreConditionR_of_flat_of_fiber fun p ↦ (hfiberSerre p).1
  have hSS : SerreConditionS S 1 :=
    serreConditionS_of_flat_of_fiber fun p ↦ (hfiberSerre p).2
  exact isReduced_of_serreConditionR_zero_and_serreConditionS_one (R := S) hSR hSS

omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: a smooth algebra over a field has reduced maximal localizations. -/
lemma isReduced_localizationAtMaximal_of_smooth_over_field
    {k : Type*} {A : Type*} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (m : Ideal A) [m.IsMaximal] :
    IsReduced (Localization.AtPrime m) := by
  -- Proof comment: global smoothness says every prime lies in the smooth locus, so the maximal
  -- localization is a regular local ring and hence a domain.
  have hsmooth : Algebra.IsSmoothAt k m := by
    have hmem : (⟨m, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := by
      rw [Algebra.smoothLocus_eq_univ (R := k) (A := A)]
      simp
    simpa [Algebra.smoothLocus] using hmem
  letI : IsRegularLocalRing (Localization.AtPrime m) :=
    Algebra.isRegularLocalRing_of_isSmoothAt (k := k) (S := A) m hsmooth
  letI : IsDomain (Localization.AtPrime m) := regularLocalRing_isDomain
  exact isReduced_of_noZeroDivisors

omit R S [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] [IsReduced R] in
/-- Helper for Lemma 10.163.7: a smooth algebra over a field is reduced. -/
lemma isReduced_of_smooth_over_field
    {k : Type*} {A : Type*} [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] :
    IsReduced A := by
  -- Proof comment: reducedness is local on maximal localizations, and the previous lemma
  -- identifies every maximal localization as a reduced regular local ring.
  refine isReduced_ofLocalizationMaximal A fun m _ ↦ ?_
  simpa using isReduced_localizationAtMaximal_of_smooth_over_field (k := k) (A := A) m

omit [IsReduced R] in
/-- Helper for Lemma 10.163.7: a smooth `R`-algebra descends to a smooth algebra over a finitely
generated `ℤ`-subalgebra of `R`. -/
lemma smooth_exists_fg_subalgebra_model :
    ∃ (R₀ : Subalgebra ℤ R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      R₀.FG ∧ Algebra.Smooth R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  simpa using (Algebra.Smooth.exists_subalgebra_fg (R := ℤ) (A := R) (B := S))

/-- Helper for Lemma 10.163.7: every residue-field fiber of a finitely generated smooth model
stage is reduced. -/
lemma smooth_model_stage_fiber_isReduced
    {R₀ : Type*} {R : Type*} {S₀ : Type*}
    [CommRing R₀] [CommRing R] [CommRing S₀]
    [Algebra R₀ R] [Algebra R₀ S₀] [Algebra.Smooth R₀ S₀]
    (A : Subalgebra R₀ R) (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber (A ⊗[R₀] S₀)) := by
  -- Proof comment: smoothness survives base change to the residue field `κ(p)`, so the fiber is a
  -- smooth algebra over a field and the field case applies directly.
  let _ : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber (A ⊗[R₀] S₀)) := inferInstance
  exact
    isReduced_of_smooth_over_field
      (k := p.asIdeal.ResidueField) (A := p.asIdeal.Fiber (A ⊗[R₀] S₀))

/-- Helper for Lemma 10.163.7: each finitely generated tensor stage of the smooth model is reduced
by the Noetherian fiber criterion. -/
lemma stage_basechange_isReduced_of_smooth_model
    {R₀ : Type*} {R : Type*} {S₀ : Type*}
    [CommRing R₀] [CommRing R] [CommRing S₀]
    [Algebra R₀ R] [Algebra R₀ S₀] [Algebra.Smooth R₀ S₀]
    [IsNoetherianRing R₀] [IsReduced R]
    (A : Subalgebra R₀ R) (hA : A.FG) :
    IsReduced (A ⊗[R₀] S₀) := by
  let _ : IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  let _ : Algebra.FiniteType R₀ A := (Subalgebra.fg_iff_finiteType A).mp hA
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R₀ A
  let _ : Algebra.Smooth A (A ⊗[R₀] S₀) := inferInstance
  let _ : Algebra.FiniteType A (A ⊗[R₀] S₀) := inferInstance
  let _ : IsNoetherianRing (A ⊗[R₀] S₀) := Algebra.FiniteType.isNoetherianRing A (A ⊗[R₀] S₀)
  -- Proof comment: after base change, the stage map is smooth and hence flat; all residue-field
  -- fibers are reduced by the previous lemma, so Lemma `10.163.6` closes the Noetherian stage.
  exact
    isReduced_of_flat_of_fiber_entry
      (R := A) (S := A ⊗[R₀] S₀)
      (fun p ↦ smooth_model_stage_fiber_isReduced (R₀ := R₀) (R := R) (S₀ := S₀) A p)

/-- Helper for Lemma 10.163.7: rewrite the reduced tensor stage into the tensor order expected by
`IsReduced.tensorProduct_of_flat_of_forall_fg`. -/
lemma tensor_stage_isReduced_of_smooth_model
    {R₀ : Type*} {R : Type*} {S₀ : Type*}
    [CommRing R₀] [CommRing R] [CommRing S₀]
    [Algebra R₀ R] [Algebra R₀ S₀] [Algebra.Smooth R₀ S₀]
    [IsNoetherianRing R₀] [IsReduced R]
    (A : Subalgebra R₀ R) (hA : A.FG) :
    IsReduced (S₀ ⊗[R₀] A) := by
  let e : S₀ ⊗[R₀] A ≃ₐ[R₀] A ⊗[R₀] S₀ := Algebra.TensorProduct.comm R₀ S₀ A
  let _ : IsReduced (A ⊗[R₀] S₀) :=
    stage_basechange_isReduced_of_smooth_model
      (R₀ := R₀) (R := R) (S₀ := S₀) A hA
  -- Proof comment: commute the two tensor factors once and descend reducedness along the induced
  -- injective ring map.
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Lemma 10.163.7: descend to a Noetherian smooth model and prove reducedness from the
finitely generated tensor stages. -/
lemma isReduced_of_smooth_model_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsReduced R] :
    IsReduced S := by
  -- Route correction: use the source proof's finitely generated `ℤ`-subalgebra model and prove
  -- reducedness stagewise, rather than descending a chosen nilpotent element through ad hoc
  -- tensor manipulations.
  rcases smooth_exists_fg_subalgebra_model (R := R) (S := S) with
    ⟨R₀, S₀, _, _, hR₀fg, hSmooth0, ⟨eModel⟩⟩
  let _ : Algebra.Smooth R₀ S₀ := hSmooth0
  let _ : Algebra.FiniteType ℤ R₀ := (Subalgebra.fg_iff_finiteType R₀).mp hR₀fg
  let _ : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have hTensorComm : IsReduced (S₀ ⊗[R₀] R) := by
    -- Proof comment: the full tensor product is reduced once every finitely generated
    -- `R₀`-subalgebra stage is reduced.
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (R := R₀) (C := S₀) (A := R) ?_
    intro A hA
    exact tensor_stage_isReduced_of_smooth_model (R₀ := R₀) (R := R) (S₀ := S₀) A hA
  let eComm : R ⊗[R₀] S₀ ≃ₐ[R] S₀ ⊗[R₀] R :=
    { __ := Algebra.TensorProduct.comm R₀ R S₀
      commutes' _ := rfl }
  let eFinal : S ≃ₐ[R] S₀ ⊗[R₀] R := eModel.trans eComm
  let _ : IsReduced (S₀ ⊗[R₀] R) := hTensorComm
  -- Proof comment: compose the model equivalence with the tensor commutor so that `S` maps
  -- injectively into the already reduced tensor order `S₀ ⊗[R₀] R`.
  exact isReduced_of_injective eFinal.toRingHom eFinal.injective

/-- Lemma 10.163.7: if `R → S` is smooth and `R` is reduced, then `S` is reduced. -/
@[stacks 033B]
theorem isReduced_of_smooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsReduced R] :
    IsReduced S := by
  -- Proof comment: the public statement is exactly the model-descent helper specialized back to
  -- the ambient section variables.
  simpa using (isReduced_of_smooth_model_descent (R := R) (S := S))

end
