import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Lemma_10_127_18
import stacks_proof.stacks_project.Chap10.Lemma_10_168_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

variable [Algebra.FinitePresentation A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
* Primary domain: descent/approximation of faithfully flat finitely presented algebra maps.
* Relevant owner declarations inspected:
  - `Algebra.IsPushout`
  - `TensorProduct.isPushout`
  - `Algebra.IsPushout.equiv`
  - `RingHom.FaithfullyFlat`
* Best owner abstraction:
  - `source-facing`: the existence theorem below
  - `core/canonical`: `Algebra.IsPushout` for the tensor-product base-change square, together with
    `Algebra.FinitePresentation` and `RingHom.FaithfullyFlat`
  - `bridge/view`: the explicit `A`-algebra equivalence `Algebra.IsPushout.equiv A₀ A B₀ B`
* Primitive vs. derived:
  - primitive data: the descended rings `A₀`, `B₀`, their algebra structures, finite-presentation
    hypotheses, faithful flatness, and the compatible tower/pushout data relating them to `A` and
    `B`
  - derived API: the explicit tensor-product comparison `A ⊗[A₀] B₀ ≃ₐ[A] B`
-/

-- Proof sketch: approximate the actual finite-presentation map `A → B` by the canonical directed
-- finite-presentation system from `10.127.17/18`. The stage maps are finitely presented, and
-- their maps to the limit commute with `A → B`. The remaining source step is to descend the
-- faithful-flat invariants to a sufficiently late stage and then package that stage as the
-- finitely presented `R`-model using the final tensor pushout bridge.
/-- Helper for Chap10 Lemma 10 168 2: a flat map whose map on prime spectra is surjective is
faithfully flat. -/
lemma faithfullyFlat_of_flat_and_comap_surjective
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] {g : A₀ →+* B₀}
    (hflat : g.Flat) (hsurj : Function.Surjective (PrimeSpectrum.comap g)) :
    g.FaithfullyFlat := by
  -- Proof comment: the owner characterization is exactly the final assembly criterion needed
  -- after the constructible complement of the spectrum image has been killed.
  exact (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).mpr ⟨hflat, hsurj⟩

/-- Helper for Chap10 Lemma 10 168 2: a faithfully flat map is surjective on prime spectra. -/
lemma comap_surjective_of_faithfullyFlat
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] {g : A₀ →+* B₀}
    (hff : g.FaithfullyFlat) : Function.Surjective (PrimeSpectrum.comap g) := by
  -- Proof comment: unpack the same owner criterion in the direction used to show that the
  -- constructible obstruction has empty pullback after base change.
  exact (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).mp hff |>.2

/-- Helper for Chap10 Lemma 10 168 2: if the pullback of a set is all of the source, then the
pullback of its complement is empty. -/
lemma preimage_compl_eq_empty_of_preimage_eq_univ
    {X Y : Type*} (f : X → Y) {s : Set Y} (hpre : f ⁻¹' s = Set.univ) :
    f ⁻¹' sᶜ = ∅ := by
  ext x
  -- Proof comment: membership in the universal pullback rules out membership in the pulled-back
  -- complement pointwise.
  have hx : f x ∈ s := by
    have hxpre : x ∈ f ⁻¹' s := by
      rw [hpre]
      exact Set.mem_univ x
    exact hxpre
  simp [hx]

/-- Helper for Chap10 Lemma 10 168 2: a spectrum map is surjective once an already-surjective
base change sees no point in the complement of its image. -/
lemma comap_surjective_of_surjective_pullback_compl_empty
    {A₀ B₀ T : Type*} [CommRing A₀] [CommRing B₀] [CommRing T]
    (φ : A₀ →+* T) (g : A₀ →+* B₀)
    (hφ : Function.Surjective (PrimeSpectrum.comap φ))
    (hempty : (PrimeSpectrum.comap φ) ⁻¹' (Set.range (PrimeSpectrum.comap g))ᶜ = ∅) :
    Function.Surjective (PrimeSpectrum.comap g) := by
  intro p
  -- Proof comment: lift `p` along the surjective comparison map; if `p` were outside the image of
  -- `Spec B₀`, the lift would lie in the empty pulled-back complement.
  obtain ⟨q, hq⟩ := hφ p
  have hqNot :
      q ∉ (PrimeSpectrum.comap φ) ⁻¹' (Set.range (PrimeSpectrum.comap g))ᶜ := by
    rw [hempty]
    simp
  have hp : p ∈ Set.range (PrimeSpectrum.comap g) := by
    by_contra hp
    exact hqNot (by simpa [Set.mem_preimage, Set.mem_compl_iff, hq] using hp)
  exact hp

/-- Helper for Chap10 Lemma 10 168 2: after a transition identifies the pulled-back spectrum
image with the later image, an empty pulled-back complement makes the later image surjective. -/
lemma surjective_of_preimage_range_eq_range_and_preimage_compl_empty
    {X Y Z W : Type*} (f : X → Y) (gY : Z → Y) (gX : W → X)
    (hrange : f ⁻¹' Set.range gY = Set.range gX)
    (hempty : f ⁻¹' (Set.range gY)ᶜ = ∅) :
    Function.Surjective gX := by
  intro x
  -- Proof comment: a point outside the later image would be outside the pulled-back earlier image,
  -- hence inside the pulled-back complement, contradicting emptiness.
  have hxNot : x ∉ f ⁻¹' (Set.range gY)ᶜ := by
    rw [hempty]
    simp
  have hxIn : x ∈ f ⁻¹' Set.range gY := by
    by_contra hx
    exact hxNot (by simpa [Set.mem_preimage, Set.mem_compl_iff] using hx)
  have hxRange : x ∈ Set.range gX := by
    rwa [hrange] at hxIn
  exact hxRange

/-- Helper for Chap10 Lemma 10 168 2: the complement of the spectrum image of a finitely
presented ring map is constructible. -/
lemma isConstructible_compl_range_comap_of_finitePresentation
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] {g : A₀ →+* B₀}
    (hg : g.FinitePresentation) :
    Topology.IsConstructible (Set.range (PrimeSpectrum.comap g))ᶜ := by
  -- Proof comment: Chevalley's theorem gives constructibility of the image, and constructible
  -- sets are closed under complement.
  exact (PrimeSpectrum.isConstructible_range_comap hg).compl

/-- Helper for Chap10 Lemma 10 168 2: eventual flatness together with a later surjective
spectrum map gives a faithfully flat stage. -/
lemma exists_faithfullyFlatStage_of_eventuallyFlat_and_stageSurjective
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] {f : A₀ →+* B₀}
    (D : DirectedFiniteTypeHomApproximation f) {i₀ : D.Λ}
    (hflat : ∀ j, i₀ ≤ j → (D.stageMap j).Flat)
    (hsurj : ∃ j, i₀ ≤ j ∧ Function.Surjective (PrimeSpectrum.comap (D.stageMap j))) :
    ∃ j, i₀ ≤ j ∧ (D.stageMap j).FaithfullyFlat := by
  -- Proof comment: choose the stage where the spectrum image is already all of the source and
  -- combine it with the flatness bound using the owner characterization of faithful flatness.
  obtain ⟨j, hij, hsurj_j⟩ := hsurj
  exact ⟨j, hij, faithfullyFlat_of_flat_and_comap_surjective (hflat j hij) hsurj_j⟩

/-- Helper for Chap10 Lemma 10 168 2: source stages in a directed finite-type approximation are
Noetherian because they are finite type over `ℤ`. -/
lemma stageSource_isNoetherianRing_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    IsNoetherianRing (D.RStage i) := by
  -- Proof comment: convert the stored ring-hom finite-type field to the algebra version, then
  -- apply the standard Noetherian finite-type theorem over `ℤ`.
  let _ : Algebra.FiniteType ℤ (D.RStage i) :=
    RingHom.finiteType_algebraMap.mp (D.source_finiteType i)
  exact Algebra.FiniteType.isNoetherianRing ℤ (D.RStage i)

/-- Helper for Chap10 Lemma 10 168 2: every stage map in a directed finite-presentation
approximation is a finite-presentation ring map. -/
lemma stageMap_finitePresentation_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    (D.stageMap i).FinitePresentation := by
  -- Proof comment: Noetherianity of the source stage upgrades the stored finite-type stage map to
  -- finite presentation.
  have hsource : IsNoetherianRing (D.RStage i) :=
    stageSource_isNoetherianRing_of_fpApproximation D i
  let _ : IsNoetherianRing (D.RStage i) := hsource
  exact (RingHom.FinitePresentation.of_finiteType).mp (D.target_finiteType i)

/-- Helper for Chap10 Lemma 10 168 2: the two maps from a source stage to the target limit agree
with the limiting ring map. -/
lemma stageToLimit_comp_stageMap_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    (D.targetStageToLimit i).comp (D.stageMap i) = f.comp (D.sourceStageToLimit i) := by
  ext x
  -- Proof comment: evaluate the stored colimit-commutativity field on the direct-limit generator
  -- represented by `x` at source stage `i`.
  have h := congrArg
    (fun g : Ring.DirectLimit D.RStage (fun i j h ↦ D.RMap i j h) →+* S' =>
      g (Ring.DirectLimit.of D.RStage (fun i j h ↦ D.RMap i j h) i x))
    D.colimit_comm
  simpa [DirectedFiniteTypeHomApproximation.sourceStageToLimit,
    DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.comp_apply,
    Ring.DirectLimit.map_apply_of] using h

/-- Helper for Chap10 Lemma 10 168 2: the target transition of a finite-presentation
approximation forms the scalar tower over the source transition. -/
lemma stageTargetTransition_isScalarTower_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
    let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage j) := ((D.stageMap j).comp (D.RMap i j hij)).toAlgebra
    IsScalarTower (D.RStage i) (D.SStage i) (D.SStage j) := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
  let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage j) := ((D.stageMap j).comp (D.RMap i j hij)).toAlgebra
  -- Proof comment: the stored commutative square identifies the direct source-to-target map with
  -- the composite through the earlier target stage.
  refine IsScalarTower.of_algebraMap_eq' ?_
  simpa [RingHom.algebraMap_toAlgebra] using D.comm hij

/-- Helper for Chap10 Lemma 10 168 2: the tensor-commuted stage base-change map is bijective
whenever the approximation has bijective base-change transitions. -/
lemma stageTensorBaseChange_bijective_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    Function.Bijective
      ((D.stageBaseChangeMap hij).comp
        (Algebra.TensorProduct.comm (D.RStage i) (D.RStage j) (D.SStage i)).toRingHom) := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  -- Proof comment: tensor-factor commutativity is an equivalence, so composing it with the stored
  -- bijective owner base-change map remains bijective.
  exact (hDbase hij).comp
    (Algebra.TensorProduct.comm (D.RStage i) (D.RStage j) (D.SStage i)).toRingEquiv.bijective

/-- Helper for Chap10 Lemma 10 168 2: the tensor-commuted stage base-change map is compatible
with the later source-stage algebra structure. -/
lemma stageTensorBaseChange_algebraMap_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
    ∀ r : D.RStage j,
      ((D.stageBaseChangeMap hij).comp
        (Algebra.TensorProduct.comm (D.RStage i) (D.RStage j) (D.SStage i)).toRingHom)
          (algebraMap (D.RStage j) (D.RStage j ⊗[D.RStage i] D.SStage i) r) =
        algebraMap (D.RStage j) (D.SStage j) r := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
  intro _instSi _instRj _instSj r
  -- Proof comment: after swapping tensor factors, the owner pure-tensor formula sends
  -- `1 ⊗ r` to the later stage map of `r`.
  change D.stageBaseChangeMap hij (1 ⊗ₜ[D.RStage i] r) = D.stageMap j r
  rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
  simp

/-- Helper for Chap10 Lemma 10 168 2: the base-change equivalence from a later source stage
tensor an earlier target stage to the later target stage. -/
noncomputable def stageRingBaseChangeEquiv_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
    D.RStage j ⊗[D.RStage i] D.SStage i ≃ₐ[D.RStage j] D.SStage j :=
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective
      ((D.stageBaseChangeMap hij).comp
        (Algebra.TensorProduct.comm (D.RStage i) (D.RStage j) (D.SStage i)).toRingHom)
      (stageTensorBaseChange_bijective_of_fpApproximation D hDbase hij))
    (stageTensorBaseChange_algebraMap_of_fpApproximation D hij)

/-- Helper for Chap10 Lemma 10 168 2: the stage base-change equivalence restricts on the earlier
target stage to the target transition map. -/
lemma stageRingBaseChangeEquiv_comp_target_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
    let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
    (stageRingBaseChangeEquiv_of_fpApproximation D hDbase hij).toRingHom.comp
        (algebraMap (D.SStage i) (D.RStage j ⊗[D.RStage i] D.SStage i)) =
      algebraMap (D.SStage i) (D.SStage j) := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
  let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
  ext x
  -- Proof comment: the algebra map from the earlier target stage is the right tensor inclusion,
  -- and the owner formula evaluates it as the target transition.
  change D.stageBaseChangeMap hij (x ⊗ₜ[D.RStage i] 1) = D.SMap i j hij x
  rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
  simp

/-- Helper for Chap10 Lemma 10 168 2: a bijective stage base-change transition gives a pushout
square between the two corresponding finite stages. -/
lemma stageRing_isPushout_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) {i j : D.Λ} (hij : i ≤ j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
    let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage j) := ((D.stageMap j).comp (D.RMap i j hij)).toAlgebra
    let _ : IsScalarTower (D.RStage i) (D.RStage j) (D.SStage j) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (D.RStage i) (D.SStage i) (D.SStage j) :=
      stageTargetTransition_isScalarTower_of_fpApproximation D hij
    Algebra.IsPushout (D.RStage i) (D.RStage j) (D.SStage i) (D.SStage j) := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage j) (D.SStage j) := (D.stageMap j).toAlgebra
  let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage j) := ((D.stageMap j).comp (D.RMap i j hij)).toAlgebra
  let _ : IsScalarTower (D.RStage i) (D.RStage j) (D.SStage j) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (D.RStage i) (D.SStage i) (D.SStage j) :=
    stageTargetTransition_isScalarTower_of_fpApproximation D hij
  -- Proof comment: compare the canonical tensor-product pushout with the actual later target
  -- stage through the base-change equivalence proved above.
  exact Algebra.IsPushout.of_equiv (R := D.RStage i) (R' := D.RStage j)
    (S := D.SStage i) (T := D.SStage j)
    (stageRingBaseChangeEquiv_of_fpApproximation D hDbase hij)
    (stageRingBaseChangeEquiv_comp_target_of_fpApproximation D hDbase hij)

/-- Helper for Chap10 Lemma 10 168 2: the target-stage-to-limit map is compatible with the
source-stage algebra structure induced through the limiting map. -/
lemma targetStageToLimit_algebraMap_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) (r : D.RStage i) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
    D.targetStageToLimit i (algebraMap (D.RStage i) (D.SStage i) r) =
      algebraMap (D.RStage i) S' r := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  -- Proof comment: evaluate the already proved stage-to-limit square on the chosen source-stage
  -- element and read it as equality of algebra maps.
  exact RingHom.congr_fun (stageToLimit_comp_stageMap_of_fpApproximation D i) r

/-- Helper for Chap10 Lemma 10 168 2: the target-stage-to-limit map as an algebra hom over the
matching source stage. -/
noncomputable def targetStageToLimitAlgHom_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
    D.SStage i →ₐ[D.RStage i] S' :=
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  { toRingHom := D.targetStageToLimit i
    commutes' := targetStageToLimit_algebraMap_of_fpApproximation D i }

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map
`R' ⊗[D.RStage i] D.SStage i → S'`. -/
noncomputable def finalStageBaseChangeMap_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    R' ⊗[D.RStage i] D.SStage i →ₐ[R'] S' :=
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (D.RStage i) R' S' := IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.lift (Algebra.ofId R' S')
    (targetStageToLimitAlgHom_of_fpApproximation D i) (fun _ _ ↦ Commute.all _ _)

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map on pure tensors. -/
lemma finalStageBaseChangeMap_tmul_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ)
    (r : R') (s : D.SStage i) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    finalStageBaseChangeMap_of_fpApproximation D i (r ⊗ₜ[D.RStage i] s) =
      f r * D.targetStageToLimit i s := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (D.RStage i) R' S' := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: the named final map is a tensor-product lift, so its pure-tensor value is the
  -- product of the two limiting structure maps.
  simp [finalStageBaseChangeMap_of_fpApproximation, targetStageToLimitAlgHom_of_fpApproximation,
    Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]

/-- Helper for Chap10 Lemma 10 168 2: on the right tensor factor, the canonical final map is the
target-stage-to-limit map. -/
lemma finalStageBaseChangeMap_includeRight_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    RingHom.comp (finalStageBaseChangeMap_of_fpApproximation D i).toRingHom
        Algebra.TensorProduct.includeRight.toRingHom =
      D.targetStageToLimit i := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (D.RStage i) R' S' := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: this is the `includeRight` computation for the tensor-product lift, with
  -- scalars restricted back from `R'` to the source stage.
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId R' S')
      (targetStageToLimitAlgHom_of_fpApproximation D i) (fun _ _ ↦ Commute.all _ _))

/-- Helper for Chap10 Lemma 10 168 2: pushing a source-tail tensor to a later source stage is
compatible with the stage base-change maps. -/
lemma stageBaseChangeMap_tail_compat_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) {i j k : D.Λ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (y :
      let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
      let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
      D.SStage i ⊗[D.RStage i] D.RStage j) :
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage k) := (D.RMap i k (hij.trans hjk)).toAlgebra
    let _ : Algebra (D.RStage j) (D.RStage k) := (D.RMap j k hjk).toAlgebra
    let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
      fun l ↦ (D.RMap i l.1 l.2).toAlgebra
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
      { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
    D.stageBaseChangeMap (hij.trans hjk)
        (M2F1278P23.pushStage D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
          i (D.SStage i) (j := ⟨j, hij⟩) (k := ⟨k, hij.trans hjk⟩) hjk y) =
      D.SMap j k hjk (D.stageBaseChangeMap hij y) := by
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage k) := (D.RMap i k (hij.trans hjk)).toAlgebra
  let _ : Algebra (D.RStage j) (D.RStage k) := (D.RMap j k hjk).toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
    fun l ↦ (D.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  -- Proof comment: tensor induction reduces compatibility to the stored commutative square and
  -- the directed-system composition laws.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul xS yR =>
      change D.stageBaseChangeMap (hij.trans hjk)
          (xS ⊗ₜ[D.RStage i] D.RMap j k hjk yR) =
        D.SMap j k hjk (D.stageBaseChangeMap hij (xS ⊗ₜ[D.RStage i] yR))
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [map_mul]
      have hS :
          D.SMap j k hjk (D.SMap i j hij xS) =
            D.SMap i k (hij.trans hjk) xS :=
        DirectedSystem.map_map (f := fun a b h ↦ D.SMap a b h) hij hjk xS
      have hR :
          D.SMap j k hjk (D.stageMap j yR) =
            D.stageMap k (D.RMap j k hjk yR) :=
        (RingHom.congr_fun (D.comm hjk) yR).symm
      rw [hS, hR]
  | add y₁ y₂ hy₁ hy₂ =>
      simp [map_add, hy₁, hy₂]

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map agrees with the target
colimit map on tensors represented at a finite source-tail stage. -/
lemma finalStageBaseChangeMap_pushHom_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f) {i j : D.Λ} (hij : i ≤ j)
    (y :
      let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
      let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
      D.SStage i ⊗[D.RStage i] D.RStage j) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
      fun l ↦ (D.RMap i l.1 l.2).toAlgebra
    let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
      { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
    finalStageBaseChangeMap_of_fpApproximation D i
        ((Algebra.TensorProduct.comm (R := D.RStage i) (A := D.SStage i) (B := R'))
          (M2F1278P23.pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
            i (D.SStage i) ⟨j, hij⟩ y)) =
      D.targetStageToLimit j (D.stageBaseChangeMap hij y) := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra (D.RStage i) (D.RStage j) := (D.RMap i j hij).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
    fun l ↦ (D.RMap i l.1 l.2).toAlgebra
  let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  -- Proof comment: tensor induction reduces the comparison to the pure-tensor formulas for
  -- `pushHom`, `stageBaseChangeMap`, and the final tensor map.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul xS yR =>
      change finalStageBaseChangeMap_of_fpApproximation D i
          ((Algebra.TensorProduct.comm (R := D.RStage i) (A := D.SStage i) (B := R'))
            (xS ⊗ₜ[D.RStage i] D.sourceStageToLimit j yR)) =
        D.targetStageToLimit j (D.stageBaseChangeMap hij (xS ⊗ₜ[D.RStage i] yR))
      rw [Algebra.TensorProduct.comm_tmul]
      rw [finalStageBaseChangeMap_tmul_of_fpApproximation]
      rw [DirectedFiniteTypeHomApproximation.stageBaseChangeMap_tmul]
      rw [map_mul]
      have hleft :
          D.targetStageToLimit j (D.SMap i j hij xS) = D.targetStageToLimit i xS := by
        exact RingHom.congr_fun
          (DirectedFinitePresentationModuleApproximation.targetStageToLimit_comp_SMap
            (f := f) D hij) xS
      have hright :
          D.targetStageToLimit j (D.stageMap j yR) = f (D.sourceStageToLimit j yR) := by
        exact RingHom.congr_fun (stageToLimit_comp_stageMap_of_fpApproximation D j) yR
      rw [hleft, hright]
      ring
  | add y₁ y₂ hy₁ hy₂ =>
      simp [map_add, hy₁, hy₂]

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map is surjective. -/
lemma finalStageBaseChangeMap_surjective_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    Function.Surjective (finalStageBaseChangeMap_of_fpApproximation D i) := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
    fun l ↦ (D.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  change Function.Surjective (finalStageBaseChangeMap_of_fpApproximation D i)
  intro s
  -- Proof comment: represent `s` at a target stage, then move to a common stage above the fixed
  -- source index `i`.
  obtain ⟨j, t, ht⟩ :=
    Ring.DirectLimit.exists_of
      (G := D.SStage) (f := fun a b h ↦ D.SMap a b h) (D.colimitTarget.symm s)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let _ : Algebra (D.RStage i) (D.RStage k) := (D.RMap i k hik).toAlgebra
  -- Proof comment: the stage base-change bijection lifts the moved target representative to a
  -- tensor over the common source stage.
  obtain ⟨y, hy⟩ := (hDbase hik).2 (D.SMap j k hjk t)
  refine ⟨
    (Algebra.TensorProduct.comm (R := D.RStage i) (A := D.SStage i) (B := R'))
      (M2F1278P23.pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
        i (D.SStage i) ⟨k, hik⟩ y), ?_⟩
  -- Proof comment: the finite-stage bridge rewrites the final tensor map to the target colimit
  -- cocone, where compatibility with the transition from `j` to `k` closes the representative.
  rw [finalStageBaseChangeMap_pushHom_of_fpApproximation D hik y, hy]
  have hcompat :
      D.targetStageToLimit k (D.SMap j k hjk t) = D.targetStageToLimit j t := by
    exact RingHom.congr_fun
      (DirectedFinitePresentationModuleApproximation.targetStageToLimit_comp_SMap
        (f := f) D hjk) t
  rw [hcompat]
  simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit, ht]
    using D.colimitTarget.apply_symm_apply s

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map is injective. -/
lemma finalStageBaseChangeMap_injective_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    Function.Injective (finalStageBaseChangeMap_of_fpApproximation D i) := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : ∀ l : M2F1278P23.Up i, Algebra (D.RStage i) (D.RStage l.1) :=
    fun l ↦ (D.RMap i l.1 l.2).toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : M2F1278P23.StagePins D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource i :=
    { stA_eq := fun _ ↦ rfl, limA_eq := rfl }
  change Function.Injective (finalStageBaseChangeMap_of_fpApproximation D i)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let c : D.SStage i ⊗[D.RStage i] R' ≃ₐ[D.RStage i] R' ⊗[D.RStage i] D.SStage i :=
    Algebra.TensorProduct.comm (R := D.RStage i) (A := D.SStage i) (B := R')
  -- Proof comment: first represent the swapped tensor at a finite source-tail stage.
  obtain ⟨j, y, hy⟩ :=
    M2F1278P23.exists_pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
      i (D.SStage i) (c.symm x)
  have hx_rep :
      finalStageBaseChangeMap_of_fpApproximation D i
          (c (M2F1278P23.pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
            i (D.SStage i) j y)) = 0 := by
    simpa [c, hy] using hx
  have htarget :
      D.targetStageToLimit j.1 (D.stageBaseChangeMap j.2 y) = 0 := by
    -- Proof comment: the finite-stage bridge translates the final-map zero into a target-colimit
    -- zero for the corresponding stage base-change value.
    exact (finalStageBaseChangeMap_pushHom_of_fpApproximation D j.2 y).symm.trans hx_rep
  have hraw :
      Ring.DirectLimit.of D.SStage (fun a b h ↦ D.SMap a b h) j.1
          (D.stageBaseChangeMap j.2 y) = 0 := by
    apply D.colimitTarget.injective
    simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit] using htarget
  -- Proof comment: direct-limit zero detection gives a later target stage where the represented
  -- stage base-change value is zero.
  obtain ⟨k, hjk, hkzero⟩ := Ring.DirectLimit.of.zero_exact hraw
  let kUp : M2F1278P23.Up i := ⟨k, j.2.trans hjk⟩
  have hbc_zero :
      D.stageBaseChangeMap (j.2.trans hjk)
          (M2F1278P23.pushStage D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
            i (D.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk) y) = 0 := by
    rw [stageBaseChangeMap_tail_compat_of_fpApproximation D j.2 hjk y]
    exact hkzero
  have hpush_zero :
      M2F1278P23.pushStage D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
          i (D.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk) y = 0 := by
    -- Proof comment: the stored finite-stage base-change map is injective, so a zero image forces
    -- the source-tail tensor itself to vanish.
    exact (hDbase (j.2.trans hjk)).1 (by simpa using hbc_zero)
  have hpushHom_zero :
      M2F1278P23.pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
          i (D.SStage i) j y = 0 := by
    have hcomp := AlgHom.congr_fun
      (M2F1278P23.pushHom_comp_pushStage D.RStage (fun a b h ↦ D.RMap a b h)
        D.colimitSource i (D.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk)) y
    have hleft :
        ((M2F1278P23.pushHom D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
              i (D.SStage i) kUp).comp
            (M2F1278P23.pushStage D.RStage (fun a b h ↦ D.RMap a b h) D.colimitSource
              i (D.SStage i) (j := j) (k := kUp) (show j ≤ kUp from hjk))) y = 0 := by
      simp only [AlgHom.comp_apply]
      rw [hpush_zero, map_zero]
    exact hcomp.symm.trans hleft
  rw [hy] at hpushHom_zero
  -- Proof comment: applying the tensor-factor commutativity equivalence back to the killed
  -- swapped tensor gives the original tensor zero.
  exact c.symm.injective (by simpa using hpushHom_zero)

/-- Helper for Chap10 Lemma 10 168 2: the canonical final tensor map is bijective. -/
lemma stageToLimitTensorMap_bijective_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    Function.Bijective (finalStageBaseChangeMap_of_fpApproximation D i) := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  -- Proof comment: combine the separate direct-limit surjectivity and zero-detection
  -- injectivity arguments for the canonical final tensor map.
  exact ⟨finalStageBaseChangeMap_injective_of_fpApproximation D hDbase i,
    finalStageBaseChangeMap_surjective_of_fpApproximation D hDbase i⟩

/-- Helper for Chap10 Lemma 10 168 2: a finite-presentation approximation stage pushes out to
the limiting square. -/
lemma stageToLimit_isPushout_of_fpApproximation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) (i : D.Λ) :
    let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
    let _ : Algebra R' S' := f.toAlgebra
    let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
    let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
    let _ : IsScalarTower (D.RStage i) R' S' := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (D.RStage i) (D.SStage i) S' :=
      IsScalarTower.of_algebraMap_eq' <|
        (stageToLimit_comp_stageMap_of_fpApproximation D i).symm
    Algebra.IsPushout (D.RStage i) R' (D.SStage i) S' := by
  let _ : Algebra (D.RStage i) R' := (D.sourceStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
  let _ : Algebra R' S' := f.toAlgebra
  let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
  let _ : Algebra (D.RStage i) S' := (f.comp (D.sourceStageToLimit i)).toAlgebra
  let _ : IsScalarTower (D.RStage i) R' S' := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (D.RStage i) (D.SStage i) S' :=
    IsScalarTower.of_algebraMap_eq' <|
      (stageToLimit_comp_stageMap_of_fpApproximation D i).symm
  let g := finalStageBaseChangeMap_of_fpApproximation D i
  have hg : Function.Bijective g :=
    stageToLimitTensorMap_bijective_of_fpApproximation D hDbase i
  let e : R' ⊗[D.RStage i] D.SStage i ≃ₐ[R'] S' :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective g.toRingHom hg) (by
      intro r
      -- Proof comment: the ring equivalence is induced by the `R'`-algebra hom `g`, so it
      -- preserves the `R'`-algebra structure by `g.commutes`.
      exact g.commutes r)
  -- Proof comment: transporting the canonical tensor-product pushout along the bijective final
  -- tensor map gives the desired limiting pushout square.
  exact Algebra.IsPushout.of_equiv (R := D.RStage i) (R' := R')
    (S := D.SStage i) (T := S') e
    (finalStageBaseChangeMap_includeRight_of_fpApproximation D i)

/-- Helper for Chap10 Lemma 10 168 2: the scalar-extension lift of an algebra structure map
`R → S` is bijective from `S ⊗[R] R` to `S`. -/
lemma algebraMap_liftBaseChange_bijective
    {R' : Type u} {S' : Type v} [CommRing R'] [CommRing S'] [Algebra R' S'] :
    Function.Bijective
      (((Algebra.linearMap R' S').liftBaseChange S') : S' ⊗[R'] R' →ₗ[S'] S') := by
  -- Proof comment: the lifted algebra map is the standard right-unit equivalence for tensor
  -- products, up to commutativity of multiplication in `S'`.
  let e : S' ⊗[R'] R' ≃ₗ[R'] S' := TensorProduct.rid R' S'
  convert e.bijective
  funext x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [e]
  | tmul s r =>
      change s * algebraMap R' S' r = r • s
      rw [Algebra.smul_def]
      rw [mul_comm]
  | add x y hx hy =>
      simp [hx, hy]

/-- Helper for Chap10 Lemma 10 168 2: a ring approximation is also a module approximation for
the limiting algebra viewed as its own module. -/
lemma selfModuleApproximation_nonempty
    {R' : Type u} {S' : Type v} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation.{u, v, w} f)
    (hDbase : D.HasBijectiveBaseChangeTransitions) :
    Nonempty (DirectedFinitePresentationModuleApproximation.{u, v, v, 0, w} f S') := by
  -- Proof comment: reuse the target rings themselves as the finite module stages; all module
  -- transition and limit maps are the corresponding algebra structure maps.
  refine ⟨{ D with
      hasBijectiveBaseChangeTransitions := hDbase
      moduleStage := D.SStage
      instAddCommGroupModuleStage := fun _ => inferInstance
      instModuleModuleStage := fun _ => inferInstance
      instModuleFiniteModuleStage := fun _ => inferInstance
      moduleMap := ?_
      moduleMap_id := ?_
      moduleMap_comp := ?_
      moduleToLimit := ?_
      moduleToLimit_comp := ?_
      transitionBaseChangeMap_bijective := ?_
      finalBaseChangeMap_bijective := ?_ }⟩
  · intro i j hij
    let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
    exact Algebra.linearMap (D.SStage i) (D.SStage j)
  · intro i m
    -- Proof comment: the identity transition acts as the identity on the target stage.
    exact DirectedSystem.map_self (f := fun {i j} h => D.SMap i j h) m
  · intro i j k hij hjk m
    -- Proof comment: composition of the module maps is the directed-system composition law for
    -- the target-stage ring maps.
    exact DirectedSystem.map_map (f := fun {i j} h => D.SMap i j h) hij hjk m
  · intro i
    let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
    exact Algebra.linearMap (D.SStage i) S'
  · intro i j hij m
    -- Proof comment: compatibility with the limiting module is exactly compatibility of target
    -- stages with the target colimit map.
    simp [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
  · intro i j hij
    -- Proof comment: after scalar extension along `S_i → S_j`, the target-stage self-module is
    -- identified with `S_j` by the tensor right-unit equivalence.
    let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
    simpa using algebraMap_liftBaseChange_bijective (R' := D.SStage i) (S' := D.SStage j)
  · intro i
    -- Proof comment: the same right-unit equivalence identifies the final base change
    -- `S' ⊗[S_i] S_i` with the limiting target ring `S'`.
    let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
    simpa using algebraMap_liftBaseChange_bijective (R' := D.SStage i) (S' := S')

/-- Helper for Chap10 Lemma 10 168 2: flatness of the limiting algebra descends eventually to
the stage maps of a directed finite-presentation approximation. -/
lemma eventually_flatStage_of_flat_limit_fpApproximation
    {R' : Type u} {S' : Type v} [CommRing R'] [CommRing S'] {f : R' →+* S'}
    (D : DirectedFiniteTypeHomApproximation.{u, v, w} f)
    (hDbase : D.HasBijectiveBaseChangeTransitions)
    (hflat : f.Flat) :
    ∃ i₀ : D.Λ, ∀ j, i₀ ≤ j → (D.stageMap j).Flat := by
  -- Proof comment: invoke Lemma 10.168.1 on the self-module approximation and then translate the
  -- resulting module-flatness statement back to flatness of the stage ring map.
  let C : DirectedFinitePresentationModuleApproximation.{u, v, v, 0, w} f S' := by
    -- Proof comment: build the self-module approximation transparently here so that the theorem
    -- output is indexed by `D.Λ` and the module stage unfolds to `D.SStage`.
    refine { D with
      hasBijectiveBaseChangeTransitions := hDbase
      moduleStage := D.SStage
      instAddCommGroupModuleStage := fun _ => inferInstance
      instModuleModuleStage := fun _ => inferInstance
      instModuleFiniteModuleStage := fun _ => inferInstance
      moduleMap := ?_
      moduleMap_id := ?_
      moduleMap_comp := ?_
      moduleToLimit := ?_
      moduleToLimit_comp := ?_
      transitionBaseChangeMap_bijective := ?_
      finalBaseChangeMap_bijective := ?_ }
    · intro i j hij
      let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
      exact Algebra.linearMap (D.SStage i) (D.SStage j)
    · intro i m
      exact DirectedSystem.map_self (f := fun {i j} h => D.SMap i j h) m
    · intro i j k hij hjk m
      exact DirectedSystem.map_map (f := fun {i j} h => D.SMap i j h) hij hjk m
    · intro i
      let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
      exact Algebra.linearMap (D.SStage i) S'
    · intro i j hij m
      simp [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    · intro i j hij
      let _ : Algebra (D.SStage i) (D.SStage j) := (D.SMap i j hij).toAlgebra
      simpa using algebraMap_liftBaseChange_bijective (R' := D.SStage i) (S' := D.SStage j)
    · intro i
      let _ : Algebra (D.SStage i) S' := (D.targetStageToLimit i).toAlgebra
      simpa using algebraMap_liftBaseChange_bijective (R' := D.SStage i) (S' := S')
  have hflatModule :
      let _ : Module R' S' := Module.compHom S' f
      Module.Flat R' S' := by
    simpa [RingHom.Flat] using hflat
  obtain ⟨i₀, hi₀⟩ :=
    eventually_flat_stageModules_of_flat_limit
      (f := f) (M := S') C hflatModule
  refine ⟨i₀, fun j hij => ?_⟩
  simpa [C, RingHom.Flat] using (hi₀ j hij)

omit [Algebra R B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] in
/-- Helper for Chap10 Lemma 10 168 2: the finite polynomial algebra on the coefficient set of a
presentation contains all coefficients of that presentation. -/
lemma presentation_hasCoeffs_mvPolynomial_coeffs
    {ι σ : Type*} (P : Algebra.Presentation A B ι σ) :
    let A₀ := MvPolynomial P.coeffs R
    letI : CommRing A₀ := inferInstance
    let aAlg : A₀ →ₐ[R] A := MvPolynomial.aeval fun x : P.coeffs => (x : A)
    let a : A₀ →+* A := aAlg.toRingHom
    letI : Algebra A₀ A := a.toAlgebra
    letI : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
    letI : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
    P.HasCoeffs A₀ := by
  let A₀ := MvPolynomial P.coeffs R
  letI : CommRing A₀ := inferInstance
  let aAlg : A₀ →ₐ[R] A := MvPolynomial.aeval fun x : P.coeffs => (x : A)
  let a : A₀ →+* A := aAlg.toRingHom
  letI : Algebra A₀ A := a.toAlgebra
  letI : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
  letI : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
  -- Proof comment: every coefficient is the image of the corresponding polynomial variable.
  refine ⟨fun x hx => ?_⟩
  refine ⟨MvPolynomial.X ⟨x, hx⟩, ?_⟩
  simp [RingHom.algebraMap_toAlgebra]

omit [Algebra R A] [Algebra R B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] in
/-- Helper for Chap10 Lemma 10 168 2: if the relation index type is finite, the polynomial
coefficient model of a presentation is finitely presented over the base. -/
lemma finitePresentation_mvPolynomial_coeffs
    {ι σ : Type*} (P : Algebra.Presentation A B ι σ) [Finite σ] :
    let A₀ := MvPolynomial P.coeffs R
    Algebra.FinitePresentation R A₀ := by
  -- Proof comment: finiteness of the relation index makes the set of relation coefficients finite,
  -- so the coefficient polynomial algebra has finitely many variables.
  haveI : Finite P.coeffs := P.finite_coeffs
  infer_instance

omit [Algebra.FinitePresentation A B] in
/-- Helper for Chap10 Lemma 10 168 2: the canonical map from a descended
`P.ModelOfHasCoeffs A₀` model to `B` agrees with the original coefficient map from `A₀`. -/
lemma modelOfHasCoeffs_comp_algebraMap
    {A₀ : Type*} [CommRing A₀] [Algebra A₀ A] [Algebra A₀ B] [IsScalarTower A₀ A B]
    {ι σ : Type*} (P : Algebra.Presentation A B ι σ) [P.HasCoeffs A₀] :
    let B₀ := P.ModelOfHasCoeffs A₀
    letI : CommRing B₀ := inferInstance
    letI : Algebra A₀ B₀ := inferInstance
    let b : B₀ →+* B :=
      ((P.tensorModelOfHasCoeffsEquiv A₀).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)
    b.comp (algebraMap A₀ B₀) = algebraMap A₀ B := by
  -- Proof comment: reuse the owner computation for the descended coefficient model, specialized
  -- to the ring homomorphism surface used by the target existential data.
  exact Algebra.Presentation.descended_model_algebraMap_eq A P

omit [Algebra.FinitePresentation A B] in
/-- Helper for Chap10 Lemma 10 168 2: a presentation model containing the coefficients gives the
canonical pushout square `A₀ → A`, `A₀ → P.ModelOfHasCoeffs A₀`, and `A → B`. -/
lemma modelOfHasCoeffs_isPushout
    {A₀ : Type*} [CommRing A₀] [Algebra A₀ A] [Algebra A₀ B] [IsScalarTower A₀ A B]
    {ι σ : Type*} (P : Algebra.Presentation A B ι σ) [P.HasCoeffs A₀] :
    let B₀ := P.ModelOfHasCoeffs A₀
    letI : CommRing B₀ := inferInstance
    letI : Algebra A₀ B₀ := inferInstance
    let b : B₀ →+* B :=
      ((P.tensorModelOfHasCoeffsEquiv A₀).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom)
    letI : Algebra B₀ B := b.toAlgebra
    letI : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <|
      (modelOfHasCoeffs_comp_algebraMap (A := A) (B := B) P).symm
    Algebra.IsPushout A₀ A B₀ B := by
  let B₀ := P.ModelOfHasCoeffs A₀
  letI : CommRing B₀ := inferInstance
  letI : Algebra A₀ B₀ := inferInstance
  let b : B₀ →+* B :=
    ((P.tensorModelOfHasCoeffsEquiv A₀).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom)
  letI : Algebra B₀ B := b.toAlgebra
  letI : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <|
    (modelOfHasCoeffs_comp_algebraMap (A := A) (B := B) P).symm
  letI : IsScalarTower A₀ A (A ⊗[A₀] B₀) := IsScalarTower.of_algebraMap_eq' rfl
  have hright :
      (P.tensorModelOfHasCoeffsEquiv A₀).toRingHom.comp (algebraMap B₀ (A ⊗[A₀] B₀)) =
        algebraMap B₀ B := by
    -- Proof comment: the right tensor algebra structure is exactly the inclusion used to define
    -- the descended map `b`, so the comparison condition for `of_equiv` is definitional.
    rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
    rfl
  -- Proof comment: transport the canonical tensor-product pushout square across the presentation
  -- equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B`.
  exact Algebra.IsPushout.of_equiv (R := A₀) (R' := A) (S := B₀)
    (S' := A ⊗[A₀] B₀) (T := B)
    (P.tensorModelOfHasCoeffsEquiv A₀) hright

/-- Helper for Chap10 Lemma 10 168 2: faithful flatness of the limit map eventually makes the
stage spectrum maps surjective. -/
lemma exists_laterStage_comapSurjective_of_faithfullyFlat_limit
    (D : DirectedFiniteTypeHomApproximation.{v, w, v} (algebraMap A B))
    (hDbase : D.HasBijectiveBaseChangeTransitions)
    (hff : (algebraMap A B).FaithfullyFlat) (i₀ : D.Λ) :
    ∃ j : D.Λ, i₀ ≤ j ∧ Function.Surjective (PrimeSpectrum.comap (D.stageMap j)) := by
  -- TODO: represent the constructible complement of the stage image by
  -- `PrimeSpectrum.exists_range_eq_of_isConstructible`, descend the empty limit pullback through
  -- the direct-limit tensor presentation, and rewrite the later pullback by
  -- `stageRing_isPushout_of_fpApproximation`.
  -- Proof comment: this is exactly the remaining spectrum-surjectivity descent frontier; all
  -- flatness data is intentionally kept out of this helper.
  sorry

/-- Helper for Chap10 Lemma 10 168 2: a faithfully flat finite approximation stage gives the
finite-presentation `R`-model witnesses in the target theorem. -/
lemma exists_baseChangeWitnesses_of_faithfullyFlatStage
    (D : DirectedFiniteTypeHomApproximation.{v, w, v} (algebraMap A B))
    (hDbase : D.HasBijectiveBaseChangeTransitions) (i : D.Λ)
    (hstageFF : (D.stageMap i).FaithfullyFlat) :
    ∃ (A₀ : Type (max u v w)) (_ : CommRing A₀) (r : R →+* A₀) (a : A₀ →+* A),
      ∃ (ha : a.comp r = algebraMap R A),
      r.FinitePresentation ∧
      ∃ (B₀ : Type (max u v w)) (_ : CommRing B₀) (g : A₀ →+* B₀) (b : B₀ →+* B),
        ∃ (hb : b.comp g = (algebraMap A B).comp a),
        g.FinitePresentation ∧
        g.FaithfullyFlat ∧
        let _ : Algebra A₀ A := a.toAlgebra
        let _ : Algebra A₀ B₀ := g.toAlgebra
        let _ : Algebra B₀ B := b.toAlgebra
        let _ : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
        let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <| by
          simpa [RingHom.algebraMap_toAlgebra] using hb.symm
        Algebra.IsPushout A₀ A B₀ B := by
  -- TODO: take `A₀ = R ⊗[ℤ] D.RStage i` and
  -- `B₀ = A₀ ⊗[D.RStage i] D.SStage i`, prove the two finite-presentation fields by base
  -- change, transport `hstageFF` by faithfully-flat base change, and compose the resulting
  -- pushout square with `stageToLimit_isPushout_of_fpApproximation`.
  -- Proof comment: the selected stage already has the right faithful-flat invariant; this helper
  -- isolates only the tensor/universe packaging into the target existential data.
  sorry

/-- Lemma 10.168.2: if `A` is an `R`-algebra and `B` is a faithfully flat finitely presented
`A`-algebra, then the map `A → B` descends to a faithfully flat finitely presented map
`A₀ → B₀` with `A₀` finitely presented over `R`, organized by a compatible pushout square
`R → A₀ → A`, `A₀ → B₀ → B`. The explicit `A`-algebra equivalence `A ⊗[A₀] B₀ ≃ₐ[A] B`
is the canonical derived map `Algebra.IsPushout.equiv A₀ A B₀ B`. -/
@[stacks 034Y]
theorem exists_faithfullyFlat_finitePresentation_approximation
    (hff : (algebraMap A B).FaithfullyFlat) :
    ∃ (A₀ : Type (max u v w)) (_ : CommRing A₀) (r : R →+* A₀) (a : A₀ →+* A),
      ∃ (ha : a.comp r = algebraMap R A),
      r.FinitePresentation ∧
      ∃ (B₀ : Type (max u v w)) (_ : CommRing B₀) (g : A₀ →+* B₀) (b : B₀ →+* B),
        ∃ (hb : b.comp g = (algebraMap A B).comp a),
        g.FinitePresentation ∧
        g.FaithfullyFlat ∧
        let _ : Algebra A₀ A := a.toAlgebra
        let _ : Algebra A₀ B₀ := g.toAlgebra
        let _ : Algebra B₀ B := b.toAlgebra
        let _ : Algebra A₀ B := ((algebraMap A B).comp a).toAlgebra
        let _ : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq' <| by
          simpa [RingHom.algebraMap_toAlgebra] using hb.symm
        Algebra.IsPushout A₀ A B₀ B := by
  -- Proof comment: faithful flatness of the given map immediately supplies the two global
  -- invariants used by the source proof: flatness and surjectivity on prime spectra.
  have hflatAB : (algebraMap A B).Flat := hff.flat
  have hsurjAB : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) :=
    comap_surjective_of_faithfullyFlat hff
  -- Route correction: the earlier coefficient-model route reduced the theorem to the same
  -- missing monolithic faithfully-flat approximation statement. We now pivot to the canonical
  -- directed finite-presentation approximation of the actual map `A → B`.
  have hfpAB : (algebraMap A B).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (inferInstance : Algebra.FinitePresentation A B)
  obtain ⟨D, hDbase⟩ :=
    exists_directedFinitePresentationHomApproximation (algebraMap A B) hfpAB
  -- Proof comment: the proved companion API gives finite-presentation stage maps and identifies
  -- the stage-to-limit composites with the original algebra map.
  have hstageFP : ∀ i : D.Λ, (D.stageMap i).FinitePresentation := fun i =>
    stageMap_finitePresentation_of_fpApproximation D i
  have hstageCompat :
      ∀ i : D.Λ,
        (D.targetStageToLimit i).comp (D.stageMap i) =
          (algebraMap A B).comp (D.sourceStageToLimit i) := fun i =>
    stageToLimit_comp_stageMap_of_fpApproximation D i
  have hstageLimitPushout :
      ∀ i : D.Λ,
        let _ : Algebra (D.RStage i) A := (D.sourceStageToLimit i).toAlgebra
        let _ : Algebra (D.RStage i) (D.SStage i) := (D.stageMap i).toAlgebra
        let _ : Algebra A B := (algebraMap A B).toAlgebra
        let _ : Algebra (D.SStage i) B := (D.targetStageToLimit i).toAlgebra
        let _ : Algebra (D.RStage i) B :=
          ((algebraMap A B).comp (D.sourceStageToLimit i)).toAlgebra
        let _ : IsScalarTower (D.RStage i) A B := IsScalarTower.of_algebraMap_eq' rfl
        let _ : IsScalarTower (D.RStage i) (D.SStage i) B :=
          IsScalarTower.of_algebraMap_eq' <|
            (stageToLimit_comp_stageMap_of_fpApproximation D i).symm
        Algebra.IsPushout (D.RStage i) A (D.SStage i) B := fun i =>
    stageToLimit_isPushout_of_fpApproximation D hDbase i
  -- Proof comment: these established stage facts reduce the remaining task to the structural
  -- descent of faithful flatness to a sufficiently late stage and the final `R`-model packaging.
  have hffAB_from_invariants : (algebraMap A B).FaithfullyFlat :=
    faithfullyFlat_of_flat_and_comap_surjective hflatAB hsurjAB
  -- Proof comment: the imported module-flatness approximation theorem, applied to the
  -- self-module approximation above, supplies a bound after which all stage maps are flat.
  obtain ⟨iFlat, hflatStageEventually⟩ :=
    eventually_flatStage_of_flat_limit_fpApproximation D hDbase hflatAB
  -- Proof comment: the remaining spectrum step finds a later stage whose image on spectra is
  -- all of the source; the new combination helper turns that plus eventual flatness into a
  -- faithfully flat finite stage.
  have hsurjStageEventually :
      ∃ j : D.Λ, iFlat ≤ j ∧ Function.Surjective (PrimeSpectrum.comap (D.stageMap j)) :=
    exists_laterStage_comapSurjective_of_faithfullyFlat_limit (A := A) (B := B)
      D hDbase hffAB_from_invariants iFlat
  obtain ⟨iFF, _hiFlat, hstageFF⟩ :=
    exists_faithfullyFlatStage_of_eventuallyFlat_and_stageSurjective D hflatStageEventually
      hsurjStageEventually
  -- Proof comment: once the faithfully flat stage is selected, the final helper performs the
  -- `R`-base-change packaging required by the statement.
  exact exists_baseChangeWitnesses_of_faithfullyFlatStage (R := R) (A := A) (B := B)
    D hDbase iFF hstageFF

end
