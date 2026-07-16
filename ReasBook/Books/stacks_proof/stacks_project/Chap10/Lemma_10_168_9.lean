import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Lemma_10_136_4
import stacks_proof.stacks_project.Chap10.Lemma_10_136_9
import stacks_proof.stacks_project.Chap10.Lemma_10_168_4
import stacks_proof.stacks_project.Chap10.Lemma_10_168_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

/-
Domain-style sampling:
* primary domain: descent of relative global complete intersections and syntomic morphisms along
  directed ring colimits via tensor-product base change;
* sampled owner declarations of the same kind:
  `Algebra.IsRelativeGlobalCompleteIntersection`,
  `Algebra.IsRelativeGlobalCompleteIntersection.baseChange`,
  `Algebra.IsRelativeGlobalCompleteIntersection.syntomic`,
  `RingHom.Syntomic.ofLocalizationSpanTarget`;
* best owner abstraction:
  `source-facing`: the direct-limit descent theorems below;
  `core/canonical`: `Algebra.IsRelativeGlobalCompleteIntersection` for the base-changed codomain
    over the base-changed source, together with `RingHom.Syntomic` for the map-level conclusion;
  `bridge/view`: the tensor-product base-change maps `Algebra.TensorProduct.map φ₀ (...)`.
* primitive vs. derived:
  primitive data are the directed system, the distinguished stage `i₀`, and the stagewise/direct-
  limit tensor-product base-change maps;
  derived API is any map-based reformulation of relative global complete intersection via the
  induced algebra structure on such a map, so it should not remain as a parallel public owner.
-/
variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
variable (A : I → Type u) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (fun i j hij ↦ f i j hij)]
variable {i₀ : I}
variable {B₀ C₀ : Type w} [CommRing B₀] [CommRing C₀]
variable [Algebra (A i₀) B₀] [Algebra (A i₀) C₀]

local notation "A∞" => Ring.DirectLimit A (fun i j hij ↦ f i j hij)

/-- Helper for Chap10 Lemma 10 168 9: the canonical stage tensor base-change map is finitely
presented whenever the original stage algebra map `φ₀` is finitely presented. -/
lemma stageTensorMap_finitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    {i : I} (hi : i₀ ≤ i) :
    letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
    (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).FinitePresentation := by
  -- Proof comment: use the tail-indexed finite-presentation lemma from the bijectivity descent
  -- file and unpack the chosen tail stage back to the ambient index `i`.
  simpa using
    literal_stage_tensor_finitePresentation
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀)
      φ₀ hfp ⟨i, hi⟩

/-- Helper for Chap10 Lemma 10 168 9: the canonical stage tensor target is finitely presented
as an algebra over the canonical stage tensor source. -/
lemma stageTensorAlgebra_finitePresentation
    (φ₀ : B₀ →ₐ[A i₀] C₀) (hfp : φ₀.FinitePresentation)
    {i : I} (hi : i₀ ≤ i) :
    letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
    letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toAlgebra
    Algebra.FinitePresentation (B₀ ⊗[A i₀] A i) (C₀ ⊗[A i₀] A i) := by
  letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
  letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toAlgebra
  -- Proof comment: reinterpret the map-level finite-presentation predicate through the algebra
  -- structure induced by the canonical tensor map.
  rw [← RingHom.finitePresentation_algebraMap]
  simpa [AlgHom.FinitePresentation, RingHom.FinitePresentation] using
    stageTensorMap_finitePresentation
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hfp hi

/-- Helper for Chap10 Lemma 10 168 9: `Algebra.IsRelativeGlobalCompleteIntersection` is
preserved by algebra equivalences over the same base ring. -/
lemma relativeGlobalCompleteIntersection_of_algEquiv
    {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T]
    (hS : Algebra.IsRelativeGlobalCompleteIntersection R S) (e : S ≃ₐ[R] T) :
    Algebra.IsRelativeGlobalCompleteIntersection R T := by
  -- Proof comment: use the canonical owner-level transport lemma instead of duplicating the
  -- presentation and fiber-dimension transport argument locally.
  exact Algebra.Presentation.IsRelativeGlobalCompleteIntersection.of_algEquiv hS e

omit [IsDirected I (· ≤ ·)] [DirectedSystem A (fun i j hij ↦ f i j hij)] in
/-- Helper for Chap10 Lemma 10 168 9: an existential witness over the cofinal tail above `i₀`
unpacks to the corresponding ambient stage witness with its lower-bound proof. -/
lemma exists_stage_of_tail_property
    {P : ∀ i : I, i₀ ≤ i → Prop}
    (htail : ∃ j : Set.Ici i₀, P j.1 j.2) :
    ∃ (j : I) (hij : i₀ ≤ j), P j hij := by
  -- Proof comment: the subtype tail index stores both the ambient stage and the needed proof
  -- that the stage lies above `i₀`.
  obtain ⟨j, hj⟩ := htail
  exact ⟨j.1, j.2, hj⟩

omit [IsDirected I (· ≤ ·)] [DirectedSystem A (fun i j hij ↦ f i j hij)] in
/-- Helper for Chap10 Lemma 10 168 9: an ambient stage witness with its lower-bound proof
packages as a witness over the cofinal tail above `i₀`. -/
lemma exists_tail_property_of_stage_property
    {P : ∀ i : I, i₀ ≤ i → Prop}
    (hstage : ∃ (j : I) (hij : i₀ ≤ j), P j hij) :
    ∃ j : Set.Ici i₀, P j.1 j.2 := by
  -- Proof comment: the public witness already contains exactly the data needed to build the
  -- tail-subtype index.
  obtain ⟨j, hij, hP⟩ := hstage
  exact ⟨⟨j, hij⟩, hP⟩

omit [IsDirected I (· ≤ ·)] [DirectedSystem A (fun i j hij ↦ f i j hij)] in
/-- Helper for Chap10 Lemma 10 168 9: existential witnesses over the cofinal tail above `i₀`
are equivalent to ambient stage witnesses carrying the lower-bound proof. -/
lemma exists_tail_property_iff_stage_property
    {P : ∀ i : I, i₀ ≤ i → Prop} :
    (∃ j : Set.Ici i₀, P j.1 j.2) ↔
      ∃ (j : I) (hij : i₀ ≤ j), P j hij := by
  -- Proof comment: this packages the two elementary conversions between tail-subtype and
  -- ambient-stage witnesses so later descent statements can consume a single bridge.
  constructor
  · exact exists_stage_of_tail_property (i₀ := i₀) (P := P)
  · exact exists_tail_property_of_stage_property (i₀ := i₀) (P := P)

/-- Helper for Chap10 Lemma 10 168 9: relative global complete intersections of the direct-limit
tensor base-change descend to a stage in the cofinal tail above `i₀`. -/
lemma relativeGlobalCompleteIntersectionLimitTensor_descends_to_tail
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hGCI :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A∞) (C₀ ⊗[A i₀] A∞)) :
    ∃ (j : Set.Ici i₀),
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A j.1) (C₀ ⊗[A i₀] A j.1) := by
  -- Proof comment: the verified prefix is to keep the target in the cofinal-tail normal form.
  -- Route correction: the earlier target-local owner-level descent wrapper reduces to the same
  -- missing presentation bad-locus descent; that prerequisite must be proved in its owner layer
  -- before this tail helper can be closed without another black-box `sorry`.
  -- TODO for Chap10 Lemma 10 168 9: choose a presentation witnessing `hGCI`, descend its finite
  -- data and empty bad fiber-dimension locus to a tail stage, then identify the descended model
  -- with the canonical tensor target using finite-presentation bijectivity descent and
  -- `relativeGlobalCompleteIntersection_of_algEquiv`.
  let _ := hfp
  let _ := hGCI
  sorry

omit [IsDirected I (· ≤ ·)] [DirectedSystem A (fun i j hij ↦ f i j hij)] in
/-- Helper for Chap10 Lemma 10 168 9: a relative-GCI witness over the cofinal tail gives the
public stage-and-inequality witness. -/
lemma exists_stage_of_tail_relativeGlobalCompleteIntersection
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (htail :
      ∃ (j : Set.Ici i₀),
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toAlgebra
        Algebra.IsRelativeGlobalCompleteIntersection
          (B₀ ⊗[A i₀] A j.1) (C₀ ⊗[A i₀] A j.1)) :
    ∃ (j : I) (hij : i₀ ≤ j),
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A j) (C₀ ⊗[A i₀] A j) := by
  -- Proof comment: the subtype tail index stores exactly the lower-bound proof required by the
  -- public statement.
  exact (exists_tail_property_iff_stage_property
    (i₀ := i₀)
    (P := fun j hij ↦
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A j) (C₀ ⊗[A i₀] A j))).1
    htail

-- Proof sketch: view the colimit base change of `φ0` as a map over the direct limit ring and use
-- a finite-type witness `R → S'` for the relative global complete intersection from Lemma
-- `10.136.11`. Finite presentation of `φ0` descends the structural map to some stage by Lemma
-- `10.127.3`, Lemma `10.168.6` upgrades the descended comparison map to an isomorphism, and Lemma
-- `10.136.9` then transports the relative global complete intersection structure to that stage.
/-- Lemma 10.168.9 (1): if the base change of `φ₀ : B₀ → C₀` to the direct limit ring is a
relative global complete intersection and `C₀` is finitely presented over `B₀`, then after
passing to some later stage the corresponding stagewise base change is already a relative global
complete intersection. -/
@[stacks 0C33]
theorem exists_relativeGlobalCompleteIntersection_stage_base_change_of_direct_limit_base_change
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hGCI :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A∞) (C₀ ⊗[A i₀] A∞)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      letI := (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection (B₀ ⊗[A i₀] A i) (C₀ ⊗[A i₀] A i) := by
  -- Proof comment: first prove the source-facing descent theorem in the cofinal-tail normal form,
  -- then unpack the tail index into the public stage and inequality witnesses.
  exact exists_stage_of_tail_relativeGlobalCompleteIntersection
    (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀
    (relativeGlobalCompleteIntersectionLimitTensor_descends_to_tail
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hfp hGCI)

/-- Helper for Chap10 Lemma 10 168 9: syntomicity of the direct-limit tensor base-change
descends to a stage in the cofinal tail above `i₀`. -/
lemma syntomicLimitTensor_descends_to_tail
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsyntomic :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.Syntomic) :
    ∃ (j : Set.Ici i₀),
      letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.Syntomic := by
  -- Proof comment: the verified prefix is again the cofinal-tail normal form.  The open step is
  -- the finite target-local RGCI chart descent and syntomic reassembly.
  -- Route correction: extracting syntomic charts locally again depends on the missing
  -- syntomic-to-finite-RGCI-principal-cover theorem from the earlier syntomic owner layer, so the
  -- target file should only consume that API once it exists.
  -- TODO for Chap10 Lemma 10 168 9: extract a finite principal-open cover of the direct-limit
  -- tensor target by relative-GCI charts from `hsyntomic`, descend the finitely many generators
  -- and their unit-ideal relation to one tail stage, apply
  -- `relativeGlobalCompleteIntersectionLimitTensor_descends_to_tail` chartwise, and reassemble
  -- syntomicity using `RingHom.Syntomic.ofLocalizationSpanTarget`.
  let _ := hfp
  let _ := hsyntomic
  sorry

omit [IsDirected I (· ≤ ·)] [DirectedSystem A (fun i j hij ↦ f i j hij)] in
/-- Helper for Chap10 Lemma 10 168 9: a syntomic witness over the cofinal tail gives the public
stage-and-inequality witness. -/
lemma exists_stage_of_tail_syntomic
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (htail :
      ∃ (j : Set.Ici i₀),
        letI : Algebra (A i₀) (A j.1) := (f i₀ j.1 j.2).toAlgebra
        (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j.1))).toRingHom.Syntomic) :
    ∃ (j : I) (hij : i₀ ≤ j),
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).toRingHom.Syntomic := by
  -- Proof comment: unpacking the tail subtype is the only bookkeeping needed at the public API
  -- boundary.
  exact (exists_tail_property_iff_stage_property
    (i₀ := i₀)
    (P := fun j hij ↦
      letI : Algebra (A i₀) (A j) := (f i₀ j hij).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A j))).toRingHom.Syntomic)).1
    htail

-- Proof sketch: choose finitely many elements generating the unit ideal on the colimit base
-- change so that each basic localization is a relative global complete intersection by Lemma
-- `10.136.15`. Descend those finitely many generators to one stage, enlarge so they still
-- generate the unit ideal there, apply the previous clause to each localization, and conclude by
-- the locality criterion for syntomic maps from Lemma `10.136.4`.
/-- Lemma 10.168.9 (2): if the base change of `φ₀ : B₀ → C₀` to the direct limit ring is syntomic
and `C₀` is finitely presented over `B₀`, then after passing to some later stage the corresponding
stagewise base change is already syntomic. -/
@[stacks 0C33]
theorem exists_syntomic_stage_base_change_of_direct_limit_base_change
    (φ₀ : B₀ →ₐ[A i₀] C₀)
    (hfp : φ₀.FinitePresentation)
    (hsyntomic :
      letI : Algebra (A i₀) A∞ := (Ring.DirectLimit.of A (fun i j hij ↦ f i j hij) i₀).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) A∞)).toRingHom.Syntomic) :
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (A i₀) (A i) := (f i₀ i hi).toAlgebra
      (Algebra.TensorProduct.map φ₀ (AlgHom.id (A i₀) (A i))).toRingHom.Syntomic := by
  -- Proof comment: prove syntomic descent in the cofinal-tail normal form and then forget the
  -- subtype packaging of the chosen stage.
  exact exists_stage_of_tail_syntomic
    (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀
    (syntomicLimitTensor_descends_to_tail
      (A := A) (f := f) (i₀ := i₀) (B₀ := B₀) (C₀ := C₀) φ₀ hfp hsyntomic)

end
