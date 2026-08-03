module

public import Topology_Munkres_2000.Book.Theorem_19_3.BoxTopology
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.WithTopology

public section

universe u v w

namespace Pi

/-- The coordinatewise map between dependent products equipped with their box topologies. -/
def boxMap {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) :
    WithTopology ((i : ι) → A i) (boxTopologicalSpace A) →
      WithTopology ((i : ι) → B i) (boxTopologicalSpace B) :=
  fun x ↦ WithTopology.toTopology (boxTopologicalSpace B) (Pi.map f x.ofTopology)

/-- Applying `boxMap` is coordinatewise application on the underlying dependent product. -/
@[simp]
theorem boxMap_apply {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i)
    (x : WithTopology ((i : ι) → A i) (boxTopologicalSpace A)) :
    (boxMap f x).ofTopology = Pi.map f x.ofTopology := by
  rfl

/-- A dependent product of coordinatewise homeomorphisms is a homeomorphism for the box
topologies. -/
theorem isHomeomorph_boxMap {ι : Type u} {A : ι → Type v} {B : ι → Type w}
    [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)]
    (f : (i : ι) → A i → B i) (hf : ∀ i, IsHomeomorph (f i)) :
    IsHomeomorph (boxMap f) := by
  -- Local instance justification (defeq pin): domain map predicates use the stated box topology.
  letI : TopologicalSpace ((i : ι) → A i) := boxTopologicalSpace A
  -- Local instance justification (defeq pin): codomain predicates use the stated box topology.
  letI : TopologicalSpace ((i : ι) → B i) := boxTopologicalSpace B
  let domainHomeomorph :
      WithTopology ((i : ι) → A i) (boxTopologicalSpace A) ≃ₜ ((i : ι) → A i) := {
    toEquiv := WithTopology.equiv _ _
    continuous_toFun := WithTopology.continuous_ofTopology _
    continuous_invFun := WithTopology.continuous_toTopology _ }
  let codomainHomeomorph :
      WithTopology ((i : ι) → B i) (boxTopologicalSpace B) ≃ₜ ((i : ι) → B i) := {
    toEquiv := WithTopology.equiv _ _
    continuous_toFun := WithTopology.continuous_ofTopology _
    continuous_invFun := WithTopology.continuous_toTopology _ }
  have hraw : IsHomeomorph (Pi.map f) := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨⟨⟨(induced_boxMap f fun i ↦ (hf i).isInducing).symm⟩,
      Function.Injective.piMap fun i ↦ (hf i).injective⟩, ?_⟩
    exact Function.Surjective.piMap fun i ↦ (hf i).surjective
  change IsHomeomorph (codomainHomeomorph.symm ∘ Pi.map f ∘ domainHomeomorph)
  exact codomainHomeomorph.symm.isHomeomorph.comp
    (hraw.comp domainHomeomorph.isHomeomorph)

end Pi

/-- The coordinatewise affine map on real sequences determined by `a` and `b`. -/
def realSequenceAffineMap (a b : ℕ → ℝ) : (ℕ → ℝ) → ℕ → ℝ :=
  Pi.map fun i x ↦ a i * x + b i

/-- Evaluating the coordinatewise affine map gives its scalar affine formula. -/
@[simp]
theorem realSequenceAffineMap_apply (a b x : ℕ → ℝ) (i : ℕ) :
    realSequenceAffineMap a b x i = a i * x i + b i := by
  -- Unfold the coordinatewise construction and evaluate `Pi.map` at the chosen index.
  rfl

/-- The coordinatewise affine homeomorphism on real sequence space with the product topology. -/
noncomputable def realSequenceAffineHomeomorph (a b : ℕ → ℝ) (ha : ∀ i, a i ≠ 0) :
    (ℕ → ℝ) ≃ₜ (ℕ → ℝ) :=
  Homeomorph.piCongrRight fun i ↦ affineHomeomorph (a i) (b i) (ha i)

/-- Applying `realSequenceAffineHomeomorph` gives the coordinatewise affine formula. -/
@[simp]
theorem realSequenceAffineHomeomorph_apply (a b : ℕ → ℝ) (ha : ∀ i, a i ≠ 0)
    (x : ℕ → ℝ) :
    realSequenceAffineHomeomorph a b ha x = realSequenceAffineMap a b x := by
  rfl

/-- The coordinatewise affine map with nonzero scale factors is a homeomorphism for the box
topology. -/
theorem isHomeomorph_realSequenceAffineMap_box_of_ne_zero
    (a b : ℕ → ℝ) (ha : ∀ i, a i ≠ 0) :
    IsHomeomorph (Pi.boxMap fun i x ↦ a i * x + b i) := by
  exact Pi.isHomeomorph_boxMap (fun i x ↦ a i * x + b i) fun i ↦
    (affineHomeomorph (a i) (b i) (ha i)).isHomeomorph
