module

public import Topology_Munkres_2000.Book.Exercise_18_13
public import Mathlib.Topology.UniformSpace.UniformEmbedding

public section

universe u v

/-- Exercise 43.2: a uniformly continuous map from a subset to a complete uniform space has a
uniformly continuous extension to the closure, unique among continuous extensions. -/
theorem UniformContinuous.exists_unique_continuous_extensionToClosure
    {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y] [T0Space Y]
    [CompleteSpace Y] {A : Set X} {f : A → Y} (hf : UniformContinuous f) :
    ∃ g : closure A → Y,
      UniformContinuous g ∧
        (∀ x : A, g ⟨x, subset_closure x.property⟩ = f x) ∧
        ∀ h : closure A → Y, Continuous h →
          (∀ x : A, h ⟨x, subset_closure x.property⟩ = f x) → h = g := by
  -- Regard `A` as a dense, uniformly inducing subspace of its closure.
  let e : A → closure A := Set.inclusion subset_closure
  have he : IsUniformInducing e := by
    exact (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hd : DenseRange e := by
    exact (denseRange_inclusion_iff subset_closure).2 subset_rfl
  -- Extend along this dense inclusion and transfer uniform continuity to the extension.
  let g : closure A → Y := (he.isDenseInducing hd).extend f
  have hg : UniformContinuous g := by
    exact uniformContinuous_uniformly_extend he hd hf
  -- The canonical dense extension agrees with `f` on the original subset.
  have hg_extends : ∀ x : A, g ⟨x, subset_closure x.property⟩ = f x := by
    intro x
    simpa only [g, e, Set.inclusion] using uniformly_extend_of_ind he hd hf x
  refine ⟨g, hg, hg_extends, ?_⟩
  -- Continuous maps agreeing on the dense subset agree throughout its closure.
  intro h hh hh_extends
  exact Continuous.extensionToClosure_unique hh hg.continuous hh_extends hg_extends

/- The continuous extension in Exercise 43.2 is unique by the earlier closure-extension theorem. -/
#check Continuous.extensionToClosure_unique
