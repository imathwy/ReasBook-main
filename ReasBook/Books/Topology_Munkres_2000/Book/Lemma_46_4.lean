module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace

public section

open CompactlyCoherentSpace

universe u v

/-
Lemma 46.4. If `X` is compactly generated, a function `f : X → Y` is continuous if
its restriction to each compact subspace of `X` is continuous.
-/
#check fun {X : Type u} [TopologicalSpace X] [CompactlyCoherentSpace X]
    {Y : Type v} [TopologicalSpace Y] (f : X → Y)
    (hf : ∀ K : Set X, IsCompact K → ContinuousOn f K) ↦
  isCoherentWith.continuous_iff.mpr hf

#check continuousOn_iff_continuous_restrict
