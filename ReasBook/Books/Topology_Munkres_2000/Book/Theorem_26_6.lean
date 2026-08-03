module

import Mathlib.Topology.Homeomorph.Lemmas

public section

universe u v

/- Theorem 26.6. Let `f : X → Y` be a bijective continuous function. If `X` is compact
and `Y` is Hausdorff, then `f` is a homeomorphism. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (f : X → Y) (hf : Continuous f)
    (hbij : Function.Bijective f) ↦
  (isHomeomorph_iff_continuous_bijective).2 ⟨hf, hbij⟩
