module

import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Defs

public section

universe u v

/-
Definition 45.2: a set `𝓕 ⊆ C(X, Y)` is equicontinuous at `x₀` when the
family of underlying functions indexed by `𝓕` is `EquicontinuousAt` at `x₀`.
It is equicontinuous when that family is `Equicontinuous`.
-/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (𝓕 : Set C(X, Y)) (x₀ : X) ↦ EquicontinuousAt (fun f : 𝓕 ↦ (f : X → Y)) x₀
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (𝓕 : Set C(X, Y)) ↦ Equicontinuous (fun f : 𝓕 ↦ (f : X → Y))
#check Metric.equicontinuousAt_iff_right
