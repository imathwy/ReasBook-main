module

public import Topology_Munkres_2000.Book.Theorem_54_6.Monodromy
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

universe u v

/- Assumption 81.1: Throughout §81, let `p : E → B` be a covering map in the
chapter-wide sense recorded in Assumption 13.0.1, with `p e₀ = b₀`. Write
`H₀ = hp.fundamentalGroupMapRange he₀` for the image of the induced map on
fundamental groups. The group of covering transformations is later identified with
`H₀.normalizer / H₀`. -/
#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E] [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    [LocallyPathConnectedSpace B] (p : E → B) ↦
  IsCoveringMap p ∧ Function.Surjective p

#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) ↦
  hp.fundamentalGroupMapRange he₀

#check fun {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) ↦
  Subgroup.normalizer
    (hp.fundamentalGroupMapRange he₀ : Set (FundamentalGroup B b₀))
