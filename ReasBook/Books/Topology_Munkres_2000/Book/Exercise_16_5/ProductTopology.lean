module

public import Mathlib.Topology.Constructions.SumProd

public section

universe u v

namespace TopologicalSpace

/-- The product topology determined by explicit topologies on the two factors. -/
@[expose, reducible]
def prod {X : Type u} {Y : Type v} (𝒯 : TopologicalSpace X) (𝒰 : TopologicalSpace Y) :
    TopologicalSpace (X × Y) :=
  induced Prod.fst 𝒯 ⊓ induced Prod.snd 𝒰

/-- The explicit product topology agrees with Mathlib's inferred product topology. -/
@[simp]
theorem prod_eq {X : Type u} {Y : Type v} [𝒯 : TopologicalSpace X] [𝒰 : TopologicalSpace Y] :
    prod 𝒯 𝒰 = (inferInstance : TopologicalSpace (X × Y)) := rfl

end TopologicalSpace
