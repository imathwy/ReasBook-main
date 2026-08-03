module

public import Mathlib.Topology.Defs.Induced

public section

universe u v

namespace Topology

/-- `tA` is the quotient topology induced by `p` from `tX`. -/
def IsQuotientTopology {X : Type u} {A : Type v} (tX : TopologicalSpace X)
    (p : X → A) (tA : TopologicalSpace A) : Prop :=
  tA = tX.coinduced p ∧ Function.Surjective p

/-- The explicit specification of `IsQuotientTopology`. -/
theorem isQuotientTopology_iff {X : Type u} {A : Type v} (tX : TopologicalSpace X)
    (p : X → A) (tA : TopologicalSpace A) :
    IsQuotientTopology tX p tA ↔ tA = tX.coinduced p ∧ Function.Surjective p := by
  rfl

/-- With the displayed topologies installed, `IsQuotientTopology` is exactly the assertion that
`p` is a quotient map. -/
theorem isQuotientTopology_iff_isQuotientMap {X : Type u} [tX : TopologicalSpace X]
    {A : Type v} [tA : TopologicalSpace A] (p : X → A) :
    IsQuotientTopology tX p tA ↔ IsQuotientMap p := by
  constructor
  · rintro ⟨h, hp⟩
    exact ⟨⟨h⟩, hp⟩
  · intro hp
    exact ⟨hp.isCoinducing.eq_coinduced, hp.surjective⟩

end Topology

/-- Definition 22.4: A surjection `p : X → A` determines a unique topology on
`A` for which `p` is a quotient map. -/
theorem existsUnique_quotientTopology {X : Type u} [tX : TopologicalSpace X]
    {A : Type v} (p : X → A) (hp : Function.Surjective p) :
    ∃! tA : TopologicalSpace A, Topology.IsQuotientTopology tX p tA := by
  let tA := tX.coinduced p
  have hq : Topology.IsQuotientTopology tX p tA := ⟨rfl, hp⟩
  refine ⟨tA, hq, ?_⟩
  intro topology htopology
  exact htopology.1
