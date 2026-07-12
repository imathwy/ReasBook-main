import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Chap12.Theorem_12_12_4_1.GammaSubgroupAction
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_2_1.AlgClosedElementaryInduction

open IsCyclotomicExtension.Rat
open scoped FiniteRepGrothendieckInduction
open scoped Representation

noncomputable section

universe u

namespace Representation

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]

local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ

local instance : NumberField Lexp := inferInstance

local instance : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

/-- Helper for Theorem 16-16.1-5: at the top cyclotomic field, Serre's arithmetic subgroup
`Γ[(⊤)](G)` is trivial. -/
theorem gammaSubgroup_top_eq_bot_bridge :
    Γ[(⊤ : IntermediateField ℚ Lexp)](G) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- Unfold `Γ[K](G)` once; the full cyclotomic field has trivial fixing subgroup.
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot (galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

omit [Finite G] in
/-- Helper for Theorem 16-16.1-5: for the trivial arithmetic subgroup, Serre's
`Γ`-elementary subgroups are exactly the ordinary elementary subgroups. -/
theorem Subgroup.isGammaElementary_bot_iff_isElementary_bridge
    (H : Subgroup G) :
    Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H ↔
      IsElementary H := by
  exact Subgroup.IsGammaElementary.bot_iff_isElementary H

/-- Helper for Theorem 16-16.1-5: isolate the source-faithful Brauer-induction specialization as
its own small theorem-local goal, stated with the public induction owner on `R₀`. -/
theorem grothendieckClass_exists_sum_of_elementary_subgroup_inductions_bridge
    (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
  exact
    algClosed_grothendieckClass_exists_sum_of_elementary_subgroup_inductions
      (k := k) (G := G) x

end

end Representation
