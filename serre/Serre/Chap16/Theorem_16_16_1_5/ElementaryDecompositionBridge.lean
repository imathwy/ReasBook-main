import Mathlib
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap12.Definition_12_12_6_1
import Serre.Chap12.Theorem_12_12_4_1.GammaSubgroupAction
import Serre.Chap17.Theorem_17_17_2_1

open IsCyclotomicExtension.Rat
open scoped FiniteRepGrothendieckInduction
open scoped Representation

noncomputable section

universe u

namespace Representation

section

variable {k : Type u} [Field k]
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

/-- Helper for Theorem 16-16.1-5: for the trivial arithmetic subgroup, Serre's
`Γ`-elementary subgroups are exactly the ordinary elementary subgroups. -/
theorem Subgroup.isGammaElementary_bot_iff_isElementary_bridge
    (H : Subgroup G) :
    Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H ↔
      IsElementary H := by
  constructor
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Collapse the trivial-`Γ` condition prime-by-prime to the Chapter `10` notion.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).1 hp⟩
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Repackage the Chapter `10` elementary witness as a trivial-`Γ` witness.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).2 hp⟩

/-- Helper for Theorem 16-16.1-5: isolate the source-faithful Brauer-induction specialization as
its own small theorem-local goal, stated with the public induction owner on `R₀`. -/
theorem grothendieckClass_exists_sum_of_elementary_subgroup_inductions_bridge
    (x : R₀[k](G)) :
    ∃ (ι : Type (u + 1)) (_ : Fintype ι) (H : ι → Subgroup G)
      (_ : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, Representation.Subgroup.finiteRepGrothendieckGroupInduction k (H i) (y i) := by
  -- Route correction: specialize the Chapter `17` surjectivity theorem at the top cyclotomic
  -- field and then rewrite the `Γ[(⊤)](G)`-elementary witnesses through the trivial-`Γ` bridge.
  rcases gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
      (G := G) (L := Lexp) k (⊤ : IntermediateField ℚ Lexp) x with
    ⟨ι, hι, H, hHΓ, y, hx⟩
  refine ⟨ι, hι, H, ?_, y, ?_⟩
  · intro i
    -- First rewrite the top-field arithmetic subgroup to `⊥`, then collapse to ordinary
    -- elementary subgroups.
    exact
      (Subgroup.isGammaElementary_bot_iff_isElementary_bridge (G := G) (H i)).1 <|
        by simpa [gammaSubgroup_top_eq_bot_bridge (G := G)] using hHΓ i
  · -- The Chapter `17` theorem already uses the same public induction owner after notation
    -- expansion.
    simpa using hx

end

end Representation
