import Mathlib
import Serre.Chap17.Theorem_17_17_2_1

open IsCyclotomicExtension.Rat
open scoped Representation

noncomputable section

universe u w

namespace Representation

section ModularBrauerCorollary

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A
local notation "Lexp" => CyclotomicField (Monoid.exponent G) ℚ
local instance : NumberField Lexp := inferInstance
local instance : IsCyclotomicExtension {Monoid.exponent G} ℚ Lexp :=
  CyclotomicField.isCyclotomicExtension (n := Monoid.exponent G) (K := ℚ)

section

open scoped FiniteRepGrothendieckInduction

/-- Helper for Corollary 17-17.2-2: for the trivial arithmetic subgroup `Γ = ⊥`, Serre's
`Γ`-elementary subgroups are exactly the ordinary elementary subgroups. -/
theorem Subgroup.isGammaElementary_bot_iff_isElementary
    (H : Subgroup G) :
    Subgroup.IsGammaElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) H ↔
      IsElementary H := by
  constructor
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Reduce the `Γ = ⊥` notion prime by prime to the Chapter `10` elementary notion.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).1 hp⟩
  · intro hH
    rcases hH with ⟨p, hp⟩
    -- Repackage the ordinary elementary witness as a trivial-`Γ` witness.
    exact ⟨p, (Subgroup.IsGammaPElementary.bot_iff_isPElementary p H).2 hp⟩

/-- Helper for Corollary 17-17.2-2: at the full cyclotomic field, Serre's arithmetic subgroup is
trivial. -/
theorem gammaSubgroup_top_eq_bot :
    Γ[(⊤ : IntermediateField ℚ Lexp)](G) =
      (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := by
  -- Unfold `Γ[K](G)` once; the top intermediate field has trivial fixing subgroup.
  unfold Representation.gammaSubgroup
  rw [IntermediateField.fixingSubgroup_top]
  simpa using OrderIso.map_bot (galEquivZMod (Monoid.exponent G) Lexp).mapSubgroup

-- Proof sketch: specialize Theorem `17-17.2-1` to the cyclotomic top field, where
-- `Γ[(⊤)](G) = ⊥`, and then rewrite `Γ`-elementary subgroups as ordinary elementary subgroups.
/-- Corollary 17-17.2-2 (1): if `K` is sufficiently large, every element of `R_k(G)` is a finite
sum of classes induced from elementary subgroups of `G`, where the summands lie in the
corresponding Grothendieck groups `R_k(H)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem residueField_grothendieckClass_exists_sum_of_elementary_subgroup_inductions
    (K : Type w) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : R₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, R₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  -- Route correction: the source proof specializes the already-built `Γ[K](G)` statement to the
  -- top cyclotomic field and only then rewrites `Γ[(⊤)](G)` to `⊥`.
  rcases gammaElementarySubgroupFiniteRepGrothendieckInduction_surjective
      (G := G) (L := Lexp) k (⊤ : IntermediateField ℚ Lexp) x with
    ⟨ι, hι, H, hHΓ, y, hx⟩
  refine ⟨ι, hι, H, ?_, y, hx⟩
  intro i
  -- The top-field specialization makes the Serre subgroup trivial, so the subgroup is ordinary
  -- elementary.
  exact
    (Subgroup.isGammaElementary_bot_iff_isElementary (G := G) (H i)).1 <|
      by simpa [gammaSubgroup_top_eq_bot (G := G)] using hHΓ i

end

section

open scoped FiniteProjectiveGrothendieckInduction

-- Proof sketch: the projective statement is identical to the ordinary one, using the projective
-- surjectivity theorem from Theorem `17-17.2-1`.
/-- Corollary 17-17.2-2 (2): if `K` is sufficiently large, every element of `P_k(G)` is a finite
sum of classes induced from elementary subgroups of `G`, where the summands lie in the
corresponding projective Grothendieck groups `P_k(H)`. Here `k = IsLocalRing.ResidueField A`. -/
theorem residueField_projectiveGrothendieckClass_exists_sum_of_elementary_subgroup_inductions
    (K : Type w) [Field K] [CharZero K] [Algebra A K] [IsFractionRing A K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : P₀[k](G)) :
    ∃ (ι : Type x) (_ : Fintype ι) (H : ι → Subgroup G)
      (hH : ∀ i, IsElementary (H i)),
        ∃ y : ∀ i, P₀[k](H i),
          x = ∑ i, (Ind[H i]) (y i) := by
  -- Route correction: reuse the same top-field specialization as in the ordinary Grothendieck
  -- case, now with the projective induction theorem.
  rcases gammaElementarySubgroupFiniteProjectiveRepGrothendieckInduction_surjective
      (G := G) (L := Lexp) k (⊤ : IntermediateField ℚ Lexp) x with
    ⟨ι, hι, H, hHΓ, y, hx⟩
  refine ⟨ι, hι, H, ?_, y, hx⟩
  intro i
  -- Again, the specialized arithmetic subgroup is trivial, so the subgroup is ordinary
  -- elementary.
  exact
    (Subgroup.isGammaElementary_bot_iff_isElementary (G := G) (H i)).1 <|
      by simpa [gammaSubgroup_top_eq_bot (G := G)] using hHΓ i

end

end ModularBrauerCorollary

end Representation
