module

public import Topology_Munkres_2000.Book.Theorem_81_2.Comparison
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

universe u v

namespace CoveringTransformation

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [SimplyConnectedSpace E] [PathConnectedSpace B]
variable [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
omit [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    [LocallyPathConnectedSpace B] in
/-- Helper for Corollary 81.4: the covering subgroup of a simply connected covering space is
trivial. -/
private lemma fundamentalGroupMapRange_eq_bot (hp : IsCoveringMap p)
    {e₀ : E} {b₀ : B} (he₀ : p e₀ = b₀) :
    hp.fundamentalGroupMapRange he₀ = ⊥ := by
  -- Every loop class upstairs is the identity, so its image is also the identity.
  rw [IsCoveringMap.fundamentalGroupMapRange, MonoidHom.range_eq_bot_iff]
  apply MonoidHom.ext
  intro γ
  have hγ : γ = 1 := Subsingleton.elim _ _
  rw [hγ]
  exact map_one _

omit [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    [LocallyPathConnectedSpace B] in
/-- Helper for Corollary 81.4: the inclusion of the normalizer of the covering subgroup is
surjective when the covering space is simply connected. -/
private lemma normalizerSubgroupSubtype_surjective (hp : IsCoveringMap p)
    {e₀ : E} {b₀ : B} (he₀ : p e₀ = b₀) :
    Function.Surjective (normalizerSubgroup hp he₀).subtype := by
  -- The covering subgroup is bottom, whose normalizer is the whole fundamental group.
  rw [← MonoidHom.range_eq_top, Subgroup.range_subtype]
  unfold normalizerSubgroup
  rw [fundamentalGroupMapRange_eq_bot hp he₀]
  exact Subgroup.normalizer_eq_top
    (H := (⊥ : Subgroup (FundamentalGroup B b₀)))

omit [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    [LocallyPathConnectedSpace B] in
/-- Helper for Corollary 81.4: inside the normalizer, the covering subgroup is exactly the
kernel of the inclusion into the ambient fundamental group. -/
private lemma normalizerQuotientSubgroup_eq_ker_subtype (hp : IsCoveringMap p)
    {e₀ : E} {b₀ : B} (he₀ : p e₀ = b₀) :
    (hp.fundamentalGroupMapRange he₀).subgroupOf (normalizerSubgroup hp he₀) =
      (normalizerSubgroup hp he₀).subtype.ker := by
  -- Both sides reduce to the bottom subgroup after trivializing the covering subgroup.
  rw [fundamentalGroupMapRange_eq_bot hp he₀, Subgroup.bot_subgroupOf,
    Subgroup.ker_subtype]

/-- Helper for Corollary 81.4: a simply connected covering space's normalizer quotient maps
canonically to the fundamental group by forgetting that a representative lies in the
normalizer. -/
noncomputable def normalizerQuotientFundamentalGroupHom (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    normalizerQuotient hp he₀ →* FundamentalGroup B b₀ :=
  -- Descend the canonical subgroup inclusion through its kernel quotient.
  QuotientGroup.lift
    ((hp.fundamentalGroupMapRange he₀).subgroupOf (normalizerSubgroup hp he₀))
    (normalizerSubgroup hp he₀).subtype
    (normalizerQuotientSubgroup_eq_ker_subtype hp he₀).le

/-- Helper for Corollary 81.4: the canonical homomorphism from the normalizer quotient to the
base fundamental group is bijective. -/
private lemma normalizerQuotientFundamentalGroupHom_bijective (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Function.Bijective (normalizerQuotientFundamentalGroupHom hp e₀ b₀ he₀) := by
  constructor
  · -- The quotient kills exactly the kernel of the normalizer inclusion.
    rw [normalizerQuotientFundamentalGroupHom, QuotientGroup.injective_lift_iff]
    exact normalizerQuotientSubgroup_eq_ker_subtype hp he₀
  · -- Surjectivity descends from the inclusion of the full normalizer.
    exact QuotientGroup.lift_surjective_of_surjective
      ((hp.fundamentalGroupMapRange he₀).subgroupOf (normalizerSubgroup hp he₀))
      (normalizerSubgroup hp he₀).subtype
      (normalizerSubgroupSubtype_surjective hp he₀)
      (normalizerQuotientSubgroup_eq_ker_subtype hp he₀).le

/-- Corollary 81.4: the canonical homomorphism from covering transformations to the
fundamental group of the base. -/
noncomputable def fundamentalGroupComparison (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    group p →* FundamentalGroup B b₀ :=
  (normalizerQuotientFundamentalGroupHom hp e₀ b₀ he₀).comp
    (normalizerQuotientComparison hp e₀ b₀ he₀)

/-- The canonical comparison from covering transformations to the fundamental group is
bijective. -/
theorem fundamentalGroupComparison_bijective (hp : IsCoveringMap p)
    (e₀ : E) (b₀ : B) (he₀ : p e₀ = b₀) :
    Function.Bijective (fundamentalGroupComparison hp e₀ b₀ he₀) := by
  -- Compose the quotient comparison from Theorem 81.2 with the canonical quotient lift.
  exact (normalizerQuotientFundamentalGroupHom_bijective hp e₀ b₀ he₀).comp
    (normalizerQuotientComparison_bijective hp e₀ b₀ he₀)

end CoveringTransformation
