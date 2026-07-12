import StacksProject_2024.Chap34.Definition_34_9_13
import StacksProject_2024.Chap34.Definition_34_10_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v

namespace AlgebraicGeometry

variable (F : Schemeᵒᵖ ⥤ Type v)

/- Semantic recall for this item:
Chapter 34 already owns the fixed-family sheaf condition as
`satisfiesSheafPropertyForFamily`. Together with the local cover predicate `IsVCovering`, the
`V`-topology clause is therefore best formalized by requiring that every `V` covering family
satisfies that fixed-family sheaf condition. -/

/-- Definition 34.10.11: a contravariant set-valued functor on schemes satisfies the sheaf
property for the `V` topology if it satisfies the sheaf property for every `V` covering family. -/
@[stacks 0ETL]
def satisfiesVSheafProperty : Prop :=
  ∀ {ι : Type w} {T : Scheme} (U : ι → Scheme) (f : ∀ i, U i ⟶ T),
    IsVCovering T U f → satisfiesSheafPropertyForFamily F U f

/-- A functor satisfying the `V`-sheaf property satisfies the canonical fixed-family sheaf
condition for each `V` covering family. -/
theorem satisfiesVSheafProperty.isSheafFor
    (hF : satisfiesVSheafProperty.{w, _} F)
    {ι : Type w} {T : Scheme} (U : ι → Scheme) (f : ∀ i, U i ⟶ T)
    (hcover : IsVCovering T U f) :
    satisfiesSheafPropertyForFamily F U f :=
  hF U f hcover

/-- Unfolding lemma for `satisfiesVSheafProperty`. -/
theorem satisfiesVSheafProperty_iff :
  satisfiesVSheafProperty.{w, _} F ↔
      ∀ {ι : Type w} {T : Scheme} (U : ι → Scheme) (f : ∀ i, U i ⟶ T),
        IsVCovering T U f → satisfiesSheafPropertyForFamily F U f :=
  Iff.rfl

end AlgebraicGeometry
