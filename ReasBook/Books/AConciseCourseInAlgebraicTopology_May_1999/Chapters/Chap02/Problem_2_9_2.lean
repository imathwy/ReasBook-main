import Mathlib.Tactic.DeriveFintype
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.SingleRelatorVanKampen

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/-- The two standard generators in the usual presentation of the Klein bottle group. -/
inductive KleinBottleGenerator
  | a
  | b
deriving DecidableEq, Fintype

/-- The standard Klein-bottle relator `aba⁻¹b` in the free group on the two generators. -/
abbrev klein_bottle_relator : FreeGroup KleinBottleGenerator :=
  let a := FreeGroup.of KleinBottleGenerator.a
  let b := FreeGroup.of KleinBottleGenerator.b
  a * b * a⁻¹ * b

/-- The standard presentation of the Klein bottle group. -/
abbrev klein_bottle_group :=
  PresentedGroup ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))

/-- The canonical image of the first Klein-bottle generator in the presented group. -/
abbrev klein_bottle_group_a : klein_bottle_group :=
  PresentedGroup.of KleinBottleGenerator.a

/-- The canonical image of the second Klein-bottle generator in the presented group. -/
abbrev klein_bottle_group_b : klein_bottle_group :=
  PresentedGroup.of KleinBottleGenerator.b

/-- The defining relator is trivial in the presented Klein bottle group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `aba⁻¹b` becomes the identity in the quotient group.
theorem klein_bottle_group_relator_eq_one :
    PresentedGroup.mk ({klein_bottle_relator} : Set (FreeGroup KleinBottleGenerator))
      klein_bottle_relator =
        (1 : klein_bottle_group) := by
  exact PresentedGroup.one_of_mem (by simp)

/-- The canonical generators in the presented Klein bottle group satisfy the relator
`aba⁻¹b = 1`. -/
theorem klein_bottle_group_generators_relator_eq_one :
    klein_bottle_group_a * klein_bottle_group_b * klein_bottle_group_a⁻¹ * klein_bottle_group_b =
      (1 : klein_bottle_group) := by
  simpa [klein_bottle_group_a, klein_bottle_group_b, klein_bottle_relator] using
    klein_bottle_group_relator_eq_one

/-- Equivalently, the canonical generators satisfy `aba⁻¹ = b⁻¹`. -/
theorem klein_bottle_group_generators_conj_eq_inv :
    klein_bottle_group_a * klein_bottle_group_b * klein_bottle_group_a⁻¹ =
      klein_bottle_group_b⁻¹ := by
  have h :=
    congrArg (fun g : klein_bottle_group ↦ g * klein_bottle_group_b⁻¹)
      klein_bottle_group_generators_relator_eq_one
  simpa [mul_assoc] using h

variable {X : Type u} [TopologicalSpace X]

section

variable (U V : TopologicalSpace.Opens X) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable
  (pi1_U_equiv :
    FundamentalGroup U ⟨x, hxU⟩ ≃* FreeGroup KleinBottleGenerator)
  (pi1_inter_equiv :
    FundamentalGroup (U ⊓ V : TopologicalSpace.Opens X) ⟨x, ⟨hxU, hxV⟩⟩ ≃* FreeGroup Unit)
variable
  [PathConnectedSpace U]
  [PathConnectedSpace (U ⊓ V : TopologicalSpace.Opens X)]
  [SimplyConnectedSpace V]
variable
  (attaching_map_eq :
    (pi1_U_equiv.toMonoidHom.comp
        (fundamental_group_inf_to_left U V x hxU hxV)).comp
      pi1_inter_equiv.symm.toMonoidHom =
      FreeGroup.lift fun _ : Unit ↦ klein_bottle_relator)

/-- Problem 2.9.2: a based space admitting the standard Klein-bottle decomposition, equivalently
the quotient `(S^1 × I)/(z,0) ∼ (z⁻¹,1)`, has fundamental group
`⟨a, b ∣ aba⁻¹b = 1⟩`, equivalently `⟨a, b ∣ aba⁻¹ = b⁻¹⟩`. -/
-- Proof sketch: apply the two-open-set van Kampen theorem to the decomposition `X = U ∪ V`.
-- Because `V` is simply connected, the resulting pushout identifies `π₁(X,x)` with the quotient
-- of `π₁(U,x)` by the normal closure of the image of `π₁(U ∩ V,x)`. Transport this quotient
-- through `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify the killed
-- subgroup with the normal closure of the single relator `aba⁻¹b`.
def klein_bottle_fundamental_group :
    FundamentalGroup X x ≃* klein_bottle_group :=
  fundamental_group_left_to_union_single_relator_presented_group_equiv
    U V hcover x hxU hxV pi1_U_equiv pi1_inter_equiv klein_bottle_relator
    attaching_map_eq

end
