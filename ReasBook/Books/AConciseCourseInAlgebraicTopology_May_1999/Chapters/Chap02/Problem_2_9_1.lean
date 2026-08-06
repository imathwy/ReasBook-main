import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.DeriveFintype
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.SingleRelatorVanKampen

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped commutatorElement

noncomputable section

/-- The four standard generators in the usual presentation of the genus-2 surface group. -/
inductive GenusTwoSurfaceGenerator
  | a1
  | b1
  | a2
  | b2
deriving DecidableEq, Fintype

/-- The standard relator `[a1,b1][a2,b2]` in the free group on the genus-2 generators. -/
abbrev genus_two_surface_relator : FreeGroup GenusTwoSurfaceGenerator :=
  let a1 := FreeGroup.of GenusTwoSurfaceGenerator.a1
  let b1 := FreeGroup.of GenusTwoSurfaceGenerator.b1
  let a2 := FreeGroup.of GenusTwoSurfaceGenerator.a2
  let b2 := FreeGroup.of GenusTwoSurfaceGenerator.b2
  ⁅a1, b1⁆ * ⁅a2, b2⁆

/-- The standard presentation of the genus-2 surface group. -/
abbrev genus_two_surface_group :=
  PresentedGroup ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))

/-- The canonical image of `a1` in the presented genus-2 surface group. -/
abbrev genus_two_surface_group_a1 : genus_two_surface_group :=
  PresentedGroup.of GenusTwoSurfaceGenerator.a1

/-- The canonical image of `b1` in the presented genus-2 surface group. -/
abbrev genus_two_surface_group_b1 : genus_two_surface_group :=
  PresentedGroup.of GenusTwoSurfaceGenerator.b1

/-- The canonical image of `a2` in the presented genus-2 surface group. -/
abbrev genus_two_surface_group_a2 : genus_two_surface_group :=
  PresentedGroup.of GenusTwoSurfaceGenerator.a2

/-- The canonical image of `b2` in the presented genus-2 surface group. -/
abbrev genus_two_surface_group_b2 : genus_two_surface_group :=
  PresentedGroup.of GenusTwoSurfaceGenerator.b2

/-- The defining relator is trivial in the presented genus-2 surface group. -/
-- Proof sketch: `PresentedGroup.mk` kills every element of the chosen relation set, so the unique
-- relator `[a1,b1][a2,b2]` becomes the identity in the quotient group.
theorem genus_two_surface_group_relator_eq_one :
    PresentedGroup.mk ({genus_two_surface_relator} : Set (FreeGroup GenusTwoSurfaceGenerator))
      genus_two_surface_relator =
        (1 : genus_two_surface_group) := by
  exact PresentedGroup.one_of_mem (by simp)

/-- The canonical generators in the presented genus-2 surface group satisfy the relator
`[a1,b1][a2,b2] = 1`. -/
theorem genus_two_surface_group_generators_relator_eq_one :
    ⁅genus_two_surface_group_a1, genus_two_surface_group_b1⁆ *
        ⁅genus_two_surface_group_a2, genus_two_surface_group_b2⁆ =
      (1 : genus_two_surface_group) := by
  simpa [genus_two_surface_group_a1, genus_two_surface_group_b1, genus_two_surface_group_a2,
    genus_two_surface_group_b2, genus_two_surface_relator] using
    genus_two_surface_group_relator_eq_one

variable {X : Type u} [TopologicalSpace X]

section

variable (U V : TopologicalSpace.Opens X) (hcover : U ⊔ V = ⊤)
variable (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
variable
  (pi1_U_equiv :
    FundamentalGroup U ⟨x, hxU⟩ ≃* FreeGroup GenusTwoSurfaceGenerator)
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
      FreeGroup.lift fun _ : Unit ↦ genus_two_surface_relator)

/-- Problem 2.9.1: a based space admitting the standard genus-2 cell decomposition, equivalently
the compact surface obtained by sewing two punctured tori along their boundary circle, has
fundamental group the presented group `⟨a1, b1, a2, b2 | [a1,b1][a2,b2] = 1⟩`. -/
-- Proof sketch: apply Proposition 2.8.6 to the open cover `X = U ∪ V`. Since `V` is simply
-- connected, that proposition identifies `π₁(X, x)` with the quotient of `π₁(U, x)` by the normal
-- closure of the image of `π₁(U ∩ V, x)`. Transport the quotient through the free-group
-- identifications in `pi1_U_equiv` and `pi1_inter_equiv`, then use `attaching_map_eq` to identify
-- the killed subgroup with the normal closure of the relator `[a1,b1][a2,b2]`.
def genus_two_surface_fundamental_group
    : FundamentalGroup X x ≃* genus_two_surface_group :=
  fundamental_group_left_to_union_single_relator_presented_group_equiv
    U V hcover x hxU hxV pi1_U_equiv pi1_inter_equiv genus_two_surface_relator
    attaching_map_eq

end
