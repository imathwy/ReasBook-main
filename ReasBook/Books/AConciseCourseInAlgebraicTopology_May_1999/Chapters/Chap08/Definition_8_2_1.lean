import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4

open CategoryTheory
open scoped unitInterval

-- The chapter already provides `smashProduct` for based topological spaces, but the reduced cone
-- here is recorded in `PointedCompactlyGenerated`. We therefore model `X ∧ I` directly as the
-- quotient of `X × I` collapsing `X × {1}` and `{x₀} × I`, and then use the canonical quotient
-- topology and inherited compactly generated structure on that quotient.

universe u w

/-- The unit interval `I`, regarded as a based compactly generated space with basepoint `1`. -/
abbrev basedInterval : PointedCompactlyGenerated :=
  PointedCompactlyGenerated.of (CompactlyGenerated.of I) (1 : I)

/-- The chosen basepoint of `basedInterval` is the endpoint `1 : I`. -/
@[simp] theorem basedInterval_point :
    basedInterval.point = (1 : I) := by
  rfl

/-- Passing from pointed compactly generated spaces to based spaces preserves the chosen
basepoint. -/
@[simp] theorem underTopBasepointU_toBasedSpace (X : PointedCompactlyGenerated.{u, w}) :
    underTopBasepoint X.toBasedSpace = X.point := by
  rfl

/-- The interval `I` based at `1` keeps the endpoint `1` as its basepoint after passing to based
spaces. -/
@[simp] private theorem underTopBasepointU_basedInterval_toBasedSpace :
    underTopBasepoint basedInterval.toBasedSpace = (1 : I) := by
  rfl

/-- For the cone smash product `X ∧ I`, the distinguished wedge pair is `(X.point, 1)`. -/
@[simp] private theorem smashProductBasepointPair_cone (X : PointedCompactlyGenerated.{u, w}) :
    smashProductBasepointPair X.toBasedSpace basedInterval.toBasedSpace = (X.point, (1 : I)) := by
  rfl

/-- The subset of `X × I` collapsed to the basepoint in the reduced-cone model. -/
def reducedConeCollapsedSet (X : PointedCompactlyGenerated.{u, w}) :
    Set (X.toCompactlyGenerated × I) :=
  { p | p.1 = X.point ∨ p.2 = (1 : I) }

/-- The reduced-cone relation used to model the quotient `CX = X ∧ I`. -/
def reducedConeRel (X : PointedCompactlyGenerated.{u, w}) :
    X.toCompactlyGenerated × I → X.toCompactlyGenerated × I → Prop :=
  fun p q ↦ p = q ∨ (p ∈ reducedConeCollapsedSet X ∧ q ∈ reducedConeCollapsedSet X)

/-- `reducedConeRel X` identifies equal points and collapses `X × {1} ∪ {X.point} × I` to one
class. -/
theorem reducedConeRel_iff
    (X : PointedCompactlyGenerated.{u, w}) (p q : X.toCompactlyGenerated × I) :
    reducedConeRel X p q ↔
      p = q ∨ (p ∈ reducedConeCollapsedSet X ∧ q ∈ reducedConeCollapsedSet X) := by
  rfl

/-- Reflexivity of `reducedConeRel`. -/
theorem reducedConeRel_refl
    (X : PointedCompactlyGenerated.{u, w}) (p : X.toCompactlyGenerated × I) :
    reducedConeRel X p p := by
  exact Or.inl rfl

/-- Symmetry of `reducedConeRel`. -/
theorem reducedConeRel_symm
    (X : PointedCompactlyGenerated.{u, w}) {p q : X.toCompactlyGenerated × I}
    (h : reducedConeRel X p q) :
    reducedConeRel X q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr ⟨h.2, h.1⟩

/-- Transitivity of `reducedConeRel`. -/
theorem reducedConeRel_trans
    (X : PointedCompactlyGenerated.{u, w}) {p q r : X.toCompactlyGenerated × I}
    (hpq : reducedConeRel X p q) (hqr : reducedConeRel X q r) :
    reducedConeRel X p r := by
  rcases hpq with rfl | ⟨hp, hq⟩
  · exact hqr
  rcases hqr with rfl | ⟨_, hr⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hr⟩

/-- The setoid presenting the quotient model of the reduced cone. -/
def reducedConeSetoid (X : PointedCompactlyGenerated.{u, w}) :
    Setoid (X.toCompactlyGenerated × I) where
  r := reducedConeRel X
  iseqv := ⟨
    reducedConeRel_refl X,
    fun {_ _} ↦ reducedConeRel_symm X,
    fun {_ _ _} ↦ reducedConeRel_trans X⟩

/-- The reduced-cone quotient underlying `reducedCone X`. -/
abbrev reducedConeType (X : PointedCompactlyGenerated.{u, w}) :=
  Quotient (reducedConeSetoid X)

/-- The quotient topology on `reducedConeType X` before applying compact generation. -/
abbrev reducedConeTypeQuotTopologicalSpace (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedConeType X) :=
  inferInstance

/-- The compactly generated replacement of the quotient topology on `reducedConeType X`. -/
abbrev reducedConeTypeKTopologicalSpace (X : PointedCompactlyGenerated.{u, w}) :
    TopologicalSpace (reducedConeType X) :=
  let _ : TopologicalSpace (reducedConeType X) := reducedConeTypeQuotTopologicalSpace X
  TopologicalSpace.compactlyGenerated.{u, w} (reducedConeType X)

section ReducedConeKification

variable (X : PointedCompactlyGenerated.{u, w})

local instance reducedConeTypeTopologicalSpace :
    TopologicalSpace (reducedConeType X) :=
  reducedConeTypeKTopologicalSpace X

local instance reducedConeTypeUCompactlyGeneratedSpace :
    UCompactlyGeneratedSpace.{u} (reducedConeType X) := by
  sorry

/-- The quotient map `X × I → CX` for the reduced-cone model. -/
abbrev reducedConeMk (X : PointedCompactlyGenerated.{u, w}) (p : X.toCompactlyGenerated × I) :
    reducedConeType X :=
  Quotient.mk'' p

/-- The reduced-cone basepoint is the class of `(X.point, 1)`. -/
def reducedConePoint (X : PointedCompactlyGenerated.{u, w}) : reducedConeType X :=
  reducedConeMk X (X.point, (1 : I))

/-- Definition 8.2.1. The reduced cone on a based space `X` is the quotient of `X × I` obtained
by collapsing `X × {1}` and `{X.point} × I` to the distinguished basepoint. This is the
source-faithful realization of `CX = X ∧ I`, where `I` is based at `1`. -/
def reducedCone (X : PointedCompactlyGenerated.{u, w}) : PointedCompactlyGenerated :=
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (reducedConeType X))
    (reducedConePoint X)

prefix:max "C " => reducedCone

/-- The reduced cone is the based compactly generated quotient of `X × I` by
`reducedConeSetoid X`. -/
theorem reducedCone_def (X : PointedCompactlyGenerated.{u, w}) :
    C X =
      PointedCompactlyGenerated.of
        (CompactlyGenerated.of (reducedConeType X))
        (reducedConePoint X) := by
  rfl

/-- The collapse locus for `C X` is exactly the wedge locus for the smash-product presentation
`X ∧ I`, with `I` based at `1`. -/
theorem mem_reducedConeCollapsedSet_iff (X : PointedCompactlyGenerated.{u, w})
    (p : X.toCompactlyGenerated × I) :
    p ∈ reducedConeCollapsedSet X ↔
      smashWedge X.toBasedSpace basedInterval.toBasedSpace p := by
  rfl

/-- The chosen basepoint of `C X` is `reducedConePoint X`. -/
@[simp] theorem reducedCone_point (X : PointedCompactlyGenerated.{u, w}) :
    (C X).point = reducedConePoint X := by
  rfl

/-- Any two points in the collapsed subset represent the same point of `C X`. -/
theorem reducedConeMk_eq_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p q : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedConeCollapsedSet X) (hq : q ∈ reducedConeCollapsedSet X) :
    reducedConeMk X p = reducedConeMk X q := by
  exact Quotient.sound (Or.inr ⟨hp, hq⟩)

/-- Any point of the collapsed subset represents the distinguished basepoint of `C X`. -/
theorem reducedConeMk_eq_point_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedConeCollapsedSet X) :
    reducedConeMk X p = (C X).point := by
  have hpoint : (X.point, (1 : I)) ∈ reducedConeCollapsedSet X := by
    left
    rfl
  simpa [reducedConePoint] using reducedConeMk_eq_of_memCollapsedSet X hp hpoint

/-- Any point of `{X.point} × I` represents the basepoint of `C X`. -/
@[simp] theorem reducedCone_mk_eq_point_of_fst_eq_point
    (X : PointedCompactlyGenerated.{u, w}) (t : I) :
    reducedConeMk X (X.point, t) = (C X).point := by
  have hp : (X.point, t) ∈ reducedConeCollapsedSet X := by
    left
    rfl
  exact reducedConeMk_eq_point_of_memCollapsedSet X hp

/-- Any point of `X × {1}` represents the basepoint of `C X`. -/
@[simp] theorem reducedCone_mk_eq_point_of_snd_eq_one
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) :
    reducedConeMk X (x, (1 : I)) = (C X).point := by
  have hp : (x, (1 : I)) ∈ reducedConeCollapsedSet X := by
    right
    rfl
  exact reducedConeMk_eq_point_of_memCollapsedSet X hp

/-- The raw representative map from the quotient model of `C X` to the smash-product presentation
`X ∧ I`, with `I` based at `1`. -/
private noncomputable def reducedConeToSmashProductRaw (X : PointedCompactlyGenerated.{u, w}) :
    X.toCompactlyGenerated × I →
      (smashProduct X.toBasedSpace basedInterval.toBasedSpace).right
  | p => smashProductMk X.toBasedSpace basedInterval.toBasedSpace p

/-- The raw map to `X ∧ I` is constant on the collapsed subset defining `C X`. -/
private theorem reducedConeToSmashProductRaw_eq_basepoint_of_memCollapsedSet
    (X : PointedCompactlyGenerated.{u, w}) {p : X.toCompactlyGenerated × I}
    (hp : p ∈ reducedConeCollapsedSet X) :
    reducedConeToSmashProductRaw X p =
      smashProductMk X.toBasedSpace basedInterval.toBasedSpace (X.point, (1 : I)) := by
  calc
    reducedConeToSmashProductRaw X p =
        (show smashProductType X.toBasedSpace basedInterval.toBasedSpace from
          underTopBasepoint (smashProduct X.toBasedSpace basedInterval.toBasedSpace)) := by
      exact smashProduct_mk_eq_basepoint_of_mem_smashWedge
        X.toBasedSpace basedInterval.toBasedSpace
        ((mem_reducedConeCollapsedSet_iff X p).1 hp)
    _ = smashProductMk X.toBasedSpace basedInterval.toBasedSpace (X.point, (1 : I)) := by
      exact congrArg
        (smashProductMk X.toBasedSpace basedInterval.toBasedSpace)
        (smashProductBasepointPair_cone X)

/-- The smash-product representative map respects the cone quotient relation. -/
private theorem reducedConeToSmashProductRaw_respects
    (X : PointedCompactlyGenerated.{u, w}) :
    ∀ ⦃p q : X.toCompactlyGenerated × I⦄,
      reducedConeRel X p q →
        reducedConeToSmashProductRaw X p = reducedConeToSmashProductRaw X q := by
  intro p q h
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · exact (reducedConeToSmashProductRaw_eq_basepoint_of_memCollapsedSet X hp).trans
      (reducedConeToSmashProductRaw_eq_basepoint_of_memCollapsedSet X hq).symm

/-- The raw representative map from `X × I` to the quotient model `C X`. -/
private noncomputable def smashProductToReducedConeRaw (X : PointedCompactlyGenerated.{u, w}) :
    X.toBasedSpace.right × basedInterval.toBasedSpace.right → reducedConeType X
  | p => reducedConeMk X p

/-- The representative map from `X × I` to `C X` respects the smash-product relation. -/
private theorem smashProductToReducedConeRaw_respects
    (X : PointedCompactlyGenerated.{u, w}) :
    ∀ ⦃p q : X.toBasedSpace.right × basedInterval.toBasedSpace.right⦄,
      smashProductRel X.toBasedSpace basedInterval.toBasedSpace p q →
        smashProductToReducedConeRaw X p = smashProductToReducedConeRaw X q := by
  intro p q h
  rw [smashProductRel_iff X.toBasedSpace basedInterval.toBasedSpace p q] at h
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · exact reducedConeMk_eq_of_memCollapsedSet X
      ((mem_reducedConeCollapsedSet_iff X p).2 hp)
      ((mem_reducedConeCollapsedSet_iff X q).2 hq)

/-- The quotient model `C X` is canonically homeomorphic to the smash product `X ∧ I`, with `I`
based at `1`. -/
noncomputable def reducedConeSmashProductHomeomorph (X : PointedCompactlyGenerated.{u, w}) :
    (C X).toBasedSpace.right ≃ₜ
      (smashProduct X.toBasedSpace basedInterval.toBasedSpace).right where
  toEquiv :=
    { toFun :=
        show reducedConeType X →
            (smashProduct X.toBasedSpace basedInterval.toBasedSpace).right from
          Quotient.lift
            (reducedConeToSmashProductRaw X)
            (fun _ _ h ↦ reducedConeToSmashProductRaw_respects X h)
      invFun :=
        show (smashProduct X.toBasedSpace basedInterval.toBasedSpace).right →
            reducedConeType X from
          Quotient.lift
            (smashProductToReducedConeRaw X)
            (fun _ _ h ↦ smashProductToReducedConeRaw_respects X h)
      left_inv := sorry
      right_inv := sorry }
  continuous_toFun := sorry
  continuous_invFun := sorry

/-- On representatives, `reducedConeSmashProductHomeomorph` sends `[(x, t)]` in `C X` to the
smash-product class of `(x, t)` in `X ∧ I`. -/
@[simp] theorem reducedConeSmashProductHomeomorph_apply_mk
    (X : PointedCompactlyGenerated.{u, w}) (x : X.toCompactlyGenerated) (t : I) :
    reducedConeSmashProductHomeomorph X (reducedConeMk X (x, t)) =
      smashProductMk X.toBasedSpace basedInterval.toBasedSpace (x, t) := by
  rfl

/-- The homeomorphism identifying `C X` with `X ∧ I` preserves the distinguished basepoint. -/
@[simp] theorem reducedConeSmashProductHomeomorph_basepoint
    (X : PointedCompactlyGenerated.{u, w}) :
    reducedConeSmashProductHomeomorph X (reducedConePoint X) =
      smashProductMk X.toBasedSpace basedInterval.toBasedSpace (X.point, (1 : I)) := by
  rfl

/-- The topological isomorphism underlying the cone-smash identification preserves the structure
map from the one-point space. -/
theorem reducedConeIsoSmashProduct_w (X : PointedCompactlyGenerated.{u, w}) :
    (reducedCone X).toBasedSpace.hom ≫
        (TopCat.isoOfHomeo (reducedConeSmashProductHomeomorph X)).hom =
      (smashProduct X.toBasedSpace basedInterval.toBasedSpace).hom := by
  ext x
  simpa using reducedConeSmashProductHomeomorph_basepoint X

/-- Definition 8.2.1, equivalently: the based-space realization of `C X` is canonically
identified with the smash product `X ∧ I`, with `I` based at `1`. -/
noncomputable def reducedConeIsoSmashProduct (X : PointedCompactlyGenerated.{u, w}) :
    (reducedCone X).toBasedSpace ≅ smashProduct X.toBasedSpace basedInterval.toBasedSpace :=
  CategoryTheory.Under.isoMk
    (TopCat.isoOfHomeo (reducedConeSmashProductHomeomorph X))
    (reducedConeIsoSmashProduct_w X)

/-- The forward morphism of `reducedConeIsoSmashProduct` is induced by
`reducedConeSmashProductHomeomorph`. -/
theorem reducedConeIsoSmashProduct_hom_right (X : PointedCompactlyGenerated.{u, w}) :
    (reducedConeIsoSmashProduct X).hom.right =
      (TopCat.isoOfHomeo (reducedConeSmashProductHomeomorph X)).hom := by
  rfl

end ReducedConeKification
