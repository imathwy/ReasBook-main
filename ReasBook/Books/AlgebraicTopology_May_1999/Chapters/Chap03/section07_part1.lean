import Mathlib
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_3_7_1 (from Chap03) -/
open scoped FundamentalGroup

universe u v w

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsCoveringMap

variable {p : E → B} [PathConnectedSpace X] [LocPathConnectedSpace X]

/- Theorem 3.7.1: the covering-space lifting criterion is the canonical mathlib theorem
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`. -/
recall IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
    {E : Type u} {X : Type v} {A : Type w}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A] {p : E → X}
    (cov : IsCoveringMap p) [PathConnectedSpace A] [LocPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (le :
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f

end IsCoveringMap

/-! ### ProofStep_3_7_2 (from Chap03) -/
universe u v w

open CategoryTheory FundamentalGroupoid
open CategoryTheory.Functor.IsCovering
open CategoryTheory.Groupoid.CategoryTheory

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsPathConnectedCoveringMap

variable {p : E → B} [PathConnectedSpace X]

/-- ProofStep 3.7.2: applying the covering-groupoid lifting criterion to the induced covering
functor `hp.fundamentalGroupoidMap : Π(E) ⥤ Π(B)` reduces the covering-space lifting problem for
`f : X → B` to the
corresponding existence and uniqueness statement for a lift of `Π(f)`. -/
-- Proof sketch: Proposition 3.3.4 shows that `Π(p)` is a covering functor. Then Theorem 3.5.1
-- applies directly to the functor `Π(f) : Π(X) ⥤ Π(B)` and the chosen object `e₀` of the fiber of
-- `Π(p)` over `Π(f)(x)`.
theorem existsUnique_fundamentalGroupoidLift_iff_mapVertexGroup_range_le
    (hp : IsPathConnectedCoveringMap p) (f : C(X, B)) (x : X)
    (e₀ : hp.fundamentalGroupoidMap.Fiber ((FundamentalGroupoid.map f).obj (mk x))) :
    (∃! g : FundamentalGroupoid X ⥤ FundamentalGroupoid E,
      g ⋙ hp.fundamentalGroupoidMap = FundamentalGroupoid.map f ∧
        g.obj (mk x) = e₀.1) ↔
      (CategoryTheory.Functor.mapVertexGroup (FundamentalGroupoid.map f) (mk x)).range ≤
        e₀.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap e₀.1).range := by
  letI : CategoryTheory.IsConnected (FundamentalGroupoid X) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  simpa using
    existsUnique_lift_iff_mapVertexGroup_range_le hp.fundamentalGroupoidMap_isCovering (mk x) e₀

end IsPathConnectedCoveringMap

/-! ### ProofStep_3_7_3 (from Chap03) -/
universe u v w

variable {E : Type u} {B : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]

namespace IsFundamentalNeighborhood

variable {p : E → B} {f : C(X, B)} {g : X → E} {x : X} {V : Set B}

/-- ProofStep 3.7.3: a set-theoretic lift is continuous at `x` once, on some neighborhood of `x`,
it stays in a single inverse-image sheet over a fundamental neighborhood of `f x`. -/
-- Proof sketch: on the neighborhood `U`, the chosen sheet homeomorphism identifies the restricted
-- lift with the map `y ↦ (f y, e₀)` into `V × p⁻¹' {f x}`. This map is continuous, so composing
-- with the inverse homeomorphism gives continuity of the restricted lift, hence continuity of `g`
-- at `x`.
theorem continuousAt_of_locally_landing_in_inverseImageSheet
    {H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({f x} : Set B))}
    (hH : ∀ e, (H e).1.1 = p e)
    (hg : p ∘ g = f)
    {U : Set X} (hxU : x ∈ U) (hU : IsOpen U) (hgU : U ⊆ g ⁻¹' (p ⁻¹' V))
    (e₀ : p ⁻¹' ({f x} : Set B))
    (hsheet : ∀ y : U, (H ⟨g y.1, hgU y.2⟩).2 = e₀) :
    ContinuousAt g x := by
  have hbase : ∀ y : U, f y.1 ∈ V := by
    intro y
    have hyV : p (g y.1) ∈ V := hgU y.2
    rw [show p (g y.1) = f y.1 by simpa using congrFun hg y.1] at hyV
    exact hyV
  let gU : U → E := fun y ↦ H.symm ((⟨f y.1, hbase y⟩ : V), e₀)
  have hgU_eq : U.restrict g = gU := by
    funext y
    have hy : (⟨g y.1, hgU y.2⟩ : p ⁻¹' V) = H.symm ((⟨f y.1, hbase y⟩ : V), e₀) := by
      apply H.injective
      apply Prod.ext
      · apply Subtype.ext
        simpa using (hH ⟨g y.1, hgU y.2⟩).trans (congrFun hg y.1)
      · exact (hsheet y).trans <| by
          exact (congrArg Prod.snd (H.right_inv ((⟨f y.1, hbase y⟩ : V), e₀))).symm
    change g y.1 = gU y
    simpa [gU] using congrArg Subtype.val hy
  have hgU_cont : Continuous gU := by
    have hfirst : Continuous (fun y : U ↦ (⟨f y.1, hbase y⟩ : V)) :=
      (f.continuous.comp continuous_subtype_val).subtype_mk hbase
    have hsymm : Continuous H.symm := H.symm.continuous
    exact continuous_subtype_val.comp <|
      hsymm.comp (hfirst.prodMk continuous_const)
  have hcont_restrict : ContinuousAt (U.restrict g) ⟨x, hxU⟩ := by
    simpa [hgU_eq] using hgU_cont.continuousAt
  have hwithin : ContinuousWithinAt g U x :=
    (continuousWithinAt_iff_continuousAt_restrict g hxU).2 hcont_restrict
  exact hwithin.continuousAt (hU.mem_nhds hxU)

end IsFundamentalNeighborhood

/-! ### Definition_3_7_4 (from Chap03) -/
open CategoryTheory

universe u v

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  (p : C(E, B)) (p' : C(E', B))

/- Definition 3.7.4: a map of covering spaces over `B`, from `p : C(E, B)` to `p' : C(E', B)`,
is a morphism in the over-category `Over (TopCat.of B)`. Equivalently, it is a
continuous map `g : C(E, E')` such that `p' ∘ g = p`. -/
#check (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))

section OverApi

variable {T : Type u} [Category.{v} T] {X Y : T}

/- An object of an over-category is given by a morphism with codomain `X`. -/
recall Over.mk (f : Y ⟶ X) : Over X

/- Equivalently, a morphism in an over-category is built from a commutative triangle. -/
recall Over.homMk {U V : Over X} (g : U.left ⟶ V.left)
    (hg : g ≫ V.hom = U.hom) : U ⟶ V

/- Every morphism in the over-category satisfies the defining commutative-triangle relation. -/
recall Over.w {U V : Over X} (g : U ⟶ V) : g.left ≫ V.hom = U.hom

end OverApi

/-! ### Lemma_3_7_5 (from Chap03) -/
open CategoryTheory

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [ConnectedSpace E] [ConnectedSpace E'] [ConnectedSpace B]
  [LocPathConnectedSpace E] [LocPathConnectedSpace E'] [LocPathConnectedSpace B]

/-- Helper for Lemma 3.7.5: a morphism of covering spaces over `B` preserves the base projection
pointwise. -/
-- Evaluating the commutative triangle `Over.w h` at a point of the total space recovers the
-- defining relation `p' ∘ h.left = p`.
private theorem covering_space_hom_comm
    {p : C(E, B)} {p' : C(E', B)}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (x : E) :
    p' (h.left.hom x) = p x := by
  have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
  simpa [ContinuousMap.comp_apply] using hx

/-- Helper for Lemma 3.7.5: a smaller open path-connected neighborhood inside a fundamental
neighborhood is again fundamental. -/
-- We restrict the given local trivialization from `U` to `V` by first rewriting the relevant
-- source as a subtype of `p ⁻¹' U`, then restricting the homeomorphism, and finally re-associating
-- the codomain as `V × (p ⁻¹' {b})`.
private theorem fundamental_neighborhood_restrict {p : E → B} {b : B} {U V : Set B}
    (hU : IsFundamentalNeighborhood p b U) (hVU : V ⊆ U) (hbV : b ∈ V)
    (hVOpen : IsOpen V) (hVPath : IsPathConnected V) :
    IsFundamentalNeighborhood p b V := by
  rcases hU with ⟨hdisc, hbU, hUOpen, hUPath, hpreUOpen, H, hH⟩
  let e₀ : p ⁻¹' V ≃ₜ { x : p ⁻¹' U // p x.1 ∈ V } :=
    { toFun := fun x ↦ ⟨⟨x.1, hVU x.2⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        cases x
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let e₁ :
      { x : p ⁻¹' U // p x.1 ∈ V } ≃ₜ
        { y : U × (p ⁻¹' ({b} : Set B)) // y.1.1 ∈ V } :=
    H.subtype fun x ↦ by
      simpa [hH x]
  let e₂ :
      { y : U × (p ⁻¹' ({b} : Set B)) // y.1.1 ∈ V } ≃ₜ
        V × (p ⁻¹' ({b} : Set B)) :=
    { toFun := fun y ↦ (⟨y.1.1.1, y.2⟩, y.1.2)
      invFun := fun y ↦ ⟨((⟨y.1.1, hVU y.1.2⟩ : U), y.2), y.1.2⟩
      left_inv := by
        intro y
        cases y
        rfl
      right_inv := by
        intro y
        cases y
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  refine ⟨hdisc, hbV, hVOpen, hVPath, ?_, e₀.trans (e₁.trans e₂), ?_⟩
  · let S : Set (p ⁻¹' U) := { x | (H x).1.1 ∈ V }
    have hSOpen : IsOpen S := by
      have hcont₁ : Continuous fun x : p ⁻¹' U ↦ (H x).1 := by
        change Continuous (fun x : p ⁻¹' U ↦ Prod.fst (H x))
        exact continuous_fst.comp H.continuous
      have hcont : Continuous fun x : p ⁻¹' U ↦ (H x).1.1 :=
        continuous_subtype_val.comp hcont₁
      simpa [S] using hVOpen.preimage hcont
    have hSV : Subtype.val '' S = p ⁻¹' V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [S, hH y] using hy
      · intro hx
        refine ⟨⟨x, hVU hx⟩, ?_, rfl⟩
        simpa [S, hH ⟨x, hVU hx⟩] using hx
    simpa [hSV] using IsOpen.isOpenMap_subtype_val hpreUOpen S hSOpen
  · intro x
    simpa [e₀, e₁, e₂] using hH ⟨x.1, hVU x.2⟩

/-- Helper for Lemma 3.7.5: a morphism of connected covering spaces over the same base is
surjective on total spaces. -/
-- Route correction: instead of packaging the groupoid-fiber argument explicitly, we use the
-- equivalent path-lifting statement. A path from a fixed image point to `y'` lifts through `p`,
-- and composing that lift with `h.left` gives another lift through `p'`; uniqueness of lifted
-- paths forces the endpoint to be `y'`.
private theorem covering_space_hom_surjective
    {p : C(E, B)} {p' : C(E', B)}
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    Function.Surjective h.left := by
  classical
  show ∀ y' : E', ∃ x : E, h.left.hom x = y'
  letI : PathConnectedSpace E := PathConnectedSpace.of_locPathConnectedSpace
  letI : PathConnectedSpace E' := PathConnectedSpace.of_locPathConnectedSpace
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  intro y'
  let y₀ : E' := h.left.hom e₀
  let γ : Path y₀ y' := (PathConnectedSpace.joined y₀ y').somePath
  let γB : Path (p' y₀) (p' y') := γ.map hp'.isCoveringMap.continuous
  let Γ : C(↑unitInterval, E) :=
    hp.isCoveringMap.liftPath γB e₀ (γB.source.trans (covering_space_hom_comm h e₀))
  let hΓ : C(↑unitInterval, E') := h.left.hom.comp Γ
  have hhΓ_lifts : p' ∘ hΓ = γB.toContinuousMap := by
    ext t
    calc
      p' (hΓ t) = p (Γ t) := covering_space_hom_comm h (Γ t)
      _ = γB.toContinuousMap t := by
        exact congrFun
          (hp.isCoveringMap.liftPath_lifts γB e₀
            (γB.source.trans (covering_space_hom_comm h e₀))) t
  have hhΓ_zero : hΓ 0 = h.left.hom e₀ := by
    simpa [hΓ, Γ] using congrArg h.left.hom
      (hp.isCoveringMap.liftPath_zero γB e₀ (γB.source.trans (covering_space_hom_comm h e₀)))
  have hhΓ_eq :
      hΓ = hp'.isCoveringMap.liftPath γB y₀ γB.source := by
    refine (hp'.isCoveringMap.eq_liftPath_iff' γB.source).2 ?_
    exact ⟨hhΓ_lifts, hhΓ_zero⟩
  have hγ_eq :
      γ.toContinuousMap = hp'.isCoveringMap.liftPath γB y₀ γB.source := by
    refine (hp'.isCoveringMap.eq_liftPath_iff' γB.source).2 ?_
    constructor
    · ext t
      change p' (γ t) = p' (γ t)
      rfl
    · simpa [γB] using γ.source
  refine ⟨Γ 1, ?_⟩
  change hΓ 1 = y'
  have hendpoint :
      hΓ 1 = γ.toContinuousMap 1 := by
    rw [hhΓ_eq, hγ_eq.symm]
  simpa [hΓ] using hendpoint.trans γ.target

/-- Helper for Lemma 3.7.5: the image of a point in one source sheet over a common fundamental
neighborhood still lies over that same base point in the target cover. -/
-- The commutative triangle `p' ∘ h.left = p` identifies the base coordinates, and the source
-- trivialization records that coordinate as `u`.
private theorem source_sheet_image_mem_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u : V) (i : p ⁻¹' ({b} : Set B)) :
    h.left.hom ((H.symm (u, i)).1) ∈ p' ⁻¹' V := by
  have hbase :
      p' (h.left.hom ((H.symm (u, i)).1)) = p ((H.symm (u, i)).1) :=
    covering_space_hom_comm h ((H.symm (u, i)).1)
  have hu :
      p ((H.symm (u, i)).1) = u.1 := by
    exact (hH (H.symm (u, i))).symm.trans (by simp)
  show p' (h.left.hom ((H.symm (u, i)).1)) ∈ V
  rw [hbase, hu]
  exact u.2

/-- Helper for Lemma 3.7.5: in the common local trivializations, `h.left` preserves the base
coordinate. -/
-- After placing the source point into the source trivialization and applying the over-category
-- commutativity relation, the first coordinate in the target trivialization is forced to be `u`.
private theorem source_sheet_image_first_coordinate
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u : V) (i : p ⁻¹' ({b} : Set B)) :
    (H' ⟨h.left.hom ((H.symm (u, i)).1),
      source_sheet_image_mem_common_neighborhood H hH h u i⟩).1 = u := by
  apply Subtype.ext
  have hbase :
      p' (h.left.hom ((H.symm (u, i)).1)) = p ((H.symm (u, i)).1) :=
    covering_space_hom_comm h ((H.symm (u, i)).1)
  have hu :
      p ((H.symm (u, i)).1) = u.1 := by
    exact (hH (H.symm (u, i))).symm.trans (by simp)
  simpa [hH' _] using hbase.trans hu

/-- Helper for Lemma 3.7.5: over a common path-connected fundamental neighborhood, the image of
one source sheet lands in a single target sheet. -/
-- The target-sheet index is a continuous map from the path-connected space `V` into the discrete
-- fiber `p' ⁻¹' {b}`, so it is constant.
private theorem source_sheet_maps_to_single_target_sheet
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hVPath : IsPathConnected V)
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u₀ : V) (i : p ⁻¹' ({b} : Set B)) :
    let j :=
      (H' ⟨h.left.hom ((H.symm (u₀, i)).1),
        source_sheet_image_mem_common_neighborhood H hH h u₀ i⟩).2
    ∀ u : V,
      (H' ⟨h.left.hom ((H.symm (u, i)).1),
        source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = j := by
  let c : C(V, p' ⁻¹' ({b} : Set B)) :=
    ⟨fun u ↦
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2,
      by
        have hpair : Continuous fun u : V ↦ ((u, i) : V × (p ⁻¹' ({b} : Set B))) := by
          fun_prop
        have hsource : Continuous fun u : V ↦ (H.symm (u, i)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        have htarget :
            Continuous fun u : V ↦
              (⟨h.left.hom ((H.symm (u, i)).1),
                source_sheet_image_mem_common_neighborhood H hH h u i⟩ : p' ⁻¹' V) := by
          exact Continuous.subtype_mk (h.left.hom.continuous.comp hsource)
            (fun u ↦ source_sheet_image_mem_common_neighborhood H hH h u i)
        have hcomp : Continuous fun u : V ↦
            H' ⟨h.left.hom ((H.symm (u, i)).1),
              source_sheet_image_mem_common_neighborhood H hH h u i⟩ :=
          H'.continuous.comp htarget
        exact continuous_snd.comp hcomp⟩
  letI : PathConnectedSpace V := (isPathConnected_iff_pathConnectedSpace).mp hVPath
  dsimp
  intro u
  have hconst : c u = c u₀ :=
    PreconnectedSpace.constant (hp := inferInstance) (f := c) c.continuous
  simpa [c] using hconst

/-- Helper for Lemma 3.7.5: a target sheet cut out by a fixed sheet index is open in the ambient
total space. -/
-- The sheet condition is the preimage of a singleton in the discrete fiber, so it is open in
-- `p' ⁻¹' V`; then the subtype projection carries it to an open subset of `E'`.
private theorem target_sheet_isOpen
    {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hpreVOpen : IsOpen (p' ⁻¹' V))
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (j : p' ⁻¹' ({b} : Set B)) :
    IsOpen (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) := by
  let S : Set (p' ⁻¹' V) := { y | (H' y).2 = j }
  have hSOpen : IsOpen S := by
    have hcont : Continuous fun y : p' ⁻¹' V ↦ (H' y).2 :=
      continuous_snd.comp H'.continuous
    simpa [S] using (isOpen_discrete ({j} : Set (p' ⁻¹' ({b} : Set B)))).preimage hcont
  simpa [S] using IsOpen.isOpenMap_subtype_val hpreVOpen S hSOpen

/-- Helper for Lemma 3.7.5: the chosen target sheet is homeomorphic to the common fundamental
neighborhood `V`. -/
-- We parameterize the sheet by its base coordinate `u : V`, then pass from the sheet subtype to
-- its image in `E'` through the subtype embedding.
private theorem target_sheet_homeomorph_common_neighborhood
    {p' : C(E', B)} {b : B} {V : Set B}
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (j : p' ⁻¹' ({b} : Set B)) :
    ∃ eW : V ≃ₜ (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }),
      ∀ u : V,
        ((eW u : Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
          (H'.symm (u, j)).1 := by
  let e₀ :
      V ≃ₜ { y : p' ⁻¹' V // (H' y).2 = j } :=
    { toFun := fun u ↦ ⟨H'.symm (u, j), by simp⟩
      invFun := fun y ↦ (H' y.1).1
      left_inv := by
        intro u
        simpa using congrArg Prod.fst (H'.apply_symm_apply (u, j))
      right_inv := by
        intro y
        apply Subtype.ext
        have hy : (H' y.1).2 = j := y.2
        apply H'.injective
        change H' (H'.symm ((H' y.1).1, j)) = H' y.1
        have hpair : ((H' y.1).1, j) = H' y.1 := by
          ext
          · rfl
          · exact congrArg Subtype.val hy.symm
        exact (H'.apply_symm_apply ((H' y.1).1, j)).trans hpair
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let S : Set (p' ⁻¹' V) := { y | (H' y).2 = j }
  let eW :
      V ≃ₜ Set.image (Subtype.val : p' ⁻¹' V → E') S :=
    e₀.trans ((Topology.IsEmbedding.subtypeVal).homeomorphImage S)
  refine ⟨eW, ?_⟩
  -- The chosen parameterization of the target sheet is pointwise the obvious inverse chart.
  intro u
  change (((Topology.IsEmbedding.subtypeVal).homeomorphImage S) (e₀ u)).1 =
      (H'.symm (u, j)).1
  rfl

/-- Helper for Lemma 3.7.5: belonging to the chosen target sheet is equivalent to having the
corresponding source sheet index map to `j`. -/
-- We compare the target trivialization of `h.left x` with the point of the chosen sheet that
-- realizes membership in the image of `Subtype.val`.
private theorem mem_target_sheet_iff_sheet_index
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (x : p ⁻¹' V) :
    h.left.hom x.1 ∈
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ↔
      φ (H x).2 = j := by
  constructor
  · rintro ⟨y, hyj, hyx⟩
    have hxBack : H.symm ((H x).1, (H x).2) = x := by
      simpa using H.symm_apply_apply x
    let hx' : p' ⁻¹' V :=
      ⟨h.left.hom ((H.symm ((H x).1, (H x).2)).1),
        source_sheet_image_mem_common_neighborhood H hH h (H x).1 (H x).2⟩
    have hsub :
        hx' = y := by
      apply Subtype.ext
      simpa [hx', hxBack] using hyx.symm
    have hsnd :
        (H' hx').2 = j := by
      exact (congrArg Prod.snd (congrArg H' hsub)).trans hyj
    simpa [hx', hxBack] using (hφ (H x).1 (H x).2).symm.trans hsnd
  · intro hxj
    have hxBack : H.symm ((H x).1, (H x).2) = x := by
      simpa using H.symm_apply_apply x
    let hx' : p' ⁻¹' V :=
      ⟨h.left.hom ((H.symm ((H x).1, (H x).2)).1),
        source_sheet_image_mem_common_neighborhood H hH h (H x).1 (H x).2⟩
    refine ⟨hx', ?_, ?_⟩
    · simpa [hx', hxBack] using (hφ (H x).1 (H x).2).trans hxj
    · simpa [hx', hxBack]

/-- Helper for Lemma 3.7.5: the preimage of the chosen target sheet is exactly the union of the
source sheets whose image index is `j`. -/
-- Once a point of `E` lands in the chosen target sheet, the commutative square forces its base
-- coordinate into `V`, and the previous iff lemma converts sheet membership into the equation
-- `φ (H x).2 = j`.
private theorem preimage_target_sheet_eq_sheet_index
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) =
      Set.image (Subtype.val : p ⁻¹' V → E) { x | φ (H x).2 = j } := by
  ext x
  constructor
  · intro hx
    have hxV : p x ∈ V := by
      rcases hx with ⟨y, _hyj, hyx⟩
      have hbase : p x = p' y.1 := by
        calc
          p x = p' (h.left.hom x) := (covering_space_hom_comm h x).symm
          _ = p' y.1 := by simpa using congrArg p' hyx.symm
      have hyV : p' y.1 ∈ V := y.2
      simpa [hbase] using hyV
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ ⟨x, hxV⟩).1 hx
  · rintro ⟨xV, hxj, rfl⟩
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).2 hxj

/-- Helper for Lemma 3.7.5: a point whose image lies in the chosen target sheet already lies over
the common neighborhood `V`. -/
-- The target-sheet witness lies in `p' ⁻¹' V`, and the relation `p' ∘ h.left = p` transfers that
-- basepoint membership back to the source point.
private theorem preimage_target_sheet_mem_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (x : h.left ⁻¹'
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) :
    p x.1 ∈ V := by
  rcases x.2 with ⟨y, _hyj, hyx⟩
  have hbase : p x.1 = p' y.1 := by
    calc
      p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
      _ = p' y.1 := by simpa using congrArg p' hyx.symm
  have hyV : p' y.1 ∈ V := y.2
  simpa [hbase] using hyV

/-- Helper for Lemma 3.7.5: over the chosen target sheet, `h.left` is modeled by `V` times the
sheet-index fiber `φ ⁻¹' {j}`. -/
-- We rewrite the restricted preimage as a subset of `p ⁻¹' V`, transport it through the source
-- trivialization `H`, and finally reassociate the remaining subtype into `V × {i // φ i = j}`.
private theorem preimage_target_sheet_homeomorph_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    ∃ Hpre :
      (h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) ≃ₜ
        V × { i : p ⁻¹' ({b} : Set B) // φ i = j },
      ∀ x,
        (Hpre x).1 =
          (H ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩).1 := by
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  let S : Set (p ⁻¹' V) := { x | φ (H x).2 = j }
  let e₀ :
      (h.left ⁻¹' W) ≃ₜ Set.image (Subtype.val : p ⁻¹' V → E) S :=
    Homeomorph.setCongr (preimage_target_sheet_eq_sheet_index H hH H' h j φ hφ)
  let e₁ : Set.image (Subtype.val : p ⁻¹' V → E) S ≃ₜ S :=
    ((Topology.IsEmbedding.subtypeVal).homeomorphImage S).symm
  let e₂ : S ≃ₜ { z : V × (p ⁻¹' ({b} : Set B)) // φ z.2 = j } :=
    H.subtype fun x ↦ by
      simp [S]
  let e₃ :
      { z : V × (p ⁻¹' ({b} : Set B)) // φ z.2 = j } ≃ₜ
        V × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    { toFun := fun z ↦ (z.1.1, ⟨z.1.2, z.2⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.1), z.2.2⟩
      left_inv := by
        intro z
        cases z
        rfl
      right_inv := by
        intro z
        cases z
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let Hpre : (h.left ⁻¹' W) ≃ₜ V × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    e₀.trans (e₁.trans (e₂.trans e₃))
  refine ⟨Hpre, ?_⟩
  intro x
  let xV : p ⁻¹' V := ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩
  have hxj : φ (H xV).2 = j := by
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).1 x.2
  let xS : S := ⟨xV, hxj⟩
  have he₀ :
      e₀ x = (Topology.IsEmbedding.subtypeVal).homeomorphImage S xS := by
    apply Subtype.ext
    rfl
  have he₁ : e₁ (e₀ x) = xS := by
    rw [he₀]
    simpa [e₁] using ((Topology.IsEmbedding.subtypeVal).homeomorphImage S).symm_apply_apply xS
  have he₂ :
      e₂ (e₁ (e₀ x)) = ⟨H xV, by simpa [S, xS] using hxj⟩ := by
    rw [he₁]
    apply Subtype.ext
    rfl
  -- After rewriting the restricted preimage into a source sheet union, the first factor is
  -- exactly the `V`-coordinate recorded by the source trivialization.
  change (e₃ (e₂ (e₁ (e₀ x)))).1 = (H xV).1
  rw [he₂]
  rfl

/-- Helper for Lemma 3.7.5: the chosen target-sheet parameterization sends the source-sheet base
coordinate to the actual image point of `x`. -/
-- The first coordinate of the target trivialization is already forced by the over-category
-- relation, and the second coordinate is `j` because `x` lies in the chosen target sheet.
private theorem chosen_target_sheet_image_eq
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (eW : V ≃ₜ (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }))
    (heW :
      ∀ u : V,
        ((eW u : Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
          (H'.symm (u, j)).1)
    (x : h.left ⁻¹'
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) :
    ((eW
        ((H ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩).1) :
      Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
      h.left x.1 := by
  let xV : p ⁻¹' V := ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩
  have hxj : φ (H xV).2 = j := by
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).1 x.2
  have hxBack : H.symm ((H xV).1, (H xV).2) = xV := by
    simpa using H.symm_apply_apply xV
  have hxBackVal : (H.symm ((H xV).1, (H xV).2)).1 = x.1 := by
    simpa [xV] using congrArg Subtype.val hxBack
  let hx' : p' ⁻¹' V :=
    ⟨h.left.hom ((H.symm ((H xV).1, (H xV).2)).1),
      source_sheet_image_mem_common_neighborhood H hH h (H xV).1 (H xV).2⟩
  have htarget :
      H' hx' = ((H xV).1, j) := by
    apply Prod.ext
    · apply Subtype.ext
      simpa [hx', hxBackVal] using congrArg Subtype.val
        (source_sheet_image_first_coordinate H hH H' hH' h (H xV).1 (H xV).2)
    · simpa [hx', hxBackVal] using (hφ (H xV).1 (H xV).2).trans hxj
  have hsub : H'.symm ((H xV).1, j) = hx' := by
    apply H'.injective
    simpa [htarget] using H'.apply_symm_apply ((H xV).1, j)
  calc
    ((eW ((H xV).1) :
        Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
        (H'.symm ((H xV).1, j)).1 := heW ((H xV).1)
    _ = h.left x.1 := by
      simpa [hx', hxBackVal] using congrArg Subtype.val hsub

/-- Helper for Lemma 3.7.5: the source-sheet indices mapping to the chosen target sheet are
homeomorphic to the actual fiber of `h.left` over `y'`. -/
-- We evaluate a source sheet at the basepoint `b` to land in the fiber over `y'`, and recover the
-- source index of a fiber point by reading its source trivialization coordinate.
private theorem sheet_index_homeomorph_covering_space_hom_fiber
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (hbV : b ∈ V)
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (y' : E') (hy'b : p' y' = b)
    (j : p' ⁻¹' ({b} : Set B))
    (hj : (H' ⟨y', by simpa [hy'b] using hbV⟩).2 = j)
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    Nonempty (
      { i : p ⁻¹' ({b} : Set B) // φ i = j } ≃ₜ
        h.left ⁻¹' ({y'} : Set E')) := by
  let toFun :
      { i : p ⁻¹' ({b} : Set B) // φ i = j } →
        h.left ⁻¹' ({y'} : Set E') :=
    fun i ↦
      let x : E := (H.symm (⟨b, hbV⟩, i.1)).1
      have hxFiber : h.left.hom x ∈ ({y'} : Set E') := by
        let hx' : p' ⁻¹' V :=
          ⟨h.left.hom x,
            source_sheet_image_mem_common_neighborhood H hH h ⟨b, hbV⟩ i.1⟩
        have hfst :
            (H' hx').1 = ⟨b, hbV⟩ := by
          apply Subtype.ext
          simpa [hx', x] using congrArg Subtype.val
            (source_sheet_image_first_coordinate H hH H' hH' h ⟨b, hbV⟩ i.1)
        have htarget :
            H' hx' = (⟨b, hbV⟩, j) := by
          exact Prod.ext hfst (by simpa [hx', x] using (hφ ⟨b, hbV⟩ i.1).trans i.2)
        have hyfst :
            (H' ⟨y', by simpa [hy'b] using hbV⟩).1 = ⟨b, hbV⟩ := by
          apply Subtype.ext
          simpa [hH' ⟨y', by simpa [hy'b] using hbV⟩, hy'b]
        have hy' :
            H' ⟨y', by simpa [hy'b] using hbV⟩ = (⟨b, hbV⟩, j) :=
          Prod.ext hyfst hj
        have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
          apply H'.injective
          exact htarget.trans hy'.symm
        simpa [hx'] using congrArg Subtype.val hsub
      ⟨x, hxFiber⟩
  let invFun :
      h.left ⁻¹' ({y'} : Set E') →
        { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    fun x ↦
      let hxb : p x.1 = b := by
        calc
          p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
          _ = p' y' := by simpa using congrArg p' x.2
          _ = b := hy'b
      let hxV : p x.1 ∈ V := by
        simpa [hxb] using hbV
      let xV' : p ⁻¹' V := ⟨x.1, hxV⟩
      let i : p ⁻¹' ({b} : Set B) := (H xV').2
      have hxSheet :
          φ i = j := by
        have hxBack : H.symm ((H xV').1, (H xV').2) = xV' := by
          simpa [i] using H.symm_apply_apply xV'
        have hxBackVal : (H.symm ((H xV').1, i)).1 = x.1 := by
          exact congrArg Subtype.val hxBack
        let hx' : p' ⁻¹' V :=
          ⟨h.left.hom ((H.symm ((H xV').1, i)).1),
            source_sheet_image_mem_common_neighborhood H hH h (H xV').1 i⟩
        have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
          apply Subtype.ext
          simpa [hx', hxBackVal] using x.2
        have hsnd : (H' hx').2 = j := by
          exact (congrArg Prod.snd (congrArg H' hsub)).trans hj
        simpa [i, xV', hx', hxBackVal] using (hφ (H xV').1 i).symm.trans hsnd
      ⟨i, hxSheet⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro i
    apply Subtype.ext
    have hsecond :
        (H ⟨(H.symm (⟨b, hbV⟩, i.1)).1, by
          have hqa' :
              (H (H.symm (⟨b, hbV⟩, i.1))).1.1 = b := by
            simpa using congrArg (fun y : V × (p ⁻¹' ({b} : Set B)) ↦ y.1.1)
              (H.apply_symm_apply (⟨b, hbV⟩, i.1))
          simpa using (hH (H.symm (⟨b, hbV⟩, i.1))).symm.trans hqa'⟩).2 = i.1 := by
      simpa using congrArg Prod.snd (H.apply_symm_apply (⟨b, hbV⟩, i.1))
    simpa [toFun, invFun, hsecond]
  have hRight : Function.RightInverse invFun toFun := by
    intro x
    apply Subtype.ext
    let hxb : p x.1 = b := by
      calc
        p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
        _ = p' y' := by simpa using congrArg p' x.2
        _ = b := hy'b
    let hxV : p x.1 ∈ V := by
      simpa [hxb] using hbV
    let xV' : p ⁻¹' V := ⟨x.1, hxV⟩
    let i : p ⁻¹' ({b} : Set B) := (H xV').2
    have hfst : (H ⟨x.1, hxV⟩).1 = ⟨b, hbV⟩ := by
      apply Subtype.ext
      simpa [hxb] using hH ⟨x.1, hxV⟩
    have hxBack :
        H.symm (⟨b, hbV⟩, i) = ⟨x.1, hxV⟩ := by
      calc
        H.symm (⟨b, hbV⟩, i) = H.symm ((H xV').1, i) := by rw [hfst]
        _ = xV' := by simpa [xV', i] using H.symm_apply_apply xV'
    simpa [toFun, invFun, hxb, hxV, xV', i, hxBack]
  refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        have hpair :
            Continuous fun i :
                { i : p ⁻¹' ({b} : Set B) // φ i = j } =>
              ((⟨b, hbV⟩, i.1) : V × (p ⁻¹' ({b} : Set B))) := by
          fun_prop
        have hBase :
            Continuous fun i :
                { i : p ⁻¹' ({b} : Set B) // φ i = j } =>
              (H.symm (⟨b, hbV⟩, i.1)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        exact Continuous.subtype_mk hBase fun i ↦ by
          let x : E := (H.symm (⟨b, hbV⟩, i.1)).1
          let hx' : p' ⁻¹' V :=
            ⟨h.left.hom x,
              source_sheet_image_mem_common_neighborhood H hH h ⟨b, hbV⟩ i.1⟩
          have hfst :
              (H' hx').1 = ⟨b, hbV⟩ := by
            apply Subtype.ext
            simpa [hx', x] using congrArg Subtype.val
              (source_sheet_image_first_coordinate H hH H' hH' h ⟨b, hbV⟩ i.1)
          have htarget :
              H' hx' = (⟨b, hbV⟩, j) := by
            exact Prod.ext hfst (by simpa [hx', x] using (hφ ⟨b, hbV⟩ i.1).trans i.2)
          have hyfst :
              (H' ⟨y', by simpa [hy'b] using hbV⟩).1 = ⟨b, hbV⟩ := by
            apply Subtype.ext
            simpa [hH' ⟨y', by simpa [hy'b] using hbV⟩, hy'b]
          have hy' :
              H' ⟨y', by simpa [hy'b] using hbV⟩ = (⟨b, hbV⟩, j) :=
            Prod.ext hyfst hj
          have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
            apply H'.injective
            exact htarget.trans hy'.symm
          simpa [toFun, x, hx'] using congrArg Subtype.val hsub
      continuous_invFun := by
        have hxV :
            ∀ x : h.left ⁻¹' ({y'} : Set E'),
              p x.1 ∈ V := by
          intro x
          have hxb : p x.1 = b := by
            calc
              p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
              _ = p' y' := by simpa using congrArg p' x.2
              _ = b := hy'b
          simpa [hxb] using hbV
        have hBase :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') => x.1 := by
          exact continuous_subtype_val
        have hLift :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
              (⟨x.1, hxV x⟩ : p ⁻¹' V) := by
          exact Continuous.subtype_mk hBase hxV
        have hSecond :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
              (H ⟨x.1, hxV x⟩).2 := by
          have hComp :
              Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
                H ⟨x.1, hxV x⟩ := H.continuous.comp hLift
          exact continuous_snd.comp hComp
        exact Continuous.subtype_mk hSecond fun x ↦ by
          let hxb : p x.1 = b := by
            calc
              p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
              _ = p' y' := by simpa using congrArg p' x.2
              _ = b := hy'b
          let xV' : p ⁻¹' V := ⟨x.1, hxV x⟩
          let i : p ⁻¹' ({b} : Set B) := (H xV').2
          have hxBack : H.symm ((H xV').1, (H xV').2) = xV' := by
            simpa [i] using H.symm_apply_apply xV'
          have hxBackVal : (H.symm ((H xV').1, i)).1 = x.1 := by
            exact congrArg Subtype.val hxBack
          let hx' : p' ⁻¹' V :=
            ⟨h.left.hom ((H.symm ((H xV').1, i)).1),
              source_sheet_image_mem_common_neighborhood H hH h (H xV').1 i⟩
          have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
            apply Subtype.ext
            simpa [hx', hxBackVal] using x.2
          have hsnd : (H' hx').2 = j := by
            exact (congrArg Prod.snd (congrArg H' hsub)).trans hj
          simpa [invFun, hxb, i, xV', hxBackVal, hx'] using
            (hφ (H xV').1 i).symm.trans hsnd }⟩

/-- Helper for Lemma 3.7.5: over the chosen target sheet, `h.left` is explicitly a product of the
sheet and the restricted source-sheet index set. -/
-- We reuse the previously identified restricted preimage over the sheet and transport the first
-- factor from `V` to the actual target sheet inside `E'`.
private theorem chosen_target_sheet_trivialization
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    ∃ Hh :
      h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ≃ₜ
        (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ×
          { i : p ⁻¹' ({b} : Set B) // φ i = j },
      ∀ x, (Hh x).1.1 = h.left x := by
  -- Route correction: we keep the sheet-based proof, but separate the restricted-preimage
  -- coordinates from the target-sheet transport instead of expanding the whole composite at once.
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  rcases preimage_target_sheet_homeomorph_common_neighborhood H hH H' h j φ hφ with
    ⟨Hpre, hHpre⟩
  rcases target_sheet_homeomorph_common_neighborhood H' j with ⟨eW, heW⟩
  let Hh :
      (h.left ⁻¹' W) ≃ₜ W × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    Hpre.trans (Homeomorph.prodCongr eW (Homeomorph.refl _))
  refine ⟨Hh, ?_⟩
  intro x
  -- The composed trivialization first reads the `V`-coordinate from the source chart and then
  -- reparameterizes that coordinate by the chosen target-sheet homeomorphism.
  change ((eW (Hpre x).1 : W) : E') = h.left x
  rw [hHpre x]
  exact chosen_target_sheet_image_eq H hH H' hH' h j φ hφ eW heW x

/-- Helper for Lemma 3.7.5: the chosen target sheet through `y'` is an evenly covered
neighborhood for `h.left`. -/
-- We first trivialize `h.left` over the chosen sheet using the restricted sheet-index set, then
-- replace that index set by the actual fiber over `y'`.
private theorem chosen_target_sheet_isEvenlyCovered
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p ⁻¹' ({b} : Set B))]
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hbV : b ∈ V)
    (hpreVOpen' : IsOpen (p' ⁻¹' V))
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (y' : E') (hy'b : p' y' = b)
    (j : p' ⁻¹' ({b} : Set B))
    (hj : (H' ⟨y', by simpa [hy'b] using hbV⟩).2 = j)
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    IsEvenlyCovered h.left y' (h.left ⁻¹' ({y'} : Set E')) := by
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  let T : Type u := { i : p ⁻¹' ({b} : Set B) // φ i = j }
  rcases chosen_target_sheet_trivialization H hH H' hH' h j φ hφ with ⟨Hh, hHh⟩
  classical
  let hFiber :=
    Classical.choice
      (sheet_index_homeomorph_covering_space_hom_fiber hbV H hH H' hH' h y' hy'b j hj φ hφ)
  have hy'W : y' ∈ W := by
    refine ⟨⟨y', by simpa [hy'b] using hbV⟩, ?_, rfl⟩
    simpa [hj]
  have hWOpen : IsOpen W := target_sheet_isOpen hpreVOpen' H' j
  have hpreWOpen : IsOpen (h.left ⁻¹' W) := hWOpen.preimage h.left.hom.continuous
  have hEvenlyCoveredT : IsEvenlyCovered h.left y' T := by
    refine ⟨inferInstance, W, hy'W, hWOpen, hpreWOpen, Hh, hHh⟩
  simpa [T] using hEvenlyCoveredT.of_fiber_homeomorph hFiber

/-- Lemma 3.7.5: under the standing hypotheses of this chapter, a morphism of connected
locally path-connected covering spaces over `B` is itself a covering map between the total
spaces. -/
-- Proof sketch: the algebraic analogue gives surjectivity. Fundamental neighborhoods for both
-- covers give fundamental neighborhoods for `h.left` by taking components of inverse images in
-- `E'` of neighborhoods of `B` that are fundamental for both `p` and `p'`.
theorem coveringSpaceHom_isCoveringMap
    {p : C(E, B)} {p' : C(E', B)}
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    IsPathConnectedCoveringMap h.left := by
  have hsurj : Function.Surjective h.left := covering_space_hom_surjective hp hp' h
  have hcov : IsCoveringMap h.left := by
    intro y'
    let b : B := p' y'
    rcases hp.2 b with ⟨hdisc, U, hbU, hUOpen, hUPath, hpreUOpen, HU, hHU⟩
    rcases hp'.2 b with ⟨hdisc', U', hbU', hU'Open, hU'Path, hpreU'Open, HU', hHU'⟩
    let V : Set B := pathComponentIn (U ∩ U') b
    have hVSubsetInter : V ⊆ U ∩ U' := pathComponentIn_subset
    have hVSubsetU : V ⊆ U := fun x hx ↦ (hVSubsetInter hx).1
    have hVSubsetU' : V ⊆ U' := fun x hx ↦ (hVSubsetInter hx).2
    have hbInter : b ∈ U ∩ U' := ⟨hbU, hbU'⟩
    have hbV : b ∈ V := mem_pathComponentIn_self hbInter
    have hVOpen : IsOpen V := (hUOpen.inter hU'Open).pathComponentIn b
    have hVPath : IsPathConnected V := isPathConnected_pathComponentIn hbInter
    have hFundV : IsFundamentalNeighborhood p b V :=
      fundamental_neighborhood_restrict
        ⟨hdisc, hbU, hUOpen, hUPath, hpreUOpen, HU, hHU⟩
        hVSubsetU hbV hVOpen hVPath
    have hFundV' : IsFundamentalNeighborhood p' b V :=
      fundamental_neighborhood_restrict
        ⟨hdisc', hbU', hU'Open, hU'Path, hpreU'Open, HU', hHU'⟩
        hVSubsetU' hbV hVOpen hVPath
    rcases hFundV with ⟨hdiscV, _, _, _, hpreVOpen, H, hH⟩
    rcases hFundV' with ⟨hdiscV', _, _, _, hpreVOpen', H', hH'⟩
    letI : DiscreteTopology (p ⁻¹' ({b} : Set B)) := hdiscV
    letI : DiscreteTopology (p' ⁻¹' ({b} : Set B)) := hdiscV'
    let u₀ : V := ⟨b, hbV⟩
    let j : p' ⁻¹' ({b} : Set B) :=
      (H' ⟨y', by
        have hyb : p' y' = b := rfl
        show p' y' ∈ V
        simpa [b] using hbV⟩).2
    let φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B) :=
      fun i ↦
        (H' ⟨h.left.hom ((H.symm (u₀, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u₀ i⟩).2
    have hφ :
        ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
          (H' ⟨h.left.hom ((H.symm (u, i)).1),
            source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i := by
      intro u i
      simpa [φ, u₀] using source_sheet_maps_to_single_target_sheet
        (hVPath := hVPath) H hH H' hH' h u₀ i u
    -- The chosen target sheet through `y'` carries the required local product structure.
    exact chosen_target_sheet_isEvenlyCovered
      (hbV := hbV) (hpreVOpen' := hpreVOpen') H hH H' hH' h y' rfl j
      (by simpa [j]) φ hφ
  -- Once `h.left` is a covering map and is surjective, the locally path-connected codomain `E'`
  -- upgrades it to a path-connected covering map in the sense of Definition 3.1.5.
  change IsPathConnectedCoveringMap h.left.hom
  exact IsCoveringMap.isPathConnectedCoveringMap (B := E')
    (show IsCoveringMap h.left.hom from hcov)
    (show Function.Surjective h.left.hom from hsurj)

/-! ### Theorem_3_7_6 (from Chap03) -/
open scoped FundamentalGroup
open CategoryTheory

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [PathConnectedSpace E] [LocPathConnectedSpace E]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)} {p' : C(E', B)}

/-- Helper for Theorem 3.7.6: when the target basepoint is definitionally unchanged, the ordinary
fundamental-group map agrees with `mapOfEq`. -/
private theorem fundamental_group_map_eq_map_of_eq_rfl {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- Reduce both maps to the same path-level representative formula.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Theorem 3.7.6: the induced map on fundamental groups respects composition of
continuous maps. -/
private theorem fundamental_group_map_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  -- On loop representatives, composition is definitionally functorial.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  rfl

/-- Helper for Theorem 3.7.6: `mapOfEq` also respects composition once the intermediate basepoint
is transported by an explicit equality. -/
private theorem fundamental_group_map_of_eq_comp {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) :
    FundamentalGroup.mapOfEq (g.comp f) (by simpa [ContinuousMap.comp_apply, hf] using hg) =
      (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) := by
  -- First normalize all endpoint equalities to the definitional `rfl` case.
  cases hf
  cases hg
  let hy : g (f x) = g (f x) := rfl
  have hleft :
      FundamentalGroup.mapOfEq (g.comp f) hy = FundamentalGroup.map (g.comp f) x := by
    simpa [hy] using
      (fundamental_group_map_eq_map_of_eq_rfl (f := g.comp f) (x := x)).symm
  have hrightg : FundamentalGroup.mapOfEq g rfl = FundamentalGroup.map g (f x) := by
    simpa using
      (fundamental_group_map_eq_map_of_eq_rfl (f := g) (x := f x)).symm
  have hrightf : FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f x := by
    simpa using
      (fundamental_group_map_eq_map_of_eq_rfl (f := f) (x := x)).symm
  have hmain :
      FundamentalGroup.mapOfEq (g.comp f) hy =
        (FundamentalGroup.mapOfEq g rfl).comp (FundamentalGroup.map f x) := by
    -- Replace both `mapOfEq` terms by ordinary functorial maps and use composition.
    have hcomp :
        FundamentalGroup.mapOfEq (g.comp f) hy =
          (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) :=
      hleft.trans (fundamental_group_map_comp f g x)
    simpa [hrightg] using hcomp
  simpa [hrightf] using hmain

/-- Helper for Theorem 3.7.6: equal continuous maps induce the same `mapOfEq` after identifying
their endpoint proofs. -/
private theorem fundamental_group_map_of_eq_eq_of_eq {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (hfg : f = g) {x : X} {y : Y} (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Once the maps coincide, proof irrelevance identifies the endpoint transports.
  cases hfg
  exact congrArg (FundamentalGroup.mapOfEq f) (Subsingleton.elim _ _)

/-- Helper for Theorem 3.7.6: a morphism of covering spaces carrying `e` to `e'` forces the image
subgroup over the basepoint to be included in the target image subgroup. -/
private theorem fundamental_group_range_le_of_covering_space_hom
    {p : C(E, B)} {p' : C(E', B)}
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    (FundamentalGroup.mapOfEq p e.2).range ≤
      (FundamentalGroup.mapOfEq p' e'.2).range := by
  rcases e with ⟨e, he⟩
  rcases e' with ⟨e', he'⟩
  subst b
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine MonoidHom.mem_range.mpr ?_
  -- Push the chosen loop class forward along the map of coverings.
  refine ⟨(FundamentalGroup.mapOfEq h.left.hom hh) γ, ?_⟩
  have hbase : (p'.comp h.left.hom) e = p e := by
    simpa using (congrArg p' hh).trans he'
  have hcomp :
      FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase =
        (FundamentalGroup.mapOfEq p' he').comp
          (FundamentalGroup.mapOfEq h.left.hom hh) := by
    simpa [hbase] using
      fundamental_group_map_of_eq_comp h.left.hom p' hh he'
  have hcomm : p'.comp h.left.hom = p := by
    -- The over-category commutative triangle says exactly `p' ∘ h = p`.
    ext y
    have hy := congrArg (fun f : TopCat.of E ⟶ TopCat.of B => f.hom y) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hy
  have hEq :
      FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase =
        FundamentalGroup.mapOfEq p rfl :=
    fundamental_group_map_of_eq_eq_of_eq hcomm hbase rfl
  -- Identify the pushed-forward class with the original one in the target subgroup.
  calc
    (FundamentalGroup.mapOfEq p' he') ((FundamentalGroup.mapOfEq h.left.hom hh) γ) =
        (FundamentalGroup.mapOfEq (p'.comp h.left.hom) hbase) γ := by
      simpa using congrArg (fun F ↦ F γ) hcomp.symm
    _ = (FundamentalGroup.mapOfEq p rfl) γ := by
      simpa using congrArg (fun F ↦ F γ) hEq

/-- Theorem 3.7.6: for covers `p : E → B` and `p' : E' → B`, and chosen fiber points
`e : p ⁻¹' {b}` and `e' : p' ⁻¹' {b}` over the same basepoint `b`, there exists a unique
morphism of covering spaces over `B` sending `e` to `e'` if and only if the image subgroup
`p_*(π₁(E,e))` is contained in `p'_*(π₁(E',e'))` inside `π₁(B,b)`. -/
-- Proof sketch: apply Theorem 3.7.1 to the covering map `p' : E' → B` and the continuous map
-- `p : E → B`, with source space `E` and chosen basepoint `e.1`. The lift produced there is
-- exactly a morphism in `Over (TopCat.of B)` by Definition 3.7.4, and uniqueness of the lift is
-- uniqueness of the point-preserving morphism of coverings.
theorem existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    (∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left.hom e.1 = e'.1) ↔
      (FundamentalGroup.mapOfEq p e.2).range ≤
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  let _ := hp
  rcases e with ⟨e, he⟩
  rcases e' with ⟨e', he'⟩
  subst b
  constructor
  · rintro ⟨h, hh, -⟩
    -- A point-preserving morphism yields the subgroup inclusion by functoriality on loops.
    exact
      fundamental_group_range_le_of_covering_space_hom
        (p e) ⟨e, rfl⟩ ⟨e', he'⟩ h hh
  · intro hsub
    have hsub' :
        (FundamentalGroup.map p e).range ≤
          (FundamentalGroup.mapOfEq p' he').range := by
      -- Rewrite the source subgroup into the form required by the lifting theorem.
      simpa [fundamental_group_map_eq_map_of_eq_rfl] using hsub
    -- Apply the covering-space lifting theorem to `p : E → B` viewed as a map into the base.
    rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
        (cov := hp'.isCoveringMap) (f := p) (a₀ := e) (e₀ := e') (he := he') hsub' with
      ⟨F, hF, huniq⟩
    have hcommF : p' ∘ F = p := hF.2
    refine ⟨Over.homMk (TopCat.ofHom F) ?_, ?_, ?_⟩
    · -- The lifted continuous map is exactly a morphism in the over-category.
      ext y
      exact congrArg (fun k ↦ k y) hcommF
    · simpa using hF.1
    · intro h hh
      -- Uniqueness of lifts is uniqueness of point-preserving morphisms over `B`.
      have hcommh : p' ∘ h.left.hom = p := by
        funext y
        have hy := congrArg (fun f : TopCat.of E ⟶ TopCat.of B => f.hom y) (Over.w h)
        simpa [ContinuousMap.comp_apply] using hy
      have hleft : h.left.hom = F := huniq h.left.hom ⟨by simpa using hh, hcommh⟩
      apply Over.OverMorphism.ext
      simpa using congrArg TopCat.ofHom hleft

section ReverseDirection

variable [PathConnectedSpace E'] [LocPathConnectedSpace E']

/-- Helper for Theorem 3.7.6: the inverse of an isomorphism of covering spaces sends the chosen
target basepoint back to the chosen source basepoint. -/
private theorem covering_space_iso_inv_maps_basepoint
    {p : C(E, B)} {p' : C(E', B)}
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) [IsIso h]
    (hh : h.left.hom e.1 = e'.1) :
    (inv h).left.hom e'.1 = e.1 := by
  -- Evaluate the identity `h ≫ inv h = 𝟙` at the chosen source point.
  have hcomp := congrArg (fun f : TopCat.of E ⟶ TopCat.of E => f.hom e.1)
    (Over.hom_left_inv_left (asIso h))
  calc
    (inv h).left.hom e'.1 = (inv h).left.hom (h.left.hom e.1) := by rw [hh]
    _ = e.1 := hcomp

/-- A point-preserving morphism of covering spaces over `B` is an isomorphism in
`Over (TopCat.of B)` exactly when the associated image subgroups in `π₁(B, b)` coincide. -/
-- Proof sketch: if `h` is an isomorphism of coverings, compose with its inverse to obtain the
-- reverse point-preserving morphism and hence the opposite subgroup inclusion. Conversely, if the
-- image subgroups are equal, apply the main theorem in the reverse direction to construct a
-- point-preserving morphism `E' → E`; uniqueness from the main theorem forces the two composites
-- to be identities, so `h` is an isomorphism in the over-category.
theorem coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    IsIso h ↔
      (FundamentalGroup.mapOfEq p e.2).range =
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  constructor
  · intro hIso
    -- An isomorphism gives subgroup inclusions in both directions, hence equality.
    have hle := fundamental_group_range_le_of_covering_space_hom b e e' h hh
    have hhi : (inv h).left.hom e'.1 = e.1 :=
      covering_space_iso_inv_maps_basepoint b e e' h hh
    have hge :
        (FundamentalGroup.mapOfEq p' e'.2).range ≤
          (FundamentalGroup.mapOfEq p e.2).range :=
      fundamental_group_range_le_of_covering_space_hom b e' e (inv h) hhi
    exact le_antisymm hle hge
  · intro hEq
    -- Equality gives a reverse morphism `g : E' → E` fixing the chosen basepoints.
    rcases
        (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
          hp' hp b e' e).mpr hEq.ge with
      ⟨g, hg, hguniq⟩
    have hself :
        ∃! k : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p),
          k.left.hom e.1 = e.1 :=
      (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
        hp hp b e e).mpr le_rfl
    rcases hself with ⟨k, hk, hkunique⟩
    have hhg : (h ≫ g).left.hom e.1 = e.1 := by
      -- The composite `h ≫ g` fixes `e`, so uniqueness forces it to be the identity.
      calc
        (h ≫ g).left.hom e.1 = g.left.hom (h.left.hom e.1) := rfl
        _ = g.left.hom e'.1 := by rw [hh]
        _ = e.1 := hg
    have hcomp_id : h ≫ g = 𝟙 _ := by
      exact (hkunique (h ≫ g) hhg).trans (hkunique (𝟙 _) rfl).symm
    have hself' :
        ∃! k : Over.mk (TopCat.ofHom p') ⟶ Over.mk (TopCat.ofHom p'),
          k.left.hom e'.1 = e'.1 :=
      (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
        hp' hp' b e' e').mpr le_rfl
    rcases hself' with ⟨k', hk', hk'unique⟩
    have hghh : (g ≫ h).left.hom e'.1 = e'.1 := by
      -- The same uniqueness argument on the other side gives `g ≫ h = 𝟙`.
      calc
        (g ≫ h).left.hom e'.1 = h.left.hom (g.left.hom e'.1) := rfl
        _ = h.left.hom e.1 := by rw [hg]
        _ = e'.1 := hh
    have hcomp'_id : g ≫ h = 𝟙 _ := by
      exact (hk'unique (g ≫ h) hghh).trans (hk'unique (𝟙 _) rfl).symm
    exact IsIso.mk ⟨g, hcomp_id, hcomp'_id⟩

/-- The underlying map of a point-preserving isomorphism of covering spaces is a homeomorphism
exactly when the associated image subgroups in `π₁(B, b)` coincide. -/
theorem coveringSpaceMorphism_isHomeomorph_iff_fundamentalGroup_range_eq
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b})
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (hh : h.left.hom e.1 = e'.1) :
    IsHomeomorph h.left ↔
      (FundamentalGroup.mapOfEq p e.2).range =
        (FundamentalGroup.mapOfEq p' e'.2).range := by
  have hforget : IsIso h.left ↔ IsIso h := by
    simpa using isIso_iff_of_reflects_iso h (Over.forget (TopCat.of B))
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact hforget.trans <|
    coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq hp hp' b e e' h hh

end ReverseDirection

end IsPathConnectedCoveringMap

/-! ### Corollary_3_7_7 (from Chap03) -/
open CategoryTheory
open scoped FundamentalGroup

universe u

namespace IsUniversalCoveringMap

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {p' : C(E', B)}

/-- Helper for Corollary 3.7.7: a universal covering has trivial image subgroup in the base
fundamental group at every chosen fiber point. -/
theorem fundamentalGroup_mapOfEq_range_eq_bot_of_universal
    (hp : IsUniversalCoveringMap p) (b : B) (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq p e.2).range = ⊥ := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- A simply connected source has subsingleton fundamental group, so the induced map is trivial.
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact congrArg (FundamentalGroup.fromPath (X := E) (x := e.1))
      (Subsingleton.elim (FundamentalGroup.toPath γ) ⟦Path.refl e.1⟧)
  rw [hγ, map_one, MonoidHom.one_apply]

variable [LocPathConnectedSpace E]

/-- Helper for Corollary 3.7.7: a universal covering admits a unique point-preserving morphism to
any path-connected covering space over the same base. -/
private theorem existsUnique_point_preserving_morphism_to_coveringSpace
    (hp : IsUniversalCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left e.1 = e'.1 := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- Theorem 3.7.6 reduces existence and uniqueness to subgroup inclusion in `π₁(B, b)`.
  simpa using
    (IsPathConnectedCoveringMap.existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
      hp.isPathConnectedCoveringMap hp' b e e').2
      (by
        -- Universality makes the source image subgroup equal to `⊥`, so the inclusion is automatic.
        rw [fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp b e]
        exact bot_le)

/-- Corollary 3.7.7 (1): if two covering spaces over `B` are universal and their total spaces are
locally path connected, then after choosing points over the same basepoint there is a unique
isomorphism of covering spaces sending one chosen point to the other. -/
-- Proof sketch: apply Theorem 3.7.6 to obtain a unique point-preserving morphism
-- `Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')`. Since both coverings are universal, the
-- subgroup-equality criterion makes this morphism a homeomorphism, hence an isomorphism in the
-- over-category. Uniqueness of the isomorphism follows from uniqueness of its underlying morphism.
theorem universalCoveringSpace_existsUnique_iso
    [LocPathConnectedSpace E']
    (hp : IsUniversalCoveringMap p) (hp' : IsUniversalCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ≅ Over.mk (TopCat.ofHom p'), h.hom.left e.1 = e'.1 := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  let _ : SimplyConnectedSpace E' := hp'.simplyConnectedSpace
  let _ : PathConnectedSpace E' := inferInstance
  rcases
      existsUnique_point_preserving_morphism_to_coveringSpace
        hp hp'.isPathConnectedCoveringMap b e e' with
    ⟨h, hh, huniq⟩
  have hIso : IsIso h := by
    -- The same source-faithful criterion from Theorem 3.7.6 upgrades the unique morphism to an iso.
    refine
      (IsPathConnectedCoveringMap.coveringSpaceMorphism_isIso_iff_fundamentalGroup_range_eq
        hp.isPathConnectedCoveringMap hp'.isPathConnectedCoveringMap b e e' h
        (by simpa using hh)).2 ?_
    -- Universality identifies both image subgroups with `⊥`.
    rw [fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp b e,
      fundamentalGroup_mapOfEq_range_eq_bot_of_universal hp' b e']
  refine ⟨asIso h, ?_, ?_⟩
  · -- The underlying morphism of `asIso h` is exactly `h`, so it preserves the chosen point.
    simpa [CategoryTheory.asIso_hom] using hh
  · intro i hi
    have hi_hom : i.hom = h := huniq i.hom (by simpa using hi)
    -- Uniqueness of the morphism forces uniqueness of the over-category isomorphism.
    apply Iso.ext
    simpa [CategoryTheory.asIso_hom] using hi_hom

/-- Corollary 3.7.7 (2): if the source total space is locally path connected, then a universal
covering space over `B` maps uniquely to any other covering space over `B` once a point of the
target fiber over the chosen basepoint is specified. -/
-- Proof sketch: use Theorem 3.7.6 with source `p` universal. The induced subgroup
-- `(FundamentalGroup.mapOfEq p e.2).range` is trivial because the total space of `p` is simply
-- connected, so the subgroup inclusion hypothesis holds automatically for every target covering.
theorem universalCoveringSpace_existsUnique_morphism_to_coveringSpace
    (hp : IsUniversalCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (b : B) (e : p ⁻¹' {b}) (e' : p' ⁻¹' {b}) :
    ∃! h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'), h.left e.1 = e'.1 := by
  -- Reuse the local helper implementing the subgroup criterion route from Theorem 3.7.6.
  simpa using existsUnique_point_preserving_morphism_to_coveringSpace hp hp' b e e'

end IsUniversalCoveringMap
