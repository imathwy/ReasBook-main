import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Lemma_1_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Proposition_3_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_5_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_7_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open CategoryTheory.Functor.IsCovering
open scoped FundamentalGroup

universe u

namespace IsPathConnectedCoveringMap

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {p' : C(E', B)}

/-- The induced morphism on fundamental groupoids from a morphism of covering spaces over `B`
commutes with the covering projections to `Π(B)`. -/
-- Proof sketch: apply `TopCat.Hom.hom` to the commutative triangle `Over.w h`, then use the
-- functoriality of `FundamentalGroupoid.map` and finally pass to `Cat` via `Functor.toCatHom`.
theorem fundamentalGroupoidMapHom_comm
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    (FundamentalGroupoid.map h.left.hom).toCatHom ≫ hp'.fundamentalGroupoidMap.toCatHom =
      hp.fundamentalGroupoidMap.toCatHom := by
  -- First rewrite the over-category commutative triangle as an equality of continuous maps.
  have hcomm : p'.comp h.left.hom = p := by
    ext x
    simpa [ContinuousMap.comp_apply] using Over.w_apply h x
  have hcomp :
      (FundamentalGroupoid.map h.left.hom).toCatHom ≫ hp'.fundamentalGroupoidMap.toCatHom =
        (FundamentalGroupoid.map (p'.comp h.left.hom)).toCatHom := by
    -- Functoriality of `FundamentalGroupoid.map` turns composition of maps
    -- into composition of functors.
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg Functor.toCatHom (FundamentalGroupoid.map_comp p' h.left.hom).symm
  have hmap :
      (FundamentalGroupoid.map (p'.comp h.left.hom)).toCatHom =
        hp.fundamentalGroupoidMap.toCatHom := by
    -- Replacing `p' ∘ h` by `p` finishes the comparison on the base groupoid.
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg Functor.toCatHom (congrArg FundamentalGroupoid.map hcomm)
  exact hcomp.trans hmap

/-- A morphism of covering spaces over `B` induces a morphism of the associated coverings over
`Π(B)`. -/
noncomputable def toFundamentalGroupoidCoveringHom
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    Over.mk hp.fundamentalGroupoidMap.toCatHom ⟶ Over.mk hp'.fundamentalGroupoidMap.toCatHom :=
  Over.homMk
    (FundamentalGroupoid.map h.left.hom).toCatHom
    (fundamentalGroupoidMapHom_comm hp hp' h)

/-- The underlying functor of `toFundamentalGroupoidCoveringHom hp hp' h` is
`FundamentalGroupoid.map h.left.hom`. -/
@[simp] theorem toFundamentalGroupoidCoveringHom_toFunctor
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor =
      FundamentalGroupoid.map h.left.hom :=
  rfl

/-- Helper for Corollary 3.7.8: membership in the topological image subgroup at the chosen source
basepoint implies membership in the corresponding transported categorical subgroup. -/
private theorem fundamental_groupoid_source_mem_of_mapOfEq_mem
    (hp : IsPathConnectedCoveringMap p) (e₀ : E)
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ (FundamentalGroup.mapOfEq p rfl).range) :
    let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
      ⟨FundamentalGroupoid.mk e₀, rfl⟩
    γ ∈ ξ.2 ▸ (Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range := by
  -- Rewrite transported membership to the literal basepoint and use the same loop witness.
  dsimp
  have hγ' :
      eqToHom rfl ≫ γ ≫ eqToHom rfl.symm ∈
        (Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e₀)).range := by
    rcases MonoidHom.mem_range.mp hγ with ⟨δ, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨δ, by
      change (Functor.mapVertexGroup (FundamentalGroupoid.map p) (FundamentalGroupoid.mk e₀)) δ =
        eqToHom rfl ≫ (FundamentalGroup.mapOfEq p rfl) δ ≫ eqToHom rfl.symm
      rw [← FundamentalGroup.map_eq_mapOfEq_rfl e₀]
      simp⟩
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
    ⟨FundamentalGroupoid.mk e₀, rfl⟩
  simpa [ξ] using hγ'

/-- Helper for Corollary 3.7.8: membership in the transported categorical subgroup at a target
fiber point implies membership in the topological image subgroup at the corresponding lifted point.
-/
private theorem mapOfEq_mem_of_fundamental_groupoid_target_mem
    (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ ξ'.2 ▸ (Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range) :
    γ ∈ (FundamentalGroup.mapOfEq p'
      (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  -- Unpack the categorical fiber point and conjugate the witness through the transport equality.
  rcases ξ' with ⟨⟨x⟩, hx⟩
  have hx' : p' x = p e₀ := by
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg FundamentalGroupoid.as hx
  have hγ' :
      eqToHom hx ≫ γ ≫ eqToHom hx.symm ∈
        (Functor.mapVertexGroup hp'.fundamentalGroupoidMap (FundamentalGroupoid.mk x)).range := by
    exact
      (mapVertexGroup_range_transport_iff hx γ).1 hγ
  rcases MonoidHom.mem_range.mp hγ' with ⟨δ, hδ⟩
  refine MonoidHom.mem_range.mpr ⟨δ, ?_⟩
  have hmk : congrArg FundamentalGroupoid.mk hx' = hx := by
    apply Subsingleton.elim
  change eqToHom (congrArg FundamentalGroupoid.mk hx').symm ≫
      (Functor.mapVertexGroup hp'.fundamentalGroupoidMap (FundamentalGroupoid.mk x)) δ ≫
      eqToHom (congrArg FundamentalGroupoid.mk hx') = γ
  rw [hmk]
  simpa [Category.assoc] using congrArg (fun η ↦ eqToHom hx.symm ≫ η ≫ eqToHom hx) hδ

/-- Helper for Corollary 3.7.8: the subgroup inclusion produced by the covering-groupoid lift
criterion rewrites to the corresponding inclusion on ordinary fundamental groups at the matching
topological fiber point. -/
private theorem subgroup_condition_topological_of_groupoid
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (k : Over.mk hp.fundamentalGroupoidMap.toCatHom ⟶ Over.mk hp'.fundamentalGroupoidMap.toCatHom)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (hξ :
      let kF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' := k.left.toFunctor
      ξ'.1 = kF.obj (FundamentalGroupoid.mk e₀)) :
    (FundamentalGroup.mapOfEq p rfl).range ≤
      (FundamentalGroup.mapOfEq p'
        (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  let kF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' := k.left.toFunctor
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
    ⟨FundamentalGroupoid.mk e₀, rfl⟩
  have hξ' : ξ'.1 = kF.obj (FundamentalGroupoid.mk e₀) := by
    simpa [kF] using hξ
  have hk : kF ⋙ hp'.fundamentalGroupoidMap = hp.fundamentalGroupoidMap := by
    -- The over-category relation says the induced functors commute with the projection to `Π(B)`.
    simpa using congrArg (fun F ↦ F.toFunctor) (Over.w k)
  have hsub_groupoid :
      ξ.2 ▸ (Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range ≤
        ξ'.2 ▸ (Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range := by
    -- Apply the covering-groupoid lifting criterion at the chosen source point `ξ`.
    simpa [ξ, kF, hξ'] using
      (Functor.mapVertexGroup_range_le_of_lift ξ.1 ξ' hk hξ'.symm)
  intro γ hγ
  have hγ_source :
      γ ∈ ξ.2 ▸ (Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range :=
    fundamental_groupoid_source_mem_of_mapOfEq_mem hp e₀ γ hγ
  have hγ_target :
      γ ∈ ξ'.2 ▸ (Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range :=
    hsub_groupoid hγ_source
  -- Convert the transported categorical target membership back into the topological subgroup.
  exact mapOfEq_mem_of_fundamental_groupoid_target_mem hp' e₀ ξ' γ hγ_target

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- Corollary 3.7.8: the fundamental groupoid functor induces a bijection between morphisms of
covering spaces over `B` and morphisms of the induced covering functors over `Π(B)`. -/
-- Proof sketch: map a covering-space morphism `h` to `toFundamentalGroupoidCoveringHom hp hp' h`.
-- For any chosen `e : E`, both Theorem 3.7.6 and Theorem 3.5.6 classify morphisms sending `e` to
-- a prescribed point of the target fiber by the same subgroup-inclusion condition, using
-- Proposition 3.3.4 to view `hp.fundamentalGroupoidMap` and `hp'.fundamentalGroupoidMap` as
-- covering functors. Hence the induced map on morphism sets is both injective and surjective.
theorem toFundamentalGroupoidCoveringHom_bijective
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') :
    Function.Bijective (toFundamentalGroupoidCoveringHom hp hp') := by
  constructor
  · intro h₁ h₂ hk
    apply Over.OverMorphism.ext
    ext x
    -- Equality of induced groupoid maps forces equality on every object `mk x`.
    let objAt :
        (Over.mk hp.fundamentalGroupoidMap.toCatHom ⟶
          Over.mk hp'.fundamentalGroupoidMap.toCatHom) → FundamentalGroupoid E' := fun m ↦
      let mF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' := m.left.toFunctor
      mF.obj (FundamentalGroupoid.mk x)
    have hobj :
        objAt (toFundamentalGroupoidCoveringHom hp hp' h₁) =
          objAt (toFundamentalGroupoidCoveringHom hp hp' h₂) := by
      simpa [objAt] using congrArg objAt hk
    exact congrArg FundamentalGroupoid.as hobj
  · intro k
    -- Work at one chosen point of the source cover and compare the two
    -- classification theorems there.
    letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
      refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
      intro α F x y
      ext
      exact CategoryTheory.Discrete.eq_of_hom <|
        F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
    obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
    let e : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩
    let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
      ⟨FundamentalGroupoid.mk e₀, rfl⟩
    let kF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' := k.left.toFunctor
    let ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) := by
      refine ⟨kF.obj ξ.1, ?_⟩
      -- The over-category relation for `k` shows that the image still lies over `mk (p e₀)`.
      have hobj := congrArg
        (fun F : FundamentalGroupoid E ⥤ FundamentalGroupoid B ↦ F.obj ξ.1)
        (congrArg (fun F ↦ F.toFunctor) (Over.w k))
      simpa [ξ, kF] using hobj
    let e' : p' ⁻¹' {p e₀} := hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ'
    have hsub_groupoid :=
      -- The given morphism of covering functors is already a lift, so it yields
      -- the subgroup inclusion.
      Functor.mapVertexGroup_range_le_of_lift
        ξ.1 ξ' (by
          simpa using congrArg (fun F ↦ F.toFunctor) (Over.w k)) rfl
    rcases
        (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
          hp' (p e₀) e e').mpr
          (subgroup_condition_topological_of_groupoid hp hp' e₀ k ξ' (by
            simp [kF, ξ, ξ'])) with
      ⟨h, hh, _⟩
    refine ⟨h, ?_⟩
    have hξ' : FundamentalGroupoid.mk e'.1 = ξ'.1 := by
      -- Re-expanding the fiber equivalence identifies the target categorical point with `ξ'`.
      have hξ'_eq :
          (hp'.fundamentalGroupoidMapFiberEquiv (p e₀)).symm e' = ξ' := by
        simp [e', ξ']
      exact congrArg Subtype.val hξ'_eq
    have hh_groupoid :
        let hF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' :=
          (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor
        hF.obj ξ.1 = ξ'.1 := by
      -- The constructed topological map hits the prescribed fiber point, so its
      -- induced functor does too.
      let hF : FundamentalGroupoid E ⥤ FundamentalGroupoid E' :=
        (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor
      have hh_to_target :
          hF.obj ξ.1 = FundamentalGroupoid.mk e'.1 := by
        change FundamentalGroupoid.mk (h.left.hom e.1) = FundamentalGroupoid.mk e'.1
        exact congrArg FundamentalGroupoid.mk hh
      simpa [hF] using hh_to_target.trans hξ'
    rcases
        (existsUnique_map_iff_mapVertexGroup_range_le
          hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e₀)) ξ ξ').mpr
          (by simpa using hsub_groupoid) with
      ⟨g, hg, huniqg⟩
    have hk_eq : k = g := huniqg k (by
      simp [kF, ξ'] )
    have hh_eq : toFundamentalGroupoidCoveringHom hp hp' h = g := by
      exact huniqg _ (by simpa using hh_groupoid)
    exact hh_eq.trans hk_eq.symm

end

end IsPathConnectedCoveringMap
