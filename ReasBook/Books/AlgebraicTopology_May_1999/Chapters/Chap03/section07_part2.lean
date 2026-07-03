import Mathlib
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_7_8 (from Chap03) -/
open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open CategoryTheory.Functor.IsCovering
open scoped FundamentalGroup

universe u

namespace IsPathConnectedCoveringMap

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {p' : C(E', B)}

/-- The induced morphism on fundamental groupoids of a morphism of covering spaces over `B`. -/
noncomputable def fundamentalGroupoidMapHom
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    Cat.of (FundamentalGroupoid E) ⟶ Cat.of (FundamentalGroupoid E') :=
  (FundamentalGroupoid.map h.left.hom).toCatHom

/-- A path-connected covering space over `B`, viewed as the induced functor over `Π(B)`. -/
noncomputable def toFundamentalGroupoidCovering (hp : IsPathConnectedCoveringMap p) :
    Over (Cat.of (FundamentalGroupoid B)) :=
  Over.mk hp.fundamentalGroupoidMap.toCatHom

/-- The induced morphism on fundamental groupoids from a morphism of covering spaces over `B`
commutes with the covering projections to `Π(B)`. -/
-- Proof sketch: apply `TopCat.Hom.hom` to the commutative triangle `Over.w h`, then use the
-- functoriality of `FundamentalGroupoid.map` and finally pass to `Cat` via `Functor.toCatHom`.
theorem fundamentalGroupoidMapHom_comm
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    fundamentalGroupoidMapHom h ≫ hp'.fundamentalGroupoidMap.toCatHom =
      hp.fundamentalGroupoidMap.toCatHom := by
  -- First rewrite the over-category commutative triangle as an equality of continuous maps.
  have hcomm : p'.comp h.left.hom = p := by
    ext x
    have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hx
  have hcomp :
      fundamentalGroupoidMapHom h ≫ hp'.fundamentalGroupoidMap.toCatHom =
        (FundamentalGroupoid.map (p'.comp h.left.hom)).toCatHom := by
    -- Functoriality of `FundamentalGroupoid.map` turns composition of maps into composition of functors.
    simpa [fundamentalGroupoidMapHom, IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
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
    hp.toFundamentalGroupoidCovering ⟶ hp'.toFundamentalGroupoidCovering :=
  Over.homMk (fundamentalGroupoidMapHom h) (fundamentalGroupoidMapHom_comm hp hp' h)

/-- Helper for Corollary 3.7.8: when the target basepoint is definitionally unchanged, the
fundamental-group map agrees with `mapOfEq`. -/
private theorem fundamental_group_map_eq_mapOfEq_rfl_local {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- Reduce both descriptions to the same formula on loop representatives.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Corollary 3.7.8: membership in the topological image subgroup at the chosen source
basepoint implies membership in the corresponding transported categorical subgroup. -/
private theorem fundamental_groupoid_source_mem_of_mapOfEq_mem
    (hp : IsPathConnectedCoveringMap p) (e₀ : E)
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ (FundamentalGroup.mapOfEq p rfl).range) :
    let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
      ⟨FundamentalGroupoid.mk e₀, rfl⟩
    γ ∈ ξ.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range := by
  -- Rewrite transported membership to the literal basepoint and use the same loop witness.
  dsimp
  have hγ' :
      eqToHom rfl ≫ γ ≫ eqToHom rfl.symm ∈
        (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e₀)).range := by
    rcases MonoidHom.mem_range.mp hγ with ⟨δ, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨δ, by
      change (CategoryTheory.Functor.mapVertexGroup (FundamentalGroupoid.map p) (FundamentalGroupoid.mk e₀)) δ =
        eqToHom rfl ≫ (FundamentalGroup.mapOfEq p rfl) δ ≫ eqToHom rfl.symm
      rw [← fundamental_group_map_eq_mapOfEq_rfl_local (f := p) (x := e₀)]
      simp⟩
  exact
    (mapVertexGroup_range_transport_iff
      (p := hp.fundamentalGroupoidMap) (e := FundamentalGroupoid.mk e₀) (h := rfl) γ).2 hγ'

/-- Helper for Corollary 3.7.8: membership in the transported categorical subgroup at a target
fiber point implies membership in the topological image subgroup at the corresponding lifted point.
-/
private theorem mapOfEq_mem_of_fundamental_groupoid_target_mem
    (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (γ : FundamentalGroup B (p e₀))
    (hγ : γ ∈ ξ'.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range) :
    γ ∈ (FundamentalGroup.mapOfEq p'
      (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  -- Unpack the categorical fiber point and conjugate the witness through the transport equality.
  rcases ξ' with ⟨⟨x⟩, hx⟩
  have hx' : p' x = p e₀ := by
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using congrArg FundamentalGroupoid.as hx
  have hγ' :
      eqToHom hx ≫ γ ≫ eqToHom hx.symm ∈
        (CategoryTheory.Functor.mapVertexGroup hp'.fundamentalGroupoidMap (FundamentalGroupoid.mk x)).range := by
    exact
      (mapVertexGroup_range_transport_iff
        (p := hp'.fundamentalGroupoidMap) (e := FundamentalGroupoid.mk x) (h := hx) γ).1 hγ
  rcases MonoidHom.mem_range.mp hγ' with ⟨δ, hδ⟩
  refine MonoidHom.mem_range.mpr ⟨δ, ?_⟩
  have hmk : congrArg FundamentalGroupoid.mk hx' = hx := by
    apply Subsingleton.elim
  change eqToHom (congrArg FundamentalGroupoid.mk hx').symm ≫
      (CategoryTheory.Functor.mapVertexGroup hp'.fundamentalGroupoidMap (FundamentalGroupoid.mk x)) δ ≫
      eqToHom (congrArg FundamentalGroupoid.mk hx') = γ
  rw [hmk]
  simpa [Category.assoc] using congrArg (fun η ↦ eqToHom hx.symm ≫ η ≫ eqToHom hx) hδ

/-- Helper for Corollary 3.7.8: the subgroup inclusion produced by the covering-groupoid lift
criterion rewrites to the corresponding inclusion on ordinary fundamental groups at the matching
topological fiber point. -/
theorem subgroup_condition_topological_of_groupoid
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (e₀ : E)
    (k : Over.mk hp.fundamentalGroupoidMap.toCatHom ⟶ Over.mk hp'.fundamentalGroupoidMap.toCatHom)
    (ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)))
    (hξ : ξ'.1 = k.left.toFunctor.obj (FundamentalGroupoid.mk e₀)) :
    (FundamentalGroup.mapOfEq p rfl).range ≤
      (FundamentalGroup.mapOfEq p' (hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ').2).range := by
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) :=
    ⟨FundamentalGroupoid.mk e₀, rfl⟩
  have hk :
      k.left.toFunctor ⋙ hp'.fundamentalGroupoidMap = hp.fundamentalGroupoidMap := by
    -- The over-category relation says the induced functors commute with the projection to `Π(B)`.
    simpa using congrArg (fun F ↦ F.toFunctor) (Over.w k)
  have hsub_groupoid :
      ξ.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range ≤
        ξ'.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range := by
    -- Apply the covering-groupoid lifting criterion at the chosen source point `ξ`.
    simpa [ξ, hξ] using
      (CategoryTheory.Functor.mapVertexGroup_range_le_of_lift
        (p := hp'.fundamentalGroupoidMap) (f := hp.fundamentalGroupoidMap)
        (g := k.left.toFunctor) ξ.1 ξ' hk hξ.symm)
  intro γ hγ
  have hγ_source :
      γ ∈ ξ.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap ξ.1).range :=
    fundamental_groupoid_source_mem_of_mapOfEq_mem hp e₀ γ hγ
  have hγ_target :
      γ ∈ ξ'.2 ▸ (CategoryTheory.Functor.mapVertexGroup hp'.fundamentalGroupoidMap ξ'.1).range :=
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
    have hobj :
        (toFundamentalGroupoidCoveringHom hp hp' h₁).left.toFunctor.obj
            (FundamentalGroupoid.mk x) =
          (toFundamentalGroupoidCoveringHom hp hp' h₂).left.toFunctor.obj
            (FundamentalGroupoid.mk x) := by
      simpa using
        congrArg
          (fun k : hp.toFundamentalGroupoidCovering ⟶ hp'.toFundamentalGroupoidCovering ↦
            k.left.toFunctor.obj (FundamentalGroupoid.mk x))
          hk
    exact congrArg FundamentalGroupoid.as hobj
  · intro k
    -- Work at one chosen point of the source cover and compare the two classification theorems there.
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
    let ξ' : hp'.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e₀)) := by
      refine ⟨k.left.toFunctor.obj ξ.1, ?_⟩
      have hw : k.left.toFunctor ⋙ hp'.fundamentalGroupoidMap = hp.fundamentalGroupoidMap := by
        exact congrArg Cat.Hom.toFunctor (Over.w k)
      simpa [ξ] using congrArg (fun F : FundamentalGroupoid E ⥤ FundamentalGroupoid B ↦ F.obj ξ.1) hw
    let e' : p' ⁻¹' {p e₀} := hp'.fundamentalGroupoidMapFiberEquiv (p e₀) ξ'
    have hsub_groupoid :=
      -- The given morphism of covering functors is already a lift, so it yields the subgroup inclusion.
      CategoryTheory.Functor.mapVertexGroup_range_le_of_lift
        (p := hp'.fundamentalGroupoidMap) (f := hp.fundamentalGroupoidMap)
        (g := k.left.toFunctor) ξ.1 ξ' (by
          exact congrArg Cat.Hom.toFunctor (Over.w k)) rfl
    rcases
        (existsUnique_coveringSpaceMorphism_iff_fundamentalGroup_range_le
          hp hp' (p e₀) e e').mpr
          (subgroup_condition_topological_of_groupoid hp hp' e₀ k ξ' (by
            change k.left.toFunctor.obj ξ.1 = k.left.toFunctor.obj (FundamentalGroupoid.mk e₀)
            simpa [ξ])) with
      ⟨h, hh, _⟩
    refine ⟨h, ?_⟩
    have hξ' : FundamentalGroupoid.mk e'.1 = ξ'.1 := by
      -- Re-expanding the fiber equivalence identifies the target categorical point with `ξ'`.
      have hξ'_eq :
          (hp'.fundamentalGroupoidMapFiberEquiv (p e₀)).symm e' = ξ' := by
        simpa [e']
      exact congrArg Subtype.val hξ'_eq
    have hh_groupoid :
        (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor.obj ξ.1 = ξ'.1 := by
      -- The constructed topological map hits the prescribed fiber point, so its induced functor does too.
      have hh_to_target :
          (toFundamentalGroupoidCoveringHom hp hp' h).left.toFunctor.obj ξ.1 =
            FundamentalGroupoid.mk e'.1 := by
        change FundamentalGroupoid.mk (h.left.hom e.1) = FundamentalGroupoid.mk e'.1
        exact congrArg FundamentalGroupoid.mk hh
      exact hh_to_target.trans hξ'
    rcases
        (existsUnique_map_iff_mapVertexGroup_range_le
          (p := hp.fundamentalGroupoidMap) (p' := hp'.fundamentalGroupoidMap)
          hp'.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e₀)) ξ ξ').mpr
          (by simpa using hsub_groupoid) with
      ⟨g, hg, huniqg⟩
    have hk_eq : k = g := huniqg k (by simpa [ξ'] using rfl)
    have hh_eq : toFundamentalGroupoidCoveringHom hp hp' h = g := by
      exact huniqg _ (by simpa using hh_groupoid)
    exact hh_eq.trans hk_eq.symm

end

end IsPathConnectedCoveringMap

/-! ### Theorem_3_7_9 (from Chap03) -/
open CategoryTheory FundamentalGroupoid
open CategoryTheory.Functor.IsCovering
open scoped FundamentalGroup

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)} {p' : C(E', B)}

/-- A morphism of covering spaces over `B` sends the fiber of `p` over `b` into the fiber of `p'`
over `b`. -/
-- Proof sketch: apply the commutative-triangle relation `Over.w h` to the chosen point of the
-- fiber and rewrite with the defining equation of that fiber point.
theorem coveringSpaceHom_obj_mem_fiber {b : B}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    p' (h.left.hom e.1) = b := by
  -- Evaluate the over-category commutative triangle on the chosen fiber point.
  have hcomm : p'.comp h.left.hom = p := by
    ext x
    have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
    simpa [ContinuousMap.comp_apply] using hx
  have hObj : p' (h.left.hom e.1) = p e.1 := by
    simpa [ContinuousMap.comp_apply] using congrArg (fun f : C(E, B) ↦ f e.1) hcomm
  exact hObj.trans e.2

/-- Restriction of a morphism of covering spaces over `B` to the fiber over `b`. -/
def coveringSpaceHomToFiberFun (b : B) :
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      p ⁻¹' {b} → p' ⁻¹' {b} :=
  fun h e ↦ ⟨h.left.hom e.1, coveringSpaceHom_obj_mem_fiber h e⟩

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]
variable [PathConnectedSpace E'] [LocPathConnectedSpace E']

/-- The identity loop acts trivially on the fiber over `b` via monodromy. -/
-- Proof sketch: this is the identity law for the monodromy functor of the covering map.
theorem fiberMonodromy_one (hp : IsPathConnectedCoveringMap p) (b : B) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (1 : FundamentalGroup B b).toPath x = x := by
  -- The constant loop has trivial monodromy.
  simpa using congrFun (hp.isCoveringMap.monodromy_refl (x := b)) x

/-- Monodromy along loops in `π₁(B, b)` defines a left action on the fiber over `b`. -/
-- Proof sketch: `monodromyFunctor` is a functor, so it turns composition in
-- `FundamentalGroupoid B` into function composition on the fiber, while
-- `loop_homotopy_mul_eq_trans` identifies multiplication in `π₁(B,b)` with the corresponding
-- loop-class composition order.
theorem fiberMonodromy_mul (hp : IsPathConnectedCoveringMap p) (b : B)
    (γ₁ γ₂ : FundamentalGroup B b) (x : p ⁻¹' {b}) :
    hp.isCoveringMap.monodromy (γ₁ * γ₂).toPath x =
      hp.isCoveringMap.monodromy γ₁.toPath
        (hp.isCoveringMap.monodromy γ₂.toPath x) := by
  -- Route correction: `FundamentalGroup B b` uses the `End`-based multiplication on loop classes,
  -- so the correct ordinary-fiber action is by direct monodromy, not by inverse loops.
  change hp.isCoveringMap.monodromy
      ((γ₁.toPath * γ₂.toPath : Path.Homotopic.Quotient b b)) x =
    hp.isCoveringMap.monodromy γ₁.toPath
      (hp.isCoveringMap.monodromy γ₂.toPath x)
  -- Rewrite the group product as path-class concatenation, then apply monodromy functoriality.
  rw [loop_homotopy_mul_eq_trans]
  simpa using hp.isCoveringMap.monodromy_trans_apply γ₂.toPath γ₁.toPath x

/-- The monodromy action of `π₁(B, b)` on the fiber over `b`, obtained by transporting the
canonical fiber-translation action of the induced covering functor on `Π(B)` across the fiber
equivalence of Proposition 3.3.4. -/
@[reducible] noncomputable def fiberMonodromyMulAction
    (hp : IsPathConnectedCoveringMap p) (b : B) :
    MulAction (FundamentalGroup B b) (p ⁻¹' {b}) where
  smul γ x := hp.fiberTranslationMap γ.toPath x
  one_smul := by
    intro x
    -- The identity element acts by monodromy along the constant loop.
    change hp.fiberTranslationMap (1 : FundamentalGroup B b).toPath x = x
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_one hp b x
  mul_smul := by
    intro γ₁ γ₂ x
    -- Multiplication in `π₁(B, b)` matches composition of the direct monodromy maps.
    change hp.fiberTranslationMap (γ₁ * γ₂).toPath x =
      hp.fiberTranslationMap γ₁.toPath (hp.fiberTranslationMap γ₂.toPath x)
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    rw [hp.fiberTranslationMap_eq_monodromy]
    exact fiberMonodromy_mul hp b γ₁ γ₂ x

/-- Helper for Theorem 3.7.9: restriction to the ordinary fiber agrees pointwise with the
categorical restriction map on the induced covering functors over `Π(B)`, transported across the
canonical fiber equivalence. -/
theorem coveringSpaceHomToFiberFun_eq_groupoidFiberMap
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (e : p ⁻¹' {b}) :
    coveringSpaceHomToFiberFun b h e =
      hp'.fundamentalGroupoidMapFiberEquiv b
        (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
          (hp.toFundamentalGroupoidCoveringHom hp' h)
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm e)) := by
  -- Both sides are the image of `e.1` under the same underlying map of total spaces.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 3.7.9: transporting categorical fiber translation along the loop `γ`
through the canonical fiber equivalence recovers the ordinary fiber translation map. -/
theorem fundamentalGroupoidMapFiberEquiv_fiberTranslation
    (hp : IsPathConnectedCoveringMap p) (b : B) (γ : FundamentalGroup B b)
    (ξ : hp.fundamentalGroupoidMap.Fiber (mk b)) :
    hp.fundamentalGroupoidMapFiberEquiv b
        (CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) =
      hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
  -- This is exactly how `fiberTranslationMap` was defined in Example 3.3.9.
  apply Subtype.ext
  rfl

/-- Restriction to the fiber over `b` commutes with the monodromy action of `π₁(B, b)`. -/
-- Proof sketch: apply `mapOfCoveringsToFiberFun_comm` to the induced morphism of covering
-- functors on fundamental groupoids from Corollary 3.7.8, then transport the resulting
-- equivariance statement across the fiber equivalences of Proposition 3.3.4 and identify fiber
-- translation with monodromy using Example 3.3.9.
theorem coveringSpaceHomToFiberFun_comm
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (γ : FundamentalGroup B b)
    (e : p ⁻¹' {b}) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    coveringSpaceHomToFiberFun b h (γ • e) = γ • coveringSpaceHomToFiberFun b h e := by
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp'.fundamentalGroupoidMap_isCovering (mk b)
  let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
  let δ : mk b ⟶ mk b := (γ⁻¹).toPath
  have hinv_toPath :
      δ⁻¹ = γ.toPath := by
    -- Undoing the inverse-loop scalar recovers the direct loop class on `Π(B)`.
    change Path.Homotopic.Quotient.symm ((γ⁻¹).toPath) = γ.toPath
    change Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.symm γ.toPath) = γ.toPath
    refine Quotient.inductionOn γ.toPath ?_
    intro p
    change Path.Homotopic.Quotient.mk (p.symm.symm) = Path.Homotopic.Quotient.mk p
    simp
  have hsource :
      δ • ξ =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- The source-facing categorical action uses inverse loops, so acting by `γ⁻¹` translates
    -- exactly by the direct loop `γ`.
    simpa [hinv_toPath] using
      (CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := mk b) δ ξ)
  have htarget :
      (δ •
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp'.fundamentalGroupoidMap_isCovering γ.toPath
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
    -- The same inverse-loop convention governs the target categorical fiber.
    simpa [hinv_toPath] using
      (CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp'.fundamentalGroupoidMap_isCovering)
        (b := mk b) δ
        (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
          (hp.toFundamentalGroupoidCoveringHom hp' h) ξ))
  have hξsmul :
      (hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e) =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering γ.toPath ξ := by
    -- Transport the monodromy action back through the canonical fiber equivalence.
    apply (hp.fundamentalGroupoidMapFiberEquiv b).injective
    calc
      hp.fundamentalGroupoidMapFiberEquiv b
          ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e)) = γ • e := by
            simp
      _ = hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fiberTranslationMap γ.toPath e =
              hp.fiberTranslationMap γ.toPath (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            simp [ξ]
      _ =
          hp.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ) := by
            simpa [ξ] using
              (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b γ ξ).symm
  -- Apply equivariance on categorical fibers and transport the result back to ordinary fibers.
  calc
    coveringSpaceHomToFiberFun b h (γ • e) =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            ((hp.fundamentalGroupoidMapFiberEquiv b).symm (γ • e))) := by
          simpa using coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h (γ • e)
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering γ.toPath ξ)) := by
          rw [hξsmul]
    _ =
        hp'.fundamentalGroupoidMapFiberEquiv b
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp'.fundamentalGroupoidMap_isCovering γ.toPath
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          rw [← hsource]
          rw [CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun_comm
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) δ ξ]
          exact congrArg (hp'.fundamentalGroupoidMapFiberEquiv b) htarget
    _ =
        hp'.fiberTranslationMap γ.toPath
          (hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)) := by
          exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b γ
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ)
    _ = γ • coveringSpaceHomToFiberFun b h e := by
          rw [coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e]
          rfl

/-- Restriction to the fiber over `b` as a bundled `π₁(B, b)`-equivariant map. -/
def coveringSpaceHomToFiber
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    (Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) →
      (p ⁻¹' {b}) →[FundamentalGroup B b] (p' ⁻¹' {b}) :=
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  fun h ↦
    { toFun := coveringSpaceHomToFiberFun b h
      map_smul' := coveringSpaceHomToFiberFun_comm hp hp' b h }

/-- Theorem 3.7.9: for path-connected covering spaces `p : E → B` and `p' : E' → B`, restriction
to the fiber over `b` gives a bijection between morphisms of covering spaces over `B` and
`π₁(B, b)`-equivariant maps `(p ⁻¹' {b}) → (p' ⁻¹' {b})`. -/
-- Proof sketch: Corollary 3.7.8 identifies morphisms of covering spaces with morphisms of the
-- induced covering functors on fundamental groupoids. Then `mapOfCoveringsToFiber_bijective`,
-- applied to those induced covering functors at `mk b`, gives the canonical bijection on groupoid
-- fibers. Transport that bijection across `fundamentalGroupoidMapFiberEquiv` and use Example 3.3.9
-- to identify the transported action with monodromy on the topological fibers.
theorem coveringSpaceHomToFiber_bijective
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p') (b : B) :
    letI := fiberMonodromyMulAction hp b
    letI := fiberMonodromyMulAction hp' b
    Function.Bijective (coveringSpaceHomToFiber hp hp' b) := by
  letI := fiberMonodromyMulAction hp b
  letI := fiberMonodromyMulAction hp' b
  letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp.fundamentalGroupoidMap_isCovering (mk b)
  letI := CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
    hp'.fundamentalGroupoidMap_isCovering (mk b)
  have hTop := toFundamentalGroupoidCoveringHom_bijective hp hp'
  have hGroupoid :=
    CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber_bijective
      hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
  constructor
  · intro h₁ h₂ hEq
    have hFiberEq :
        CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₁) =
          CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h₂) := by
      apply MulActionHom.ext
      intro ξ
      let e : p ⁻¹' {b} := hp.fundamentalGroupoidMapFiberEquiv b ξ
      -- Equality on ordinary fibers transports to equality on categorical fibers.
      apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
      calc
        hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h₁) ξ) =
            coveringSpaceHomToFiber hp hp' b h₁ e := by
              simpa [coveringSpaceHomToFiber, e] using
                (coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₁ e).symm
        _ = coveringSpaceHomToFiber hp hp' b h₂ e := by
              exact congrArg (fun φ ↦ φ e) hEq
        _ =
            hp'.fundamentalGroupoidMapFiberEquiv b
              (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiberFun (mk b)
                (hp.toFundamentalGroupoidCoveringHom hp' h₂) ξ) := by
              simpa [coveringSpaceHomToFiber, e] using
                coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h₂ e
    exact hTop.1 (hGroupoid.1 hFiberEq)
  · intro φ
    let φcat :
        hp.fundamentalGroupoidMap.Fiber (mk b) →[(mk b ⟶ mk b)]
          hp'.fundamentalGroupoidMap.Fiber (mk b) :=
      { toFun := fun ξ ↦
          (hp'.fundamentalGroupoidMapFiberEquiv b).symm
            (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))
        map_smul' := fun γ ξ ↦ by
          -- Transport equivariance of `φ` through the canonical fiber equivalences.
          have htransport :
              hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ) =
                (fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ) := by
            change hp.fundamentalGroupoidMapFiberEquiv b
                (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                  hp.fundamentalGroupoidMap_isCovering γ⁻¹ ξ) =
              hp.fiberTranslationMap γ⁻¹ (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp b
              (γ := (γ⁻¹ : FundamentalGroup B b)) ξ
          have htransport' :
              (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
            change hp'.fiberTranslationMap γ⁻¹
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) =
              hp'.fundamentalGroupoidMapFiberEquiv b
                (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                  hp'.fundamentalGroupoidMap_isCovering γ⁻¹
                  ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))))
            exact (fundamentalGroupoidMapFiberEquiv_fiberTranslation hp' b
              (γ := (γ⁻¹ : FundamentalGroup B b))
              ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)))).symm
          apply (hp'.fundamentalGroupoidMapFiberEquiv b).injective
          calc
            hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)))) =
                φ (hp.fundamentalGroupoidMapFiberEquiv b (γ • ξ)) := by
                  simp
            _ = φ ((fiberMonodromyMulAction hp b).smul
                  (γ⁻¹ : FundamentalGroup B b) (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact congrArg φ htransport
            _ = (fiberMonodromyMulAction hp' b).smul
                  (γ⁻¹ : FundamentalGroup B b) (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ)) := by
                  exact φ.map_smul' (γ⁻¹ : FundamentalGroup B b)
                    (hp.fundamentalGroupoidMapFiberEquiv b ξ)
            _ =
                hp'.fundamentalGroupoidMapFiberEquiv b
                  (γ • (hp'.fundamentalGroupoidMapFiberEquiv b).symm
                    (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) := by
                  exact htransport' }
    obtain ⟨k, hk⟩ := hGroupoid.2 φcat
    obtain ⟨h, hh⟩ := hTop.2 k
    refine ⟨h, ?_⟩
    apply MulActionHom.ext
    intro e
    let ξ : hp.fundamentalGroupoidMap.Fiber (mk b) := (hp.fundamentalGroupoidMapFiberEquiv b).symm e
    have hkξ :
        CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
            hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
            (hp.toFundamentalGroupoidCoveringHom hp' h) ξ =
          φcat ξ := by
      simpa [hh] using congrArg (fun ψ ↦ ψ ξ) hk
    -- The categorical surjection lifts back to the required topological covering map.
    calc
      coveringSpaceHomToFiber hp hp' b h e =
          hp'.fundamentalGroupoidMapFiberEquiv b
            (CategoryTheory.Functor.IsCovering.mapOfCoveringsToFiber
              hp.fundamentalGroupoidMap_isCovering hp'.fundamentalGroupoidMap_isCovering (mk b)
              (hp.toFundamentalGroupoidCoveringHom hp' h) ξ) := by
            simpa [coveringSpaceHomToFiber, ξ] using
              coveringSpaceHomToFiberFun_eq_groupoidFiberMap hp hp' b h e
      _ = hp'.fundamentalGroupoidMapFiberEquiv b (φcat ξ) := by
            rw [hkξ]
      _ = φ e := by
            change hp'.fundamentalGroupoidMapFiberEquiv b
                ((hp'.fundamentalGroupoidMapFiberEquiv b).symm
                  (φ (hp.fundamentalGroupoidMapFiberEquiv b ξ))) = φ e
            simp [ξ]

end

end IsPathConnectedCoveringMap

/-! ### Definition_3_7_10 (from Chap03) -/
open CategoryTheory

universe u

/-
The core/canonical owner for the automorphism group of an object in a category is
`CategoryTheory.Aut X`.
-/
recall CategoryTheory.Aut {C : Type u} [Category C] (X : C) : Type _

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))

/- Definition 3.7.10: for a covering space `p : E → B`, the automorphism group `Aut(E)` is the
categorical automorphism group of the corresponding object `Over.mk (TopCat.ofHom p)` in the
over-category `Over (TopCat.of B)`. Equivalently, its elements are invertible maps of covering
spaces from `p` to itself over `B`. -/
#check (Aut (Over.mk (TopCat.ofHom p)))

/-! ### Corollary_3_7_11 (from Chap03) -/
open CategoryTheory FundamentalGroupoid
open CategoryTheory.Groupoid.CategoryTheory
open scoped FundamentalGroup QuotientGroup

universe u

variable {E B : Type u}
  [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : C(E, B)}

/-- Helper for Corollary 3.7.11: restricting the identity covering-space endomorphism to a fiber
gives the identity map. -/
theorem coveringSpaceHomToFiberFun_id (b : B) :
    coveringSpaceHomToFiberFun (p := p) (p' := p) b (𝟙 (Over.mk (TopCat.ofHom p))) = id := by
  funext x
  -- The identity over-morphism acts trivially on the chosen fiber point.
  apply Subtype.ext
  rfl

/-- Helper for Corollary 3.7.11: restricting a composite covering-space endomorphism to a fiber
composes the induced fiber maps in the same order. -/
theorem coveringSpaceHomToFiberFun_comp (b : B)
    (h₁ h₂ : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p)) :
    coveringSpaceHomToFiberFun (p := p) (p' := p) b (h₁ ≫ h₂) =
      coveringSpaceHomToFiberFun (p := p) (p' := p) b h₂ ∘
        coveringSpaceHomToFiberFun (p := p) (p' := p) b h₁ := by
  funext x
  -- Composition in the over-category composes the underlying maps on fiber points.
  apply Subtype.ext
  rfl

/-- The fiber map induced by a covering-space automorphism is bijective. -/
-- Proof sketch: the inverse automorphism of the covering induces the inverse map on the fiber
-- over `p e`, and the two composites are identities because `α.hom ≫ α.inv = 𝟙 _` and
-- `α.inv ≫ α.hom = 𝟙 _`.
theorem coveringSpaceAutFiberMap_bijective
    (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    Function.Bijective (coveringSpaceHomToFiberFun (p e) α.hom) := by
  let f := coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) α.hom
  let g := coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) α.inv
  have hleft : Function.LeftInverse g f := by
    intro x
    have hcomp : g ∘ f = id := by
      -- Restricting `α.hom ≫ α.inv = 𝟙` to the fiber gives a left inverse.
      calc
        g ∘ f =
            coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) (α.hom ≫ α.inv) := by
              symm
              exact coveringSpaceHomToFiberFun_comp (p := p) (p e) α.hom α.inv
        _ = id := by
              simpa [coveringSpaceHomToFiberFun_id (p := p)] using
                congrArg
                  (coveringSpaceHomToFiberFun (p := p) (p' := p) (p e))
                  α.hom_inv_id
    simpa [f, g] using congrFun hcomp x
  have hright : Function.RightInverse g f := by
    intro x
    have hcomp : f ∘ g = id := by
      -- Restricting `α.inv ≫ α.hom = 𝟙` to the fiber gives a right inverse.
      calc
        f ∘ g =
            coveringSpaceHomToFiberFun (p := p) (p' := p) (p e) (α.inv ≫ α.hom) := by
              symm
              exact coveringSpaceHomToFiberFun_comp (p := p) (p e) α.inv α.hom
        _ = id := by
              simpa [coveringSpaceHomToFiberFun_id (p := p)] using
                congrArg
                  (coveringSpaceHomToFiberFun (p := p) (p' := p) (p e))
                  α.inv_hom_id
    simpa [f, g] using congrFun hcomp x
  exact ⟨hleft.injective, hright.surjective⟩

/-- The permutation of the fiber over `p e` induced by a covering-space automorphism. -/
noncomputable def coveringSpaceAutFiberPerm
    (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    Equiv.Perm (p ⁻¹' {p e}) :=
  Equiv.ofBijective
    (coveringSpaceHomToFiberFun (p e) α.hom)
    (coveringSpaceAutFiberMap_bijective e α)

/-- The identity covering-space automorphism induces the identity permutation on the fiber. -/
-- Proof sketch: unfold `coveringSpaceAutFiberPerm`; the identity morphism of
-- `Over.mk (TopCat.ofHom p)` restricts to the identity map on each fiber.
theorem coveringSpaceAutFiberPerm_one (e : E) :
    coveringSpaceAutFiberPerm e (1 : Aut (Over.mk (TopCat.ofHom p))) = 1 := by
  ext x
  -- The identity covering automorphism restricts to the identity on the fiber.
  rfl

/-- The permutation induced on the fiber is multiplicative in the covering-space automorphism. -/
-- Proof sketch: restriction to the fiber respects composition of morphisms in the over-category,
-- so the permutation attached to `α * β` is the composite of the permutations attached to `α` and
-- `β`.
theorem coveringSpaceAutFiberPerm_mul
    (e : E) (α β : Aut (Over.mk (TopCat.ofHom p))) :
    coveringSpaceAutFiberPerm e (α * β) =
      coveringSpaceAutFiberPerm e α * coveringSpaceAutFiberPerm e β := by
  ext x
  -- Restriction to the fiber respects composition of covering automorphisms.
  rfl

/-- Helper for Corollary 3.7.11: membership in the ordinary image subgroup is equivalent to
membership of the corresponding loop morphism in the image of the induced functor on vertex
groups. -/
private theorem mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range
    (hp : IsPathConnectedCoveringMap p) (e : E) (γ : FundamentalGroup B (p e)) :
    γ ∈ (FundamentalGroup.map p e).range ↔
      γ.toPath ∈
        (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e)).range := by
  constructor
  · rintro ⟨δ, rfl⟩
    exact ⟨δ.toPath, rfl⟩
  · rintro ⟨δ, hδ⟩
    refine ⟨FundamentalGroup.fromPath δ, ?_⟩
    simpa using hδ

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- The monodromy action of `π₁(B, p e)` on the fiber over `p e` is pretransitive for a
path-connected covering space. -/
-- Proof sketch: given two points in the fiber over `p e`, choose a path in the path-connected
-- total space joining them. Projecting that path to `B` gives a loop at `p e`, and monodromy
-- along that loop sends the first point to the second.
theorem fiberMonodromyMulAction_isPretransitive
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    MulAction.IsPretransitive (FundamentalGroup B (p e)) (p ⁻¹' {p e}) := by
  letI := fiberMonodromyMulAction hp (p e)
  letI : CategoryTheory.IsConnected (FundamentalGroupoid E) := by
    refine CategoryTheory.IsConnected.of_any_functor_const_on_obj ?_
    intro α F x y
    ext
    exact CategoryTheory.Discrete.eq_of_hom <|
      F.map (show x ⟶ y from ⟦PathConnectedSpace.somePath x.as y.as⟧)
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  letI : MulAction.IsPretransitive
      (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction_isPretransitive
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  let x₀ : p ⁻¹' {p e} := hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀
  refine (MulAction.isPretransitive_iff_base (G := FundamentalGroup B (p e)) x₀).2 ?_
  intro x
  let ξ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    (hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x
  rcases (MulAction.isPretransitive_iff_base
      (G := FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀).mp
      inferInstance ξ with ⟨δ, hδ⟩
  refine ⟨FundamentalGroup.fromPath δ⁻¹, ?_⟩
  have hsmul :
      δ • ξ₀ =
        CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀ := by
    change δ • ξ₀ =
      (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
        hp.fundamentalGroupoidMap_isCovering).map δ⁻¹ ξ₀
    exact CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
      (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
        hp.fundamentalGroupoidMap_isCovering)
      (b := FundamentalGroupoid.mk (p e)) δ ξ₀
  have htransport :
      hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀) =
        hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀ := by
    change hp.fundamentalGroupoidMapFiberEquiv (p e)
        (CategoryTheory.Functor.IsCovering.fiberTranslationMap
          hp.fundamentalGroupoidMap_isCovering ((FundamentalGroup.fromPath δ⁻¹).toPath) ξ₀) =
      hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀
    exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e)
      (FundamentalGroup.fromPath δ⁻¹) ξ₀
  calc
    (FundamentalGroup.fromPath δ⁻¹) • x₀ =
        hp.fiberTranslationMap ((FundamentalGroup.fromPath δ⁻¹).toPath) x₀ := by
          rfl
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ⁻¹ ξ₀) := htransport.symm
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e) (δ • ξ₀) := by
          exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul.symm
    _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ := by rw [hδ]
    _ = x := by simp [ξ]

/-- The stabilizer of the distinguished fiber point `e` under monodromy is exactly the image of
`p_* : π₁(E, e) → π₁(B, p e)`. -/
-- Proof sketch: a loop in `B` fixes `e` under monodromy precisely when it lifts to a loop in `E`
-- based at `e`, which is the defining membership condition for the image subgroup
-- `(FundamentalGroup.map p e).range`.
theorem fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    MulAction.stabilizer (FundamentalGroup B (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) =
      (FundamentalGroup.map p e).range := by
  letI := fiberMonodromyMulAction hp (p e)
  letI : MulAction (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e))
      (hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e))) :=
    CategoryTheory.Functor.IsCovering.fiberTranslationMulAction
      hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk (p e))
  let x₀ : p ⁻¹' {p e} := ⟨e, rfl⟩
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (FundamentalGroupoid.mk (p e)) :=
    ⟨FundamentalGroupoid.mk e, rfl⟩
  have hstab_groupoid :
      MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ =
        (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e)).range := by
    -- The categorical fiber-translation stabilizer is the image of the upstairs vertex group.
    simpa [ξ₀] using
      (CategoryTheory.Functor.IsCovering.fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range
        hp.fundamentalGroupoidMap_isCovering (FundamentalGroupoid.mk e))
  ext γ
  let δ : FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e) := γ.toPath
  constructor
  · intro hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    have hsmul :
        δ⁻¹ • ξ₀ =
          CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ ξ₀ := by
      change δ⁻¹ • ξ₀ =
        (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering).map δ ξ₀
      simpa using CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := FundamentalGroupoid.mk (p e)) δ⁻¹ ξ₀
    have htransport :
        hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) =
          hp.fiberTranslationMap γ.toPath x₀ := by
      change hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering γ.toPath ξ₀) =
        hp.fiberTranslationMap γ.toPath x₀
      exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e) γ ξ₀
    have hfixed_groupoid : δ⁻¹ • ξ₀ = ξ₀ := by
      apply (hp.fundamentalGroupoidMapFiberEquiv (p e)).injective
      calc
        hp.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ₀) =
            hp.fundamentalGroupoidMapFiberEquiv (p e)
              (CategoryTheory.Functor.IsCovering.fiberTranslationMap
                hp.fundamentalGroupoidMap_isCovering δ ξ₀) := by
                  exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul
        _ = hp.fiberTranslationMap γ.toPath x₀ := htransport
        _ = γ • x₀ := by rfl
        _ = x₀ := hγ
        _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀ := by rfl
    have hmem_stab : δ⁻¹ ∈
        MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ := by
      -- Fixing the distinguished categorical fiber point is stabilizer membership.
      rwa [MulAction.mem_stabilizer_iff]
    have hmem_groupoid_inv : δ⁻¹ ∈
        (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e)).range := by
      -- Rewrite categorical stabilizer membership using the standard basepoint theorem.
      simpa [hstab_groupoid] using hmem_stab
    have hmem_ordinary_inv : γ⁻¹ ∈ (FundamentalGroup.map p e).range :=
      (mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range hp e (γ⁻¹)).2
        hmem_groupoid_inv
    -- Inverting the subgroup witness returns membership for `γ` itself.
    simpa using Subgroup.inv_mem ((FundamentalGroup.map p e).range) hmem_ordinary_inv
  · intro hγ
    rw [MulAction.mem_stabilizer_iff]
    have hmem_ordinary_inv : γ⁻¹ ∈ (FundamentalGroup.map p e).range := by
      -- The image subgroup is closed under inversion.
      simpa using Subgroup.inv_mem ((FundamentalGroup.map p e).range) hγ
    have hmem_groupoid_inv : δ⁻¹ ∈
        (CategoryTheory.Functor.mapVertexGroup hp.fundamentalGroupoidMap (FundamentalGroupoid.mk e)).range :=
      (mem_fundamentalGroup_range_iff_toPath_mem_mapVertexGroup_range hp e (γ⁻¹)).1
        hmem_ordinary_inv
    have hmem_stab : δ⁻¹ ∈
        MulAction.stabilizer (FundamentalGroupoid.mk (p e) ⟶ FundamentalGroupoid.mk (p e)) ξ₀ := by
      -- Transport the subgroup-membership statement back to the categorical stabilizer.
      simpa [hstab_groupoid] using hmem_groupoid_inv
    have hfixed_groupoid : δ⁻¹ • ξ₀ = ξ₀ := by
      rwa [MulAction.mem_stabilizer_iff] at hmem_stab
    have hsmul :
        δ⁻¹ • ξ₀ =
          CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering δ ξ₀ := by
      change δ⁻¹ • ξ₀ =
        (CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering).map δ ξ₀
      simpa using CategoryTheory.Functor.vertexGroupAction_smul_eq_map_inv
        (T := CategoryTheory.Functor.IsCovering.fiberTranslationFunctor
          hp.fundamentalGroupoidMap_isCovering)
        (b := FundamentalGroupoid.mk (p e)) δ⁻¹ ξ₀
    have htransport :
        hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) =
          hp.fiberTranslationMap γ.toPath x₀ := by
      change hp.fundamentalGroupoidMapFiberEquiv (p e)
          (CategoryTheory.Functor.IsCovering.fiberTranslationMap
            hp.fundamentalGroupoidMap_isCovering γ.toPath ξ₀) =
        hp.fiberTranslationMap γ.toPath x₀
      exact fundamentalGroupoidMapFiberEquiv_fiberTranslation hp (p e) γ ξ₀
    -- Transport the categorical fixed-point statement back to the ordinary monodromy action.
    calc
      γ • x₀ = hp.fiberTranslationMap γ.toPath x₀ := by rfl
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e)
            (CategoryTheory.Functor.IsCovering.fiberTranslationMap
              hp.fundamentalGroupoidMap_isCovering δ ξ₀) := htransport.symm
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e) (δ⁻¹ • ξ₀) := by
            exact congrArg (hp.fundamentalGroupoidMapFiberEquiv (p e)) hsmul.symm
      _ = hp.fundamentalGroupoidMapFiberEquiv (p e) ξ₀ := by rw [hfixed_groupoid]
      _ = x₀ := by rfl

/-- The permutation induced on the fiber by a covering-space automorphism is equivariant for the
monodromy action of `π₁(B, p e)`. -/
-- Proof sketch: `coveringSpaceHomToFiberFun_comm` from Theorem 3.7.9 gives the required
-- commutation relation with monodromy, which is exactly membership in the subgroup `gSetAut`.
theorem coveringSpaceAutFiberPerm_mem_gSetAut
    (hp : IsPathConnectedCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI := fiberMonodromyMulAction hp (p e)
    coveringSpaceAutFiberPerm e α ∈ gSetAut (FundamentalGroup B (p e)) (p ⁻¹' {p e}) := by
  letI := fiberMonodromyMulAction hp (p e)
  change coveringSpaceAutFiberPerm e α ∈
    Subgroup.centralizer
      (((MulAction.toPermHom (FundamentalGroup B (p e)) (p ⁻¹' {p e})).range :
        Set (Equiv.Perm (p ⁻¹' {p e}))))
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  rcases hτ with ⟨γ, rfl⟩
  ext x
  -- Pointwise centralizer equality is exactly monodromy equivariance from Theorem 3.7.9.
  simpa [coveringSpaceAutFiberPerm] using
    congrArg Subtype.val (coveringSpaceHomToFiberFun_comm hp hp (p e) α.hom γ x).symm

/-- The canonical homomorphism from covering-space automorphisms to automorphisms of the fiber as
a `π₁(B, p e)`-set. -/
noncomputable def coveringSpaceAutToFiberAutHom
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut (Over.mk (TopCat.ofHom p)) →*
      Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
  letI := fiberMonodromyMulAction hp (p e)
  ((autMulEquivGSetAut (FundamentalGroup B (p e)) (p ⁻¹' {p e})).symm.toMonoidHom).comp
    { toFun := fun α ↦
        ⟨coveringSpaceAutFiberPerm e α, coveringSpaceAutFiberPerm_mem_gSetAut hp e α⟩
      map_one' := Subtype.ext (coveringSpaceAutFiberPerm_one e)
      map_mul' := fun α β ↦ Subtype.ext (coveringSpaceAutFiberPerm_mul e α β) }

/-- The canonical homomorphism to fiber `π₁(B, p e)`-set automorphisms is bijective. -/
-- Proof sketch: Theorem 3.7.9 identifies all morphisms of covering spaces `p ⟶ p` with
-- equivariant fiber maps. Restricting to invertible morphisms on both sides gives bijectivity on
-- the corresponding automorphism groups.
theorem coveringSpaceAutToFiberAutHom_bijective
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Function.Bijective (coveringSpaceAutToFiberAutHom hp e) := by
  letI := fiberMonodromyMulAction hp (p e)
  constructor
  · intro α β hαβ
    apply Iso.ext
    apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
    apply MulActionHom.ext
    intro x
    have hx :
        (coveringSpaceAutToFiberAutHom hp e α).hom.hom x =
          (coveringSpaceAutToFiberAutHom hp e β).hom.hom x := by
      simpa using
        congrArg
          (fun φ : Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ↦ φ.hom.hom x)
          hαβ
    -- Equality of fiber automorphisms gives equality of the restricted covering maps.
    simpa [coveringSpaceAutToFiberAutHom, coveringSpaceAutFiberPerm, coveringSpaceHomToFiber] using
      hx
  · intro φ
    -- Route correction: lift the inverse fiber automorphism through Theorem 3.7.9 instead of
    -- rebuilding the Weyl-group argument directly.
    have hφ_hom_smul :
        ∀ (γ : FundamentalGroup B (p e)) (x : p ⁻¹' {p e}),
          φ.hom.hom (γ • x) = γ • (show p ⁻¹' {p e} from φ.hom.hom x) := by
      intro γ x
      -- The forward fiber automorphism is equivariant by definition.
      simpa [Action.ofMulAction_apply] using ConcreteCategory.congr_hom (φ.hom.comm γ) x
    let φhom : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) :=
      { toFun := φ.hom.hom
        map_smul' := hφ_hom_smul }
    have hφ_inv_smul :
        ∀ (γ : FundamentalGroup B (p e)) (x : p ⁻¹' {p e}),
          φ.inv.hom (γ • x) = γ • (show p ⁻¹' {p e} from φ.inv.hom x) := by
      intro γ x
      -- The inverse fiber automorphism is equivariant for the same monodromy action.
      simpa [Action.ofMulAction_apply] using ConcreteCategory.congr_hom (φ.inv.comm γ) x
    let φinv : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) :=
      { toFun := φ.inv.hom
        map_smul' := hφ_inv_smul }
    obtain ⟨h, hh⟩ := (coveringSpaceHomToFiber_bijective hp hp (p e)).2 φhom
    obtain ⟨i, hi⟩ := (coveringSpaceHomToFiber_bijective hp hp (p e)).2 φinv
    have hh_apply (x : p ⁻¹' {p e}) :
        coveringSpaceHomToFiberFun (p e) h x = φ.hom.hom x := by
      -- The lifted endomorphism `h` restricts to the given fiber automorphism `φ.hom`.
      simpa [coveringSpaceHomToFiber] using
        congrArg
          (fun ψ : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) ↦ ψ x)
          hh
    have hi_apply (x : p ⁻¹' {p e}) :
        coveringSpaceHomToFiberFun (p e) i x = φ.inv.hom x := by
      -- Likewise, `i` restricts to the inverse fiber automorphism `φ.inv.hom`.
      simpa [coveringSpaceHomToFiber] using
        congrArg
          (fun ψ : (p ⁻¹' {p e}) →[FundamentalGroup B (p e)] (p ⁻¹' {p e}) ↦ ψ x)
          hi
    have hhi : h ≫ i = 𝟙 (Over.mk (TopCat.ofHom p)) := by
      apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
      apply MulActionHom.ext
      intro x
      -- The lifted maps compose to the identity because `φ.hom` and `φ.inv.hom` are inverse.
      have hcompose :
          coveringSpaceHomToFiberFun (p e) (h ≫ i) x =
            φ.inv.hom (φ.hom.hom x) := by
        calc
          coveringSpaceHomToFiberFun (p e) (h ≫ i) x =
              coveringSpaceHomToFiberFun (p e) i
                (coveringSpaceHomToFiberFun (p e) h x) := by
                  simpa [Function.comp] using
                    congrFun (coveringSpaceHomToFiberFun_comp (p := p) (p e) h i) x
          _ = φ.inv.hom (φ.hom.hom x) := by
                rw [hh_apply x, hi_apply (φ.hom.hom x)]
      have hidentity : φ.inv.hom (φ.hom.hom x) = x := by
        simp only [← comp_apply, Action.hom_inv_hom, id_apply]
      exact hcompose.trans hidentity
    have hih : i ≫ h = 𝟙 (Over.mk (TopCat.ofHom p)) := by
      apply (coveringSpaceHomToFiber_bijective hp hp (p e)).1
      apply MulActionHom.ext
      intro x
      -- The opposite composite is also the identity because `φ.inv.hom` and `φ.hom` are inverse.
      have hcompose :
          coveringSpaceHomToFiberFun (p e) (i ≫ h) x =
            φ.hom.hom (φ.inv.hom x) := by
        calc
          coveringSpaceHomToFiberFun (p e) (i ≫ h) x =
              coveringSpaceHomToFiberFun (p e) h
                (coveringSpaceHomToFiberFun (p e) i x) := by
                  simpa [Function.comp] using
                    congrFun (coveringSpaceHomToFiberFun_comp (p := p) (p e) i h) x
          _ = φ.hom.hom (φ.inv.hom x) := by
                rw [hi_apply x, hh_apply (φ.inv.hom x)]
      have hidentity : φ.hom.hom (φ.inv.hom x) = x := by
        simp only [← comp_apply, Action.inv_hom_hom, id_apply]
      exact hcompose.trans hidentity
    have hIso : IsIso h := IsIso.mk ⟨i, hhi, hih⟩
    refine ⟨asIso h, ?_⟩
    ext x
    -- The reconstructed covering automorphism acts on the fiber as the original automorphism `φ`.
    simpa [coveringSpaceAutToFiberAutHom, coveringSpaceAutFiberPerm, coveringSpaceHomToFiber,
      CategoryTheory.asIso_hom, φhom] using hh_apply x

/-- The automorphism group of a covering space is canonically isomorphic to the automorphism group
of its fiber over `p e` as a `π₁(B, p e)`-set. -/
noncomputable def coveringSpaceAutMulEquivFiberAut
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut (Over.mk (TopCat.ofHom p)) ≃*
      Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
  letI := fiberMonodromyMulAction hp (p e)
  MulEquiv.ofBijective
    (coveringSpaceAutToFiberAutHom hp e)
    (coveringSpaceAutToFiberAutHom_bijective hp e)

/-- The automorphism group of the fiber monodromy `π₁(B, p e)`-set is canonically identified with
the Weyl group of the image subgroup `(FundamentalGroup.map p e).range`. -/
noncomputable def fiberAutMulEquivWeylGroup_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    letI := fiberMonodromyMulAction hp (p e)
    Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ≃*
      Subgroup.weylGroup ((FundamentalGroup.map p e).range) :=
  letI := fiberMonodromyMulAction hp (p e)
  letI : MulAction.IsPretransitive (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
    fiberMonodromyMulAction_isPretransitive hp e
  let x₀ : p ⁻¹' {p e} := ⟨e, rfl⟩
  let eW :
      Subgroup.weylGroup (MulAction.stabilizer (FundamentalGroup B (p e)) x₀) ≃*
        Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) :=
    weylGroup_stabilizer_mulEquiv_aut x₀
  show Aut_ (FundamentalGroup B (p e)) (p ⁻¹' {p e}) ≃*
      Subgroup.weylGroup ((FundamentalGroup.map p e).range) from
    eW.symm.trans
      (MulEquiv.cast (fiberMonodromyMulAction_stabilizer_eq_fundamentalGroupRange hp e))

/-- Corollary 3.7.11 (1): if `G = π₁(B, p e)` and `H = p_*(π₁(E, e))`, then the automorphism
group of the covering space `p` is canonically isomorphic to the Weyl group `W H`. -/
noncomputable def coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    Aut (Over.mk (TopCat.ofHom p)) ≃* Subgroup.weylGroup ((FundamentalGroup.map p e).range) :=
  (coveringSpaceAutMulEquivFiberAut hp e).trans
    (fiberAutMulEquivWeylGroup_fundamentalGroupRange hp e)

/-- Evaluating the first clause identifies a covering-space automorphism with its Weyl-group
class through the fiber `π₁(B, p e)`-set. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange`; the value is
-- the composite of the covering-automorphism/fiber-action equivalence and the bundled
-- fiber-action Weyl-group bridge.
theorem coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange_apply
    (hp : IsPathConnectedCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI := fiberMonodromyMulAction hp (p e)
    coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange hp e α =
      fiberAutMulEquivWeylGroup_fundamentalGroupRange hp e
        (coveringSpaceAutMulEquivFiberAut hp e α) := rfl

end

end IsPathConnectedCoveringMap

namespace IsRegularCoveringMap

variable {p : C(E, B)} {e : E}

section

variable [PathConnectedSpace E] [LocPathConnectedSpace E]

/-- Corollary 3.7.11 (2): if `p` is regular at `e`, then the automorphism group of the covering
space `p` is canonically isomorphic to `π₁(B, p e) / p_*(π₁(E, e))`. -/
noncomputable def coveringSpaceAutMulEquivQuotientFundamentalGroupRange
    (hp : IsRegularCoveringMap p e) :
    letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
    Aut (Over.mk (TopCat.ofHom p)) ≃*
      (FundamentalGroup B (p e) ⧸ (FundamentalGroup.map p e).range) :=
  letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
  (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
      hp.isPathConnectedCoveringMap e).trans
    (Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range))

/-- Evaluating the second clause factors through the Weyl-group description and then the quotient
by the normal image subgroup. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivQuotientFundamentalGroupRange`; its value is the
-- application of `weylGroupMulEquivQuotientOfNormal` to the Weyl-group class from the first
-- clause.
theorem coveringSpaceAutMulEquivQuotientFundamentalGroupRange_apply
    (hp : IsRegularCoveringMap p e) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI : (FundamentalGroup.map p e).range.Normal := hp.normal_fundamentalGroup_map_range
    coveringSpaceAutMulEquivQuotientFundamentalGroupRange hp α =
      Subgroup.weylGroupMulEquivQuotientOfNormal ((FundamentalGroup.map p e).range)
        (IsPathConnectedCoveringMap.coveringSpaceAutMulEquivWeylGroup_fundamentalGroupRange
          hp.isPathConnectedCoveringMap e α) := rfl

end

end IsRegularCoveringMap

namespace IsUniversalCoveringMap

variable [LocPathConnectedSpace E] {p : C(E, B)}

/-- Helper for Corollary 3.7.11: a universal covering has trivial image subgroup in the base
fundamental group at every chosen basepoint. -/
private theorem fundamentalGroup_map_range_eq_bot_of_universal
    (hp : IsUniversalCoveringMap p) (e : E) :
    (FundamentalGroup.map p e).range = ⊥ := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  -- A simply connected source has subsingleton fundamental group, so the induced map is trivial.
  rw [MonoidHom.range_eq_bot_iff]
  ext γ
  have hγ : γ = 1 := by
    exact congrArg (FundamentalGroup.fromPath (X := E) (x := e))
      (Subsingleton.elim (FundamentalGroup.toPath γ) ⟦Path.refl e⟧)
  rw [hγ, map_one, MonoidHom.one_apply]

/-- A universal covering map is regular at every chosen basepoint. -/
-- Proof sketch: the image subgroup `p_*(π₁(E, e))` is trivial for a universal covering, hence
-- normal, so the regularity condition follows immediately.
theorem isRegularCoveringMap (hp : IsUniversalCoveringMap p) (e : E) :
    IsRegularCoveringMap p e := by
  let _ : SimplyConnectedSpace E := hp.simplyConnectedSpace
  let _ : PathConnectedSpace E := inferInstance
  have hbot : (FundamentalGroup.map p e).range = ⊥ :=
    fundamentalGroup_map_range_eq_bot_of_universal hp e
  refine
    { toIsPathConnectedCoveringMap := hp.isPathConnectedCoveringMap
      normal_fundamentalGroup_map_range := ?_ }
  -- The trivial subgroup is normal, so the regularity condition is automatic.
  exact hbot ▸ Subgroup.normal_bot

/-- For a universal covering, the image subgroup `p_*(π₁(E, e))` is trivial. -/
-- Proof sketch: a simply connected total space has trivial fundamental group at every basepoint,
-- so the image of `FundamentalGroup.map p e` is the bottom subgroup.
theorem fundamentalGroup_map_range_eq_bot (hp : IsUniversalCoveringMap p) (e : E) :
    (FundamentalGroup.map p e).range = ⊥ :=
  fundamentalGroup_map_range_eq_bot_of_universal hp e

/-- Corollary 3.7.11 (3): if `p` is universal, then the automorphism group of the covering space
`p` is canonically isomorphic to `π₁(B, p e)`. -/
noncomputable def coveringSpaceAutMulEquivFundamentalGroup
    (hp : IsUniversalCoveringMap p) (e : E) :
    Aut (Over.mk (TopCat.ofHom p)) ≃* FundamentalGroup B (p e) :=
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  letI : LocPathConnectedSpace E := inferInstance
  let h_regular := isRegularCoveringMap hp e
  letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
  (IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange h_regular).trans
    ((QuotientGroup.quotientMulEquivOfEq (fundamentalGroup_map_range_eq_bot hp e)).trans
      QuotientGroup.quotientBot)

/-- Evaluating the third clause specializes the quotient description along the equality
`p_*(π₁(E, e)) = ⊥`. -/
-- Proof sketch: unfold `coveringSpaceAutMulEquivFundamentalGroup`; its value is the regular-case
-- quotient class, followed by the quotient identifications for the trivial subgroup.
theorem coveringSpaceAutMulEquivFundamentalGroup_apply
    (hp : IsUniversalCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p))) :
    letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    let h_regular := isRegularCoveringMap hp e
    letI : (FundamentalGroup.map p e).range.Normal := h_regular.normal_fundamentalGroup_map_range
    coveringSpaceAutMulEquivFundamentalGroup hp e α =
      ((QuotientGroup.quotientMulEquivOfEq (fundamentalGroup_map_range_eq_bot hp e)).trans
        QuotientGroup.quotientBot)
        (IsRegularCoveringMap.coveringSpaceAutMulEquivQuotientFundamentalGroupRange
          h_regular α) := rfl

end IsUniversalCoveringMap
