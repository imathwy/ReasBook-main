module

public import Topology_Munkres_2000.Book.Lemma_79_1
public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homotopy.Product
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Covering.Basic

public section

universe u v

namespace FundamentalGroup

/-- Helper for Exercise 79.6: a reflexive target-basepoint choice in `mapOfEq`
is the ordinary induced fundamental-group map. -/
private lemma mapOfEq_refl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    mapOfEq f (rfl : f x = f x) = map f x := by
  -- Evaluate on loop classes and remove the reflexive endpoint cast.
  ext γ
  simp only [mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl, map_apply]

/-- Helper for Exercise 79.6: pointed fundamental-group maps preserve composition,
including the chosen endpoint equalities. -/
private lemma mapOfEq_comp {X : Type u} {Y : Type v} {Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (mapOfEq g hg).comp (mapOfEq f hf) = mapOfEq (g.comp f) hgf := by
  -- Normalize the selected endpoints, then compare the mapped loop classes.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext γ
  simp only [MonoidHom.coe_comp, Function.comp_apply, mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Exercise 79.6: changing only the chosen target-basepoint equality in
`mapOfEq` gives a heterogeneously equal loop class. -/
private lemma mapOfEq_heq {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X} {y z : Y}
    (hy : f x = y) (hz : f x = z) (γ : FundamentalGroup X x) :
    HEq (mapOfEq f hy γ) (mapOfEq f hz γ) := by
  -- Both endpoint casts are heterogeneously equal to the same uncast mapped loop.
  rw [mapOfEq_apply, mapOfEq_apply]
  exact (Path.Homotopic.Quotient.cast_heq hy.symm hy.symm).trans
    (Path.Homotopic.Quotient.cast_heq hz.symm hz.symm).symm

/-- Helper for Exercise 79.6: mapping a product of identity-based loop classes by
group multiplication gives their ordinary fundamental-group product. -/
private lemma map_prod_mul {G : Type v} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (a b : FundamentalGroup G 1) :
    mapOfEq ⟨fun z : G × G ↦ z.1 * z.2, continuous_mul⟩ (mul_one 1)
      (Path.Homotopic.prod a b) = b * a := by
  let e : FundamentalGroup G 1 := 1
  have map_left :
      mapOfEq ⟨fun z : G × G ↦ z.1 * z.2, continuous_mul⟩ (mul_one 1)
        (Path.Homotopic.prod a e) = a := by
    induction a using Path.Homotopic.Quotient.ind with
    | mk α =>
        rw [mapOfEq_apply]
        simp only [e]
        rw [FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_refl]
        rw [Path.Homotopic.prod_lift, ← Path.Homotopic.Quotient.mk_map,
          ← Path.Homotopic.Quotient.mk_cast]
        apply congrArg Path.Homotopic.Quotient.mk
        ext t
        exact mul_one (α t)
  have map_right :
      mapOfEq ⟨fun z : G × G ↦ z.1 * z.2, continuous_mul⟩ (mul_one 1)
        (Path.Homotopic.prod e b) = b := by
    induction b using Path.Homotopic.Quotient.ind with
    | mk β =>
        rw [mapOfEq_apply]
        simp only [e]
        rw [FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_refl]
        rw [Path.Homotopic.prod_lift, ← Path.Homotopic.Quotient.mk_map,
          ← Path.Homotopic.Quotient.mk_cast]
        apply congrArg Path.Homotopic.Quotient.mk
        ext t
        exact one_mul (β t)
  have split_product :
      Path.Homotopic.prod a b =
        (Path.Homotopic.prod a e).trans (Path.Homotopic.prod e b) := by
    rw [Path.Homotopic.comp_prod_eq_prod_comp]
    simp only [e, ← FundamentalGroup.mul_def, one_mul, mul_one]
  -- Split the product loop into its coordinate loops before mapping by multiplication.
  rw [split_product]
  rw [← FundamentalGroup.mul_def]
  rw [map_mul, map_left, map_right]

/-- Helper for Exercise 79.6: the induced loop of a pointwise product of two
identity-based maps is the product of their induced loops, in the order fixed by
the fundamental-group multiplication convention. -/
private lemma mapOfEq_pointwiseMul_apply {X : Type u} {G : Type v}
    [TopologicalSpace X] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (f g : C(X, G)) (x : X) (hf : f x = 1) (hg : g x = 1)
    (hfg : (⟨fun y ↦ f y * g y, f.continuous.mul g.continuous⟩ : C(X, G)) x = 1)
    (γ : FundamentalGroup X x) :
    mapOfEq ⟨fun y ↦ f y * g y, f.continuous.mul g.continuous⟩ hfg γ =
      mapOfEq g hg γ * mapOfEq f hf γ := by
  let pairMap : C(X, G × G) := f.prodMk g
  let mulMap : C(G × G, G) :=
    ⟨fun z ↦ z.1 * z.2, continuous_mul⟩
  let pointwiseMap : C(X, G) :=
    ⟨fun y ↦ f y * g y, f.continuous.mul g.continuous⟩
  have hpair : pairMap x = (1, 1) := Prod.ext hf hg
  have hmul : mulMap (1, 1) = 1 := mul_one 1
  have hcomposite : mulMap.comp pairMap = pointwiseMap := by
    ext y
    rfl
  have hfst : ContinuousMap.fst.comp pairMap = f := by
    ext y
    rfl
  have hsnd : ContinuousMap.snd.comp pairMap = g := by
    ext y
    rfl
  have hcomp_base : (mulMap.comp pairMap) x = 1 := by
    rw [hcomposite]
    exact hfg
  let δ := mapOfEq pairMap hpair γ
  have left_projection :
      FundamentalGroup.fromPath (Path.Homotopic.projLeft δ) = mapOfEq f hf γ := by
    have hmap := DFunLike.congr_fun
      (mapOfEq_comp pairMap ContinuousMap.fst hpair rfl hf) γ
    rw [MonoidHom.comp_apply] at hmap
    simp only [hfst] at hmap
    rw [mapOfEq_apply, mapOfEq_apply] at hmap
    simp only [mapOfEq_apply] at hmap
    simpa only [δ, mapOfEq_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.projLeft,
      ContinuousMap.fst, ContinuousMap.coe_mk] using hmap
  have right_projection :
      FundamentalGroup.fromPath (Path.Homotopic.projRight δ) = mapOfEq g hg γ := by
    have hmap := DFunLike.congr_fun
      (mapOfEq_comp pairMap ContinuousMap.snd hpair rfl hg) γ
    rw [MonoidHom.comp_apply] at hmap
    simp only [hsnd] at hmap
    rw [mapOfEq_apply, mapOfEq_apply] at hmap
    simp only [mapOfEq_apply] at hmap
    simpa only [δ, mapOfEq_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.projRight,
      ContinuousMap.snd, ContinuousMap.coe_mk] using hmap
  have composite_map :
      mapOfEq pointwiseMap hfg γ = mapOfEq mulMap hmul δ := by
    simpa only [MonoidHom.comp_apply, hcomposite, δ] using (DFunLike.congr_fun
      (mapOfEq_comp pairMap mulMap hpair hmul hcomp_base) γ).symm
  -- Decompose the loop in the product, then apply the quotient-level calculation.
  calc
    mapOfEq ⟨fun y ↦ f y * g y, f.continuous.mul g.continuous⟩ hfg γ =
        mapOfEq mulMap hmul δ := composite_map
    _ = mapOfEq mulMap hmul
        (Path.Homotopic.prod
          (FundamentalGroup.fromPath (Path.Homotopic.projLeft δ))
          (FundamentalGroup.fromPath (Path.Homotopic.projRight δ))) := by
      rw [Path.Homotopic.prod_projLeft_projRight]
    _ = FundamentalGroup.fromPath (Path.Homotopic.projRight δ) *
        FundamentalGroup.fromPath (Path.Homotopic.projLeft δ) := map_prod_mul _ _
    _ = mapOfEq g hg γ * mapOfEq f hf γ := by
      rw [left_projection, right_projection]

end FundamentalGroup

namespace IsCoveringMap

/-- A group structure on the total space is a lifted topological group structure when its
identity is the chosen point, its operations are continuous, and the covering map
preserves multiplication. -/
structure IsLiftedTopologicalGroup {G' : Type u} {G : Type v}
    [topG' : TopologicalSpace G'] [TopologicalSpace G] [Group G]
    (p : G' → G) (e' : G') (s : Group G') : Prop where
  one_eq : s.one = e'
  continuous_mul : Continuous fun x : G' × G' ↦ s.mul x.1 x.2
  continuous_inv : Continuous s.inv
  map_mul : ∀ x y : G', p (s.mul x y) = p x * p y

/-- Helper for Exercise 79.6: a binary product of locally path-connected spaces
is locally path-connected. -/
private lemma prodLocallyPathConnectedSpace
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B] :
    LocallyPathConnectedSpace (A × B) := by
  -- Products of path-connected neighborhood bases give the required local basis.
  refine LocallyPathConnectedSpace.of_bases
    (fun x ↦ (path_connected_basis x.1).prod_nhds (path_connected_basis x.2)) ?_
  intro x U hU
  exact hU.1.2.prod hU.2.2

/-- Helper for Exercise 79.6: the pointwise multiplication map sends fundamental
groups into the subgroup determined by the covering projection. -/
private lemma mulMap_range_le_fundamentalGroupMapRange
    {G' : Type u} {G : Type v} [TopologicalSpace G'] [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] (p : G' → G) (hp : IsCoveringMap p)
    (e' : G') (he' : p e' = 1)
    (heMul : p e' =
      (⟨fun z : G' × G' ↦ p z.1 * p z.2,
        (hp.continuous.comp continuous_fst).mul
          (hp.continuous.comp continuous_snd)⟩ : C(G' × G', G)) (e', e')) :
    (FundamentalGroup.map
      ⟨fun z : G' × G' ↦ p z.1 * p z.2,
        (hp.continuous.comp continuous_fst).mul
          (hp.continuous.comp continuous_snd)⟩ (e', e')).range ≤
      hp.fundamentalGroupMapRange heMul := by
  let pMap : C(G', G) := ⟨p, hp.continuous⟩
  let pFst : C(G' × G', G) := pMap.comp ContinuousMap.fst
  let pSnd : C(G' × G', G) := pMap.comp ContinuousMap.snd
  let mulMap : C(G' × G', G) :=
    ⟨fun z ↦ p z.1 * p z.2,
      (hp.continuous.comp continuous_fst).mul
        (hp.continuous.comp continuous_snd)⟩
  have hfst : pFst (e', e') = 1 := he'
  have hsnd : pSnd (e', e') = 1 := he'
  have hmul : mulMap (e', e') = 1 := by
    calc
      mulMap (e', e') = p e' * p e' := rfl
      _ = 1 * 1 := congrArg₂ (fun a b : G ↦ a * b) he' he'
      _ = 1 := one_mul 1
  have hfst_base : ContinuousMap.fst (e', e') = e' := rfl
  have hsnd_base : ContinuousMap.snd (e', e') = e' := rfl
  rintro _ ⟨γ, rfl⟩
  let γfst : FundamentalGroup G' e' :=
    FundamentalGroup.mapOfEq ContinuousMap.fst hfst_base γ
  let γsnd : FundamentalGroup G' e' :=
    FundamentalGroup.mapOfEq ContinuousMap.snd hsnd_base γ
  refine ⟨γsnd * γfst, ?_⟩
  have fst_map : FundamentalGroup.mapOfEq pMap he' γfst =
      FundamentalGroup.mapOfEq pFst hfst γ := by
    have hcomp := DFunLike.congr_fun
      (FundamentalGroup.mapOfEq_comp ContinuousMap.fst pMap hfst_base he' hfst) γ
    rw [MonoidHom.comp_apply] at hcomp
    simpa only [γfst, pFst] using hcomp
  have snd_map : FundamentalGroup.mapOfEq pMap he' γsnd =
      FundamentalGroup.mapOfEq pSnd hsnd γ := by
    have hcomp := DFunLike.congr_fun
      (FundamentalGroup.mapOfEq_comp ContinuousMap.snd pMap hsnd_base he' hsnd) γ
    rw [MonoidHom.comp_apply] at hcomp
    simpa only [γsnd, pSnd] using hcomp
  have pointwise_map : FundamentalGroup.mapOfEq mulMap hmul γ =
      FundamentalGroup.mapOfEq pSnd hsnd γ *
        FundamentalGroup.mapOfEq pFst hfst γ := by
    exact FundamentalGroup.mapOfEq_pointwiseMul_apply
      pFst pSnd (e', e') hfst hsnd hmul γ
  -- Compare the identity-based calculation with the basepoint chosen by the lift criterion.
  apply eq_of_heq
  have map_mul_eq : FundamentalGroup.mapOfEq pMap he' (γsnd * γfst) =
      FundamentalGroup.mapOfEq pMap he' γsnd *
        FundamentalGroup.mapOfEq pMap he' γfst := by
    rw [map_mul]
  have projections_eq : FundamentalGroup.mapOfEq pMap he' γsnd *
      FundamentalGroup.mapOfEq pMap he' γfst =
        FundamentalGroup.mapOfEq pSnd hsnd γ *
          FundamentalGroup.mapOfEq pFst hfst γ := by
    rw [fst_map, snd_map]
  have refl_map_eq : FundamentalGroup.mapOfEq mulMap rfl γ =
      FundamentalGroup.map mulMap (e', e') γ := by
    exact DFunLike.congr_fun
      (FundamentalGroup.mapOfEq_refl mulMap (e', e')) γ
  exact (((FundamentalGroup.mapOfEq_heq pMap heMul he' _).trans
    (heq_of_eq map_mul_eq)).trans (heq_of_eq projections_eq)).trans
      ((heq_of_eq pointwise_map.symm).trans
        ((FundamentalGroup.mapOfEq_heq mulMap hmul rfl _).trans
          (heq_of_eq refl_map_eq)))

/-- Helper for Exercise 79.6: the pointwise inverse map sends fundamental groups
into the subgroup determined by the covering projection. -/
private lemma invMap_range_le_fundamentalGroupMapRange
    {G' : Type u} {G : Type v} [TopologicalSpace G'] [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] (p : G' → G) (hp : IsCoveringMap p)
    (e' : G') (he' : p e' = 1)
    (heInv : p e' =
      (⟨fun x : G' ↦ (p x)⁻¹, continuous_inv.comp hp.continuous⟩ : C(G', G)) e') :
    (FundamentalGroup.map
      ⟨fun x : G' ↦ (p x)⁻¹, continuous_inv.comp hp.continuous⟩ e').range ≤
      hp.fundamentalGroupMapRange heInv := by
  let pMap : C(G', G) := ⟨p, hp.continuous⟩
  let invMap : C(G', G) :=
    ⟨fun x ↦ (p x)⁻¹, continuous_inv.comp hp.continuous⟩
  let oneMap : C(G', G) := ⟨fun _ ↦ 1, continuous_const⟩
  let productMap : C(G', G) :=
    ⟨fun x ↦ pMap x * invMap x, pMap.continuous.mul invMap.continuous⟩
  have hp_base : pMap e' = 1 := he'
  have hinv_base : invMap e' = 1 := by
    simp only [invMap, ContinuousMap.coe_mk, he', inv_one]
  have hproduct_base : productMap e' = 1 := by
    simp only [productMap, ContinuousMap.coe_mk, hp_base, hinv_base, one_mul]
  rintro _ ⟨γ, rfl⟩
  refine ⟨γ⁻¹, ?_⟩
  have product_loop : FundamentalGroup.mapOfEq productMap hproduct_base γ =
      FundamentalGroup.mapOfEq invMap hinv_base γ *
        FundamentalGroup.mapOfEq pMap hp_base γ := by
    exact FundamentalGroup.mapOfEq_pointwiseMul_apply
      pMap invMap e' hp_base hinv_base hproduct_base γ
  have product_map_eq : productMap = oneMap := by
    ext x
    exact mul_inv_cancel (p x)
  have constant_loop : FundamentalGroup.mapOfEq oneMap rfl γ = 1 := by
    induction γ using Path.Homotopic.Quotient.ind with
    | mk α =>
        rw [FundamentalGroup.mapOfEq_apply]
        rw [FundamentalGroup.one_def, ← Path.Homotopic.Quotient.mk_refl]
        rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
        apply congrArg Path.Homotopic.Quotient.mk
        ext t
        rfl
  have inverse_formula : FundamentalGroup.mapOfEq invMap hinv_base γ =
      (FundamentalGroup.mapOfEq pMap hp_base γ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← product_loop]
    simpa only [product_map_eq] using constant_loop
  -- Move both sides to the identity basepoint, use the inverse formula, and
  -- return to the endpoint equality appearing in the lifting criterion.
  apply eq_of_heq
  have map_inv_eq : FundamentalGroup.mapOfEq pMap hp_base (γ⁻¹) =
      (FundamentalGroup.mapOfEq pMap hp_base γ)⁻¹ := by
    rw [map_inv]
  have refl_map_eq : FundamentalGroup.mapOfEq invMap rfl γ =
      FundamentalGroup.map invMap e' γ := by
    exact DFunLike.congr_fun
      (FundamentalGroup.mapOfEq_refl invMap e') γ
  exact (((FundamentalGroup.mapOfEq_heq pMap heInv hp_base _).trans
    (heq_of_eq map_inv_eq)).trans (heq_of_eq inverse_formula.symm)).trans
      ((FundamentalGroup.mapOfEq_heq invMap hinv_base rfl _).trans
        (heq_of_eq refl_map_eq))

/-- Exercise 79.6: a pointed covering of a path-connected, locally path-connected
topological group admits a topological group structure with the chosen point as its
identity and with multiplication preserved by the covering map; this multiplication
is unique. -/
theorem existsUnique_groupStructure {G' : Type u} {G : Type v}
    [TopologicalSpace G'] [PathConnectedSpace G'] [LocallyPathConnectedSpace G']
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [PathConnectedSpace G] [LocallyPathConnectedSpace G]
    (p : G' → G) (hp : IsCoveringMap p) (e' : G') (he' : p e' = 1) :
    ∃! s : Group G', IsLiftedTopologicalGroup p e' s := by
  letI : LocallyPathConnectedSpace (G' × G') :=
    prodLocallyPathConnectedSpace
  have mulMap_continuous : Continuous (fun z : G' × G' ↦ p z.1 * p z.2) :=
    (hp.continuous.comp continuous_fst).mul
      (hp.continuous.comp continuous_snd)
  let mulMap : C(G' × G', G) :=
    ⟨fun z ↦ p z.1 * p z.2, mulMap_continuous⟩
  have heMul : p e' = mulMap (e', e') := by
    simp only [mulMap, ContinuousMap.coe_mk, he', one_mul]
  have mulRange : (FundamentalGroup.map mulMap (e', e')).range ≤
      hp.fundamentalGroupMapRange heMul := by
    exact mulMap_range_le_fundamentalGroupMapRange p hp e' he' heMul
  obtain ⟨mLift, hmLift, -⟩ :=
    (existsUnique_continuousMap_lifts_iff_range_le
      p hp mulMap (e', e') e' heMul).mpr mulRange
  have invMap_continuous : Continuous (fun x : G' ↦ (p x)⁻¹) :=
    continuous_inv.comp hp.continuous
  let invMap : C(G', G) := ⟨fun x ↦ (p x)⁻¹, invMap_continuous⟩
  have heInv : p e' = invMap e' := by
    simp only [invMap, ContinuousMap.coe_mk, he', inv_one]
  have invRange : (FundamentalGroup.map invMap e').range ≤
      hp.fundamentalGroupMapRange heInv := by
    exact invMap_range_le_fundamentalGroupMapRange p hp e' he' heInv
  obtain ⟨invLift, hinvLift, -⟩ :=
    (existsUnique_continuousMap_lifts_iff_range_le
      p hp invMap e' e' heInv).mpr invRange
  have mLift_projection (x y : G') : p (mLift (x, y)) = p x * p y := by
    exact congrFun hmLift.2 (x, y)
  have invLift_projection (x : G') : p (invLift x) = (p x)⁻¹ := by
    exact congrFun hinvLift.2 x
  -- The left-unit map and the identity are lifts of the same map and agree at `e'`.
  have leftUnit_continuous : Continuous (fun x : G' ↦ mLift (e', x)) :=
    mLift.continuous.comp (continuous_const.prodMk continuous_id)
  have leftUnit_projection :
      p ∘ (fun x : G' ↦ mLift (e', x)) = p ∘ id := by
    funext x
    simp only [Function.comp_apply, id_eq]
    rw [mLift_projection, he', one_mul]
  have leftUnit_base : mLift (e', e') = id e' := by
    exact hmLift.1
  have leftUnit_function : (fun x : G' ↦ mLift (e', x)) = id :=
    hp.eq_of_comp_eq leftUnit_continuous continuous_id leftUnit_projection e' leftUnit_base
  have leftUnit (x : G') : mLift (e', x) = x := by
    exact congrFun leftUnit_function x
  -- The inverse composite and the constant map are lifts of the constant identity map.
  have leftInverse_continuous :
      Continuous (fun x : G' ↦ mLift (invLift x, x)) :=
    mLift.continuous.comp (invLift.continuous.prodMk continuous_id)
  have leftInverse_projection :
      p ∘ (fun x : G' ↦ mLift (invLift x, x)) = p ∘ (fun _ : G' ↦ e') := by
    funext x
    simp only [Function.comp_apply]
    rw [mLift_projection, invLift_projection, inv_mul_cancel, he']
  have leftInverse_base : mLift (invLift e', e') = e' := by
    rw [hinvLift.1]
    exact hmLift.1
  have leftInverse_function :
      (fun x : G' ↦ mLift (invLift x, x)) = fun _ ↦ e' :=
    hp.eq_of_comp_eq leftInverse_continuous continuous_const
      leftInverse_projection e' leftInverse_base
  have leftInverse (x : G') : mLift (invLift x, x) = e' := by
    exact congrFun leftInverse_function x
  have first_continuous : Continuous (fun z : G' × G' × G' ↦ z.1) :=
    continuous_fst
  have middle_continuous : Continuous (fun z : G' × G' × G' ↦ z.2.1) :=
    continuous_fst.comp continuous_snd
  have last_continuous : Continuous (fun z : G' × G' × G' ↦ z.2.2) :=
    continuous_snd.comp continuous_snd
  have firstProduct_continuous :
      Continuous (fun z : G' × G' × G' ↦ mLift (z.1, z.2.1)) :=
    mLift.continuous.comp (first_continuous.prodMk middle_continuous)
  have lastProduct_continuous :
      Continuous (fun z : G' × G' × G' ↦ mLift (z.2.1, z.2.2)) :=
    mLift.continuous.comp (middle_continuous.prodMk last_continuous)
  have leftAssociated_continuous :
      Continuous (fun z : G' × G' × G' ↦ mLift (mLift (z.1, z.2.1), z.2.2)) :=
    mLift.continuous.comp (firstProduct_continuous.prodMk last_continuous)
  have rightAssociated_continuous :
      Continuous (fun z : G' × G' × G' ↦ mLift (z.1, mLift (z.2.1, z.2.2))) :=
    mLift.continuous.comp (first_continuous.prodMk lastProduct_continuous)
  -- Associativity downstairs identifies the projections of the two iterated lifts.
  have associative_projection :
      p ∘ (fun z : G' × G' × G' ↦ mLift (mLift (z.1, z.2.1), z.2.2)) =
        p ∘ (fun z : G' × G' × G' ↦ mLift (z.1, mLift (z.2.1, z.2.2))) := by
    funext z
    simp only [Function.comp_apply]
    rw [mLift_projection, mLift_projection, mLift_projection, mLift_projection, mul_assoc]
  have associative_base :
      mLift (mLift (e', e'), e') = mLift (e', mLift (e', e')) := by
    calc
      mLift (mLift (e', e'), e') = mLift (e', e') :=
        congrArg (fun x ↦ mLift (x, e')) hmLift.1
      _ = e' := hmLift.1
      _ = mLift (e', mLift (e', e')) :=
        ((congrArg (fun x ↦ mLift (e', x)) hmLift.1).trans hmLift.1).symm
  have associative_function :
      (fun z : G' × G' × G' ↦ mLift (mLift (z.1, z.2.1), z.2.2)) =
        fun z ↦ mLift (z.1, mLift (z.2.1, z.2.2)) :=
    hp.eq_of_comp_eq leftAssociated_continuous rightAssociated_continuous
      associative_projection (e', e', e') associative_base
  have associative (x y z : G') :
      mLift (mLift (x, y), z) = mLift (x, mLift (y, z)) := by
    exact congrFun associative_function (x, y, z)
  letI liftedMul : Mul G' := ⟨fun x y ↦ mLift (x, y)⟩
  letI liftedOne : One G' := ⟨e'⟩
  letI liftedInv : Inv G' := ⟨fun x ↦ invLift x⟩
  have lifted_assoc : ∀ x y z : G', (x * y) * z = x * (y * z) := associative
  have lifted_one_mul : ∀ x : G', 1 * x = x := leftUnit
  have lifted_inv_mul : ∀ x : G', x⁻¹ * x = 1 := leftInverse
  let s : Group G' := Group.ofLeftAxioms lifted_assoc lifted_one_mul lifted_inv_mul
  have hs : IsLiftedTopologicalGroup p e' s := by
    constructor
    · rfl
    · exact mLift.continuous
    · exact invLift.continuous
    · intro x y
      exact mLift_projection x y
  refine ⟨s, hs, ?_⟩
  intro t ht
  -- Covering-lift uniqueness also identifies any competing multiplication.
  have multiplication_projection :
      p ∘ (fun z : G' × G' ↦ s.mul z.1 z.2) =
        p ∘ (fun z : G' × G' ↦ t.mul z.1 z.2) := by
    funext z
    simp only [Function.comp_apply]
    rw [hs.map_mul, ht.map_mul]
  have s_base : s.mul e' e' = e' := by
    rw [← hs.one_eq]
    exact s.one_mul s.one
  have t_base : t.mul e' e' = e' := by
    rw [← ht.one_eq]
    exact t.one_mul t.one
  have multiplication_base : s.mul e' e' = t.mul e' e' :=
    s_base.trans t_base.symm
  have multiplication_function :
      (fun z : G' × G' ↦ s.mul z.1 z.2) =
        fun z ↦ t.mul z.1 z.2 :=
    hp.eq_of_comp_eq hs.continuous_mul ht.continuous_mul
      multiplication_projection (e', e') multiplication_base
  have multiplication_eq :
      @HMul.hMul G' G' G' (@instHMul G' s.toMulOneClass.toMul) =
        @HMul.hMul G' G' G' (@instHMul G' t.toMulOneClass.toMul) := by
    funext x y
    exact congrFun multiplication_function (x, y)
  exact (@Group.ext G' s t multiplication_eq).symm

/-- The multiplication of a compatible group structure on the total space is unique. -/
theorem IsLiftedTopologicalGroup.mul_eq {G' : Type u} {G : Type v}
    [TopologicalSpace G'] [PathConnectedSpace G'] [LocallyPathConnectedSpace G']
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [PathConnectedSpace G] [LocallyPathConnectedSpace G]
    (p : G' → G) (hp : IsCoveringMap p) (e' : G') (he' : p e' = 1)
    {s s' : Group G'} (hs : IsLiftedTopologicalGroup p e' s)
    (hs' : IsLiftedTopologicalGroup p e' s') :
    s.mul = s'.mul := by
  exact congr_arg (fun t : Group G' ↦ t.mul) <|
    (existsUnique_groupStructure p hp e' he').unique hs hs'

end IsCoveringMap
