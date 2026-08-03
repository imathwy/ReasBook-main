module

public import Topology_Munkres_2000.Book.Exercise_54_7
public import Topology_Munkres_2000.Book.Exercise_54_6.Power
public import Topology_Munkres_2000.Book.Theorem_53_3.Product
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

noncomputable section

public section

/- Exercise 79.4: The two projections identify `π₁(S¹ × S¹, (1, 1))` with `ℤ × ℤ`. -/
#check fundamentalGroup_circle_prod_circle

namespace TorusCover

/-- The covering candidate `(z, t) ↦ (z ^ m, Circle.exp t)`. -/
def firstCyclic (m : ℕ) : C(Circle × ℝ, Circle × Circle) :=
  (CircleMap.zpower (m : ℤ)).prodMap Circle.exp

/-- Evaluation of the covering candidate whose first coordinate has degree `m`. -/
theorem firstCyclic_apply (m : ℕ) (z : Circle) (t : ℝ) :
    firstCyclic m (z, t) = (z ^ m, Circle.exp t) := by
  -- Evaluate the product map and identify the integer power with the natural power.
  simp only [firstCyclic, ContinuousMap.prodMap_apply, Prod.map_apply,
    CircleMap.zpower_apply, zpow_natCast]

/-- The first cyclic covering candidate sends `(1, 0)` to the torus basepoint. -/
theorem firstCyclic_basepoint (m : ℕ) : firstCyclic m (1, 0) = (1, 1) := by
  -- Both coordinate maps carry the chosen source point to `1`.
  simp only [firstCyclic_apply, one_pow, Circle.exp_zero]

/-- The universal covering candidate `(s, t) ↦ (Circle.exp s, Circle.exp t)`. -/
def universal : C(ℝ × ℝ, Circle × Circle) :=
  Circle.exp.prodMap Circle.exp

/-- Evaluation of the universal covering candidate for the torus. -/
theorem universal_apply (s t : ℝ) :
    universal (s, t) = (Circle.exp s, Circle.exp t) := by
  -- Evaluation of a bundled product map is coordinatewise.
  rfl

/-- The universal covering candidate sends `(0, 0)` to the torus basepoint. -/
theorem universal_basepoint : universal (0, 0) = (1, 1) := by
  -- The exponential map sends zero to the circle basepoint.
  simp only [universal_apply, Circle.exp_zero]

/-- The rectangular covering candidate `(z, w) ↦ (z ^ m, w ^ n)`. -/
def rectangular (m n : ℕ) : C(Circle × Circle, Circle × Circle) :=
  (CircleMap.zpower (m : ℤ)).prodMap (CircleMap.zpower (n : ℤ))

/-- Evaluation of the rectangular covering candidate. -/
theorem rectangular_apply (m n : ℕ) (z w : Circle) :
    rectangular m n (z, w) = (z ^ m, w ^ n) := by
  -- Evaluate each power coordinate and normalize integer casts of natural exponents.
  simp only [rectangular, ContinuousMap.prodMap_apply, Prod.map_apply,
    CircleMap.zpower_apply, zpow_natCast]

/-- The rectangular covering candidate fixes the torus basepoint. -/
theorem rectangular_basepoint (m n : ℕ) : rectangular m n (1, 1) = (1, 1) := by
  -- Natural powers preserve the identity in both coordinates.
  simp only [rectangular_apply, one_pow]

end TorusCover

namespace CircleMap

/-- Helper for Exercise 79.4: a nonzero natural power map of the circle is a covering map. -/
private lemma isCoveringMap_zpower_nat (m : ℕ) (hm : m ≠ 0) :
    IsCoveringMap (zpower (m : ℤ)) := by
  -- Supply the nonzero-degree instance and compare natural and integer powers pointwise.
  letI : NeZero m := ⟨hm⟩
  have hfun : (zpower (m : ℤ) : Circle → Circle) = fun z ↦ z ^ m := by
    funext z
    rw [zpower_apply, zpow_natCast]
  rw [hfun]
  exact (Circle.isQuotientCoveringMap_npow m).isCoveringMap

/-- Helper for Exercise 79.4: the induced integer-power map has the expected cyclic range. -/
private lemma induced_zpower_range (k : ℤ) :
    (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
      (FundamentalGroup.mapOfEq (zpower k) (zpower_one k))).range =
        Subgroup.zpowers (Multiplicative.ofAdd k) := by
  -- Transport the induced-map formula through the circle coordinate equivalence.
  calc
    (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (zpower k) (zpower_one k))).range =
        ((zpowGroupHom k).comp
          Circle.fundamentalGroupEquivInt.toMonoidHom).range :=
      congrArg MonoidHom.range
        (induced_zpower k Circle.fundamentalGroupEquivInt)
    _ = Circle.fundamentalGroupEquivInt.toMonoidHom.range.map (zpowGroupHom k) :=
      MonoidHom.range_comp _ _
    _ = (⊤ : Subgroup (Multiplicative ℤ)).map (zpowGroupHom k) := by
      exact congrArg (fun S : Subgroup (Multiplicative ℤ) ↦ S.map (zpowGroupHom k))
        (MulEquiv.range_eq_top Circle.fundamentalGroupEquivInt)
    _ = (zpowGroupHom k : Multiplicative ℤ →* Multiplicative ℤ).range :=
      (MonoidHom.range_eq_map _).symm
    _ = Subgroup.zpowers (Multiplicative.ofAdd k) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨y.toAdd, ?_⟩
        apply Multiplicative.ext
        simp only [toAdd_zpow, toAdd_ofAdd]
        exact mul_comm _ _
      · rintro ⟨j, rfl⟩
        refine ⟨Multiplicative.ofAdd j, ?_⟩
        apply Multiplicative.ext
        simp only [toAdd_zpow, toAdd_ofAdd]
        exact mul_comm _ _

end CircleMap

/-- Helper for Exercise 79.4: projecting an induced product map onto its first coordinate
recovers the induced map of the first factor. -/
private lemma projLeft_mapOfEq_prodMap {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (x : X) (y : Y) (x' : X') (y' : Y') (f : C(X, X')) (g : C(Y, Y'))
    (hf : f x = x') (_hg : g y = y') (hfg : f.prodMap g (x, y) = (x', y'))
    (a : FundamentalGroup (X × Y) (x, y)) :
    Path.Homotopic.projLeft (FundamentalGroup.mapOfEq (f.prodMap g) hfg a) =
      FundamentalGroup.mapOfEq f hf (Path.Homotopic.projLeft a) := by
  -- On a representative loop, projection cancels the coordinatewise product map.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  unfold Path.Homotopic.projLeft
  rw [Path.Homotopic.Quotient.map_cast]
  have hcomp : ContinuousMap.fst.comp (f.prodMap g) = f.comp ContinuousMap.fst := by
    ext z
    rfl
  have hmiddle : HEq
      ((FundamentalGroup.toPath a).map
        (ContinuousMap.fst.comp (f.prodMap g)))
      ((FundamentalGroup.toPath a).map (f.comp ContinuousMap.fst)) := by
    cases hcomp
    rfl
  have hcore : HEq
      (((FundamentalGroup.toPath a).map (f.prodMap g)).map ContinuousMap.fst)
      (((FundamentalGroup.toPath a).map ContinuousMap.fst).map f) :=
    (heq_of_eq Path.Homotopic.Quotient.map_comp.symm).trans
      (hmiddle.trans (heq_of_eq Path.Homotopic.Quotient.map_comp))
  apply eq_of_heq
  exact (Path.Homotopic.Quotient.cast_heq _ _).trans
    (hcore.trans (Path.Homotopic.Quotient.cast_heq _ _).symm)

/-- Helper for Exercise 79.4: projecting an induced product map onto its second coordinate
recovers the induced map of the second factor. -/
private lemma projRight_mapOfEq_prodMap {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (x : X) (y : Y) (x' : X') (y' : Y') (f : C(X, X')) (g : C(Y, Y'))
    (_hf : f x = x') (hg : g y = y') (hfg : f.prodMap g (x, y) = (x', y'))
    (a : FundamentalGroup (X × Y) (x, y)) :
    Path.Homotopic.projRight (FundamentalGroup.mapOfEq (f.prodMap g) hfg a) =
      FundamentalGroup.mapOfEq g hg (Path.Homotopic.projRight a) := by
  -- The second projection gives the symmetric representative-loop computation.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  unfold Path.Homotopic.projRight
  rw [Path.Homotopic.Quotient.map_cast]
  have hcomp : ContinuousMap.snd.comp (f.prodMap g) = g.comp ContinuousMap.snd := by
    ext z
    rfl
  have hmiddle : HEq
      ((FundamentalGroup.toPath a).map
        (ContinuousMap.snd.comp (f.prodMap g)))
      ((FundamentalGroup.toPath a).map (g.comp ContinuousMap.snd)) := by
    cases hcomp
    rfl
  have hcore : HEq
      (((FundamentalGroup.toPath a).map (f.prodMap g)).map ContinuousMap.snd)
      (((FundamentalGroup.toPath a).map ContinuousMap.snd).map g) :=
    (heq_of_eq Path.Homotopic.Quotient.map_comp.symm).trans
      (hmiddle.trans (heq_of_eq Path.Homotopic.Quotient.map_comp))
  apply eq_of_heq
  exact (Path.Homotopic.Quotient.cast_heq _ _).trans
    (hcore.trans (Path.Homotopic.Quotient.cast_heq _ _).symm)

/-- Helper for Exercise 79.4: torus coordinates turn the range of an induced product map
into the product of its two coordinate ranges. -/
private lemma fundamentalGroup_circle_prod_circle_range_prodMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f : C(X, Circle)) (g : C(Y, Circle))
    (hf : f x = 1) (hg : g y = 1) (hfg : f.prodMap g (x, y) = (1, 1)) :
    (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
      (FundamentalGroup.mapOfEq (f.prodMap g) hfg)).range =
        (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
            (FundamentalGroup.mapOfEq f hf)).range.prod
          (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
            (FundamentalGroup.mapOfEq g hg)).range := by
  let coordinateMap :=
    (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
        (FundamentalGroup.mapOfEq f hf)).prodMap
      (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
        (FundamentalGroup.mapOfEq g hg))
  have hmap :
      fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (f.prodMap g) hfg) =
        coordinateMap.comp (FundamentalGroup.prodMulEquiv x y).toMonoidHom := by
    -- The product equivalence exposes the two projections, where the projection lemmas apply.
    apply MonoidHom.ext
    intro a
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    calc
      fundamentalGroup_circle_prod_circle.toMonoidHom
          (FundamentalGroup.mapOfEq (f.prodMap g) hfg a) =
          (Circle.fundamentalGroupEquivInt
              (Path.Homotopic.projLeft
                (FundamentalGroup.mapOfEq (f.prodMap g) hfg a)),
            Circle.fundamentalGroupEquivInt
              (Path.Homotopic.projRight
                (FundamentalGroup.mapOfEq (f.prodMap g) hfg a))) :=
        fundamentalGroup_circle_prod_circle_apply _
      _ = coordinateMap
          (Path.Homotopic.projLeft a, Path.Homotopic.projRight a) := by
        simp only [coordinateMap, MonoidHom.coe_prodMap, Prod.map_apply,
          MonoidHom.coe_comp, Function.comp_apply]
        apply Prod.ext
        · exact congrArg Circle.fundamentalGroupEquivInt
            (projLeft_mapOfEq_prodMap x y 1 1 f g hf hg hfg a)
        · exact congrArg Circle.fundamentalGroupEquivInt
            (projRight_mapOfEq_prodMap x y 1 1 f g hf hg hfg a)
      _ = coordinateMap ((FundamentalGroup.prodMulEquiv x y).toMonoidHom a) :=
        congrArg coordinateMap (FundamentalGroup.prodMulEquiv_apply x y a).symm
  -- Surjectivity of the product equivalence removes the source-coordinate precomposition.
  calc
    (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (f.prodMap g) hfg)).range =
        (coordinateMap.comp (FundamentalGroup.prodMulEquiv x y).toMonoidHom).range :=
      congrArg MonoidHom.range hmap
    _ = (FundamentalGroup.prodMulEquiv x y).toMonoidHom.range.map coordinateMap :=
      MonoidHom.range_comp _ _
    _ = (⊤ : Subgroup
          (FundamentalGroup X x × FundamentalGroup Y y)).map coordinateMap := by
      exact congrArg (fun S : Subgroup
          (FundamentalGroup X x × FundamentalGroup Y y) ↦ S.map coordinateMap)
        (MulEquiv.range_eq_top (FundamentalGroup.prodMulEquiv x y))
    _ = coordinateMap.range := (MonoidHom.range_eq_map _).symm
    _ = _ := MonoidHom.range_prodMap _ _

/-- Helper for Exercise 79.4: a homomorphism from a subsingleton group has trivial range. -/
private lemma MonoidHom.range_eq_bot_of_subsingleton_domain
    {G H : Type*} [Group G] [Group H] [Subsingleton G] (f : G →* H) :
    f.range = ⊥ := by
  -- Every source element equals `1`, so the homomorphism is the constant-one map.
  rw [MonoidHom.range_eq_bot_iff]
  ext a
  simpa only [MonoidHom.one_apply, map_one] using congrArg f (Subsingleton.elim a 1)

namespace Subgroup

/-- Helper for Exercise 79.4: the product of two cyclic subgroups is generated by their
two coordinate-axis generators. -/
private lemma zpowers_prod_eq_sup {G H : Type*} [Group G] [Group H] (a : G) (b : H) :
    (zpowers a).prod (zpowers b) = zpowers (a, 1) ⊔ zpowers (1, b) := by
  -- Each factor embeds as its corresponding coordinate-axis cyclic subgroup.
  apply le_antisymm
  · rw [prod_le_iff]
    constructor
    · simpa only [MonoidHom.map_zpowers, MonoidHom.inl_apply] using
        (le_sup_left : zpowers (a, 1) ≤ zpowers (a, 1) ⊔ zpowers (1, b))
    · simpa only [MonoidHom.map_zpowers, MonoidHom.inr_apply] using
        (le_sup_right : zpowers (1, b) ≤ zpowers (a, 1) ⊔ zpowers (1, b))
  · rw [sup_le_iff]
    constructor
    · rw [zpowers_le]
      exact ⟨mem_zpowers a, one_mem (zpowers b)⟩
    · rw [zpowers_le]
      exact ⟨one_mem (zpowers a), mem_zpowers b⟩

end Subgroup

/-- Exercise 79.4 (1): the map `(z, t) ↦ (z ^ m, Circle.exp t)` is a covering of the
torus corresponding, in projection-induced coordinates, to the subgroup generated by
`(m, 0)`. -/
theorem torusCover_firstCyclic (m : ℕ) (hm : 0 < m) :
    IsCoveringMap (TorusCover.firstCyclic m) ∧
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (TorusCover.firstCyclic m)
          (TorusCover.firstCyclic_basepoint m))).range =
        Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1) := by
  refine ⟨?_, ?_⟩
  · -- Product the two coordinate covering maps.
    exact (CircleMap.isCoveringMap_zpower_nat m (Nat.ne_of_gt hm)).prodMap
      Circle.isCoveringMap_exp
  · -- Split the induced range into its power and exponential coordinate ranges.
    have hexp : Circle.exp 0 = 1 := Circle.exp_zero
    unfold TorusCover.firstCyclic
    rw [fundamentalGroup_circle_prod_circle_range_prodMap 1 0
      (CircleMap.zpower (m : ℤ)) Circle.exp (CircleMap.zpower_one (m : ℤ)) hexp
      (TorusCover.firstCyclic_basepoint m)]
    rw [CircleMap.induced_zpower_range]
    rw [MonoidHom.range_eq_bot_of_subsingleton_domain]
    rw [← Subgroup.zpowers_one_eq_bot, Subgroup.zpowers_prod_eq_sup]
    have hpone : Subgroup.zpowers
        ((1, 1) : Multiplicative ℤ × Multiplicative ℤ) = ⊥ :=
      Subgroup.zpowers_one_eq_bot
    rw [hpone, sup_bot_eq]

/-- Companion to Exercise 79.4 (2): the map `(s, t) ↦ (Circle.exp s, Circle.exp t)` is a
covering of the torus corresponding, in projection-induced coordinates, to the trivial subgroup. -/
theorem torusCover_universal :
    IsCoveringMap TorusCover.universal ∧
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq TorusCover.universal
          TorusCover.universal_basepoint)).range = ⊥ := by
  refine ⟨?_, ?_⟩
  · -- The product of the two exponential coverings covers the torus.
    exact Circle.isCoveringMap_exp.prodMap Circle.isCoveringMap_exp
  · -- Both source fundamental groups are trivial, hence so are both coordinate ranges.
    have hexp : Circle.exp 0 = 1 := Circle.exp_zero
    unfold TorusCover.universal
    rw [fundamentalGroup_circle_prod_circle_range_prodMap 0 0 Circle.exp Circle.exp
      hexp hexp TorusCover.universal_basepoint]
    rw [MonoidHom.range_eq_bot_of_subsingleton_domain]
    exact Subgroup.bot_prod_bot

/-- Companion to Exercise 79.4 (3): the map `(z, w) ↦ (z ^ m, w ^ n)` is a covering of the torus
corresponding, in projection-induced coordinates, to the subgroup generated by `(m, 0)` and
`(0, n)`. -/
theorem torusCover_rectangular (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsCoveringMap (TorusCover.rectangular m n) ∧
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (TorusCover.rectangular m n)
          (TorusCover.rectangular_basepoint m n))).range =
        Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1) ⊔
          Subgroup.zpowers (1, Multiplicative.ofAdd (n : ℤ)) := by
  refine ⟨?_, ?_⟩
  · -- Product the two positive-degree circle coverings.
    exact (CircleMap.isCoveringMap_zpower_nat m (Nat.ne_of_gt hm)).prodMap
      (CircleMap.isCoveringMap_zpower_nat n (Nat.ne_of_gt hn))
  · -- Compute both coordinate ranges and assemble their two axis generators.
    unfold TorusCover.rectangular
    rw [fundamentalGroup_circle_prod_circle_range_prodMap 1 1
      (CircleMap.zpower (m : ℤ)) (CircleMap.zpower (n : ℤ))
      (CircleMap.zpower_one (m : ℤ)) (CircleMap.zpower_one (n : ℤ))
      (TorusCover.rectangular_basepoint m n)]
    rw [CircleMap.induced_zpower_range, CircleMap.induced_zpower_range,
      Subgroup.zpowers_prod_eq_sup]
