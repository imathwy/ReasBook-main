import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_3_9_1 (from Chap03) -/
universe u v

open scoped FundamentalGroup

variable {H : Type u} {G : Type v}
  [TopologicalSpace H] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [ConnectedSpace H] [LocPathConnectedSpace H]
  {p : H → G}

section

variable (hp : IsCoveringMap p) (e : p ⁻¹' ({1} : Set G))

include hp e

/-- Helper for Problem 3.9.1: the multiplication map on `G` pulled back along the covering map
`p`. -/
def covering_base_mul : C(H × H, G) :=
  { toFun := fun z ↦ p z.1 * p z.2
    continuous_toFun := (hp.continuous.comp continuous_fst).mul (hp.continuous.comp continuous_snd) }

/-- Helper for Problem 3.9.1: the inversion map on `G` pulled back along the covering map `p`. -/
def covering_base_inv : C(H, G) :=
  { toFun := fun x ↦ (p x)⁻¹
    continuous_toFun := hp.continuous.inv }

/-- Helper for Problem 3.9.1: when the target basepoint is definitionally unchanged, the ordinary
fundamental-group map agrees with `mapOfEq`. -/
theorem fundamental_group_map_eq_mapOfEq_rfl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (x : X) :
    FundamentalGroup.map f x = FundamentalGroup.mapOfEq f rfl := by
  -- In the definitional-basepoint case, both maps act identically on loop representatives.
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  simpa using (FundamentalGroup.mapOfEq_apply (f := f) (h := rfl) (p := r)).symm

/-- Helper for Problem 3.9.1: two continuous lifts through the fixed covering map agree on a
preconnected domain once their composites with `p` agree and they match at one point. -/
theorem covering_lift_ext
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (f g : C(A, H)) {a₀ : A}
    (hcomp : p ∘ f = p ∘ g) (hbase : f a₀ = g a₀) :
    f = g := by
  -- Uniqueness of lifts for coverings reduces equality of continuous maps to one point check.
  ext a
  exact congrFun (hp.eq_of_comp_eq f.continuous g.continuous hcomp a₀ hbase) a

/-- Helper for Problem 3.9.1: the image of the base multiplication map on
`π₁(H × H, (e, e))` lands in the covering subgroup determined by `p`. -/
theorem mul_lift_range_le
    (he_mul : p e = covering_base_mul hp (e, e)) :
    (FundamentalGroup.map (covering_base_mul hp) (e, e)).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_mul).range := by
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine Quotient.inductionOn γ ?_
  intro γ
  -- Route correction: normalize the covering criterion on explicit loop representatives.
  have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
  let γ₁ : Path (e : H) (e : H) := γ.map continuous_fst
  let γ₂ : Path (e : H) (e : H) := γ.map continuous_snd
  -- The normalized loop representative provides an explicit witness in the covering subgroup.
  refine MonoidHom.mem_range.mpr ?_
  refine ⟨FundamentalGroup.fromPath (.mk (γ₁.trans γ₂)), ?_⟩
  have hnorm :
      FundamentalGroup.map (covering_base_mul hp) ((e : H), (e : H))
          (FundamentalGroup.fromPath (.mk γ)) =
        FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_mul
          (FundamentalGroup.fromPath (.mk (γ₁.trans γ₂))) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change FundamentalGroup.fromPath (.mk (γ.map (covering_base_mul hp).continuous)) =
      FundamentalGroup.fromPath (.mk (((γ₁.trans γ₂).map hp.continuous).cast he_mul.symm he_mul.symm))
    apply congrArg FundamentalGroup.fromPath
    rw [Path.map_trans]
    have hmul :
        γ.map (covering_base_mul hp).continuous =
          (γ₁.map hp.continuous).mul (γ₂.map hp.continuous) := by
      ext t
      rfl
    rw [hmul]
    exact Path.Homotopic.Quotient.eq.mpr <| by
      simpa [he_one, covering_base_mul, γ₁, γ₂] using
        (loop_pointwise_mul_homotopic_trans
          ((γ₁.map hp.continuous).cast he_one.symm he_one.symm)
          ((γ₂.map hp.continuous).cast he_one.symm he_one.symm))
  simpa using hnorm.symm

/-- Problem 3.9.1 (1): for a connected locally path-connected covering space `H` over a
topological group `G`, the base multiplication has a unique continuous lift sending `(e, e)` to
`e`. The identity laws are then forced by uniqueness of lifts. -/
-- Proof sketch: apply the covering-space lifting theorem to the base multiplication
-- `fun z : H × H ↦ p z.1 * p z.2`, using the chosen point `(e, e)` over `1`. Uniqueness follows
-- from uniqueness of point-preserving lifts.
theorem existsUnique_liftedGroupMul
    : ∃! m : C(H × H, H), m (e, e) = e ∧
        ∀ z : H × H, p (m z) = p z.1 * p z.2 := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  let _ : LocPathConnectedSpace (H × H) := by
    refine LocPathConnectedSpace.of_bases
      (fun x : H × H ↦
        (LocPathConnectedSpace.path_connected_basis x.1).prod_nhds
          (LocPathConnectedSpace.path_connected_basis x.2)) ?_
    intro x i hi
    rcases i with ⟨u, v⟩
    rcases hi with ⟨hu, hv⟩
    rcases hu with ⟨-, hu_pc⟩
    rcases hv with ⟨-, hv_pc⟩
    rcases hu_pc with ⟨x₀, hx₀, hx₀_conn⟩
    rcases hv_pc with ⟨y₀, hy₀, hy₀_conn⟩
    refine ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, ?_⟩
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    refine ⟨(hx₀_conn hz₁).somePath.prod (hy₀_conn hz₂).somePath, ?_⟩
    intro t
    exact ⟨(hx₀_conn hz₁).somePath_mem t, (hy₀_conn hz₂).somePath_mem t⟩
  let _ : PathConnectedSpace (H × H) := PathConnectedSpace.of_locPathConnectedSpace
  have he_mul : p e = covering_base_mul hp (e, e) := by
    -- The chosen point `e` lies over the identity, so the base multiplication also sends `(e,e)`
    -- to that identity.
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [covering_base_mul, he_one]
  -- Apply the covering lifting criterion to the base multiplication map.
  rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
      (cov := hp) (f := covering_base_mul hp) (a₀ := (e, e)) (e₀ := e)
      (he := he_mul) (le := mul_lift_range_le (hp := hp) (e := e) he_mul) with
    ⟨m, hm, huniq⟩
  refine ⟨m, ?_, ?_⟩
  · refine ⟨hm.1, ?_⟩
    intro z
    -- Read the lift equation pointwise.
    exact congrArg (fun f : H × H → G ↦ f z) hm.2
  · intro m' hm'
    -- Any other point-preserving lift is equal by uniqueness in the lifting theorem.
    apply huniq
    refine ⟨hm'.1, ?_⟩
    ext z
    exact hm'.2 z

/-- The canonical lifted multiplication obtained from the unique existence statement. -/
noncomputable def liftedGroupMul
    : C(H × H, H) :=
  Classical.choose (ExistsUnique.exists (existsUnique_liftedGroupMul hp e))

/- The canonical lifted multiplication is the unique lift fixing `(e, e)` and covering the base
multiplication. -/
-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem for
-- `liftedGroupMul`.
theorem liftedGroupMul_spec
    : liftedGroupMul hp e (e, e) = e ∧
        ∀ z : H × H, p (liftedGroupMul hp e z) = p z.1 * p z.2 := by
  -- Unpack the point-preserving lift chosen from the unique existence statement.
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_liftedGroupMul hp e))

/-- The canonical lifted multiplication is sent to multiplication in the base group by `p`. -/
theorem liftedGroupMul_lifts
    (z : H × H) :
    p (liftedGroupMul hp e z) = p z.1 * p z.2 :=
  (liftedGroupMul_spec hp e).2 z

/-- The canonical lifted multiplication sends `(e, e)` to `e`. -/
theorem liftedGroupMul_basepoint
    : liftedGroupMul hp e (e, e) = e :=
  (liftedGroupMul_spec hp e).1

/-- The chosen point `e` is a left identity for the canonical lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (e, x)` with the identity map on `H`. Both
-- are lifts of `x ↦ p x` sending `e` to `e`, so uniqueness of lifts forces equality.
theorem liftedGroupMul_left_id
    (x : H) :
    liftedGroupMul hp e (e, x) = x := by
  let leftTranslate : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (e, y)
      continuous_toFun := by
        -- This map is the lifted multiplication restricted along `y ↦ (e, y)`.
        exact (liftedGroupMul hp e).continuous.comp (continuous_const.prodMk continuous_id) }
  have hcomp : p ∘ leftTranslate = p := by
    -- Both maps cover the same base map `y ↦ p y`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [leftTranslate, he_one] using liftedGroupMul_lifts hp e (e, y)
  have hbase : leftTranslate e = e := by
    -- The two lifts agree at the chosen point over the identity.
    simpa [leftTranslate] using liftedGroupMul_basepoint hp e
  have heq : leftTranslate = ContinuousMap.id H := by
    exact covering_lift_ext (hp := hp) (e := e) leftTranslate (ContinuousMap.id H) hcomp hbase
  simpa [leftTranslate] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- The chosen point `e` is a right identity for the canonical lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (x, e)` with the identity map on `H`. Both
-- are lifts of `x ↦ p x` sending `e` to `e`, so uniqueness of lifts forces equality.
theorem liftedGroupMul_right_id
    (x : H) :
    liftedGroupMul hp e (x, e) = x := by
  let rightTranslate : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (y, e)
      continuous_toFun := by
        -- This map is the lifted multiplication restricted along `y ↦ (y, e)`.
        exact (liftedGroupMul hp e).continuous.comp (continuous_id.prodMk continuous_const) }
  have hcomp : p ∘ rightTranslate = p := by
    -- Both maps cover the same base map `y ↦ p y`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [rightTranslate, he_one] using liftedGroupMul_lifts hp e (y, e)
  have hbase : rightTranslate e = e := by
    -- The two lifts agree at the chosen point over the identity.
    simpa [rightTranslate] using liftedGroupMul_basepoint hp e
  have heq : rightTranslate = ContinuousMap.id H := by
    exact covering_lift_ext (hp := hp) (e := e) rightTranslate (ContinuousMap.id H) hcomp hbase
  simpa [rightTranslate] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- Problem 3.9.1 (2): the canonical lifted multiplication is associative; together with the
continuous inverse from (3), this gives a group structure on `H` with identity `e`. -/
-- Proof sketch: compare the two continuous lifts of the base map
-- `fun ((x, y), z) ↦ p x * p y * p z` obtained from the two bracketings. They agree at
-- `(e, e, e)`, so uniqueness of lifts forces them to coincide everywhere.
theorem liftedGroupMul_assoc
    (x y z : H) :
    liftedGroupMul hp e (liftedGroupMul hp e (x, y), z) =
      liftedGroupMul hp e (x, liftedGroupMul hp e (y, z)) := by
  let leftAssoc : C((H × H) × H, H) :=
    { toFun := fun t ↦ liftedGroupMul hp e (liftedGroupMul hp e (t.1.1, t.1.2), t.2)
      continuous_toFun := by
        -- Compose the lifted multiplication with itself along the left-associated pairing map.
        have hleft : Continuous fun t : (H × H) × H ↦ (t.1.1, t.1.2) := by
          exact continuous_fst.fst.prodMk continuous_fst.snd
        have hpair : Continuous fun t : (H × H) × H ↦
            (liftedGroupMul hp e (t.1.1, t.1.2), t.2) := by
          exact ((liftedGroupMul hp e).continuous.comp hleft).prodMk continuous_snd
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let rightAssoc : C((H × H) × H, H) :=
    { toFun := fun t ↦ liftedGroupMul hp e (t.1.1, liftedGroupMul hp e (t.1.2, t.2))
      continuous_toFun := by
        -- Compose the lifted multiplication with itself along the right-associated pairing map.
        have hright : Continuous fun t : (H × H) × H ↦ (t.1.2, t.2) := by
          exact continuous_fst.snd.prodMk continuous_snd
        have hpair : Continuous fun t : (H × H) × H ↦
            (t.1.1, liftedGroupMul hp e (t.1.2, t.2)) := by
          exact continuous_fst.fst.prodMk ((liftedGroupMul hp e).continuous.comp hright)
        exact (liftedGroupMul hp e).continuous.comp hpair }
  have hcomp : p ∘ leftAssoc = p ∘ rightAssoc := by
    -- Both lifts cover the same ternary multiplication map in `G`.
    funext t
    rcases t with ⟨⟨x', y'⟩, z'⟩
    simp [leftAssoc, rightAssoc, liftedGroupMul_lifts, mul_assoc]
  have hbase : leftAssoc ((e, e), e) = rightAssoc ((e, e), e) := by
    -- The two lifts agree at the chosen basepoint triple.
    simp [leftAssoc, rightAssoc, liftedGroupMul_basepoint hp e]
  have heq : leftAssoc = rightAssoc := by
    exact covering_lift_ext (hp := hp) (e := e) leftAssoc rightAssoc hcomp hbase
  simpa [leftAssoc, rightAssoc] using congrArg (fun f : C((H × H) × H, H) ↦ f ((x, y), z)) heq

/-- Helper for Problem 3.9.1: the pointwise inverse loop at `1` represents the inverse class in
`π₁(G, 1)`. -/
theorem pointwise_inv_loop_class_mul_eq_one
    (δ : Path (1 : G) 1) :
    FundamentalGroup.fromPath (.mk δ) *
      FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) = 1 := by
  let δinv : Path (1 : G) 1 := δ.inv.cast inv_one.symm inv_one.symm
  -- The pointwise product of a loop with its pointwise inverse is the constant loop.
  have hmul_refl :
      ((δinv.mul δ).cast (one_mul (1 : G)).symm (one_mul (1 : G)).symm) =
        Path.refl (1 : G) := by
    ext t
    simp [δinv, Path.mul, Path.inv_apply]
  -- Route correction: first identify the pointwise inverse loop as a genuine inverse class, and
  -- only afterward rewrite that inverse class as the reversed loop class.
  have hhom : (δinv.trans δ).Homotopic (Path.refl (1 : G)) := by
    have hmul := loop_pointwise_mul_homotopic_trans δinv δ
    rw [hmul_refl] at hmul
    simpa using hmul.symm
  -- Translate the homotopy statement into the group law on `π₁(G, 1)`.
  rw [show (1 : FundamentalGroup G (1 : G)) =
      FundamentalGroup.fromPath (.mk (Path.refl (1 : G))) by rfl]
  rw [← Path.Homotopic.Quotient.eq] at hhom
  simpa [δinv, loop_homotopy_mul_eq_trans, Path.Homotopic.Quotient.mk_trans] using hhom

/-- Helper for Problem 3.9.1: the casted pointwise inverse loop has the same class as path
reversal in `π₁(G, 1)`. -/
theorem pointwise_inv_loop_class_eq_symm
    (δ : Path (1 : G) 1) :
    FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) =
      FundamentalGroup.fromPath (.mk δ.symm) := by
  -- First express the pointwise inverse loop class as the group inverse in `π₁(G, 1)`.
  have hinv :
      FundamentalGroup.fromPath (.mk (δ.inv.cast inv_one.symm inv_one.symm)) =
        (FundamentalGroup.fromPath (.mk δ))⁻¹ := by
    simpa using
      (inv_eq_of_mul_eq_one_right
        (pointwise_inv_loop_class_mul_eq_one (hp := hp) (e := e) (δ := δ))).symm
  -- Then rewrite inversion in the fundamental group as path reversal.
  have hsymm :
      (FundamentalGroup.fromPath (.mk δ))⁻¹ =
        FundamentalGroup.fromPath (.mk δ.symm) := by
    simpa using (loop_homotopy_inv_eq_symm (γ := FundamentalGroup.fromPath (.mk δ)))
  exact hinv.trans hsymm

/-- Helper for Problem 3.9.1: a normalized inverse-loop equality at basepoint `1` implies the
original inverse-loop equality for the covering-space basepoint. -/
theorem fromPath_inv_normalization_eq
    {γ : Path (e : H) (e : H)} {he_one : p e = 1}
    {hbase_inv : covering_base_inv hp e = 1}
    {he_inv : p e = covering_base_inv hp e}
    {he_inv_to_one : 1 = p e}
    (hmain :
      FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast
        he_inv_to_one he_inv_to_one)) =
        FundamentalGroup.fromPath (.mk ((γ.map (f := fun x ↦ (p x)⁻¹) (hp.continuous.inv)).cast
          hbase_inv.symm hbase_inv.symm))) :
    FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast
      he_inv.symm he_inv.symm)) =
      FundamentalGroup.fromPath (.mk (γ.map (f := fun x ↦ (p x)⁻¹) (hp.continuous.inv))) :=
  -- Route correction: move the equality to quotient classes, where endpoint casts compose
  -- transparently and the basepoint transport can be normalized by `cast_cast`.
  by
  have hmainQ := congrArg FundamentalGroup.toPath hmain
  have hcastQ := congrArg (fun q => q.cast hbase_inv hbase_inv) hmainQ
  -- The left-hand transport composes to the original endpoint equality `he_inv.symm`.
  have hleft_eq : hbase_inv.trans he_inv_to_one = he_inv.symm := by
    exact Subsingleton.elim _ _
  -- The right-hand transport goes from `covering_base_inv hp e` to `1` and back, so it cancels.
  have hright_eq : hbase_inv.trans hbase_inv.symm = rfl := by
    exact Subsingleton.elim _ _
  simpa [Path.Homotopic.Quotient.cast_cast, hleft_eq, hright_eq] using hcastQ

/-- Helper for Problem 3.9.1: the image of the base inversion map on `π₁(H, e)` lands in the
covering subgroup determined by `p`. -/
theorem inv_lift_range_le
    (he_inv : p e = covering_base_inv hp e) :
    (FundamentalGroup.map (covering_base_inv hp) e).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he_inv).range := by
  intro x hx
  rcases MonoidHom.mem_range.mp hx with ⟨γ, rfl⟩
  refine Quotient.inductionOn γ ?_
  intro γ
  have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
  have hbase_inv : covering_base_inv hp e = 1 := by
    simpa [covering_base_inv, he_one]
  have he_inv_to_one : 1 = p e := by
    simpa [hbase_inv] using he_inv.symm
  let δ : Path (1 : G) 1 := (γ.map hp.continuous).cast he_one.symm he_one.symm
  -- The reversed representative `γ.symm` provides the explicit witness in the covering subgroup.
  refine MonoidHom.mem_range.mpr ?_
  refine ⟨FundamentalGroup.fromPath (.mk γ.symm), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  rw [FundamentalGroup.map_apply]
  -- Rewrite the ordinary fundamental-group map on `γ` to the explicit mapped loop.
  have hmap :
      Path.Homotopic.Quotient.map ⟦γ⟧ (covering_base_inv hp) =
        FundamentalGroup.fromPath (.mk (γ.map (covering_base_inv hp).continuous)) := by
    simpa using (Path.Homotopic.Quotient.mk_map (P₀ := γ) (f := covering_base_inv hp))
  rw [hmap]
  suffices hmain :
      FundamentalGroup.fromPath (.mk (((γ.symm).map hp.continuous).cast he_inv_to_one he_inv_to_one)) =
        FundamentalGroup.fromPath (.mk ((γ.map (covering_base_inv hp).continuous).cast
          hbase_inv.symm hbase_inv.symm)) by
    exact fromPath_inv_normalization_eq
      (hp := hp) (e := e) (γ := γ) (he_one := he_one)
      (hbase_inv := hbase_inv) (he_inv := he_inv)
      (he_inv_to_one := he_inv_to_one)
      (by simpa [covering_base_inv] using hmain)
  -- Normalize the mapped inverse loop to the casted pointwise inverse loop at basepoint `1`.
  have hleft :
      (γ.map (covering_base_inv hp).continuous).cast hbase_inv.symm hbase_inv.symm =
        δ.inv.cast inv_one.symm inv_one.symm := by
    ext t
    simp [δ, covering_base_inv, Path.inv_apply]
  -- Normalize the `mapOfEq` image of `γ.symm` to the reversed normalized loop `δ.symm`.
  have hright :
      ((γ.symm).map hp.continuous).cast he_inv_to_one he_inv_to_one = δ.symm := by
    ext t
    simp [δ]
  rw [hleft, pointwise_inv_loop_class_eq_symm (hp := hp) (e := e) (δ := δ)]
  rw [← hright]

/-- Problem 3.9.1 (3): the inversion map of `G` has a unique continuous lift fixing `e`; the
inverse laws for the lifted multiplication are then forced by uniqueness. -/
-- Proof sketch: lift the inversion map `fun x ↦ (p x)⁻¹` through the covering, using `e` over
-- `1`, and then compare the left- and right-inverse identities by uniqueness of lifts.
theorem existsUnique_liftedGroupInv
    : ∃! inv : C(H, H), inv e = e ∧
        ∀ x : H, p (inv x) = (p x)⁻¹ := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  have he_inv : p e = covering_base_inv hp e := by
    -- The chosen point `e` lies over the identity, so inversion also fixes the basepoint.
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simpa [covering_base_inv, he_one]
  -- Apply the covering lifting criterion to the base inversion map.
  rcases IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le
      (cov := hp) (f := covering_base_inv hp) (a₀ := e) (e₀ := e)
      (he := he_inv) (le := inv_lift_range_le (hp := hp) (e := e) he_inv) with
    ⟨inv, hinv, huniq⟩
  refine ⟨inv, ?_, ?_⟩
  · refine ⟨hinv.1, ?_⟩
    intro x
    -- Read the lift equation pointwise.
    exact congrArg (fun f : H → G ↦ f x) hinv.2
  · intro inv' hinv'
    -- Any other point-preserving lift is equal by uniqueness in the lifting theorem.
    apply huniq
    refine ⟨hinv'.1, ?_⟩
    ext x
    exact hinv'.2 x

/-- The canonical lifted inverse obtained from the unique existence statement. -/
noncomputable def liftedGroupInv
    : C(H, H) :=
  Classical.choose (ExistsUnique.exists (existsUnique_liftedGroupInv hp e))

/- The canonical lifted inverse is the unique lift fixing `e` and covering inversion in `G`. -/
-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem for
-- `liftedGroupInv`.
theorem liftedGroupInv_spec
    : liftedGroupInv hp e e = e ∧
        ∀ x : H, p (liftedGroupInv hp e x) = (p x)⁻¹ := by
  -- Unpack the point-preserving lift chosen from the unique existence statement.
  exact Classical.choose_spec (ExistsUnique.exists (existsUnique_liftedGroupInv hp e))

/-- The canonical lifted inverse covers inversion in the base group. -/
theorem liftedGroupInv_lifts
    (x : H) :
    p (liftedGroupInv hp e x) = (p x)⁻¹ :=
  (liftedGroupInv_spec hp e).2 x

/-- The canonical lifted inverse fixes the chosen point `e`. -/
theorem liftedGroupInv_basepoint
    : liftedGroupInv hp e e = e :=
  (liftedGroupInv_spec hp e).1

/-- The canonical lifted inverse is a left inverse for the lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (liftedGroupInv hp e x, x)` with the
-- constant map `e`. Both lift the constant map `1 : H → G` and agree at `e`.
theorem liftedGroupInv_left_inv
    (x : H) :
    liftedGroupMul hp e (liftedGroupInv hp e x, x) = e := by
  let leftInverseMap : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (liftedGroupInv hp e y, y)
      continuous_toFun := by
        -- Compose multiplication with the pair `(inv y, y)`.
        have hpair : Continuous fun y : H ↦ (liftedGroupInv hp e y, y) := by
          exact (liftedGroupInv hp e).continuous.prodMk continuous_id
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let constE : C(H, H) :=
    { toFun := fun _ ↦ e
      continuous_toFun := continuous_const }
  have hcomp : p ∘ leftInverseMap = p ∘ constE := by
    -- Both lifts cover the constant map with value `1`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simp [leftInverseMap, constE, liftedGroupMul_lifts, liftedGroupInv_lifts, he_one]
  have hbase : leftInverseMap e = constE e := by
    -- They also agree at the chosen lift of `1`.
    simp [leftInverseMap, constE, liftedGroupMul_basepoint hp e, liftedGroupInv_basepoint hp e]
  have heq : leftInverseMap = constE := by
    exact covering_lift_ext (hp := hp) (e := e) leftInverseMap constE hcomp hbase
  simpa [leftInverseMap, constE] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- The canonical lifted inverse is a right inverse for the lifted multiplication. -/
-- Proof sketch: compare `x ↦ liftedGroupMul hp e (x, liftedGroupInv hp e x)` with the
-- constant map `e`. Both lift the constant map `1 : H → G` and agree at `e`.
theorem liftedGroupInv_right_inv
    (x : H) :
    liftedGroupMul hp e (x, liftedGroupInv hp e x) = e := by
  let rightInverseMap : C(H, H) :=
    { toFun := fun y ↦ liftedGroupMul hp e (y, liftedGroupInv hp e y)
      continuous_toFun := by
        -- Compose multiplication with the pair `(y, inv y)`.
        have hpair : Continuous fun y : H ↦ (y, liftedGroupInv hp e y) := by
          exact continuous_id.prodMk (liftedGroupInv hp e).continuous
        exact (liftedGroupMul hp e).continuous.comp hpair }
  let constE : C(H, H) :=
    { toFun := fun _ ↦ e
      continuous_toFun := continuous_const }
  have hcomp : p ∘ rightInverseMap = p ∘ constE := by
    -- Both lifts cover the constant map with value `1`.
    funext y
    have he_one : p e = 1 := Set.mem_singleton_iff.mp e.2
    simp [rightInverseMap, constE, liftedGroupMul_lifts, liftedGroupInv_lifts, he_one]
  have hbase : rightInverseMap e = constE e := by
    -- They also agree at the chosen lift of `1`.
    simp [rightInverseMap, constE, liftedGroupMul_basepoint hp e, liftedGroupInv_basepoint hp e]
  have heq : rightInverseMap = constE := by
    exact covering_lift_ext (hp := hp) (e := e) rightInverseMap constE hcomp hbase
  simpa [rightInverseMap, constE] using congrArg (fun f : C(H, H) ↦ f x) heq

/-- Problem 3.9.1, owner form: the lifted multiplication and inverse define a group structure on
`H` with identity `e`. -/
@[reducible] noncomputable def liftedGroup
    : Group H where
  mul x y := liftedGroupMul hp e (x, y)
  mul_assoc x y z := liftedGroupMul_assoc hp e x y z
  one := e
  one_mul x := liftedGroupMul_left_id hp e x
  mul_one x := liftedGroupMul_right_id hp e x
  inv := liftedGroupInv hp e
  inv_mul_cancel x := liftedGroupInv_left_inv hp e x

/-- Problem 3.9.1, owner form: the lifted group structure is topological because the chosen
multiplication and inverse were constructed as continuous maps. -/
@[reducible] noncomputable def liftedIsTopologicalGroup
    : letI : Group H := liftedGroup hp e
      IsTopologicalGroup H := by
  letI := liftedGroup hp e
  refine
    { continuous_mul := ?_
      continuous_inv := ?_ }
  · change Continuous fun z : H × H ↦ liftedGroupMul hp e z
    exact (liftedGroupMul hp e).continuous
  · change Continuous fun x : H ↦ liftedGroupInv hp e x
    exact (liftedGroupInv hp e).continuous

/-- Problem 3.9.1, canonical bridge: with the lifted group structure on `H`, the covering map is a
continuous group homomorphism. -/
noncomputable def liftedCoveringHom
    : letI : Group H := liftedGroup hp e
      letI : IsTopologicalGroup H := liftedIsTopologicalGroup hp e
      H →ₜ* G := by
  letI : Group H := liftedGroup hp e
  letI : IsTopologicalGroup H := liftedIsTopologicalGroup hp e
  exact
    { toFun := p
      map_one' := by
        change p e = 1
        exact Set.mem_singleton_iff.mp e.2
      map_mul' := fun x y ↦ by
        change p (liftedGroupMul hp e (x, y)) = p x * p y
        simpa using liftedGroupMul_lifts hp e (x, y)
      continuous_toFun := hp.continuous }

/-- The canonical lifted covering homomorphism is the original underlying map `p`. -/
@[simp] theorem liftedCoveringHom_apply
    (x : H) :
    liftedCoveringHom hp e x = p x :=
  by
    change p x = p x
    rfl

end

section

variable {H : Type u} {G : Type v}
  [TopologicalSpace H] [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
  [ConnectedSpace H] [LocPathConnectedSpace H]
  {p : H → G}

variable (hp : IsCoveringMap p) (e : p ⁻¹' ({1} : Set G))

include hp e

/-- Helper for Problem 3.9.1: the swapped lifted multiplication covers the same base
multiplication map when the base group is commutative. -/
theorem swapped_liftedGroupMul_lifts
    (z : H × H) :
    p (({ toFun := fun w : H × H ↦ liftedGroupMul hp e (w.2, w.1)
          continuous_toFun :=
            (liftedGroupMul hp e).continuous.comp (continuous_snd.prodMk continuous_fst) } :
        C(H × H, H)) z) =
      p z.1 * p z.2 := by
  -- Swapping the arguments only changes the order of multiplication in the abelian base group.
  simpa [mul_comm] using liftedGroupMul_lifts hp e (z.2, z.1)

/-- Problem 3.9.1 (4): if the base topological group `G` is abelian, then the canonical lifted
multiplication on `H` is commutative, so `H` is abelian as well. -/
-- Proof sketch: compare the two continuous lifts of the commutative base multiplication
-- `fun z : H × H ↦ p z.1 * p z.2`, namely `liftedGroupMul hp e` and
-- `fun z ↦ liftedGroupMul hp e (z.2, z.1)`. In the commutative base group they cover the same map
-- and both send `(e, e)` to `e`, so uniqueness forces them to agree.
theorem liftedGroupMul_comm
    (x y : H) :
    liftedGroupMul hp e (x, y) =
      liftedGroupMul hp e (y, x) := by
  let _ : PathConnectedSpace H := PathConnectedSpace.of_locPathConnectedSpace
  let _ : LocPathConnectedSpace (H × H) := by
    refine LocPathConnectedSpace.of_bases
      (fun x : H × H ↦
        (LocPathConnectedSpace.path_connected_basis x.1).prod_nhds
          (LocPathConnectedSpace.path_connected_basis x.2)) ?_
    intro x i hi
    rcases i with ⟨u, v⟩
    rcases hi with ⟨hu, hv⟩
    rcases hu with ⟨-, hu_pc⟩
    rcases hv with ⟨-, hv_pc⟩
    rcases hu_pc with ⟨x₀, hx₀, hx₀_conn⟩
    rcases hv_pc with ⟨y₀, hy₀, hy₀_conn⟩
    refine ⟨(x₀, y₀), ⟨hx₀, hy₀⟩, ?_⟩
    intro z hz
    rcases hz with ⟨hz₁, hz₂⟩
    refine ⟨(hx₀_conn hz₁).somePath.prod (hy₀_conn hz₂).somePath, ?_⟩
    intro t
    exact ⟨(hx₀_conn hz₁).somePath_mem t, (hy₀_conn hz₂).somePath_mem t⟩
  let _ : PathConnectedSpace (H × H) := PathConnectedSpace.of_locPathConnectedSpace
  let swapMul : C(H × H, H) :=
    { toFun := fun z ↦ liftedGroupMul hp e (z.2, z.1)
      continuous_toFun := (liftedGroupMul hp e).continuous.comp (continuous_snd.prodMk continuous_fst) }
  have hcomp : p ∘ swapMul = p ∘ liftedGroupMul hp e := by
    -- Both maps cover the same base multiplication map because `G` is commutative.
    funext z
    calc
      p (swapMul z) = p z.1 * p z.2 := by
        simpa [swapMul] using swapped_liftedGroupMul_lifts (hp := hp) (e := e) z
      _ = p (liftedGroupMul hp e z) := by
        symm
        exact liftedGroupMul_lifts hp e z
  have hbase : swapMul (e, e) = liftedGroupMul hp e (e, e) := by
    -- The two lifts agree at the chosen point over the identity.
    simp [swapMul, liftedGroupMul_basepoint hp e]
  have heq : swapMul = liftedGroupMul hp e := by
    -- Uniqueness of lifts on the preconnected product domain forces equality.
    exact covering_lift_ext (hp := hp) (e := e) swapMul (liftedGroupMul hp e) hcomp hbase
  simpa [swapMul] using congrArg (fun f : C(H × H, H) ↦ f (x, y)) heq.symm

/-- If the base group is commutative, the lifted group structure upgrades to a commutative group. -/
@[reducible] noncomputable def liftedCommGroup :
    CommGroup H :=
  { liftedGroup hp e with
    mul_comm := liftedGroupMul_comm hp e }

end

/-! ### Problem_3_9_2 (from Chap03) -/
open CategoryTheory

universe u

variable {H G : Type u}
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Helper for Problem 3.9.2: the kernel of a covering homomorphism inherits the discrete
topology from the fiber over `1`. -/
private theorem kernel_discreteTopology_of_covering
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    DiscreteTopology p.ker := by
  -- The kernel is exactly the fiber over the identity element.
  simpa using (hp 1).discreteTopology_fiber

/-- Helper for Problem 3.9.2: the conjugation map into a discrete normal subgroup is constant on a
connected group. -/
private theorem conjugation_to_discrete_normal_subgroup_constant
    [ConnectedSpace G] {N : Subgroup G} [DiscreteTopology N] [hN : N.Normal]
    (n : G) (hn : n ∈ N) :
    ∀ g : G, (⟨g * n * g⁻¹, hN.conj_mem n hn g⟩ : N) = ⟨n, hn⟩ := by
  let c : G → N := fun x ↦ ⟨x * n * x⁻¹, hN.conj_mem n hn x⟩
  -- A continuous map from a connected space to a discrete space must be constant.
  have hc : Continuous c := by
    exact Continuous.subtype_mk
      ((continuous_id.mul continuous_const).mul continuous_inv)
      (fun x ↦ hN.conj_mem n hn x)
  intro g
  simpa [c] using TotallyDisconnectedSpace.eq_of_continuous c hc g 1

/-- Helper for Problem 3.9.2: a covering-space automorphism preserves the base projection
pointwise. -/
private theorem covering_space_aut_comm
    (p : H →ₜ* G) (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) (x : H) :
    p (α.hom.left.hom x) = p x := by
  -- Evaluate the commutative triangle defining the morphism in `Over`.
  have hx := congrArg
    (fun f : TopCat.of H ⟶ TopCat.of G ↦ f.hom x)
    (Over.w α.hom)
  simpa [ContinuousMap.comp_apply] using hx

/-- Problem 3.9.2 (1): the kernel of a covering homomorphism is a discrete normal subgroup. -/
-- Proof sketch: the kernel is the fiber over `1`, so its discreteness comes from the covering
-- condition. Normality is the usual kernel-normality property of a group homomorphism.
theorem kernel_discrete_and_normal
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    DiscreteTopology p.ker ∧ p.ker.Normal := by
  -- Combine the covering-space discreteness of the fiber with kernel normality.
  refine ⟨kernel_discreteTopology_of_covering p hp, ?_⟩
  simpa using p.toMonoidHom.normal_ker

/-- Problem 3.9.2 (2): a discrete normal subgroup of a connected topological group is central. -/
-- Proof sketch: for each `n ∈ N`, the conjugation map `g ↦ g * n * g⁻¹` is continuous from the
-- connected space `G` into the discrete subgroup `N`, hence constant. Evaluating at `1` shows
-- every conjugate of `n` equals `n`.
theorem discreteNormalSubgroup_le_center
    [ConnectedSpace G] {N : Subgroup G} [DiscreteTopology N] [N.Normal] :
    N ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  -- The conjugation map is constant, so the conjugate of `n` by `g` is again `n`.
  have hconj := congrArg Subtype.val
    (conjugation_to_discrete_normal_subgroup_constant (N := N) n hn g)
  have hconj' : g * n * g⁻¹ = n := by
    simpa using hconj
  calc
    g * n = (g * n * g⁻¹) * g := by group
    _ = n * g := by rw [hconj']

-- Left translation by a kernel element lies over the covering homomorphism `p`.
-- Proof sketch: if `k ∈ ker p`, then `p (k * h) = p k * p h = p h`, so left translation by `k`
-- commutes with the map `p`.
private theorem kernelLeftTranslation_over
    (p : H →ₜ* G) (k : p.ker) :
    TopCat.ofHom (Homeomorph.mulLeft (k : H)) ≫ TopCat.ofHom p.toContinuousMap =
      TopCat.ofHom p.toContinuousMap := by
  -- Evaluate the commutative triangle pointwise and use `p k = 1`.
  ext x
  have hk : p (k : H) = 1 := k.2
  simp [Homeomorph.coe_mulLeft, hk, map_mul]

/-- Left translation by a kernel element defines a covering-space automorphism of `p`. -/
def kernelLeftTranslationAut
    (p : H →ₜ* G) (k : p.ker) :
    Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) :=
  Over.isoMk
    ((TopCat.isoOfHomeo (Homeomorph.mulLeft (k : H))) : TopCat.of H ≅ TopCat.of H)
    (kernelLeftTranslation_over p k)

/-- Left translation by the identity kernel element is the identity covering automorphism. -/
-- Proof sketch: multiplication by `1` is the identity map on `H`, hence also the identity in the
-- over-category.
theorem kernelLeftTranslationAut_one
    (p : H →ₜ* G) :
    kernelLeftTranslationAut p (1 : p.ker) = 1 := by
  -- It suffices to compare the underlying morphisms in `Over`.
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  ext x
  change ((Homeomorph.mulLeft (1 : H)) x : H) = x
  simp [Homeomorph.coe_mulLeft]

/-- Left translation sends multiplication in the kernel to multiplication in the covering
automorphism group. -/
-- Proof sketch: the composite of left translations by `k` and `l` is left translation by
-- `k * l`, and multiplication in `Aut` is composition.
theorem kernelLeftTranslationAut_mul
    (p : H →ₜ* G) (k l : p.ker) :
    kernelLeftTranslationAut p (k * l) =
      kernelLeftTranslationAut p k * kernelLeftTranslationAut p l := by
  -- The underlying homeomorphisms compose exactly by multiplication in the group.
  have hIso :
      (TopCat.isoOfHomeo (Homeomorph.mulLeft (((k * l : p.ker) : H))) :
          TopCat.of H ≅ TopCat.of H) =
        (TopCat.isoOfHomeo (Homeomorph.mulLeft (l : H)) :
            TopCat.of H ≅ TopCat.of H) ≪≫
          (TopCat.isoOfHomeo (Homeomorph.mulLeft (k : H)) :
            TopCat.of H ≅ TopCat.of H) := by
    apply Iso.ext
    ext x
    change (↑(k * l) : H) * x = ↑k * (↑l * x)
    change (↑k * ↑l) * x = ↑k * (↑l * x)
    simp [mul_assoc]
  rw [CategoryTheory.Aut.Aut_mul_def]
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  simpa [kernelLeftTranslationAut, TopCat.isoOfHomeo_hom, CategoryTheory.Iso.trans_hom] using
    congrArg Iso.hom hIso

/-- The canonical homomorphism from `ker p` to covering-space automorphisms is given by left
translation. -/
def kernelLeftTranslationAutHom
    (p : H →ₜ* G) :
    p.ker →* Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) where
  toFun := kernelLeftTranslationAut p
  map_one' := kernelLeftTranslationAut_one p
  map_mul' := kernelLeftTranslationAut_mul p

section ConnectedTotalSpace

variable [ConnectedSpace H]

/-- Helper for Problem 3.9.2: the image of `1` under a covering-space automorphism lies in the
kernel. -/
private theorem autInvFun_mem_kernel
    (p : H →ₜ* G) (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) :
    α.hom.left.hom (1 : H) ∈ p.ker := by
  -- The automorphism lies over `p`, so it preserves the basepoint value.
  simpa using covering_space_aut_comm p α (1 : H)

/-- Helper for Problem 3.9.2: evaluating a covering-space automorphism at `1` gives the candidate
kernel element inverse to left translation. -/
private def autInvFun
    (p : H →ₜ* G) :
    Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) → p.ker :=
  fun α ↦ ⟨α.hom.left.hom (1 : H), autInvFun_mem_kernel p α⟩

/-- Helper for Problem 3.9.2: the evaluation map at `1` is a left inverse to left translation. -/
private theorem autInvFun_leftInverse
    (p : H →ₜ* G) :
    Function.LeftInverse (autInvFun p) (kernelLeftTranslationAutHom p) := by
  intro k
  -- Left translation by `k` sends `1` to `k`.
  ext
  change (k : H) * 1 = k
  simp

/-- Helper for Problem 3.9.2: on a connected total space, every covering-space automorphism is the
left translation by its value at `1`. -/
private theorem autInvFun_rightInverse
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    Function.RightInverse (autInvFun p) (kernelLeftTranslationAutHom p) := by
  letI : DiscreteTopology p.ker := kernel_discreteTopology_of_covering p hp
  intro α
  let f : H → H := α.hom.left.hom
  have hf : Continuous f := α.hom.left.hom.continuous
  -- The ratio `f y * y⁻¹` lands in the discrete kernel, so connectedness forces it to be constant.
  have hratio_mem : ∀ y : H, f y * y⁻¹ ∈ p.ker := by
    intro y
    show p (f y * y⁻¹) = 1
    have hy := covering_space_aut_comm p α y
    rw [map_mul, map_inv, hy]
    simp
  let ratio : H → p.ker := fun y ↦ ⟨f y * y⁻¹, hratio_mem y⟩
  have hratio : Continuous ratio := by
    exact Continuous.subtype_mk (hf.mul continuous_inv) hratio_mem
  have hconst : ∀ y : H, ratio y = ratio (1 : H) := by
    intro y
    exact TotallyDisconnectedSpace.eq_of_continuous ratio hratio y 1
  have hratio_val : ∀ y : H, f y * y⁻¹ = autInvFun p α := by
    intro y
    have hy := hconst y
    have hval : (ratio y : H) = ratio (1 : H) := congrArg (fun z : p.ker ↦ (z : H)) hy
    simpa [ratio, autInvFun, f] using hval
  apply Iso.ext
  apply CostructuredArrow.hom_ext
  ext x
  let xH : H := x
  -- Rewrite the automorphism value using the constant ratio.
  have happly :
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H) =
        (autInvFun p α : H) * xH := by
    change ((Homeomorph.mulLeft (autInvFun p α : H)) x : H) =
      (autInvFun p α : H) * xH
    rfl
  have htranslate :
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H) = f xH := by
    calc
      ((kernelLeftTranslationAutHom p (autInvFun p α)).hom.left.hom x : H)
          = (autInvFun p α : H) * xH := happly
      _ = (f xH * xH⁻¹) * xH := by rw [hratio_val xH]
      _ = f xH := by group
  simpa [f, xH] using htranslate

/-- The canonical homomorphism from `ker p` to covering automorphisms is bijective when the total
space `H` is connected. -/
-- Proof sketch: injectivity follows by evaluating a deck transformation at `1`. For
-- surjectivity, any covering automorphism sends `1` to some kernel element `k`, and uniqueness of
-- lifts on the connected total space `H` forces the automorphism to be left translation by `k`.
theorem kernelLeftTranslationAutHom_bijective
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    Function.Bijective (kernelLeftTranslationAutHom p) := by
  -- The explicit inverse is evaluation at `1`.
  refine ⟨(autInvFun_leftInverse p).injective, ?_⟩
  intro α
  exact ⟨autInvFun p α, autInvFun_rightInverse p hp α⟩

/-- Problem 3.9.2 (3): if the total group `H` is connected, left translation `h ↦ k * h`
identifies `ker p` with the automorphism group of the covering space `p`. -/
noncomputable def kernelMulEquivCoveringSpaceAut
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    p.ker ≃* Aut (Over.mk (TopCat.ofHom p.toContinuousMap)) :=
  MulEquiv.ofBijective
    (kernelLeftTranslationAutHom p)
    (kernelLeftTranslationAutHom_bijective p hp)

/-- The equivalence `kernelMulEquivCoveringSpaceAut` sends a kernel element to its left-translation
covering automorphism. -/
-- Proof sketch: unfold `kernelMulEquivCoveringSpaceAut`; `MulEquiv.ofBijective` keeps the same
-- underlying forward map as `kernelLeftTranslationAutHom`.
@[simp] theorem kernelMulEquivCoveringSpaceAut_apply
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) (k : p.ker) :
    kernelMulEquivCoveringSpaceAut p hp k = kernelLeftTranslationAut p k := by
  -- `MulEquiv.ofBijective` preserves the original forward map.
  rfl

/-- Applying the inverse equivalence recovers the kernel element whose left translation realizes
a given covering automorphism. -/
-- Proof sketch: this is the inverse-direction analogue of
-- `kernelMulEquivCoveringSpaceAut_apply`, using the defining inverse property of the
-- multiplicative equivalence.
@[simp] theorem kernelMulEquivCoveringSpaceAut_symm_apply
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G))
    (α : Aut (Over.mk (TopCat.ofHom p.toContinuousMap))) :
    kernelLeftTranslationAut p ((kernelMulEquivCoveringSpaceAut p hp).symm α) = α := by
  -- Apply the inverse property of the multiplicative equivalence.
  simpa using (kernelMulEquivCoveringSpaceAut p hp).apply_symm_apply α

/-- The equivalence `kernelMulEquivCoveringSpaceAut` is realized by the canonical homomorphism
`kernelLeftTranslationAutHom`. -/
-- Proof sketch: unfold `kernelMulEquivCoveringSpaceAut`; `MulEquiv.ofBijective` keeps the same
-- underlying monoid homomorphism.
@[simp] theorem kernelMulEquivCoveringSpaceAut_toMonoidHom
    (p : H →ₜ* G) (hp : IsCoveringMap (p : H → G)) :
    (kernelMulEquivCoveringSpaceAut p hp).toMonoidHom = kernelLeftTranslationAutHom p := by
  -- This is definitional for `MulEquiv.ofBijective`.
  rfl

end ConnectedTotalSpace

/-! ### Problem_3_9_3 (from Chap03) -/
/-- The branching interval obtained from countably many copies of `(0,1]` and a single point over
`0`. -/
abbrev BranchingInterval : Type :=
  { z : Set.Icc (0 : ℝ) 1 × ℕ // ((z.1 : ℝ) = 0 → z.2 = 0) }

/-- Problem 3.9.3: the projection from the branching interval onto the closed unit interval is the
standard example of a surjective local homeomorphism that fails to be a covering map. -/
def branchingIntervalProjection : BranchingInterval → Set.Icc (0 : ℝ) 1 :=
  fun z ↦ z.1.1

/-- Helper for Problem 3.9.3: the distinguished point `0` of the closed unit interval. -/
def zero_base : Set.Icc (0 : ℝ) 1 :=
  ⟨0, ⟨le_rfl, zero_le_one⟩⟩

/-- Helper for Problem 3.9.3: the `0`th branch exists above every base point. -/
def zero_branch_point (x : Set.Icc (0 : ℝ) 1) : BranchingInterval :=
  ⟨⟨x, 0⟩, fun _ ↦ rfl⟩

/-- Helper for Problem 3.9.3: the positive part of the closed unit interval. -/
def positive_base_slice : Set (Set.Icc (0 : ℝ) 1) :=
  { x | 0 < (x : ℝ) }

/-- Helper for Problem 3.9.3: the fixed `n`th branch above the positive part of the base. -/
def positive_branch_slice (n : ℕ) : Set BranchingInterval :=
  { z | 0 < (branchingIntervalProjection z : ℝ) ∧ z.1.2 = n }

/-- Helper for Problem 3.9.3: a small neighborhood of `0` in the base interval. -/
def zero_base_slice : Set (Set.Icc (0 : ℝ) 1) :=
  { x | (x : ℝ) < (1 / 2 : ℝ) }

/-- Helper for Problem 3.9.3: the `0`th branch above the small neighborhood of `0`. -/
def zero_branch_slice : Set BranchingInterval :=
  { z | (branchingIntervalProjection z : ℝ) < (1 / 2 : ℝ) ∧ z.1.2 = 0 }

/-- Helper for Problem 3.9.3: a positive base point supports every branch index. -/
theorem positive_base_supports_branch (n : ℕ) {x : Set.Icc (0 : ℝ) 1}
    (hx : 0 < (x : ℝ)) : ((x : ℝ) = 0 → n = 0) := by
  -- A positive base point cannot satisfy the branch-collapsing condition at `0`.
  intro hx0
  linarith

/-- Helper for Problem 3.9.3: reinserting a positive base point into a chosen branch. -/
def positive_branch_point (n : ℕ)
    (x : { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice }) : BranchingInterval :=
  ⟨⟨x.1, n⟩, positive_base_supports_branch n x.2⟩

/-- Helper for Problem 3.9.3: the branching projection is continuous. -/
theorem continuous_branchingIntervalProjection : Continuous branchingIntervalProjection := by
  change Continuous (fun z : BranchingInterval ↦ z.1.1)
  fun_prop

/-- Helper for Problem 3.9.3: the branch index is a continuous map to the discrete space `ℕ`. -/
theorem continuous_branch_index : Continuous fun z : BranchingInterval ↦ z.1.2 := by
  fun_prop

/-- Helper for Problem 3.9.3: the positive base slice is open in the closed interval. -/
theorem isOpen_positive_base_slice : IsOpen positive_base_slice := by
  simpa [positive_base_slice] using isOpen_lt continuous_const continuous_subtype_val

/-- Helper for Problem 3.9.3: the small neighborhood of `0` is open in the closed interval. -/
theorem isOpen_zero_base_slice : IsOpen zero_base_slice := by
  simpa [zero_base_slice] using isOpen_lt continuous_subtype_val continuous_const

/-- Helper for Problem 3.9.3: each positive branch slice is open in the branching interval. -/
theorem isOpen_positive_branch_slice (n : ℕ) : IsOpen (positive_branch_slice n) := by
  have hpos : IsOpen { z : BranchingInterval | 0 < (branchingIntervalProjection z : ℝ) } := by
    simpa [positive_base_slice] using
      isOpen_positive_base_slice.preimage continuous_branchingIntervalProjection
  have hbranch : IsOpen { z : BranchingInterval | z.1.2 = n } := by
    simpa using (isOpen_discrete ({n} : Set ℕ)).preimage continuous_branch_index
  simpa [positive_branch_slice, Set.setOf_and] using hpos.inter hbranch

/-- Helper for Problem 3.9.3: the zero-branch neighborhood is open in the branching interval. -/
theorem isOpen_zero_branch_slice : IsOpen zero_branch_slice := by
  have hsmall :
      IsOpen { z : BranchingInterval | (branchingIntervalProjection z : ℝ) < (1 / 2 : ℝ) } := by
    simpa [zero_base_slice] using
      isOpen_zero_base_slice.preimage continuous_branchingIntervalProjection
  have hbranch : IsOpen { z : BranchingInterval | z.1.2 = 0 } := by
    simpa using (isOpen_discrete ({0} : Set ℕ)).preimage continuous_branch_index
  simpa [zero_branch_slice, Set.setOf_and] using hsmall.inter hbranch

/-- Helper for Problem 3.9.3: on a fixed positive branch, the projection is an open embedding. -/
theorem positive_branch_slice_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding ((positive_branch_slice n).restrict branchingIntervalProjection) := by
  let e : { z : BranchingInterval | z ∈ positive_branch_slice n } ≃ₜ
      { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice } :=
    { toEquiv :=
        { toFun := fun z ↦ ⟨branchingIntervalProjection z.1, z.2.1⟩
          invFun := fun x ↦
            ⟨positive_branch_point n x, ⟨x.2, rfl⟩⟩
          left_inv := by
            -- Reinsert the same base point into the same branch.
            rintro ⟨z, hz⟩
            apply Subtype.ext
            apply Subtype.ext
            rcases z with ⟨⟨x, m⟩, hz0⟩
            exact Prod.ext rfl hz.2.symm
          right_inv := by
            -- Forgetting and then reinserting the branch does nothing on the base slice.
            intro x
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        -- The forward map just forgets the fixed branch coordinate.
        exact Continuous.subtype_mk
          (by
            change Continuous
              (fun z : { z : BranchingInterval | z ∈ positive_branch_slice n } ↦ z.1.1.1)
            fun_prop)
          (fun z ↦ z.2.1)
      continuous_invFun := by
        -- The inverse continuously reinserts the constant branch index.
        exact Continuous.subtype_mk
          (Continuous.subtype_mk
            (by
              fun_prop)
            (fun x ↦ positive_base_supports_branch n x.2))
          (fun x ↦ ⟨x.2, rfl⟩) }
  -- Compose the branchwise homeomorphism with the open inclusion of the positive base slice.
  simpa [e] using
    (isOpen_positive_base_slice.isOpenEmbedding_subtypeVal).comp e.isOpenEmbedding

/-- Helper for Problem 3.9.3: near `0`, the zero branch projects by an open embedding. -/
theorem zero_branch_slice_isOpenEmbedding :
    Topology.IsOpenEmbedding (zero_branch_slice.restrict branchingIntervalProjection) := by
  let e : { z : BranchingInterval | z ∈ zero_branch_slice } ≃ₜ
      { x : Set.Icc (0 : ℝ) 1 | x ∈ zero_base_slice } :=
    { toEquiv :=
        { toFun := fun z ↦ ⟨branchingIntervalProjection z.1, z.2.1⟩
          invFun := fun x ↦
            ⟨zero_branch_point x.1, ⟨x.2, rfl⟩⟩
          left_inv := by
            -- Over this neighborhood the branch index is forced to be `0`.
            rintro ⟨z, hz⟩
            apply Subtype.ext
            apply Subtype.ext
            rcases z with ⟨⟨x, m⟩, hz0⟩
            exact Prod.ext rfl hz.2.symm
          right_inv := by
            -- Forgetting and then reinserting the zero branch fixes the base point.
            intro x
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        -- The forward map again forgets the branch coordinate.
        exact Continuous.subtype_mk
          (by
            change Continuous (fun z : { z : BranchingInterval | z ∈ zero_branch_slice } ↦ z.1.1.1)
            fun_prop)
          (fun z ↦ z.2.1)
      continuous_invFun := by
        -- The inverse continuously inserts the constant zero branch.
        exact Continuous.subtype_mk
          (Continuous.subtype_mk
            (by
              fun_prop)
            (fun _ ↦ fun _ ↦ rfl))
          (fun x ↦ ⟨x.2, rfl⟩) }
  -- The chart identifies the zero branch neighborhood with an open base neighborhood.
  simpa [e] using
    (isOpen_zero_base_slice.isOpenEmbedding_subtypeVal).comp e.isOpenEmbedding

/-- Helper for Problem 3.9.3: every open neighborhood of `0` in `[0,1]` contains a positive
point. -/
theorem unit_interval_exists_positive_mem_of_open_zero
    {V : Set (Set.Icc (0 : ℝ) 1)} (hVOpen : IsOpen V) (hzV : zero_base ∈ V) :
    ∃ y : Set.Icc (0 : ℝ) 1, 0 < (y : ℝ) ∧ y ∈ V := by
  -- Move from openness at `0` to a metric ball around the endpoint.
  have hVnhds : V ∈ nhds zero_base := hVOpen.mem_nhds hzV
  rcases Metric.mem_nhds_iff.mp hVnhds with ⟨ε, hεpos, hεsub⟩
  let y : Set.Icc (0 : ℝ) 1 := ⟨min (ε / 2) (1 / 2), by
    constructor
    · have hy_nonneg : 0 ≤ min (ε / 2) (1 / 2) := by
        apply le_min
        · linarith
        · norm_num
      simpa using hy_nonneg
    · have hy_le_half : min (ε / 2) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
      linarith⟩
  have hypos : 0 < (y : ℝ) := by
    -- Choosing the smaller of `ε / 2` and `1 / 2` keeps us positive and inside the interval.
    dsimp [y]
    apply lt_min
    · linarith
    · norm_num
  have hylt : (y : ℝ) < ε := by
    dsimp [y]
    have hmin : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
    linarith
  refine ⟨y, hypos, hεsub ?_⟩
  -- This chosen point lies in the radius-`ε` ball around `0`.
  change dist (y : ℝ) (zero_base : ℝ) < ε
  rw [show ((zero_base : Set.Icc (0 : ℝ) 1) : ℝ) = 0 by rfl, Real.dist_eq]
  have hy_nonneg : 0 ≤ (y : ℝ) := y.2.1
  simp [abs_of_nonneg hy_nonneg, hylt]

/-- Helper for Problem 3.9.3: the fiber over `0` is a singleton. -/
theorem branching_interval_projection_fiber_zero_subsingleton :
    Subsingleton (branchingIntervalProjection ⁻¹' ({zero_base} : Set (Set.Icc (0 : ℝ) 1))) := by
  refine ⟨?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  apply Subtype.ext
  apply Subtype.ext
  -- Both lifts have first coordinate `0`, hence their branch indices are forced to be `0`.
  have ha0 : ((a.1.1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    simpa [branchingIntervalProjection, zero_base] using
      congrArg (fun x : Set.Icc (0 : ℝ) 1 ↦ ((x : Set.Icc (0 : ℝ) 1) : ℝ)) ha
  have hb0 : ((b.1.1 : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
    simpa [branchingIntervalProjection, zero_base] using
      congrArg (fun x : Set.Icc (0 : ℝ) 1 ↦ ((x : Set.Icc (0 : ℝ) 1) : ℝ)) hb
  have haBranch : a.1.2 = 0 := a.2 ha0
  have hbBranch : b.1.2 = 0 := b.2 hb0
  exact Prod.ext (ha.trans hb.symm) (haBranch.trans hbBranch.symm)

/-- Helper for Problem 3.9.3: every positive base point has two distinct lifts. -/
theorem branching_interval_projection_has_two_lifts_of_pos (y : Set.Icc (0 : ℝ) 1)
    (hy : 0 < (y : ℝ)) :
    ∃ a b : branchingIntervalProjection ⁻¹' ({y} : Set (Set.Icc (0 : ℝ) 1)), a ≠ b := by
  let yPos : { x : Set.Icc (0 : ℝ) 1 | x ∈ positive_base_slice } := ⟨y, hy⟩
  -- Take one lift on the zero branch and another on branch `1`.
  refine ⟨⟨zero_branch_point y, rfl⟩, ⟨positive_branch_point 1 yPos, rfl⟩, ?_⟩
  intro hEq
  -- Distinct branch indices force the two lifts to be different.
  have hUnderlying := Subtype.ext_iff.mp hEq
  have hNat : 0 = 1 := by
    simpa [zero_branch_point, positive_branch_point, yPos] using
      congrArg (fun z : BranchingInterval ↦ z.1.2) hUnderlying
  exact Nat.zero_ne_one hNat

/-- The branching interval projection is surjective onto the closed unit interval. -/
-- Proof sketch: send `0` to the distinguished point lying over `0`, and send every positive
-- `x ∈ [0,1]` to the point on the `0`th branch with first coordinate `x`.
theorem branchingIntervalProjection_surjective :
    Function.Surjective branchingIntervalProjection := by
  -- Every base point has a canonical lift on branch `0`.
  intro y
  exact ⟨zero_branch_point y, rfl⟩

/-- The branching interval projection is a local homeomorphism. -/
-- Proof sketch: away from `0`, restrict to a neighborhood inside a single branch `{n}`; at the
-- distinguished point over `0`, use the `0`th branch together with the relative topology on
-- `[0,1]` to obtain a neighborhood homeomorphic to an interval in the base.
theorem branchingIntervalProjection_isLocalHomeomorph :
    IsLocalHomeomorph branchingIntervalProjection := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro z
  by_cases hzpos : 0 < (branchingIntervalProjection z : ℝ)
  · -- Away from `0`, stay inside the unique branch already containing `z`.
    refine ⟨positive_branch_slice z.1.2, ?_, ?_⟩
    · exact (isOpen_positive_branch_slice z.1.2).mem_nhds ⟨hzpos, rfl⟩
    · exact positive_branch_slice_isOpenEmbedding z.1.2
  · -- At `0`, the branching relation forces us onto branch `0`.
    have hznonneg : 0 ≤ (branchingIntervalProjection z : ℝ) := z.1.1.2.1
    have hzzero : (branchingIntervalProjection z : ℝ) = 0 := by
      linarith
    have hzbranch : z.1.2 = 0 := z.2 hzzero
    refine ⟨zero_branch_slice, ?_, ?_⟩
    · refine isOpen_zero_branch_slice.mem_nhds ?_
      refine ⟨?_, hzbranch⟩
      simp [hzzero]
    · exact zero_branch_slice_isOpenEmbedding

/-- The branching interval projection is not a covering map in the sense of Definition 3.1.5. -/
-- Proof sketch: every neighborhood of `0` in `[0,1]` contains positive points. Over `0` the fiber
-- is a singleton, while over every positive point the fiber is countably infinite, so no
-- neighborhood of `0` can be evenly covered with a fixed discrete fiber.
theorem branchingIntervalProjection_not_isPathConnectedCoveringMap :
    ¬ IsPathConnectedCoveringMap branchingIntervalProjection := by
  -- Route correction: the contradiction is detected at the evenly covered neighborhood of `0`.
  intro hp
  rcases hp.2 zero_base with ⟨_hdisc, V, hzV, hVOpen, _hVPath, _hpre, H, hH⟩
  -- Any open neighborhood of `0` in the base contains a positive point.
  obtain ⟨y, hypos, hyV⟩ := unit_interval_exists_positive_mem_of_open_zero hVOpen hzV
  obtain ⟨a, b, hab⟩ := branching_interval_projection_has_two_lifts_of_pos y hypos
  have haV : branchingIntervalProjection a.1 ∈ V := by
    rw [a.2]
    exact hyV
  have hbV : branchingIntervalProjection b.1 ∈ V := by
    rw [b.2]
    exact hyV
  let aV : branchingIntervalProjection ⁻¹' V := ⟨a.1, haV⟩
  let bV : branchingIntervalProjection ⁻¹' V := ⟨b.1, hbV⟩
  have hzeroSub :
      Subsingleton (branchingIntervalProjection ⁻¹' ({zero_base} : Set (Set.Icc (0 : ℝ) 1))) :=
    branching_interval_projection_fiber_zero_subsingleton
  have hImages : H aV = H bV := by
    apply Prod.ext
    · -- The chart sends both lifts to the same base point `y`.
      apply Subtype.ext
      rw [hH aV, hH bV]
      rw [a.2, b.2]
    · -- The fiber coordinate over `0` is unique.
      exact hzeroSub.elim _ _
  have hEqV : aV = bV := H.injective hImages
  have hEq : a = b := by
    -- Forget the ambient neighborhood restriction to recover equality in the fiber over `y`.
    apply Subtype.ext
    exact congrArg (fun x : branchingIntervalProjection ⁻¹' V ↦ x.1) hEqV
  exact hab hEq

/-! ### Problem_3_9_4 (from Chap03) -/
universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsLocalHomeomorph

/-- Compactness of the source and singleton-closedness of the target force the fibers of a local
homeomorphism to be finite. -/
theorem finite_preimage_singleton [CompactSpace X] [T1Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) (y : Y) : Set.Finite (f ⁻¹' ({y} : Set Y)) := by
  let s : Set X := f ⁻¹' ({y} : Set Y)
  have hsLocal : IsLocalHomeomorphOn f s := hf.isLocalHomeomorphOn
  letI : Subsingleton (f '' s) := by
    refine ⟨?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨x', hx', rfl⟩
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    simp [hx, hx']
  letI : DiscreteTopology (f '' s) := inferInstance
  letI : DiscreteTopology s := hsLocal.discreteTopology_of_image
  have hsClosed : IsClosed s := by
    simpa [s] using (isClosed_singleton : IsClosed ({y} : Set Y)).preimage hf.continuous
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hsClosed.isCompact
  have hsFinite : Finite s := finite_of_compact_of_discrete
  exact Set.toFinite s

/-- A compact-domain Hausdorff local homeomorphism to a Hausdorff target is a covering map. -/
-- Proof sketch: use `finite_preimage_singleton` to identify the finite discrete fiber over each
-- base point. Then choose local homeomorphism charts around the finitely many points of that
-- fiber, shrink their images to a common open neighborhood, and assemble the resulting disjoint
-- local sheets into the evenly covered neighborhood required by `IsCoveringMap`.
theorem isCoveringMap_of_compact [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsCoveringMap f := by
  -- Work over `Set.univ`, where mathlib's covering-on criterion matches the global statement.
  refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
  -- Every point of the source lies in a local homeomorphism chart realizing `f`.
  refine IsCoveringMapOn.of_openPartialHomeomorph hf.continuous ?_
  intro e _
  obtain ⟨φ, heφ, hφ⟩ := hf e
  exact ⟨φ, heφ, hφ.symm⟩

/-- Problem 3.9.4: a compact-domain local homeomorphism from a nonempty Hausdorff space to a
preconnected locally path-connected Hausdorff target is a path-connected covering map. -/
-- Proof sketch: first apply `isCoveringMap_of_compact` to obtain the canonical covering-map
-- owner. The image of a compact-domain local homeomorphism is compact and therefore closed in a
-- Hausdorff codomain, while local homeomorphisms are open; connectedness of the target then
-- forces the image to be all of `Y`, giving surjectivity. Only preconnectedness is needed here:
-- nonemptiness comes from the nonempty compact domain. Finally invoke
-- `IsCoveringMap.isPathConnectedCoveringMap`.
theorem isPathConnectedCoveringMap_of_compact [CompactSpace X] [Nonempty X] [T2Space X]
    [PreconnectedSpace Y] [LocPathConnectedSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsPathConnectedCoveringMap f := by
  have hRangeClosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hRangeOpen : IsOpen (Set.range f) := hf.isOpenMap.isOpen_range
  have hRangeNonempty : (Set.range f).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨f x, ⟨x, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨hRangeClosed, hRangeOpen⟩ hRangeNonempty
  exact (hf.isCoveringMap_of_compact).isPathConnectedCoveringMap hsurj

end IsLocalHomeomorph

/-! ### Problem_3_9_5 (from Chap03) -/
universe u v

open CategoryTheory
open QuotientGroup
open Topology

variable {G : Type u} [Group G]
variable {H K : O(G)}
variable {X : Type v} [TopologicalSpace X] [MulAction G X]

section Topological

variable [TopologicalSpace G] [DiscreteTopology G]

/-- For a discrete topological group, every quotient `G ⧸ H` is discrete. -/
instance quotientGroup_discreteTopology (H : Subgroup G) : DiscreteTopology (G ⧸ H) :=
  QuotientGroup.discreteTopology (isOpen_discrete (H : Set G))

/-- The compact-open space of continuous `G`-equivariant maps from `G ⧸ H` to `X`. -/
abbrev equivariantContinuousMapSpace (H : O(G)) (X : Type v) [TopologicalSpace X]
    [MulAction G X] :=
  { f : C(G ⧸ H, X) // ∀ g : G, ∀ q : G ⧸ H, f (g • q) = g • f q }

end Topological

/-- An `H`-fixed point of `X` has stabilizer containing `H`. -/
-- Proof sketch: unfold `MulAction.fixedPoints`; the `H`-fixed hypothesis says exactly that every
-- `h : H` fixes `x`, which is the defining condition for membership in the ambient stabilizer.
theorem fixedPoints_le_stabilizer (x : MulAction.fixedPoints H X) :
    H ≤ MulAction.stabilizer G (x : X) := by
  -- Translate the fixed-point condition into the stabilizer membership condition.
  intro h hh
  rw [MulAction.mem_stabilizer_iff]
  exact (MulAction.mem_fixedPoints.mp x.2) ⟨h, hh⟩

/-- The function on `G ⧸ H` determined by an `H`-fixed point `x`, namely `gH ↦ g • x`. -/
def fixedPointsOrbitMap (x : MulAction.fixedPoints H X) : G ⧸ H → X :=
  fun q ↦
    MulAction.ofQuotientStabilizer G (x : X)
      (Subgroup.quotientMapOfLE (fixedPoints_le_stabilizer x) q)

/-- Helper for Problem 3.9.5: on a representative `gH`, the orbit map attached to `x`
is exactly `g • x`. -/
theorem fixedPointsOrbitMap_apply_mk (x : MulAction.fixedPoints H X) (g : G) :
    fixedPointsOrbitMap x ((g : G) : G ⧸ H) = g • (x : X) := by
  -- Evaluate the quotient-stabilizer map on the representative `g`.
  simp [fixedPointsOrbitMap, Subgroup.quotientMapOfLE_apply_mk,
    MulAction.ofQuotientStabilizer_mk]

/-- The orbit-map formula attached to an `H`-fixed point is `G`-equivariant. -/
-- Proof sketch: both `quotientMapOfLE` and `MulAction.ofQuotientStabilizer` respect the left
-- `G`-action on quotient sets, so their composite does as well.
theorem fixedPointsOrbitMap_equivariant (x : MulAction.fixedPoints H X)
    (g : G) (q : G ⧸ H) :
    fixedPointsOrbitMap x (g • q) = g • fixedPointsOrbitMap x q := by
  -- Push the action through the quotient map and then through the quotient-stabilizer map.
  unfold fixedPointsOrbitMap
  rw [Subgroup.quotientMapOfLE_smul]
  simpa using
    (MulAction.ofQuotientStabilizer_smul G (x : X) g
      (Subgroup.quotientMapOfLE (fixedPoints_le_stabilizer x) q))

/-- The orbit map attached to an `H`-fixed point sends the identity coset to that point. -/
-- Proof sketch: the quotient map induced by `H ≤ stab(x)` fixes the identity coset, and
-- `MulAction.ofQuotientStabilizer` sends that identity coset to `x`.
theorem fixedPointsOrbitMap_apply_one (x : MulAction.fixedPoints H X) :
    fixedPointsOrbitMap x ((1 : G) : G ⧸ H) = x := by
  -- Specialize the representative formula to the identity coset.
  simpa using fixedPointsOrbitMap_apply_mk (H := H) x (1 : G)

section Topological

variable [TopologicalSpace G]

/-- Evaluating a `G`-equivariant map `G ⧸ H → X` at the identity coset gives an `H`-fixed point
of `X`. -/
-- Proof sketch: for `h : H`, the coset `hH` equals the identity coset in `G ⧸ H`; apply
-- equivariance of `f` to this equality.
theorem equivariantContinuousMapSpace_evalOne_mem_fixedPoints
    (f : equivariantContinuousMapSpace H X) :
    f.1 ((1 : G) : G ⧸ H) ∈ MulAction.fixedPoints H X := by
  rw [MulAction.mem_fixedPoints]
  intro h
  -- Every `h ∈ H` fixes the identity coset in `G ⧸ H`.
  have hh : (h : G) • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    simpa using
      (QuotientGroup.eq.mpr (show ((h : G)⁻¹ * 1) ∈ H by
        simp [show ((h : G)⁻¹) ∈ (H : Subgroup G) from (H : Subgroup G).inv_mem h.2]) :
          ((h : G) : G ⧸ H) = ((1 : G) : G ⧸ H))
  -- Equivariance transports that fixedness to the value of `f` at `1H`.
  calc
    (h : G) • f.1 ((1 : G) : G ⧸ H) = f.1 ((h : G) • ((1 : G) : G ⧸ H)) := by
      symm
      exact f.2 (h : G) (((1 : G) : G ⧸ H))
    _ = f.1 ((1 : G) : G ⧸ H) := by
      simp [hh]

/-- Evaluation at the identity coset sends an equivariant continuous map to its corresponding
`H`-fixed point. -/
def equivariantContinuousMapSpaceEvalOne (f : equivariantContinuousMapSpace H X) :
    MulAction.fixedPoints H X :=
  ⟨f.1 ((1 : G) : G ⧸ H), equivariantContinuousMapSpace_evalOne_mem_fixedPoints f⟩

/-- Evaluation at the identity coset is continuous on the equivariant mapping space. -/
-- Proof sketch: compose the subtype inclusion into `C(G ⧸ H, X)` with the standard continuous
-- evaluation map at the point `1H`.
theorem equivariantContinuousMapSpaceEvalOne_continuous :
    Continuous
      (equivariantContinuousMapSpaceEvalOne :
        equivariantContinuousMapSpace H X → MulAction.fixedPoints H X) := by
  -- First prove continuity of the underlying evaluation map into `X`.
  simpa [equivariantContinuousMapSpaceEvalOne] using
    (Continuous.subtype_mk
      ((continuous_eval_const ((1 : G) : G ⧸ H)).comp continuous_subtype_val)
      fun f => equivariantContinuousMapSpace_evalOne_mem_fixedPoints f)

section Discrete

variable [DiscreteTopology G]

/-- The map `gH ↦ g • x` is continuous because the quotient `G ⧸ H` is discrete. -/
-- Proof sketch: once `G ⧸ H` is given the discrete topology, every function out of it is
-- continuous.
theorem fixedPointsOrbitMap_continuous (x : MulAction.fixedPoints H X) :
    Continuous (fixedPointsOrbitMap x) := by
  letI : DiscreteTopology (G ⧸ H) := quotientGroup_discreteTopology (H := (H : Subgroup G))
  -- Every map out of a discrete space is continuous.
  exact continuous_of_discreteTopology

/-- An `H`-fixed point determines a continuous `G`-equivariant map `G ⧸ H → X`. -/
def fixedPointsToEquivariantContinuousMap (x : MulAction.fixedPoints H X) :
    equivariantContinuousMapSpace H X :=
  ⟨⟨fixedPointsOrbitMap x, fixedPointsOrbitMap_continuous x⟩,
    fixedPointsOrbitMap_equivariant x⟩

/-- Evaluating the orbit map attached to an `H`-fixed point recovers that point. -/
-- Proof sketch: unfold `equivariantContinuousMapSpaceEvalOne` and apply
-- `fixedPointsOrbitMap_apply_one`.
theorem fixedPointsToEquivariantContinuousMap_evalOne (x : MulAction.fixedPoints H X) :
    equivariantContinuousMapSpaceEvalOne (fixedPointsToEquivariantContinuousMap x) = x := by
  -- Compare the two fixed points by their underlying points of `X`.
  apply Subtype.ext
  simpa [equivariantContinuousMapSpaceEvalOne, fixedPointsToEquivariantContinuousMap] using
    fixedPointsOrbitMap_apply_one (H := H) x

/-- An equivariant continuous map is determined by its value on the identity coset. -/
-- Proof sketch: every coset has the form `g • 1H`, so equivariance forces the value at `gH` to be
-- `g • f(1H)`, which is exactly the orbit map attached to `f(1H)`.
theorem fixedPointsToEquivariantContinuousMap_right_inv
    (f : equivariantContinuousMapSpace H X) :
    fixedPointsToEquivariantContinuousMap (equivariantContinuousMapSpaceEvalOne f) = f := by
  -- Compare the two equivariant maps pointwise on quotient representatives.
  apply Subtype.ext
  ext q
  refine Quotient.inductionOn' q ?_
  intro g
  calc
    (fixedPointsToEquivariantContinuousMap (equivariantContinuousMapSpaceEvalOne f)).1
        (g : G ⧸ H) = g • (equivariantContinuousMapSpaceEvalOne f : X) := by
          simp [fixedPointsToEquivariantContinuousMap, fixedPointsOrbitMap_apply_mk]
    _ = g • f.1 ((1 : G) : G ⧸ H) := by
          rfl
    _ = f.1 (g • ((1 : G) : G ⧸ H)) := by
          exact (f.2 g (((1 : G) : G ⧸ H))).symm
    _ = f.1 (g : G ⧸ H) := by
          simp

/-- Evaluation at the identity coset gives the canonical equivalence between equivariant
continuous maps `G ⧸ H → X` and the `H`-fixed point space of `X`. -/
noncomputable def equivariantContinuousMapSpaceEquivFixedPoints :
    equivariantContinuousMapSpace H X ≃ MulAction.fixedPoints H X where
  toFun := equivariantContinuousMapSpaceEvalOne
  invFun := fixedPointsToEquivariantContinuousMap
  left_inv := fixedPointsToEquivariantContinuousMap_right_inv
  right_inv := fixedPointsToEquivariantContinuousMap_evalOne

/-- Helper for Problem 3.9.5: evaluation of the orbit-map family at a fixed coset is continuous
in the fixed point. -/
theorem fixedPointsOrbitMap_eval_continuous [ContinuousConstSMul G X] (q : G ⧸ H) :
    Continuous fun x : MulAction.fixedPoints H X => fixedPointsOrbitMap x q := by
  -- Reduce to quotient representatives, where the map is `x ↦ g • x`.
  refine Quotient.inductionOn' q ?_
  intro g
  simpa [fixedPointsOrbitMap_apply_mk] using
    (continuous_const_smul g).comp continuous_subtype_val

/-- The orbit-map construction is continuous from the `H`-fixed point space into the equivariant
mapping space. -/
-- Proof sketch: the action map `(g, x) ↦ g • x` is continuous in `x` for each fixed `g`, so the
-- family `x ↦ (gH ↦ g • x)` is continuous as a map into the compact-open function space.

theorem fixedPointsToEquivariantContinuousMap_continuous [ContinuousConstSMul G X] :
    Continuous
      (fixedPointsToEquivariantContinuousMap :
        MulAction.fixedPoints H X → equivariantContinuousMapSpace H X) := by
  letI : DiscreteTopology (G ⧸ H) := quotientGroup_discreteTopology (H := (H : Subgroup G))
  -- First build continuity of the underlying family into the plain function space.
  have hfun : Continuous fun x : MulAction.fixedPoints H X => fixedPointsOrbitMap x := by
    exact continuous_pi fun q ↦ fixedPointsOrbitMap_eval_continuous (H := H) (X := X) q
  -- Transport that continuity across the discrete-domain homeomorphism to `C(G ⧸ H, X)`.
  have hcont :
      Continuous fun x : MulAction.fixedPoints H X =>
        ContinuousMap.homeoFnOfDiscrete.symm (fixedPointsOrbitMap x) := by
    exact ContinuousMap.homeoFnOfDiscrete.symm.continuous.comp hfun
  -- Finally restrict to the equivariant subspace using the algebraic equivariance lemma.
  simpa [fixedPointsToEquivariantContinuousMap] using
    (Continuous.subtype_mk hcont fun x => fixedPointsOrbitMap_equivariant x)

/-- Problem 3.9.5 (1): for a `G`-space `X`, the space of `G`-maps `G ⧸ H → X` is naturally
homeomorphic to the `H`-fixed point space `X^H`. -/
noncomputable def equivariantContinuousMapSpaceHomeomorphFixedPoints [ContinuousConstSMul G X] :
    equivariantContinuousMapSpace H X ≃ₜ MulAction.fixedPoints H X where
  toEquiv := equivariantContinuousMapSpaceEquivFixedPoints
  continuous_toFun := equivariantContinuousMapSpaceEvalOne_continuous
  continuous_invFun := fixedPointsToEquivariantContinuousMap_continuous

/-- The homeomorphism of Problem 3.9.5 (1) evaluates an equivariant map at the identity coset. -/
@[simp] theorem equivariantContinuousMapSpaceHomeomorphFixedPoints_apply
    [ContinuousConstSMul G X] (f : equivariantContinuousMapSpace H X) :
    equivariantContinuousMapSpaceHomeomorphFixedPoints f =
      equivariantContinuousMapSpaceEvalOne f :=
  rfl

end Discrete
end Topological

/- Problem 3.9.5 (2): in particular, the orbit-category morphism set
`O(G/H, G/K)` is canonically equivalent to the `H`-fixed point set `(G ⧸ K)^H`. -/
/- This is exactly `Subgroup.orbitCategoryHomEquivFixedPoints`. -/
#check
  (Subgroup.orbitCategoryHomEquivFixedPoints :
    ∀ H K : O(G), (H ⟶ K) ≃ MulAction.fixedPoints H (G ⧸ K))
