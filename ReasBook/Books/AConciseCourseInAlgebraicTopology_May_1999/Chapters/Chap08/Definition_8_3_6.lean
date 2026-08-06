import Mathlib.Topology.UnitInterval
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_3_5

open CategoryTheory
open scoped BasedSpace unitInterval

noncomputable section

local notation "I₊" => (TopCat.of I)₊

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopy.toContinuousMap` confirms that
-- homotopies are canonically maps out of `X × I`, while the current chapter already fixes `X ∧ Y₊`
-- as the owner for based smash products. The source statement is
-- therefore formalized by combining those two existing owners.

/-- A based homotopy from `X` to `Y` is a continuous map `X.right × I → Y.right` that is constant
on `{underTopBasepoint X} × I`. -/
structure BasedHomotopy (X Y : BasedSpace) where
  /-- The underlying continuous map of the based homotopy. -/
  toContinuousMap : C(X.right × I, Y.right)
  /-- A based homotopy keeps the chosen basepoint of `X` fixed for all `t : I`. -/
  map_basepoint' : ∀ t : I, toContinuousMap (underTopBasepoint X, t) = underTopBasepoint Y

namespace BasedHomotopy

variable {X Y : BasedSpace}

/-- A based homotopy can be used as its underlying function `X.right × I → Y.right`. -/
instance instCoeFun : CoeFun (BasedHomotopy X Y) (fun _ ↦ X.right × I → Y.right) where
  coe H := H.toContinuousMap

/-- A based homotopy sends the entire track of the chosen basepoint of `X` to the chosen basepoint
of `Y`. -/
@[simp] theorem map_basepoint (H : BasedHomotopy X Y) (t : I) :
    H (underTopBasepoint X, t) = underTopBasepoint Y := by
  -- This is exactly the basepoint condition stored in the structure.
  exact H.map_basepoint' t

/-- Helper for Definition 8.3.6: based homotopies are equal when their underlying functions agree
pointwise. -/
@[ext] theorem ext {H K : BasedHomotopy X Y} (h : ∀ p, H p = K p) : H = K := by
  cases H with
  | mk f hf =>
    cases K with
    | mk g hg =>
      -- Pointwise equality identifies the underlying continuous maps.
      have hfg : f = g := ContinuousMap.ext h
      cases hfg
      -- The remaining proof field is proposition-valued, so proof irrelevance finishes.
      have hh : hf = hg := by
        funext t
        apply Subsingleton.elim
      cases hh
      rfl

end BasedHomotopy

/-- Definition 8.3.6 (1): the reduced cylinder on `X` is the smash product `X ∧ I₊`, formalized
here as `X ∧ I₊`. -/
abbrev reducedCylinder (X : BasedSpace) : BasedSpace :=
  X ∧ I₊

/-- The raw map on `X × I₊` attached to a based homotopy sends the adjoined basepoint of `I₊` and
the strip `{underTopBasepoint X} × I` to the chosen basepoint of `Y`. -/
def basedHomotopyToReducedCylinderRaw {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    X.right × (I₊).right → Y.right
  | (_, Sum.inl _) => underTopBasepoint Y
  | (x, Sum.inr t) => H (x, t)

/-- Helper for Definition 8.3.6: the raw forward map sends every point of the smash wedge to the
chosen basepoint of `Y`. -/
theorem basedHomotopyToReducedCylinderRaw_eq_basepoint_of_mem_smashWedge {X Y : BasedSpace}
    (H : BasedHomotopy X Y) {p : X.right × (I₊).right} (hp : smashWedge X I₊ p) :
    basedHomotopyToReducedCylinderRaw H p = underTopBasepoint Y := by
  rcases p with ⟨x, s⟩
  rcases s with _ | t
  · -- The adjoined basepoint summand is sent to the chosen basepoint by definition.
    simp [basedHomotopyToReducedCylinderRaw]
  · -- On the interval summand, wedge membership forces `x` to be the basepoint of `X`.
    rcases (smashWedge_iff X I₊ (x, Sum.inr t)).1 hp with hx | hs
    · subst hx
      simpa [basedHomotopyToReducedCylinderRaw] using H.map_basepoint t
    · simp [underTopBasepoint_adjoinBasepoint] at hs

/-- The raw formula attached to a based homotopy respects the smash-product relation defining
`reducedCylinder X`. -/
theorem basedHomotopyToReducedCylinderRaw_respects {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    ∀ ⦃p q : X.right × (I₊).right⦄,
      smashProductRel X I₊ p q →
        basedHomotopyToReducedCylinderRaw H p =
          basedHomotopyToReducedCylinderRaw H q := by
  intro p q hpq
  rcases hpq with rfl | ⟨hp, hq⟩
  · -- Equal representatives clearly have the same image.
    rfl
  · -- Wedge-related representatives are both collapsed to the chosen basepoint.
    exact
      (basedHomotopyToReducedCylinderRaw_eq_basepoint_of_mem_smashWedge H hp).trans
        (basedHomotopyToReducedCylinderRaw_eq_basepoint_of_mem_smashWedge H hq).symm

/-- Helper for Definition 8.3.6: the raw forward map is continuous before quotient descent. -/
theorem basedHomotopyToReducedCylinderRawContinuous {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    Continuous (basedHomotopyToReducedCylinderRaw H) := by
  change Continuous (basedHomotopyToReducedCylinderRaw H : X.right × (PUnit ⊕ I) → Y.right)
  let left : X.right × PUnit → Y.right := fun _ ↦ underTopBasepoint Y
  let right : X.right × I → Y.right := fun p ↦ H p
  have hsum : Continuous (Sum.elim left right) := by
    -- Each branch is continuous on its corresponding summand.
    exact Continuous.sumElim continuous_const H.toContinuousMap.continuous
  have hraw :
      basedHomotopyToReducedCylinderRaw H =
        (Sum.elim left right) ∘
          ((Homeomorph.prodSumDistrib : X.right × (PUnit ⊕ I) ≃ₜ
              (X.right × PUnit) ⊕ (X.right × I))) := by
    funext p
    rcases p with ⟨x, s⟩
    rcases s with _ | t <;> rfl
  -- Rewrite the raw map through the standard product/sum distributivity homeomorphism.
  rw [hraw]
  exact
    hsum.comp
      ((Homeomorph.prodSumDistrib : X.right × (PUnit ⊕ I) ≃ₜ
          (X.right × PUnit) ⊕ (X.right × I)).continuous_toFun)

/-- The quotient lift of `basedHomotopyToReducedCylinderRaw H` is continuous on
`(reducedCylinder X).right`. -/
theorem basedHomotopyToReducedCylinderContinuous {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    Continuous
          (Quotient.lift
        (basedHomotopyToReducedCylinderRaw H)
        (basedHomotopyToReducedCylinderRaw_respects H) :
          (reducedCylinder X).right → Y.right) := by
  -- Descend continuity from the representative-level raw map.
  exact
    (basedHomotopyToReducedCylinderRawContinuous H).quotient_lift
      (fun a b h ↦ by
        simpa [smashProductSetoid] using basedHomotopyToReducedCylinderRaw_respects H h)

/-- The continuous map on the reduced cylinder induced by a based homotopy. -/
def basedHomotopyToReducedCylinderContinuousMap {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    C((reducedCylinder X).right, Y.right) :=
  ⟨Quotient.lift
      (basedHomotopyToReducedCylinderRaw H)
      (basedHomotopyToReducedCylinderRaw_respects H),
    basedHomotopyToReducedCylinderContinuous H⟩

/-- The continuous map induced by a based homotopy sends the reduced-cylinder basepoint to the
chosen basepoint of `Y`. -/
theorem basedHomotopyToReducedCylinderContinuousMap_map_basepoint {X Y : BasedSpace}
    (H : BasedHomotopy X Y) :
    basedHomotopyToReducedCylinderContinuousMap H
        (underTopBasepoint (reducedCylinder X)) =
      underTopBasepoint Y := by
  have hbase :
      underTopBasepoint (reducedCylinder X) =
        smashProductMk X I₊ (smashProductBasepointPair X I₊) := by
    simpa [reducedCylinder] using underTopBasepoint_smashProduct X I₊
  -- Rewrite the reduced-cylinder basepoint to its smash-product representative.
  rw [hbase]
  change basedHomotopyToReducedCylinderRaw H (smashProductBasepointPair X I₊) = underTopBasepoint Y
  simp [basedHomotopyToReducedCylinderRaw, smashProductBasepointPair,
    underTopBasepoint_adjoinBasepoint]

/-- The continuous map induced by a based homotopy is a morphism of based spaces
`reducedCylinder X ⟶ Y`. -/
theorem basedHomotopyToReducedCylinder_w {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    (reducedCylinder X).hom ≫ TopCat.ofHom (basedHomotopyToReducedCylinderContinuousMap H) =
      Y.hom := by
  -- Maps out of the terminal object are determined by their value at the unique point.
  ext x
  have hbase :
      smashProductMk X I₊ (smashProductBasepointPair X I₊) =
        underTopBasepoint (reducedCylinder X) := by
    simpa [reducedCylinder] using (underTopBasepoint_smashProduct X I₊).symm
  change
    basedHomotopyToReducedCylinderContinuousMap H
        (smashProductMk X I₊ (smashProductBasepointPair X I₊)) =
      (ConcreteCategory.hom Y.hom) x
  rw [hbase]
  rw [basedHomotopyToReducedCylinderContinuousMap_map_basepoint (X := X) (Y := Y) H]
  have hx :
      x =
        (ConcreteCategory.hom TopCat.terminalIsoPUnit.inv)
          ((ConcreteCategory.hom TopCat.terminalIsoPUnit.hom) x) := by
    simp
  rw [hx]
  cases (TopCat.terminalIsoPUnit.hom x)
  rfl

/-- A based homotopy determines a based map out of the reduced cylinder. -/
def basedHomotopyToReducedCylinderMap {X Y : BasedSpace} (H : BasedHomotopy X Y) :
    reducedCylinder X ⟶ Y :=
  Under.homMk
    (TopCat.ofHom (basedHomotopyToReducedCylinderContinuousMap H))
    (basedHomotopyToReducedCylinder_w H)

/-- On a class represented by `(x, t) ∈ X × I`, the map induced by a based homotopy evaluates to
`H (x, t)`. -/
@[simp] theorem basedHomotopyToReducedCylinderMap_apply_mk {X Y : BasedSpace}
    (H : BasedHomotopy X Y) (x : X.right) (t : I) :
    (basedHomotopyToReducedCylinderMap H).right.hom
        (smashProductMk X I₊ (x, Sum.inr t)) =
      H (x, t) := by
  -- On interval representatives, the descended map evaluates by the raw formula.
  rfl

/-- The raw map `X × I → Y` obtained by restricting a based map `reducedCylinder X ⟶ Y` along the
quotient map `X × I → X ∧ I₊`. -/
def reducedCylinderToBasedHomotopyRaw {X Y : BasedSpace} (f : reducedCylinder X ⟶ Y) :
    X.right × I → Y.right :=
  fun p ↦
    f.right.hom
      (smashProductMk X I₊ (p.1, Sum.inr p.2))

/-- The restriction of a based map `reducedCylinder X ⟶ Y` along `X × I → X ∧ I₊` is continuous. -/
theorem reducedCylinderToBasedHomotopyRaw_continuous {X Y : BasedSpace}
    (f : reducedCylinder X ⟶ Y) :
    Continuous (reducedCylinderToBasedHomotopyRaw f) := by
  have hmk : Continuous (fun p : X.right × I ↦ smashProductMk X I₊ (p.1, Sum.inr p.2)) := by
    -- The section `X × I → X ∧ I₊` is the quotient constructor composed with `Sum.inr`.
    simpa [smashProductMk] using
      (continuous_quotient_mk'.comp
        (continuous_fst.prodMk (continuous_inr.comp continuous_snd)))
  -- Restrict the based map along that continuous section.
  exact f.right.hom.continuous.comp hmk

/-- The restriction of a based map `reducedCylinder X ⟶ Y` along `X × I → X ∧ I₊` is constant on
`{underTopBasepoint X} × I`. -/
theorem reducedCylinderToBasedHomotopyRaw_map_basepoint {X Y : BasedSpace}
    (f : reducedCylinder X ⟶ Y) :
    ∀ t : I,
      reducedCylinderToBasedHomotopyRaw f (underTopBasepoint X, t) =
        underTopBasepoint Y := by
  intro t
  -- First collapse the basepoint track to the reduced-cylinder basepoint.
  calc
    reducedCylinderToBasedHomotopyRaw f (underTopBasepoint X, t)
        = f.right.hom (underTopBasepoint (reducedCylinder X)) := by
            unfold reducedCylinderToBasedHomotopyRaw
            simpa [reducedCylinder] using
              congrArg f.right.hom
                (smashProduct_mk_eq_basepoint_of_mem_smashWedge X I₊
                  ((smashWedge_iff X I₊ (underTopBasepoint X, Sum.inr t)).2 (Or.inl rfl)))
    _ = underTopBasepoint Y := by
      exact fundamentalGroupFunctorMap_basepoint f

/-- A based map `reducedCylinder X ⟶ Y` restricts to a based homotopy `X × I → Y`. -/
def reducedCylinderToBasedHomotopy {X Y : BasedSpace} (f : reducedCylinder X ⟶ Y) :
    BasedHomotopy X Y where
  toContinuousMap :=
    ⟨reducedCylinderToBasedHomotopyRaw f, reducedCylinderToBasedHomotopyRaw_continuous f⟩
  map_basepoint' := reducedCylinderToBasedHomotopyRaw_map_basepoint f

/-- Evaluating the based homotopy induced by `f : reducedCylinder X ⟶ Y` at `(x, t)` recovers the
value of `f` on the corresponding class in `X ∧ I₊`. -/
@[simp] theorem reducedCylinderToBasedHomotopy_apply {X Y : BasedSpace}
    (f : reducedCylinder X ⟶ Y) (x : X.right) (t : I) :
    reducedCylinderToBasedHomotopy f (x, t) =
      f.right.hom (smashProductMk X I₊ (x, Sum.inr t)) := by
  -- This is the defining evaluation formula of the restricted raw map.
  rfl

/-- Converting a based homotopy to a based map on the reduced cylinder and restricting back
recovers the original based homotopy. -/
theorem reducedCylinderToBasedHomotopy_comp_basedHomotopyToReducedCylinderMap {X Y : BasedSpace}
    (H : BasedHomotopy X Y) :
    reducedCylinderToBasedHomotopy (basedHomotopyToReducedCylinderMap H) = H := by
  -- Compare the two based homotopies pointwise on `X × I`.
  apply BasedHomotopy.ext
  intro p
  rcases p with ⟨x, t⟩
  simpa using basedHomotopyToReducedCylinderMap_apply_mk H x t

/-- Converting a based map on the reduced cylinder to a based homotopy and then descending again
recovers the original based map. -/
theorem basedHomotopyToReducedCylinderMap_comp_reducedCylinderToBasedHomotopy {X Y : BasedSpace}
    (f : reducedCylinder X ⟶ Y) :
    basedHomotopyToReducedCylinderMap (reducedCylinderToBasedHomotopy f) = f := by
  -- Equality in `Under` reduces to equality of the underlying maps.
  apply Under.UnderMorphism.ext
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  -- Quotient induction reduces the comparison to representative computations.
  refine Quotient.inductionOn' z ?_
  intro p
  rcases p with ⟨x, s⟩
  rcases s with _ | t
  · have hbase :
        smashProductMk X I₊ (x, Sum.inl PUnit.unit) =
          underTopBasepoint (reducedCylinder X) := by
        -- Any representative in the adjoined-basepoint summand is the smash-product basepoint.
        simpa [reducedCylinder] using
          (smashProduct_mk_eq_basepoint_of_mem_smashWedge X I₊
            ((smashWedge_iff X I₊ (x, Sum.inl PUnit.unit)).2
              (Or.inr (by
                simpa using (underTopBasepoint_adjoinBasepoint (TopCat.of I)).symm))))
    -- Both maps send the smash-product basepoint to the chosen basepoint of `Y`.
    calc
      (basedHomotopyToReducedCylinderMap (reducedCylinderToBasedHomotopy f)).right.hom
          (smashProductMk X I₊ (x, Sum.inl PUnit.unit))
          =
        (basedHomotopyToReducedCylinderMap (reducedCylinderToBasedHomotopy f)).right.hom
          (underTopBasepoint (reducedCylinder X)) := by
            rw [hbase]
      _ = underTopBasepoint Y := by
        exact fundamentalGroupFunctorMap_basepoint
          (basedHomotopyToReducedCylinderMap (reducedCylinderToBasedHomotopy f))
      _ = f.right.hom (underTopBasepoint (reducedCylinder X)) := by
        symm
        exact fundamentalGroupFunctorMap_basepoint f
      _ = f.right.hom (smashProductMk X I₊ (x, Sum.inl PUnit.unit)) := by
        rw [hbase]
  · -- On interval representatives, the round-trip is the identity by the two evaluation lemmas.
    calc
      (basedHomotopyToReducedCylinderMap (reducedCylinderToBasedHomotopy f)).right.hom
          (smashProductMk X I₊ (x, Sum.inr t))
          = reducedCylinderToBasedHomotopy f (x, t) := by
              simpa using
                (basedHomotopyToReducedCylinderMap_apply_mk
                  (H := reducedCylinderToBasedHomotopy f) x t)
      _ = f.right.hom (smashProductMk X I₊ (x, Sum.inr t)) := by
        simpa using reducedCylinderToBasedHomotopy_apply f x t

/-- Definition 8.3.6 (2): a based homotopy `X × I → Y` is equivalently a based map
`reducedCylinder X ⟶ Y`, i.e. a based map `X ∧ I₊ → Y`. -/
def basedHomotopyEquivReducedCylinderMap (X Y : BasedSpace) :
    BasedHomotopy X Y ≃ (reducedCylinder X ⟶ Y) where
  toFun := basedHomotopyToReducedCylinderMap
  invFun := reducedCylinderToBasedHomotopy
  left_inv := reducedCylinderToBasedHomotopy_comp_basedHomotopyToReducedCylinderMap
  right_inv := basedHomotopyToReducedCylinderMap_comp_reducedCylinderToBasedHomotopy

/-- The equivalence of Definition 8.3.6 (2) is determined by the two conversion maps between
based homotopies and based maps on the reduced cylinder. -/
theorem basedHomotopyEquivReducedCylinderMap_spec (X Y : BasedSpace) :
    basedHomotopyEquivReducedCylinderMap X Y =
      { toFun := basedHomotopyToReducedCylinderMap
        invFun := reducedCylinderToBasedHomotopy
        left_inv := reducedCylinderToBasedHomotopy_comp_basedHomotopyToReducedCylinderMap
        right_inv :=
          basedHomotopyToReducedCylinderMap_comp_reducedCylinderToBasedHomotopy } := by
  -- The equivalence was defined using exactly these four fields.
  rfl

/-- The forward map of `basedHomotopyEquivReducedCylinderMap X Y` is
`basedHomotopyToReducedCylinderMap`. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_toFun (X Y : BasedSpace) :
    (basedHomotopyEquivReducedCylinderMap X Y).toFun =
      basedHomotopyToReducedCylinderMap := by
  -- The forward map is the `toFun` field of the definition.
  rfl

/-- As a function, `basedHomotopyEquivReducedCylinderMap X Y` sends a based homotopy to the
corresponding based map on the reduced cylinder. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_def (X Y : BasedSpace) :
    (basedHomotopyEquivReducedCylinderMap X Y).toFun =
      fun H ↦ basedHomotopyEquivReducedCylinderMap X Y H := by
  -- Coercing the equivalence to a function exposes its forward map.
  rfl

/-- Evaluating the forward map of `basedHomotopyEquivReducedCylinderMap X Y` on a based homotopy
recovers the corresponding based map on the reduced cylinder. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_toFun_apply (X Y : BasedSpace)
    (H : BasedHomotopy X Y) :
    (basedHomotopyEquivReducedCylinderMap X Y).toFun H =
      basedHomotopyToReducedCylinderMap H := by
  -- Evaluating the forward map is definitional.
  rfl

/-- As a function, `basedHomotopyEquivReducedCylinderMap X Y` sends a based homotopy to the
corresponding based map on the reduced cylinder. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_coe (X Y : BasedSpace) :
    ⇑(basedHomotopyEquivReducedCylinderMap X Y) =
      fun H ↦ basedHomotopyEquivReducedCylinderMap X Y H := by
  -- The coercion of an equivalence to a function is its `toFun`.
  rfl

/-- As a function, the inverse of `basedHomotopyEquivReducedCylinderMap X Y` is
`reducedCylinderToBasedHomotopy`. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_invFun (X Y : BasedSpace) :
    (basedHomotopyEquivReducedCylinderMap X Y).invFun =
      reducedCylinderToBasedHomotopy := by
  -- The inverse map is the `invFun` field of the definition.
  rfl

/-- Applying `basedHomotopyEquivReducedCylinderMap` to a based homotopy returns the corresponding
based map on the reduced cylinder. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_apply (X Y : BasedSpace)
    (H : BasedHomotopy X Y) :
    basedHomotopyEquivReducedCylinderMap X Y H =
      basedHomotopyToReducedCylinderMap H := by
  -- Applying the equivalence uses its forward map.
  rfl

/-- Applying the inverse of `basedHomotopyEquivReducedCylinderMap` to a based map on the reduced
cylinder returns the corresponding based homotopy. -/
@[simp] theorem basedHomotopyEquivReducedCylinderMap_symm_apply (X Y : BasedSpace)
    (f : reducedCylinder X ⟶ Y) :
    (basedHomotopyEquivReducedCylinderMap X Y).symm
      f =
        reducedCylinderToBasedHomotopy f := by
  -- Applying the inverse equivalence uses its `invFun` field.
  rfl
