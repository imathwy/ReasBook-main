import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.CompactlyGenerated
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_2_15
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4.MappingSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Adjunction_8_1_4.SmashMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_2

open CategoryTheory
open scoped BasedSpace Topology

noncomputable section

universe u s w

/-- Adjunction 8.1.4: the forward map of the natural homeomorphism
`F(X ∧ Y, Z) ≅ F(X, F(Y, Z))` for based spaces `X`, `Y`, and `Z`. -/
private def smashProductMappingAdjunctionToFun
    (X Y Z : BasedSpace) :
    underBasedMapSpace (X ∧ Y) Z →
      underBasedMapSpace X (underBasedMapSpaceObject Y Z) :=
  fun f ↦
    let quotientMk : C(smashProductPair X Y, (X ∧ Y).right) :=
      ⟨smashProductMk X Y, by
        simpa [smashProductMk, smashProductType] using
          (continuous_quotient_mk' :
            Continuous (@Quotient.mk' (smashProductPair X Y) (smashProductSetoid X Y)))⟩
    let curried : C(X.right, C(Y.right, Z.right)) :=
      ContinuousMap.curry (f.1.comp quotientMk)
    let basedCurried : C(X.right, underBasedMapSpace Y Z) :=
      { toFun := fun x ↦
          ⟨curried x, by
            have hbase :
                f.1 (smashProductMk X Y (x, underTopBasepoint Y)) = underTopBasepoint Z := by
              rw [smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y (by right; rfl)]
              exact f.2
            simpa [curried, quotientMk, ContinuousMap.curry_apply] using hbase
          ⟩
        continuous_toFun :=
          Continuous.subtype_mk curried.continuous fun x ↦ by
            have hbase :
                f.1 (smashProductMk X Y (x, underTopBasepoint Y)) = underTopBasepoint Z := by
              rw [smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y (by right; rfl)]
              exact f.2
            simpa [curried, quotientMk, ContinuousMap.curry_apply] using hbase }
    ⟨basedCurried, by
      apply Subtype.ext
      ext y
      have hbase :
          f.1 (smashProductMk X Y (underTopBasepoint X, y)) = underTopBasepoint Z := by
        rw [smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y (by left; rfl)]
        exact f.2
      simpa [basedCurried, curried, quotientMk, underBasedMapSpaceBasepoint,
        ContinuousMap.curry_apply] using hbase
    ⟩

/-- Helper for Adjunction 8.1.4: in the locally compact branch, the raw formula
`(x, y) ↦ (g x) y` is continuous on `X × Y`. -/
private theorem smashProductMappingAdjunctionInvUncurried_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z)) :
    Continuous fun p : smashProductPair X Y ↦ ((g.1 p.1).1 p.2) := by
  let forget : C(X.right, C(Y.right, Z.right)) :=
    ⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩
  -- In the locally compact branch, ordinary compact-open uncurrying applies directly.
  simpa [forget, Function.uncurry] using
    (ContinuousMap.continuous_uncurry_of_continuous forget)

private def smashProductMappingAdjunctionInvFun
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right] :
    underBasedMapSpace X (underBasedMapSpaceObject Y Z) →
      underBasedMapSpace (X ∧ Y) Z :=
  fun g ↦
    let uncurried : C(smashProductPair X Y, Z.right) :=
      ⟨fun p ↦ ((g.1 p.1).1 p.2),
        smashProductMappingAdjunctionInvUncurried_continuous X Y Z g⟩
    let wedgeValue :
        ∀ p : smashProductPair X Y, smashWedge X Y p → uncurried p = underTopBasepoint Z
      | (x, y), hp => by
          rcases hp with rfl | rfl
          · have hbase := congrArg (fun h : underBasedMapSpace Y Z ↦ h.1 y) g.2
            simpa [uncurried, forget, underBasedMapSpaceBasepoint] using hbase
          · simpa [uncurried, forget] using (g.1 x).2
    let descends :
        ∀ p q : smashProductPair X Y, (smashProductSetoid X Y).r p q → uncurried p = uncurried q
      | p, q, hpq => by
          change smashProductRel X Y p q at hpq
          rcases hpq with rfl | ⟨hp, hq⟩
          · rfl
          · exact (wedgeValue p hp).trans (wedgeValue q hq).symm
    let descended : C((X ∧ Y).right, Z.right) :=
      ⟨Quotient.lift (fun p : smashProductPair X Y ↦ uncurried p) descends,
        uncurried.continuous.quotient_lift descends⟩
    ⟨descended, by
      rw [underTopBasepoint_smashProduct X Y]
      exact wedgeValue (smashProductBasepointPair X Y) (smashWedge_basepointPair X Y)
    ⟩

/-- Helper for Adjunction 8.1.4: uncurrying after currying recovers a based map on each smash
generator `smashProductMk X Y p`. -/
private theorem smashProductMappingAdjunctionInvToFun_apply_mk
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (f : underBasedMapSpace (X ∧ Y) Z) (p : X.right × Y.right) :
    (smashProductMappingAdjunctionInvFun X Y Z
      (smashProductMappingAdjunctionToFun X Y Z f)).1 (smashProductMk X Y p) =
      f.1 (smashProductMk X Y p) := by
  rcases p with ⟨x, y⟩
  -- On a smash generator, the inverse map reduces to the raw uncurried evaluation.
  rfl

/-- Helper for Adjunction 8.1.4: currying after uncurrying agrees pointwise with the original
based family of maps. -/
private theorem smashProductMappingAdjunctionToInv_apply
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z))
    (x : X.right) (y : Y.right) :
    ((smashProductMappingAdjunctionToFun X Y Z
      (smashProductMappingAdjunctionInvFun X Y Z g)).1 x).1 y =
      (g.1 x).1 y := by
  -- Evaluating the re-curried inverse on `(x, y)` recovers the original family pointwise.
  rfl

/-- Helper for Adjunction 8.1.4: the forward and inverse constructions compose to the identity on
maps out of the smash product. -/
private theorem smashProductMappingAdjunctionHomeomorph_leftInv
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (f : underBasedMapSpace (X ∧ Y) Z) :
    smashProductMappingAdjunctionInvFun X Y Z
      (smashProductMappingAdjunctionToFun X Y Z f) = f := by
  apply Subtype.ext
  ext q
  -- Equality on the smash product is checked on quotient generators.
  refine Quotient.inductionOn' q ?_
  intro p
  exact smashProductMappingAdjunctionInvToFun_apply_mk X Y Z f p

/-- Helper for Adjunction 8.1.4: the inverse and forward constructions compose to the identity on
iterated based mapping spaces. -/
private theorem smashProductMappingAdjunctionHomeomorph_rightInv
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z)) :
    smashProductMappingAdjunctionToFun X Y Z
      (smashProductMappingAdjunctionInvFun X Y Z g) = g := by
  apply Subtype.ext
  ext x
  apply Subtype.ext
  ext y
  -- The iterated mapping space equality is detected by evaluating at both variables.
  exact smashProductMappingAdjunctionToInv_apply X Y Z g x y

/-- Helper for Adjunction 8.1.4: the forward currying map is continuous for the compact-open
topology on based mapping spaces. -/
private theorem smashProductMappingAdjunctionToFun_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous (smashProductMappingAdjunctionToFun X Y Z) := by
  have hQuotientMkContinuous : Continuous (smashProductMk X Y) := by
    simpa [smashProductMk, smashProductType] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (smashProductPair X Y) (smashProductSetoid X Y)))
  let quotientMk : C(smashProductPair X Y, (X ∧ Y).right) :=
    ⟨smashProductMk X Y, hQuotientMkContinuous⟩
  let H : underBasedMapSpace (X ∧ Y) Z → C(X.right, C(Y.right, Z.right)) := fun f ↦
    ContinuousMap.curry (f.1.comp quotientMk)
  have hH : Continuous H := by
    -- Precompose by the quotient map `X × Y → X ∧ Y`, then use the locally compact currying
    -- operator on `X.right × Y.right`.
    exact (ContinuousMap.continuous_curry).comp
      ((ContinuousMap.continuous_precomp quotientMk).comp continuous_subtype_val)
  have hCurriedAtBase :
      ∀ f : underBasedMapSpace (X ∧ Y) Z, ∀ x : X.right,
        H f x (underTopBasepoint Y) = underTopBasepoint Z := by
    intro f x
    -- The smash-product relation collapses `(x, *)` to the basepoint, so each curried slice is
    -- based in the `Y`-variable.
    have hbase :
        f.1 (smashProductMk X Y (x, underTopBasepoint Y)) = underTopBasepoint Z := by
      rw [smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y (by right; rfl)]
      exact f.2
    simpa [H, quotientMk, ContinuousMap.curry_apply] using hbase
  let F :
      underBasedMapSpace (X ∧ Y) Z → C(X.right, underBasedMapSpace Y Z) := fun f ↦
    ⟨fun x ↦ ⟨H f x, hCurriedAtBase f x⟩,
      Continuous.subtype_mk (H f).continuous (fun x ↦ hCurriedAtBase f x)⟩
  let forgetY : C(underBasedMapSpace Y Z, C(Y.right, Z.right)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hForgetY :
      Topology.IsInducing (ContinuousMap.comp forgetY :
        C(X.right, underBasedMapSpace Y Z) → C(X.right, C(Y.right, Z.right))) := by
    exact
      ContinuousMap.isInducing_postcomp forgetY
        Topology.IsEmbedding.subtypeVal.isInducing
  have hF : Continuous F := by
    -- Continuity into the based mapping space is checked after forgetting the basepoint
    -- condition in the `Y`-variable.
    exact hForgetY.continuous_iff.mpr <| by
      simpa [F, H, forgetY] using hH
  have hFBase :
      ∀ f : underBasedMapSpace (X ∧ Y) Z,
        F f (underTopBasepoint X) = underBasedMapSpaceBasepoint Y Z := by
    intro f
    apply Subtype.ext
    ext y
    -- Evaluating the curried family at the basepoint of `X` recovers the constant based map.
    have hbase :
        f.1 (smashProductMk X Y (underTopBasepoint X, y)) = underTopBasepoint Z := by
      rw [smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y (by left; rfl)]
      exact f.2
    simpa [F, H, quotientMk, underBasedMapSpaceBasepoint, ContinuousMap.curry_apply] using hbase
  -- The forward map lands in the based mapping-space subtype by the previous basepoint check.
  refine Continuous.subtype_mk ?_ (fun f ↦ by
    change F f (underTopBasepoint X) = underBasedMapSpaceBasepoint Y Z
    exact hFBase f)
  simpa [F, H, quotientMk, smashProductMappingAdjunctionToFun] using hF

/-- Helper for Adjunction 8.1.4: the raw joint evaluation `(g, (x, y)) ↦ ((g x) y)` is continuous
before descending along the smash-product quotient. -/
private theorem smashProductMappingAdjunctionInvRawEval_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous
      (fun gp : underBasedMapSpace X (underBasedMapSpaceObject Y Z) × smashProductPair X Y ↦
        ((gp.1.1 gp.2.1).1 gp.2.2)) := by
  have hEvalX :
      Continuous
        (fun gp : underBasedMapSpace X (underBasedMapSpaceObject Y Z) × smashProductPair X Y ↦
          gp.1.1 gp.2.1) := by
    -- Evaluate the based family in the `X`-variable before forgetting the `Y`-basedness.
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  -- Evaluate the resulting based map in the `Y`-variable.
  exact continuous_eval.comp
    ((continuous_subtype_val.comp hEvalX).prodMk (continuous_snd.comp continuous_snd))

/-- Helper for Adjunction 8.1.4: evaluating the inverse map on a smash generator `x ∧ y`
recovers the raw formula `((g x) y)`. -/
private theorem smashProductMappingAdjunctionInvFun_precomp_smashProductMk
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (gp : underBasedMapSpace X (underBasedMapSpaceObject Y Z) × smashProductPair X Y) :
    (smashProductMappingAdjunctionInvFun X Y Z gp.1).1 (smashProductMk X Y gp.2) =
      ((gp.1.1 gp.2.1).1 gp.2.2) := by
  rcases gp with ⟨g, p⟩
  rcases p with ⟨x, y⟩
  -- The quotient-descended inverse agrees with the raw formula on every generator.
  rfl

/-- Helper for Adjunction 8.1.4: the uncurried prequotient family
`g ↦ ((x, y) ↦ (g x) y)` is continuous as a map into `C(X.right × Y.right, Z.right)`. -/
private theorem smashProductMappingAdjunctionInvRawFamily_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous
      (fun g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) ↦
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right))) :
          C(smashProductPair X Y, Z.right))) := by
  -- Convert continuity of the map-valued family into the already-proved joint evaluation formula.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  simpa [Function.uncurry] using smashProductMappingAdjunctionInvRawEval_continuous X Y Z

/-- Helper for Adjunction 8.1.4: each uncurried prequotient map is constant on the fibres of
`smashProductMk X Y`. -/
private theorem smashProductMappingAdjunctionInvRawFamily_factorsThrough
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z)) :
    Function.FactorsThrough
      (ContinuousMap.uncurry
        (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
          C(X.right, C(Y.right, Z.right))))
      (smashProductMk X Y) := by
  let forget : C(X.right, C(Y.right, Z.right)) :=
    ⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩
  let uncurried : C(smashProductPair X Y, Z.right) := ContinuousMap.uncurry forget
  have wedgeValue :
      ∀ p : smashProductPair X Y, smashWedge X Y p → uncurried p = underTopBasepoint Z := by
    -- Points on the wedge are forced to the target basepoint by the basedness of `g`.
    intro p hp
    rcases p with ⟨x, y⟩
    rcases hp with rfl | rfl
    · have hbase := congrArg (fun h : underBasedMapSpace Y Z ↦ h.1 y) g.2
      simpa [uncurried, forget, underBasedMapSpaceBasepoint] using hbase
    · simpa [uncurried, forget] using (g.1 x).2
  intro p q hpq
  have hrel : (smashProductSetoid X Y).r p q := Quotient.exact hpq
  change smashProductRel X Y p q at hrel
  rcases hrel with rfl | ⟨hp, hq⟩
  · rfl
  · exact (wedgeValue p hp).trans (wedgeValue q hq).symm

/-- Helper for Adjunction 8.1.4: descending a factor-through map along `smashProductMk X Y`
agrees with the original map on every smash-product generator. -/
private theorem smashProductQuotientLift_apply_mk
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (quotientMk : C(smashProductPair X Y, (X ∧ Y).right))
    (hQuotientMk : (quotientMk : smashProductPair X Y → (X ∧ Y).right) = smashProductMk X Y)
    (hquot : Topology.IsQuotientMap quotientMk)
    (s : { u : C(smashProductPair X Y, Z.right) // Function.FactorsThrough u quotientMk })
    (p : smashProductPair X Y) :
    (hquot.lift s.1 s.2) (smashProductMk X Y p) = s.1 p := by
  -- Rewrite the descended map back along the quotient triangle and evaluate on the generator.
  have hcomp : (hquot.lift s.1 s.2).comp quotientMk = s.1 := hquot.lift_comp s.1 s.2
  have happly := congrArg (fun f : C(smashProductPair X Y, Z.right) ↦ f p) hcomp
  have hpoint : quotientMk p = smashProductMk X Y p := by
    exact congrArg (fun f : smashProductPair X Y → (X ∧ Y).right ↦ f p) hQuotientMk
  simpa [ContinuousMap.comp_apply] using hpoint ▸ happly

/-- Helper for Adjunction 8.1.4: any quotient class equal to the smash-product basepoint comes from
the wedge locus `X ∨ Y`. -/
private theorem smashWedge_of_smashProductMk_eq_basepoint
    (X Y : BasedSpace) {p : smashProductPair X Y}
    (hp : smashProductMk X Y p = underTopBasepoint (X ∧ Y)) :
    smashWedge X Y p := by
  -- Compare `p` with the distinguished basepoint representative inside the quotient relation.
  have hrel : (smashProductSetoid X Y).r p (smashProductBasepointPair X Y) := by
    apply Quotient.exact
    simpa [underTopBasepoint_smashProduct X Y] using hp
  change smashProductRel X Y p (smashProductBasepointPair X Y) at hrel
  rcases hrel with hEq | ⟨hpw, _⟩
  · subst hEq
    exact smashWedge_basepointPair X Y
  · exact hpw

/-- Helper for Adjunction 8.1.4: a smash-product class is the basepoint exactly when its
representative lies in the wedge locus. -/
private theorem smashProductMk_eq_basepoint_iff_smashWedge
    (X Y : BasedSpace) (p : smashProductPair X Y) :
    smashProductMk X Y p = underTopBasepoint (X ∧ Y) ↔ smashWedge X Y p := by
  constructor
  · intro hp
    -- A quotient class equal to the distinguished basepoint must come from the collapsed wedge.
    exact smashWedge_of_smashProductMk_eq_basepoint X Y hp
  · intro hp
    -- Every wedge representative is identified with the smash-product basepoint.
    exact smashProduct_mk_eq_basepoint_of_mem_smashWedge X Y hp

/-- Helper for Adjunction 8.1.4: away from the wedge locus, `smashProductMk X Y` is injective. -/
private theorem smashProductMk_injective_of_not_smashWedge
    (X Y : BasedSpace) {p q : smashProductPair X Y}
    (hp : ¬ smashWedge X Y p) (hq : ¬ smashWedge X Y q)
    (hpq : smashProductMk X Y p = smashProductMk X Y q) :
    p = q := by
  -- Outside the wedge, the smash-product relation has no nontrivial identifications left.
  have hrel : (smashProductSetoid X Y).r p q := Quotient.exact hpq
  change smashProductRel X Y p q at hrel
  rcases hrel with rfl | ⟨hpw, hqw⟩
  · rfl
  · exact (hp hpw).elim

/-- Helper for Adjunction 8.1.4: after precomposing with `smashProductMk X Y`, the descended
inverse evaluation recovers the raw formula `((g x) y)`. -/
private theorem smashProductMappingAdjunctionInvDescendedEval_precomp_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous
      (fun gp : underBasedMapSpace X (underBasedMapSpaceObject Y Z) × smashProductPair X Y ↦
        (smashProductMappingAdjunctionInvFun X Y Z gp.1).1 (smashProductMk X Y gp.2)) := by
  -- Before quotient descent, the inverse evaluation is exactly the raw jointly continuous family.
  simpa [smashProductMappingAdjunctionInvFun_precomp_smashProductMk] using
    smashProductMappingAdjunctionInvRawEval_continuous X Y Z

/-- Helper for Adjunction 8.1.4: a continuous family on `smashProductPair X Y` that is constant on
the fibres of `quotientMk` descends continuously to maps on `(X ∧ Y).right`. -/
private theorem smashProductQuotientLift_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    {A : Type*} [TopologicalSpace A]
    (quotientMk : C(smashProductPair X Y, (X ∧ Y).right))
    (hquot : Topology.IsQuotientMap quotientMk)
    [LocallyCompactSpace A]
    (F : A → C(smashProductPair X Y, Z.right))
    (hEval : Continuous fun ap : A × smashProductPair X Y ↦ F ap.1 ap.2)
    (hFactor : ∀ a, Function.FactorsThrough (F a) quotientMk) :
    Continuous fun a : A ↦ hquot.lift (F a) (hFactor a) := by
  -- Route correction: instead of handling arbitrary compact subsets of the quotient space
  -- directly, descend the already-continuous joint evaluation along the quotient in the
  -- `smashProductPair X Y` coordinate, where the parameter space is locally compact.
  let descendedEval : A × (X ∧ Y).right → Z.right := fun aq ↦
    hquot.lift (F aq.1) (hFactor aq.1) aq.2
  have hPrecomp :
      Continuous fun ap : A × smashProductPair X Y ↦
        descendedEval (ap.1, quotientMk ap.2) := by
    have hPoint :
        (fun ap : A × smashProductPair X Y ↦
          descendedEval (ap.1, quotientMk ap.2)) =
        fun ap : A × smashProductPair X Y ↦ F ap.1 ap.2 := by
      funext ap
      have hcomp : (hquot.lift (F ap.1) (hFactor ap.1)).comp quotientMk = F ap.1 :=
        hquot.lift_comp (F ap.1) (hFactor ap.1)
      exact congrArg (fun f : C(smashProductPair X Y, Z.right) ↦ f ap.2) hcomp
    exact hPoint ▸ hEval
  have hDescendedEval : Continuous descendedEval := by
    -- The quotient-lift theorem applies because the parameter space is locally compact here.
    exact hquot.continuous_lift_prod_right hPrecomp
  -- Recover continuity of the map-valued family from continuity of its joint evaluation.
  exact ContinuousMap.continuous_of_continuous_uncurry _ hDescendedEval

/-- Helper for Adjunction 8.1.4: every compact-open subbasic preimage for the raw uncurried family
is already open in the source mapping space. -/
private theorem smashProductMappingAdjunctionInvRawFamily_subbasicPreimage_isOpen
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (L : Set (smashProductPair X Y)) (hL : IsCompact L) (U : Set Z.right) (hU : IsOpen U) :
    IsOpen
      { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
          Set.MapsTo
            (ContinuousMap.uncurry
              (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
                C(X.right, C(Y.right, Z.right))))
            L U } := by
  -- The raw family is continuous as a map into the compact-open mapping space, so its subbasic
  -- preimages are open by the defining compact-open criterion.
  exact
    (ContinuousMap.continuous_compactOpen.mp
      (smashProductMappingAdjunctionInvRawFamily_continuous X Y Z))
      L hL U hU

/-- Helper for Adjunction 8.1.4: any locally compact parameter family into the source based
mapping space pulls a compact-open subbasic condition for the inverse family back to an open set.
-/
private theorem invSubbasicPreimage_isOpen_locallyCompactParam
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    {S : Type*} [TopologicalSpace S] [LocallyCompactSpace S]
    (φ : C(S, underBasedMapSpace X (underBasedMapSpaceObject Y Z)))
    (K : Set ((X ∧ Y).right)) (hK : IsCompact K) (U : Set Z.right) (hU : IsOpen U) :
    IsOpen
      { s : S | Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z (φ s)).1) K U } := by
  let quotientMk : C(smashProductPair X Y, (X ∧ Y).right) :=
    ⟨smashProductMk X Y, by
      simpa [smashProductMk, smashProductType] using
        (continuous_quotient_mk' :
          Continuous (@Quotient.mk' (smashProductPair X Y) (smashProductSetoid X Y)))⟩
  have hquot : Topology.IsQuotientMap quotientMk := by
    -- The smash-product constructor is the quotient map presenting `X ∧ Y`.
    simpa [quotientMk, smashProductMk, smashProductType] using
      (isQuotientMap_quot_mk :
        Topology.IsQuotientMap
          (@Quot.mk (smashProductPair X Y) (smashProductSetoid X Y).r))
  let F : S → C(smashProductPair X Y, Z.right) := fun s ↦
    ContinuousMap.uncurry
      (⟨fun x ↦ ((φ s).1 x).1, continuous_subtype_val.comp (φ s).1.continuous⟩ :
        C(X.right, C(Y.right, Z.right)))
  have hEval :
      Continuous fun sp : S × smashProductPair X Y ↦ F sp.1 sp.2 := by
    -- Precomposing the already-continuous raw evaluation family with the probe keeps it
    -- continuous.
    simpa [F, Function.uncurry] using
      (smashProductMappingAdjunctionInvRawEval_continuous X Y Z).comp
        ((φ.continuous.comp continuous_fst).prodMk continuous_snd)
  have hFactor :
      ∀ s, Function.FactorsThrough (F s) quotientMk := by
    -- Each raw uncurried family still factors through the smash-product quotient.
    intro s
    exact smashProductMappingAdjunctionInvRawFamily_factorsThrough X Y Z (φ s)
  have hDescended :
      Continuous fun s : S ↦ hquot.lift (F s) (hFactor s) := by
    -- The quotient lifting theorem only needs local compactness of the parameter space.
    exact smashProductQuotientLift_continuous X Y Z quotientMk hquot F hEval hFactor
  have hLiftEq :
      (fun s : S ↦ hquot.lift (F s) (hFactor s)) =
        fun s : S ↦ (smashProductMappingAdjunctionInvFun X Y Z (φ s)).1 := by
    funext s
    ext q
    -- Equality on all smash-product classes is detected on quotient generators.
    refine Quotient.inductionOn' q ?_
    intro p
    calc
      hquot.lift (F s) (hFactor s) (smashProductMk X Y p) = F s p := by
        exact smashProductQuotientLift_apply_mk X Y Z quotientMk rfl hquot
          ⟨F s, hFactor s⟩ p
      _ = ((φ s).1 p.1).1 p.2 := by
        rfl
      _ = (smashProductMappingAdjunctionInvFun X Y Z (φ s)).1 (smashProductMk X Y p) := by
        symm
        simpa using
          smashProductMappingAdjunctionInvFun_precomp_smashProductMk X Y Z (φ s, p)
  have hInvContinuous :
      Continuous fun s : S ↦ (smashProductMappingAdjunctionInvFun X Y Z (φ s)).1 := by
    -- Replace the explicit inverse family with its quotient-lift presentation.
    rw [← hLiftEq]
    exact hDescended
  -- The compact-open criterion now converts continuity of the probe family into openness of the
  -- pulled-back subbasic set.
  exact (ContinuousMap.continuous_compactOpen.mp hInvContinuous) K hK U hU

/-- Helper for Adjunction 8.1.4: the compactly generated replacement of a `Type s` is itself a
compactly generated space. -/
private theorem compactlyGeneratedTopologyCompactlyGeneratedSpace
    (T : Type s) [TopologicalSpace T] :
    @CompactlyGeneratedSpace T (TopologicalSpace.compactlyGenerated.{s} T) := by
  let f : (Σ (i : (S : CompHaus.{s}) × C(S, T)), i.fst) → T := fun x ↦ x.1.2 x.2
  -- The replacement topology is the standard coinduced topology generated by compact probes.
  have hf :
      @Continuous ((Σ (i : (S : CompHaus.{s}) × C(S, T)), i.fst)) T
        instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact
    @uCompactlyGeneratedSpace_of_coinduced.{s, _, _}
      ((Σ (i : (S : CompHaus.{s}) × C(S, T)), i.fst)) T instTopologicalSpaceSigma
      (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Helper for Adjunction 8.1.4: the source type for the inverse family is the iterated based
mapping space `F(X, F(Y, Z))`. -/
private abbrev smashProductMappingAdjunctionInvSource
    (X Y Z : BasedSpace) : Type _ :=
  underBasedMapSpace X (underBasedMapSpaceObject Y Z)

/-- Helper for Adjunction 8.1.4: this is the compactly generated replacement of the source based
mapping-space topology used for the verified probe-level continuity frontier. -/
private abbrev smashProductMappingAdjunctionInvSourceTopology
    (X Y Z : BasedSpace) :
    TopologicalSpace (smashProductMappingAdjunctionInvSource X Y Z) :=
  TopologicalSpace.compactlyGenerated.{u}
    (smashProductMappingAdjunctionInvSource X Y Z)

/-- Helper for Adjunction 8.1.4: compact-Hausdorff probes into the source based mapping space pull
back inverse-family compact-open subbasic sets to open subsets. -/
private theorem invSubbasicPreimage_isOpen_compHausParam
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (φ : C(S, underBasedMapSpace X (underBasedMapSpaceObject Y Z)))
    (K : Set ((X ∧ Y).right)) (hK : IsCompact K) (U : Set Z.right) (hU : IsOpen U) :
    IsOpen
      { s : S | Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z (φ s)).1) K U } := by
  -- Compact Hausdorff probes are locally compact, so the locally compact parameter theorem applies
  -- directly to every probe into the source mapping space.
  letI : LocallyCompactSpace S := inferInstance
  exact
    invSubbasicPreimage_isOpen_locallyCompactParam
      X Y Z φ K hK U hU

/-- Helper for Adjunction 8.1.4: after replacing the source based mapping space by its compactly
generated topology, the inverse family is continuous. -/
private theorem smashProductMappingAdjunctionInvFun_continuous_compactlyGeneratedSource
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous[
      TopologicalSpace.compactlyGenerated.{u}
        (smashProductMappingAdjunctionInvSource X Y Z),
      inferInstance]
      (smashProductMappingAdjunctionInvFun X Y Z) := by
  let T := smashProductMappingAdjunctionInvSource X Y Z
  let invAmbient : T → C((X ∧ Y).right, Z.right) :=
    fun g ↦ (smashProductMappingAdjunctionInvFun X Y Z g).1
  have hInvAmbient :
      Continuous[TopologicalSpace.compactlyGenerated.{u} T, inferInstance] invAmbient := by
    -- The compactly generated source topology asks only for continuity after compact-Hausdorff
    -- probes, and each probe is covered by the compact-parameter openness lemma.
    refine continuous_from_compactlyGenerated invAmbient ?_
    intro S φ
    refine ContinuousMap.continuous_compactOpen.2 ?_
    intro K hK U hU
    simpa [invAmbient, T] using
      invSubbasicPreimage_isOpen_compHausParam
        X Y Z φ K hK U hU
  -- Repackage the ambient map continuity with the already-verified basepoint condition.
  letI : TopologicalSpace T := TopologicalSpace.compactlyGenerated.{u} T
  have hEq :
      (smashProductMappingAdjunctionInvFun X Y Z :
          T → underBasedMapSpace (X ∧ Y) Z) =
        fun g : T ↦
          (⟨invAmbient g, (smashProductMappingAdjunctionInvFun X Y Z g).2⟩ :
            underBasedMapSpace (X ∧ Y) Z) := by
    funext g
    rfl
  rw [hEq]
  rw [continuous_induced_rng]
  simpa only [Function.comp_apply, invAmbient] using hInvAmbient

/-- Helper for Adjunction 8.1.4: mapping a compact set in the smash product into `U` by the
descended inverse map is equivalent to mapping its quotient preimage into `U` by the raw
uncurried family. -/
private theorem smashProductMappingAdjunctionInvFun_mapsTo_iff_rawPreimage
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z))
    (K : Set ((X ∧ Y).right)) (U : Set Z.right) :
    Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z g).1) K U ↔
      Set.MapsTo
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right))))
        (smashProductMk X Y ⁻¹' K) U := by
  constructor
  · intro h p hp
    -- Push a source-side point into the quotient-side compact test set and evaluate there.
    have hImage :
        (smashProductMappingAdjunctionInvFun X Y Z g).1 (smashProductMk X Y p) ∈ U := h hp
    simpa [smashProductMappingAdjunctionInvFun_precomp_smashProductMk] using hImage
  · intro h q hq
    -- Every smash-product class has a representative, so the quotient-side condition reduces to
    -- the raw source-side condition on that representative.
    revert hq
    refine Quotient.inductionOn' q ?_
    intro p hp
    have hImage :
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right)))) p ∈ U := h hp
    simpa [smashProductMappingAdjunctionInvFun_precomp_smashProductMk] using hImage

/-- Helper for Adjunction 8.1.4: the inverse-image subbasic set on the smash product is exactly
the raw-family subbasic set on the quotient preimage in `X × Y`. -/
private theorem smashProductMappingAdjunctionInvFun_subbasicPreimage_eq_raw
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (K : Set ((X ∧ Y).right)) (U : Set Z.right) :
    { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
        Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z g).1) K U } =
      { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
          Set.MapsTo
            (ContinuousMap.uncurry
              (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
                C(X.right, C(Y.right, Z.right))))
            (smashProductMk X Y ⁻¹' K) U } := by
  -- Extensionality converts the set equality into the pointwise `MapsTo` comparison.
  ext g
  exact smashProductMappingAdjunctionInvFun_mapsTo_iff_rawPreimage X Y Z g K U

/-- Helper for Adjunction 8.1.4: if a compact test set `K` is represented as the image of a
source-side set `L`, then the descended inverse family maps `K` into `U` exactly when the raw
uncurried family maps `L` into `U`. -/
private theorem smashProductMappingAdjunctionInvFun_mapsTo_iff_rawLift
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z))
    (L : Set (smashProductPair X Y)) (K : Set ((X ∧ Y).right)) (U : Set Z.right)
    (hLift : smashProductMk X Y '' L = K) :
    Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z g).1) K U ↔
      Set.MapsTo
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right))))
        L U := by
  constructor
  · intro h p hpL
    -- Push the source-side representative into `K` using the chosen image description.
    have hK : smashProductMk X Y p ∈ K := by
      rw [← hLift]
      exact ⟨p, hpL, rfl⟩
    have hImage :
        (smashProductMappingAdjunctionInvFun X Y Z g).1 (smashProductMk X Y p) ∈ U := h hK
    simpa [smashProductMappingAdjunctionInvFun_precomp_smashProductMk] using hImage
  · intro h q hqK
    -- Pull a quotient-side point back to its chosen representative in `L`.
    have hImage : q ∈ smashProductMk X Y '' L := by
      simpa [hLift] using hqK
    rcases hImage with ⟨p, hpL, rfl⟩
    have hRaw :
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right)))) p ∈ U := h hpL
    simpa [smashProductMappingAdjunctionInvFun_precomp_smashProductMk] using hRaw

/-- Helper for Adjunction 8.1.4: once a compact test set is replaced by a source-side image lift,
the inverse-family subbasic set rewrites to the corresponding raw-family subbasic set. -/
private theorem smashProductMappingAdjunctionInvFun_subbasicPreimage_eq_lift
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (L : Set (smashProductPair X Y)) (K : Set ((X ∧ Y).right)) (U : Set Z.right)
    (hLift : smashProductMk X Y '' L = K) :
    { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
        Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z g).1) K U } =
      { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
          Set.MapsTo
            (ContinuousMap.uncurry
              (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
                C(X.right, C(Y.right, Z.right))))
            L U } := by
  -- Extensionality reduces the rewrite to the pointwise `MapsTo` bridge.
  ext g
  exact smashProductMappingAdjunctionInvFun_mapsTo_iff_rawLift X Y Z g L K U hLift

/-- Helper for Adjunction 8.1.4: a factor-through witness can be transported across an explicit
identification of quotient maps. -/
private theorem factorsThrough_of_eq_quotientMap
    {A B C : Type*} {f g : A → B} (hfg : f = g) (u : A → C)
    (hu : Function.FactorsThrough u g) :
    Function.FactorsThrough u f := by
  -- Rewrite the quotient-map comparison once, then reuse the original factor-through witness.
  intro x y hxy
  exact hu (hfg ▸ hxy)

/-- Helper for Adjunction 8.1.4: the existing inverse map agrees with the generic quotient lift of
the raw uncurried family. -/
private theorem smashProductMappingAdjunctionInvFun_eq_liftedRawFamily
    (X Y Z : BasedSpace) [LocallyCompactSpace Y.right]
    (quotientMk : C(smashProductPair X Y, (X ∧ Y).right))
    (hQuotientMk : (quotientMk : smashProductPair X Y → (X ∧ Y).right) = smashProductMk X Y)
    (hquot : Topology.IsQuotientMap quotientMk)
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z)) :
    let raw : C(smashProductPair X Y, Z.right) :=
      ContinuousMap.uncurry
        (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
          C(X.right, C(Y.right, Z.right)))
    (smashProductMappingAdjunctionInvFun X Y Z g).1 =
      hquot.lift raw
        (factorsThrough_of_eq_quotientMap hQuotientMk raw
          (smashProductMappingAdjunctionInvRawFamily_factorsThrough X Y Z g)) := by
  -- Equality on the quotient is checked on smash-product generators.
  dsimp
  ext q
  refine Quotient.inductionOn' q ?_
  intro p
  calc
    (smashProductMappingAdjunctionInvFun X Y Z g).1 (smashProductMk X Y p) =
        (ContinuousMap.uncurry
          (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
            C(X.right, C(Y.right, Z.right)))) p := by
      simpa using smashProductMappingAdjunctionInvFun_precomp_smashProductMk X Y Z (g, p)
    _ =
        hquot.lift
          (ContinuousMap.uncurry
            (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
              C(X.right, C(Y.right, Z.right))))
          (factorsThrough_of_eq_quotientMap hQuotientMk
            (ContinuousMap.uncurry
              (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
                C(X.right, C(Y.right, Z.right))))
            (smashProductMappingAdjunctionInvRawFamily_factorsThrough X Y Z g))
          (smashProductMk X Y p) := by
      symm
      exact smashProductQuotientLift_apply_mk X Y Z quotientMk hQuotientMk hquot
        ⟨ContinuousMap.uncurry
            (⟨fun x ↦ (g.1 x).1, continuous_subtype_val.comp g.1.continuous⟩ :
              C(X.right, C(Y.right, Z.right))),
          by
            exact factorsThrough_of_eq_quotientMap hQuotientMk _ <|
              smashProductMappingAdjunctionInvRawFamily_factorsThrough X Y Z g⟩
        p

/-- Helper for Adjunction 8.1.4: once a compact test set `K` in `X ∧ Y` is replaced by a compact
source-side lift `L`, the inverse-family compact-open subbasic set is open. -/
private theorem invSubbasicPreimage_isOpen_of_compactLift
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (K : Set ((X ∧ Y).right)) (U : Set Z.right) (hU : IsOpen U)
    (L : Set (smashProductPair X Y)) (hL : IsCompact L)
    (hLift : smashProductMk X Y '' L = K) :
    IsOpen
      { g : underBasedMapSpace X (underBasedMapSpaceObject Y Z) |
          Set.MapsTo ((smashProductMappingAdjunctionInvFun X Y Z g).1) K U } := by
  -- Rewrite the quotient-side subbasic condition along the chosen compact lift and then apply
  -- the already-proved raw-family compact-open openness theorem.
  rw [smashProductMappingAdjunctionInvFun_subbasicPreimage_eq_lift X Y Z L K U hLift]
  exact
    smashProductMappingAdjunctionInvRawFamily_subbasicPreimage_isOpen X Y Z L hL U hU

/-- Helper for Adjunction 8.1.4: a compact-lift theorem for `smashProductMk X Y` is enough to
finish continuity of the inverse family in the ordinary compact-open topology. -/
private theorem smashProductMappingAdjunctionInvFun_continuous_of_compactLift
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (hLift :
      ∀ K : Set ((X ∧ Y).right), IsCompact K →
        ∃ L : Set (smashProductPair X Y), IsCompact L ∧ smashProductMk X Y '' L = K) :
    Continuous (smashProductMappingAdjunctionInvFun X Y Z) := by
  refine Continuous.subtype_mk ?_ fun g ↦ (smashProductMappingAdjunctionInvFun X Y Z g).2
  -- The compact-open criterion reduces continuity to subbasic openness, and each compact test set
  -- is handled by the supplied compact source-side lift.
  refine ContinuousMap.continuous_compactOpen.2 ?_
  intro K hK U hU
  rcases hLift K hK with ⟨L, hL, hLiftK⟩
  exact
    invSubbasicPreimage_isOpen_of_compactLift
      X Y Z K U hU L hL hLiftK

/-- Helper for Adjunction 8.1.4: the inverse uncurrying map is continuous on based mapping
spaces. -/
private theorem smashProductMappingAdjunctionInvFun_continuous
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    Continuous (smashProductMappingAdjunctionInvFun X Y Z) := by
  -- TODO: this reduces to `smashProductMappingAdjunctionInvFun_continuous_of_compactLift`, but the
  -- missing ingredient is a smash-specific compact-lift theorem for compact subsets of `X ∧ Y`.
  sorry

/-- Helper for Adjunction 8.1.4: the explicit locally compact bridge homeomorphism data
implementing `F(smashProduct X Y, Z) ≅ F(X, F(Y, Z))` for based spaces `X`, `Y`, and `Z`. -/
private def smashProductMappingAdjunctionRawHomeomorph_of_locallyCompact
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    underBasedMapSpace (smashProduct X Y) Z ≃ₜ
      underBasedMapSpace X (underBasedMapSpaceObject Y Z) where
  toFun := smashProductMappingAdjunctionToFun X Y Z
  invFun := smashProductMappingAdjunctionInvFun X Y Z
  left_inv := smashProductMappingAdjunctionHomeomorph_leftInv X Y Z
  right_inv := smashProductMappingAdjunctionHomeomorph_rightInv X Y Z
  continuous_toFun := smashProductMappingAdjunctionToFun_continuous X Y Z
  continuous_invFun := smashProductMappingAdjunctionInvFun_continuous X Y Z

/-- A locally compact bridge for the smash-product mapping adjunction on raw based spaces. -/
def smashProductMappingAdjunctionHomeomorph_of_locallyCompact
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] :
    underBasedMapSpace (smashProduct X Y) Z ≃ₜ
      underBasedMapSpace X (underBasedMapSpaceObject Y Z) :=
  smashProductMappingAdjunctionRawHomeomorph_of_locallyCompact X Y Z

/-- The forward map of `smashProductMappingAdjunctionHomeomorph_of_locallyCompact` sends a based map
`f : X ∧ Y → Z` to its curried form `x ↦ (y ↦ f (x ∧ y))`. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_apply
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (f : underBasedMapSpace (X ∧ Y) Z) (x : X.right) (y : Y.right) :
    ((smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z f).1 x).1 y =
      f.1 (smashProductMk X Y (x, y)) := by
  change ((smashProductMappingAdjunctionToFun X Y Z f).1 x).1 y =
    f.1 (smashProductMk X Y (x, y))
  rfl

/-- The inverse map of `smashProductMappingAdjunctionHomeomorph_of_locallyCompact` evaluates the
uncurried based map on a smash-product class `x ∧ y` by `(g x) y`. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_symm_apply_mk
    (X Y Z : BasedSpace) [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (g : underBasedMapSpace X (underBasedMapSpaceObject Y Z))
    (p : X.right × Y.right) :
    ((smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z).symm g).1
        (smashProductMk X Y p) =
      (g.1 p.1).1 p.2 := by
  rcases p with ⟨x, y⟩
  change (smashProductMappingAdjunctionInvFun X Y Z g).1 (smashProductMk X Y (x, y)) =
    (g.1 x).1 y
  rfl

/-- The locally compact bridge homeomorphism is natural in all three variables. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural
    {X X' Y Y' Z Z' : BasedSpace}
    [LocallyCompactSpace X.right] [LocallyCompactSpace X'.right]
    [LocallyCompactSpace Y.right] [LocallyCompactSpace Y'.right]
    (f : X' ⟶ X) (g : Y' ⟶ Y) (k : Z ⟶ Z')
    (h : underBasedMapSpace (X ∧ Y) Z) :
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact X' Y' Z'
      (underBasedMapSpaceMap (smashProductMap f g) k h) =
    underBasedMapSpaceMap f (underBasedMapSpaceObjectMap g k)
      (smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z h) := by
  apply Subtype.ext
  ext x
  apply Subtype.ext
  ext y
  -- Both sides evaluate to `k (h (f x ∧ g y))` on every pair `(x, y)`.
  change
    k.right.hom (h.1 ((smashProductMap f g).right.hom (smashProductMk X' Y' (x, y)))) =
      k.right.hom
        (((smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z h).1
          (f.right.hom x)).1
        (g.right.hom y))
  rw [smashProductMap_apply_mk, smashProductMappingAdjunctionHomeomorph_of_locallyCompact_apply]

/-- Naturality of `smashProductMappingAdjunctionHomeomorph_of_locallyCompact` in the
`X`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural_X
    {X X' Y Z : BasedSpace}
    [LocallyCompactSpace X.right] [LocallyCompactSpace X'.right] [LocallyCompactSpace Y.right]
    (f : X' ⟶ X) (h : underBasedMapSpace (X ∧ Y) Z) :
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact X' Y Z
      (underBasedMapSpaceMap (smashProductMap f (𝟙 Y)) (𝟙 Z) h) =
    underBasedMapSpaceMap f (𝟙 (underBasedMapSpaceObject Y Z))
      (smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z h) := by
  -- This is the three-variable naturality statement with identities in `Y` and `Z`.
  simpa using
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural f (𝟙 Y) (𝟙 Z) h

/-- Naturality of `smashProductMappingAdjunctionHomeomorph_of_locallyCompact` in the
`Y`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural_Y
    {X Y Y' Z : BasedSpace}
    [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right] [LocallyCompactSpace Y'.right]
    (g : Y' ⟶ Y) (h : underBasedMapSpace (X ∧ Y) Z) :
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y' Z
      (underBasedMapSpaceMap (smashProductMap (𝟙 X) g) (𝟙 Z) h) =
    underBasedMapSpaceMap (𝟙 X) (underBasedMapSpaceObjectMap g (𝟙 Z))
      (smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z h) := by
  -- This is the three-variable naturality statement with identities in `X` and `Z`.
  simpa using
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural (𝟙 X) g (𝟙 Z) h

/-- Naturality of `smashProductMappingAdjunctionHomeomorph_of_locallyCompact` in the
`Z`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural_Z
    {X Y Z Z' : BasedSpace}
    [LocallyCompactSpace X.right] [LocallyCompactSpace Y.right]
    (k : Z ⟶ Z') (h : underBasedMapSpace (X ∧ Y) Z) :
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z'
      (underBasedMapSpaceMap (smashProductMap (𝟙 X) (𝟙 Y)) k h) =
    underBasedMapSpaceMap (𝟙 X) (underBasedMapSpaceObjectMap (𝟙 Y) k)
      (smashProductMappingAdjunctionHomeomorph_of_locallyCompact X Y Z h) := by
  -- This is the three-variable naturality statement with identities in `X` and `Y`.
  simpa using
    smashProductMappingAdjunctionHomeomorph_of_locallyCompact_natural (𝟙 X) (𝟙 Y) k h

/-- Helper for Adjunction 8.1.4::statement_repair::1: for pointed compactly generated spaces, the
inverse uncurrying map is continuous on the chapter's canonical mapping-space owner. -/
private theorem smashProductMappingAdjunctionPointedProbeEvalContinuous
    (X Y Z : PointedCompactlyGenerated.{u, w})
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace))
    (a : C(S, X.toCompactlyGenerated)) (b : C(S, Y.toCompactlyGenerated)) :
    Continuous fun s ↦ ((g.1 (a s)).1 (b s)) := by
  let outer : C(S, underBasedMapSpace Y.toBasedSpace Z.toBasedSpace) :=
    ⟨fun s ↦ g.1 (a s), g.1.continuous.comp a.continuous⟩
  let forgetY :
      C(underBasedMapSpace Y.toBasedSpace Z.toBasedSpace,
        C(Y.toCompactlyGenerated, Z.toCompactlyGenerated)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let family : C(S, C(Y.toCompactlyGenerated, Z.toCompactlyGenerated)) := forgetY.comp outer
  let precompB :
      C(C(Y.toCompactlyGenerated, Z.toCompactlyGenerated), C(S, Z.toCompactlyGenerated)) :=
    ⟨fun f ↦ f.comp b, ContinuousMap.continuous_precomp b⟩
  let evaluated : C(S, C(S, Z.toCompactlyGenerated)) := precompB.comp family
  letI : LocallyCompactSpace S := inferInstance
  have hEval : Continuous fun s ↦ evaluated s s := by
    -- Route correction: precompose each `Y → Z` slice with the compact probe `b`, then evaluate
    -- in `C(S, Z)` where ordinary compact-open evaluation is available.
    exact continuous_eval.comp (evaluated.continuous.prodMk continuous_id)
  -- Unfolding the two precomposition steps recovers the desired probe evaluation formula.
  simpa [outer, forgetY, family, precompB, evaluated, ContinuousMap.comp_apply] using hEval

/-- Helper for Adjunction 8.1.4: a compact Hausdorff space is `UCompactlyGeneratedSpace` because
the identity probe already appears in the defining compact family. -/
private theorem smashAdjunctionCompactHausdorff_uCompactlyGenerated
    {K : Type w} [TopologicalSpace K] [CompactSpace K] [T2Space K] :
    @UCompactlyGeneratedSpace.{w} K ‹TopologicalSpace K› := by
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z _ f hf
  -- The identity compact probe on `K` already certifies continuity.
  simpa [Function.comp] using hf (CompHaus.of K) ⟨id, continuous_id⟩

/-- Helper for Adjunction 8.1.4: the product of a compact Hausdorff space with a
`UCompactlyGeneratedSpace` is again `UCompactlyGeneratedSpace`. -/
private theorem smashAdjunctionUCompactlyGeneratedSpaceProdCompHaus
    {S : Type s} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    UCompactlyGeneratedSpace.{max u s} (S × X) := by
  let _ : LocallyCompactSpace S := inferInstance
  -- Prove continuity on `S × X` by currying into the compact-open mapping space `C(S, Z)`.
  refine uCompactlyGeneratedSpace_of_continuous_maps ?_
  intro Z tZ f hf
  let F : X → C(S, Z) := fun x ↦
    ⟨fun s ↦ f (s, x), by
      let gx : C(ULift.{u} S, S × X) :=
        ⟨fun s ↦ (s.down, x), continuous_uliftDown.prodMk continuous_const⟩
      have hsec : Continuous fun s : ULift.{u} S ↦ f (s.down, x) := by
        simpa [gx] using hf (CompHaus.of (ULift.{u} S)) gx
      simpa using hsec.comp continuous_uliftUp⟩
  have hF : Continuous F := by
    -- Continuity into `C(S, Z)` is checked after precomposing with compact Hausdorff probes.
    refine continuous_from_uCompactlyGeneratedSpace F ?_
    intro T g
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    let h : C(T × S, S × X) :=
      ⟨fun p ↦ (p.2, g p.1), continuous_snd.prodMk (g.continuous.comp continuous_fst)⟩
    simpa [F, h, Function.uncurry, Function.comp_def] using hf (CompHaus.of (T × S)) h
  have hUncurry : Continuous fun xs : X × S ↦ f (xs.2, xs.1) := by
    -- Uncurrying the continuous family `x ↦ (s ↦ f (s, x))` gives continuity on `X × S`.
    simpa [F, Function.uncurry] using ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩
  -- Swap the factors back to the requested source order.
  simpa [Function.comp_def] using hUncurry.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Adjunction 8.1.4: if a map on `X × Y` is continuous on every compact-Hausdorff
probe into the product, then each section in the `Y`-variable is continuous. -/
private theorem smashAdjunctionContinuousSectionOfProbeTest
    {X Y Z : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [UCompactlyGeneratedSpace.{u} Y]
    (f : X × Y → Z)
    (hf : ∀ (S : CompHaus.{u}) (g : C(S, X × Y)), Continuous (f ∘ g))
    (x : X) :
    Continuous fun y : Y ↦ f (x, y) := by
  -- Test the `Y`-section against compact probes into `Y` and pair them with the constant map at
  -- the chosen point `x`.
  refine continuous_from_uCompactlyGeneratedSpace _ ?_
  intro S k
  let pairProbe : C(S, X × Y) :=
    ⟨fun s ↦ (x, k s), continuous_const.prodMk k.continuous⟩
  simpa [Function.comp, pairProbe] using hf S pairProbe

/-- Helper for Adjunction 8.1.4::statement_repair::1: the Chapter 5 source-facing owner
`F(X, Y)` is the based subspace of the kified mapping space `Y ^ X`. -/
private abbrev basedCompactlyGeneratedMappingSpace
    (X : PointedCompactlyGenerated.{u, w}) (Y : PointedCompactlyGenerated.{v, w}) :=
  { f : CompactlyGenerated.MapSpace X.toCompactlyGenerated Y.toCompactlyGenerated //
      ((f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point = Y.point) }

namespace basedCompactlyGeneratedMappingSpace

variable {X : PointedCompactlyGenerated.{u, w}} {Y : PointedCompactlyGenerated.{v, w}}

private instance : Coe
    (basedCompactlyGeneratedMappingSpace X Y)
    (CompactlyGenerated.MapSpace X.toCompactlyGenerated Y.toCompactlyGenerated) := ⟨Subtype.val⟩

private instance : Coe
    (basedCompactlyGeneratedMappingSpace X Y)
    C(X.toCompactlyGenerated, Y.toCompactlyGenerated) := ⟨fun f ↦ f.1⟩

private instance : CoeFun (basedCompactlyGeneratedMappingSpace X Y)
    (fun _ ↦ X.toCompactlyGenerated → Y.toCompactlyGenerated) := ⟨fun f ↦ (f : C(_, _))⟩

/-- Helper for Adjunction 8.1.4::statement_repair::1: a continuous based map determines a point
of the compactly generated based mapping-space owner. -/
private abbrev ofContinuousMap
    (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))
    (hf : f X.point = Y.point) :
    basedCompactlyGeneratedMappingSpace X Y :=
  ⟨CompactlyGenerated.MapSpace.ofContinuousMap f, hf⟩

@[simp] private theorem ofContinuousMap_apply
    (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated))
    (hf : f X.point = Y.point) (x : X.toCompactlyGenerated) :
    ofContinuousMap f hf x = f x := rfl

@[simp] private theorem map_point (f : basedCompactlyGeneratedMappingSpace X Y) :
    (f : C(X.toCompactlyGenerated, Y.toCompactlyGenerated)) X.point = Y.point := f.2

private instance : Zero (basedCompactlyGeneratedMappingSpace X Y) := ⟨
  ofContinuousMap (ContinuousMap.const X.toCompactlyGenerated Y.point) rfl
⟩

@[simp] private theorem zero_apply (x : X.toCompactlyGenerated) :
    (0 : basedCompactlyGeneratedMappingSpace X Y) x = Y.point := rfl

@[ext] private theorem ext
    (f g : basedCompactlyGeneratedMappingSpace X Y)
    (h : ∀ x : X.toCompactlyGenerated, f x = g x) : f = g := by
  apply Subtype.ext
  exact CompactlyGenerated.MapSpace.ext _ _ h

end basedCompactlyGeneratedMappingSpace

/-- Helper for Adjunction 8.1.4::statement_repair::1: for pointed compactly generated spaces, the
raw formula `(x, y) ↦ (g x) y` is continuous on `X × Y`. -/
private theorem smashProductMappingAdjunctionPointedUncurried_continuous
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace)) :
    Continuous fun p : smashProductPair X.toBasedSpace Y.toBasedSpace ↦ ((g.1 p.1).1 p.2) := by
  -- Route correction: the previous proof route depended on the false owner claim that ordinary
  -- products of arbitrary `UCompactlyGeneratedSpace`s stay compactly generated. The next repair
  -- has to transport `g` through the based subspace of the Chapter 5 `MapSpace` owner instead of
  -- forcing continuity directly on the raw ordinary product.
  sorry

/-- Helper for Adjunction 8.1.4::statement_repair::1: the pointed inverse map is obtained by
descending the raw formula `(x, y) ↦ (g x) y` along the smash-product quotient. -/
private def smashProductMappingAdjunctionPointedInvFun
    (X Y Z : PointedCompactlyGenerated.{u, w}) :
    underBasedMapSpace X.toBasedSpace
        (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace) →
      underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace :=
  fun g ↦
    let uncurried :
        C(smashProductPair X.toBasedSpace Y.toBasedSpace, Z.toBasedSpace.right) :=
      ⟨fun p ↦ ((g.1 p.1).1 p.2),
        smashProductMappingAdjunctionPointedUncurried_continuous X Y Z g⟩
    let wedgeValue :
        ∀ p : smashProductPair X.toBasedSpace Y.toBasedSpace,
          smashWedge X.toBasedSpace Y.toBasedSpace p → uncurried p = underTopBasepoint Z.toBasedSpace
      | (x, y), hp => by
          rcases hp with rfl | rfl
          · have hbase := congrArg (fun h : underBasedMapSpace Y.toBasedSpace Z.toBasedSpace ↦ h.1 y) g.2
            simpa [uncurried, forget, underBasedMapSpaceBasepoint] using hbase
          · simpa [uncurried, forget] using (g.1 x).2
    let descends :
        ∀ p q : smashProductPair X.toBasedSpace Y.toBasedSpace,
          (smashProductSetoid X.toBasedSpace Y.toBasedSpace).r p q → uncurried p = uncurried q
      | p, q, hpq => by
          change smashProductRel X.toBasedSpace Y.toBasedSpace p q at hpq
          rcases hpq with rfl | ⟨hp, hq⟩
          · rfl
          · exact (wedgeValue p hp).trans (wedgeValue q hq).symm
    let descended : C((X.toBasedSpace ∧ Y.toBasedSpace).right, Z.toBasedSpace.right) :=
      ⟨Quotient.lift
          (fun p : smashProductPair X.toBasedSpace Y.toBasedSpace ↦ uncurried p) descends,
        uncurried.continuous.quotient_lift descends⟩
    ⟨descended, by
      rw [underTopBasepoint_smashProduct X.toBasedSpace Y.toBasedSpace]
      exact
        wedgeValue
          (smashProductBasepointPair X.toBasedSpace Y.toBasedSpace)
          (smashWedge_basepointPair X.toBasedSpace Y.toBasedSpace)
    ⟩

/-- Helper for Adjunction 8.1.4::statement_repair::1: the pointed inverse map agrees with the raw
evaluation formula on every smash-product generator. -/
private theorem smashProductMappingAdjunctionPointedInvFun_apply_mk
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace))
    (p : X.toCompactlyGenerated × Y.toCompactlyGenerated) :
    (smashProductMappingAdjunctionPointedInvFun X Y Z g).1
        (smashProductMk X.toBasedSpace Y.toBasedSpace p) =
      (g.1 p.1).1 p.2 := by
  rcases p with ⟨x, y⟩
  -- On quotient generators, the descended pointed inverse is the original raw formula.
  rfl

/-- Helper for Adjunction 8.1.4::statement_repair::1: currying after the pointed inverse recovers
the original family pointwise. -/
private theorem smashProductMappingAdjunctionPointedToInv_apply
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace))
    (x : X.toCompactlyGenerated) (y : Y.toCompactlyGenerated) :
    ((smashProductMappingAdjunctionToFun
      X.toBasedSpace Y.toBasedSpace Z.toBasedSpace
      (smashProductMappingAdjunctionPointedInvFun X Y Z g)).1 x).1 y =
      (g.1 x).1 y := by
  -- Evaluating the re-curried pointed inverse recovers the original family at `(x, y)`.
  rfl

/-- Helper for Adjunction 8.1.4::statement_repair::1: the pointed inverse is a left inverse to
currying on maps out of the smash product. -/
private theorem smashProductMappingAdjunctionPointedHomeomorph_leftInv
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (f : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace) :
    smashProductMappingAdjunctionPointedInvFun X Y Z
      (smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f) = f := by
  apply Subtype.ext
  ext q
  -- Equality on the smash product is checked on quotient generators.
  refine Quotient.inductionOn' q ?_
  intro p
  calc
    (smashProductMappingAdjunctionPointedInvFun X Y Z
      (smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f)).1
        (smashProductMk X.toBasedSpace Y.toBasedSpace p) =
      ((smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f).1 p.1).1 p.2 := by
        exact smashProductMappingAdjunctionPointedInvFun_apply_mk X Y Z _ p
    _ = f.1 (smashProductMk X.toBasedSpace Y.toBasedSpace p) := by
      rfl

/-- Helper for Adjunction 8.1.4::statement_repair::1: the pointed inverse and forward maps
compose to the identity on iterated pointed mapping spaces. -/
private theorem smashProductMappingAdjunctionPointedHomeomorph_rightInv
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace)) :
    smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace
      (smashProductMappingAdjunctionPointedInvFun X Y Z g) = g := by
  apply Subtype.ext
  ext x
  apply Subtype.ext
  ext y
  -- The iterated mapping-space equality is detected by evaluation in both variables.
  exact smashProductMappingAdjunctionPointedToInv_apply X Y Z g x y

/-- Helper for Adjunction 8.1.4::statement_repair::1: a forward compact-open subbasic condition on
`K ⊆ X` and `L ⊆ Y` is exactly the corresponding compact-open condition on
`smashProductMk '' (K ×ˢ L)`. -/
private theorem smashProductMappingAdjunctionToFun_subbasicPreimage_eq_image
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (K : Set X.toCompactlyGenerated) (L : Set Y.toCompactlyGenerated) (U : Set Z.toCompactlyGenerated) :
    { f : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace |
        Set.MapsTo
          ((smashProductMappingAdjunctionToFun
            X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f).1)
          K
          { g : underBasedMapSpace Y.toBasedSpace Z.toBasedSpace | Set.MapsTo g.1 L U } } =
      { f : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace |
          Set.MapsTo f.1
            (smashProductMk X.toBasedSpace Y.toBasedSpace '' (K ×ˢ L)) U } := by
  ext f
  constructor
  · intro hf p hp
    rcases hp with ⟨⟨x, y⟩, hxy, rfl⟩
    rcases hxy with ⟨hx, hy⟩
    -- Evaluate the curried map at `x` and then at `y`.
    change
      (((smashProductMappingAdjunctionToFun
        X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f).1 x).1 y) ∈ U
    exact hf hx hy
  · intro hf x hx y hy
    -- Repackage `(x, y)` as a smash-product generator in the chosen compact image.
    change f.1 (smashProductMk X.toBasedSpace Y.toBasedSpace (x, y)) ∈ U
    exact hf ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/-- Helper for Adjunction 8.1.4::statement_repair::1: the forward compact-open subbasic sets are
open after rewriting through `smashProductMk '' (K ×ˢ L)`. -/
private theorem smashProductMappingAdjunctionToFun_subbasicPreimage_isOpen
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (K : Set X.toCompactlyGenerated) (hK : IsCompact K)
    (L : Set Y.toCompactlyGenerated) (hL : IsCompact L)
    (U : Set Z.toCompactlyGenerated) (hU : IsOpen U) :
    IsOpen
      { f : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace |
          Set.MapsTo
            ((smashProductMappingAdjunctionToFun
              X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f).1)
            K
            { g : underBasedMapSpace Y.toBasedSpace Z.toBasedSpace | Set.MapsTo g.1 L U } } := by
  rw [smashProductMappingAdjunctionToFun_subbasicPreimage_eq_image X Y Z K L U]
  have hSmashProductMk :
      Continuous (smashProductMk X.toBasedSpace Y.toBasedSpace) := by
    simpa [smashProductMk, smashProductType] using
      (continuous_quotient_mk' :
        Continuous
          (@Quotient.mk' (smashProductPair X.toBasedSpace Y.toBasedSpace)
            (smashProductSetoid X.toBasedSpace Y.toBasedSpace)))
  have hCompactImage :
      IsCompact
        (smashProductMk X.toBasedSpace Y.toBasedSpace '' (K ×ˢ L)) := by
    -- Compactness is preserved along the smash-product quotient map.
    exact (hK.prod hL).image hSmashProductMk
  -- The source mapping space uses the ordinary compact-open topology.
  exact
    (ContinuousMap.continuous_compactOpen.mp continuous_subtype_val)
      _ hCompactImage _ hU

/-- Helper for Adjunction 8.1.4::statement_repair::1: for pointed compactly generated spaces, the
inverse uncurrying map is continuous on the chapter's canonical mapping-space owner. -/
private theorem smashAdjunctionContinuousToFun
    (X Y Z : PointedCompactlyGenerated.{u, w}) :
    Continuous
      (smashProductMappingAdjunctionToFun
        X.toBasedSpace Y.toBasedSpace Z.toBasedSpace) := by
  -- Route correction: the next viable route is to compare `underBasedMapSpace` with the based
  -- subspace of the Chapter 5 owner `Y ^ X`, then transport continuity from a restricted curry
  -- homeomorphism. The missing step is a topology bridge from the raw based mapping-space owner to
  -- `basedCompactlyGeneratedMappingSpace`, not another direct compact-open evaluation argument.
  sorry

/-- Helper for Adjunction 8.1.4::statement_repair::1: for pointed compactly generated spaces, the
inverse uncurrying map is continuous on the chapter's canonical mapping-space owner. -/
private theorem smashAdjunctionContinuousInvFun
    (X Y Z : PointedCompactlyGenerated.{u, w}) :
    Continuous
      (smashProductMappingAdjunctionPointedInvFun X Y Z) := by
  -- Route correction: after isolating the based `MapSpace` owner, the inverse continuity problem
  -- is no longer a compact-lift calculation. The first blocker is that packaging the based
  -- `MapSpace` subtype as a compactly generated object requires singleton-basepoint closedness,
  -- i.e. extra `T1`/weak-Hausdorff data not present in the current `PointedCompactlyGenerated`
  -- hypotheses.
  sorry

/-- Helper for Adjunction 8.1.4::statement_repair::1: the raw mapping-space owner carries the
smash-product mapping adjunction homeomorphism for pointed compactly generated spaces. -/
private def smashProductMappingAdjunctionRawHomeomorph
    (X Y Z : PointedCompactlyGenerated.{u, w}) :
    underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace ≃ₜ
      underBasedMapSpace X.toBasedSpace
        (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace) where
  toFun := smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace
  invFun := smashProductMappingAdjunctionPointedInvFun X Y Z
  left_inv :=
    smashProductMappingAdjunctionPointedHomeomorph_leftInv X Y Z
  right_inv :=
    smashProductMappingAdjunctionPointedHomeomorph_rightInv X Y Z
  continuous_toFun :=
    smashAdjunctionContinuousToFun X Y Z
  continuous_invFun := smashAdjunctionContinuousInvFun X Y Z

/-- Adjunction 8.1.4::statement_repair::1: there is a natural homeomorphism
`F(X ∧ Y, Z) ≅ F(X, F(Y, Z))` for pointed compactly generated spaces `X`, `Y`, and `Z`. -/
def smashProductMappingAdjunctionHomeomorph
    (X Y Z : PointedCompactlyGenerated.{u, w}) :
    underBasedMapSpace (smashProduct X.toBasedSpace Y.toBasedSpace) Z.toBasedSpace ≃ₜ
      underBasedMapSpace X.toBasedSpace
        (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace) :=
  smashProductMappingAdjunctionRawHomeomorph X Y Z

/-- The forward map of `smashProductMappingAdjunctionHomeomorph` sends a based map
`f : X ∧ Y → Z` to its curried form `x ↦ (y ↦ f (x ∧ y))`. -/
theorem smashProductMappingAdjunctionHomeomorph_apply
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (f : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace)
    (x : X.toCompactlyGenerated) (y : Y.toCompactlyGenerated) :
    ((smashProductMappingAdjunctionHomeomorph X Y Z f).1 x).1 y =
      f.1 (smashProductMk X.toBasedSpace Y.toBasedSpace (x, y)) := by
  change
    ((smashProductMappingAdjunctionToFun X.toBasedSpace Y.toBasedSpace Z.toBasedSpace f).1 x).1 y
      = f.1 (smashProductMk X.toBasedSpace Y.toBasedSpace (x, y))
  rfl

/-- The inverse map of `smashProductMappingAdjunctionHomeomorph` evaluates the uncurried based map
on a smash-product class `x ∧ y` by `(g x) y`. -/
theorem smashProductMappingAdjunctionHomeomorph_symm_apply_mk
    (X Y Z : PointedCompactlyGenerated.{u, w})
    (g : underBasedMapSpace X.toBasedSpace
      (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace))
    (p : X.toCompactlyGenerated × Y.toCompactlyGenerated) :
    ((smashProductMappingAdjunctionHomeomorph X Y Z).symm g).1
        (smashProductMk X.toBasedSpace Y.toBasedSpace p) =
      (g.1 p.1).1 p.2 := by
  rcases p with ⟨x, y⟩
  change
    (smashProductMappingAdjunctionPointedInvFun X Y Z g).1
        (smashProductMk X.toBasedSpace Y.toBasedSpace (x, y)) =
      (g.1 x).1 y
  rfl

/-- The homeomorphism `smashProductMappingAdjunctionHomeomorph` is natural in all three variables
`X`, `Y`, and `Z`. -/
theorem smashProductMappingAdjunctionHomeomorph_natural
    {X X' Y Y' Z Z' : PointedCompactlyGenerated.{u, w}}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (k : Z ⟶ Z')
    (h : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace) :
    smashProductMappingAdjunctionHomeomorph X' Y' Z'
      (underBasedMapSpaceMap
        (smashProductMap (PointedCompactlyGenerated.toBasedSpaceMap f)
          (PointedCompactlyGenerated.toBasedSpaceMap g))
        (PointedCompactlyGenerated.toBasedSpaceMap k) h) =
    underBasedMapSpaceMap (PointedCompactlyGenerated.toBasedSpaceMap f)
      (underBasedMapSpaceObjectMap
        (PointedCompactlyGenerated.toBasedSpaceMap g)
        (PointedCompactlyGenerated.toBasedSpaceMap k))
      (smashProductMappingAdjunctionHomeomorph X Y Z h) := by
  apply Subtype.ext
  ext x
  apply Subtype.ext
  ext y
  change
    (PointedCompactlyGenerated.Hom.hom k)
        (h.1
          ((smashProductMap (PointedCompactlyGenerated.toBasedSpaceMap f)
              (PointedCompactlyGenerated.toBasedSpaceMap g)).right.hom
            (smashProductMk X'.toBasedSpace Y'.toBasedSpace (x, y)))) =
      (PointedCompactlyGenerated.Hom.hom k)
        (((smashProductMappingAdjunctionHomeomorph X Y Z h).1
          ((PointedCompactlyGenerated.Hom.hom f) x)).1
          ((PointedCompactlyGenerated.Hom.hom g) y))
  rw [smashProductMap_apply_mk, smashProductMappingAdjunctionHomeomorph_apply]
  change
    (ConcreteCategory.hom k.right)
        (h.1
          (smashProductMk X.toBasedSpace Y.toBasedSpace
            ((f.right.hom) x, (g.right.hom) y))) =
      (ConcreteCategory.hom k.right)
        (h.1
          (smashProductMk X.toBasedSpace Y.toBasedSpace
            ((f.right.hom) x, (g.right.hom) y)))
  rfl

/-- Naturality of `smashProductMappingAdjunctionHomeomorph` in the `X`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_natural_X
    {X X' Y Z : PointedCompactlyGenerated.{u, w}}
    (f : X' ⟶ X) (h : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace) :
    smashProductMappingAdjunctionHomeomorph X' Y Z
      (underBasedMapSpaceMap
        (smashProductMap (PointedCompactlyGenerated.toBasedSpaceMap f)
          (𝟙 Y.toBasedSpace))
        (𝟙 Z.toBasedSpace) h) =
    underBasedMapSpaceMap (PointedCompactlyGenerated.toBasedSpaceMap f)
      (𝟙 (underBasedMapSpaceObject Y.toBasedSpace Z.toBasedSpace))
      (smashProductMappingAdjunctionHomeomorph X Y Z h) := by
  simpa using
    smashProductMappingAdjunctionHomeomorph_natural f (𝟙 Y) (𝟙 Z) h

/-- Naturality of `smashProductMappingAdjunctionHomeomorph` in the `Y`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_natural_Y
    {X Y Y' Z : PointedCompactlyGenerated.{u, w}}
    (g : Y' ⟶ Y) (h : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace) :
    smashProductMappingAdjunctionHomeomorph X Y' Z
      (underBasedMapSpaceMap
        (smashProductMap (𝟙 X.toBasedSpace) (PointedCompactlyGenerated.toBasedSpaceMap g))
        (𝟙 Z.toBasedSpace) h) =
    underBasedMapSpaceMap (𝟙 X.toBasedSpace)
      (underBasedMapSpaceObjectMap
        (PointedCompactlyGenerated.toBasedSpaceMap g) (𝟙 Z.toBasedSpace))
      (smashProductMappingAdjunctionHomeomorph X Y Z h) := by
  simpa using
    smashProductMappingAdjunctionHomeomorph_natural (𝟙 X) g (𝟙 Z) h

/-- Naturality of `smashProductMappingAdjunctionHomeomorph` in the `Z`-variable. -/
theorem smashProductMappingAdjunctionHomeomorph_natural_Z
    {X Y Z Z' : PointedCompactlyGenerated.{u, w}}
    (k : Z ⟶ Z')
    (h : underBasedMapSpace (X.toBasedSpace ∧ Y.toBasedSpace) Z.toBasedSpace) :
    smashProductMappingAdjunctionHomeomorph X Y Z'
      (underBasedMapSpaceMap
        (smashProductMap (𝟙 X.toBasedSpace) (𝟙 Y.toBasedSpace))
        (PointedCompactlyGenerated.toBasedSpaceMap k) h) =
    underBasedMapSpaceMap (𝟙 X.toBasedSpace)
      (underBasedMapSpaceObjectMap
        (𝟙 Y.toBasedSpace) (PointedCompactlyGenerated.toBasedSpaceMap k))
      (smashProductMappingAdjunctionHomeomorph X Y Z h) := by
  simpa using
    smashProductMappingAdjunctionHomeomorph_natural (𝟙 X) (𝟙 Y) k h
