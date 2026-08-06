import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory
open scoped FundamentalGroupoid

noncomputable section

variable {X : Type u} [TopologicalSpace X]

private noncomputable def basepointPathIso (x y : X) [PathConnectedSpace X] :
    FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
  letI : DecidableEq X := Classical.decEq X
  if h : y = x then
    eqToIso (congrArg FundamentalGroupoid.mk h.symm)
  else
    (Groupoid.isoEquivHom _ _).symm
      (FundamentalGroupoid.fromPath ⟦PathConnectedSpace.somePath x y⟧)

private theorem basepointPathIso_self (x : X) [PathConnectedSpace X] :
    basepointPathIso x x = Iso.refl (FundamentalGroupoid.mk x) := by
  -- The special case in `basepointPathIso` forces the self-isomorphism to be reflexive.
  simp [basepointPathIso]

/-- The inclusion of `π₁(X, x)` viewed as a one-object category into the fundamental groupoid
`Π(X)`. -/
noncomputable def fundamentalGroupInclusionFunctor (x : X) :
    SingleObj (FundamentalGroup X x) ⥤ FundamentalGroupoid X :=
  SingleObj.functor (MonoidHom.id (FundamentalGroup X x))

private def fundamentalGroupoidToSingleObj (x : X) [PathConnectedSpace X] :
    FundamentalGroupoid X ⥤ SingleObj (FundamentalGroup X x) where
  obj _ := SingleObj.star (FundamentalGroup X x)
  map {y z} f :=
    FundamentalGroup.fromArrow
      ((basepointPathIso x y.as).hom ≫ f ≫ (basepointPathIso x z.as).inv)
  map_id y := by
    -- The chosen isomorphism cancels its inverse on identity morphisms.
    change ((basepointPathIso x y.as).hom ≫ 𝟙 y ≫ (basepointPathIso x y.as).inv :
        FundamentalGroup X x) = 𝟙 _
    simp
  map_comp {X} {Y} {Z} f g := by
    -- Insert the middle identity through the chosen basepoint isomorphism and reassociate.
    change ((basepointPathIso x X.as).hom ≫ (f ≫ g) ≫ (basepointPathIso x Z.as).inv :
        FundamentalGroup _ x) =
      (((basepointPathIso x X.as).hom ≫
            f ≫
            (basepointPathIso x Y.as).inv : FundamentalGroup _ x) ≫
        ((basepointPathIso x Y.as).hom ≫
            g ≫
            (basepointPathIso x Z.as).inv : FundamentalGroup _ x))
    calc
      (basepointPathIso x X.as).hom ≫ (f ≫ g) ≫ (basepointPathIso x Z.as).inv
          = (basepointPathIso x X.as).hom ≫ f ≫
              ((basepointPathIso x Y.as).inv ≫ (basepointPathIso x Y.as).hom) ≫ g ≫
                (basepointPathIso x Z.as).inv := by
                simp [Category.assoc]
      _ = (((basepointPathIso x X.as).hom ≫
              f ≫
              (basepointPathIso x Y.as).inv : FundamentalGroup _ x) ≫
            ((basepointPathIso x Y.as).hom ≫
                g ≫
                (basepointPathIso x Z.as).inv : FundamentalGroup _ x)) := by
            simp [Category.assoc]

private def fundamentalGroupInclusionCounitIso (x : X) [PathConnectedSpace X] :
    fundamentalGroupoidToSingleObj x ⋙
        fundamentalGroupInclusionFunctor x ≅
      𝟭 (FundamentalGroupoid X) := by
  refine NatIso.ofComponents (fun y ↦ basepointPathIso x y.as) ?_
  intro y z f
  -- Naturality is exactly cancellation of the chosen isomorphism at the target object.
  change
    (((basepointPathIso x y.as).hom ≫
          f ≫
          (basepointPathIso x z.as).inv : FundamentalGroup X x) ≫
        (basepointPathIso x z.as).hom) =
      (basepointPathIso x y.as).hom ≫ f
  simp [Category.assoc]

private def fundamentalGroupInclusionUnitIso (x : X) [PathConnectedSpace X] :
    𝟭 (SingleObj (FundamentalGroup X x)) ≅
      fundamentalGroupInclusionFunctor x ⋙
        fundamentalGroupoidToSingleObj x := by
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro _ _ a
  -- Route correction: forcing the chosen self-isomorphism to be `Iso.refl` removes all conjugation.
  change a ≫ 𝟙 _ = 𝟙 _ ≫
      FundamentalGroup.fromArrow
        ((basepointPathIso x x).hom ≫ (MonoidHom.id (FundamentalGroup X x)) a ≫
          (basepointPathIso x x).inv)
  simp [basepointPathIso_self]

private theorem fundamentalGroupInclusionCounitIso_app_basepoint
    (x : X) [PathConnectedSpace X] :
    (fundamentalGroupInclusionCounitIso x).hom.app (FundamentalGroupoid.mk x) = 𝟙 _ := by
  simp [fundamentalGroupInclusionCounitIso, fundamentalGroupInclusionFunctor,
    basepointPathIso_self]

/-- The canonical equivalence between the one-object category on `π₁(X, x)` and the fundamental
groupoid `Π(X)` of a path-connected space. -/
noncomputable def fundamentalGroupInclusionEquivalence (x : X) [PathConnectedSpace X] :
    SingleObj (FundamentalGroup X x) ≌ FundamentalGroupoid X where
  functor := fundamentalGroupInclusionFunctor x
  inverse := fundamentalGroupoidToSingleObj x
  unitIso := fundamentalGroupInclusionUnitIso x
  counitIso := fundamentalGroupInclusionCounitIso x
  functor_unitIso_comp X' := by
    cases X'
    change 𝟙 (FundamentalGroupoid.mk x) ≫
        (fundamentalGroupInclusionCounitIso x).hom.app (FundamentalGroupoid.mk x) =
      𝟙 (FundamentalGroupoid.mk x)
    simp [fundamentalGroupInclusionCounitIso_app_basepoint, fundamentalGroupInclusionFunctor]

instance fundamentalGroupInclusionFunctorIsEquivalence (x : X) [PathConnectedSpace X] :
    Functor.IsEquivalence (fundamentalGroupInclusionFunctor x) := by
  -- The source proof identifies `π₁(X,x)` with a one-object skeleton of `Π(X)`.
  let e := fundamentalGroupInclusionEquivalence x
  exact e.isEquivalence_functor

/-- Proposition 2.5.7: if `X` is path connected, then for each basepoint `x`, the inclusion of
`π₁(X,x)` viewed as a one-object category into the fundamental groupoid `Π(X)` is an equivalence
of categories. -/
-- Proof sketch: regard `π₁(X,x)` as the full subgroupoid of `Π(X)` on the object `x`;
-- a path from
-- `x` to any point yields an isomorphism in `Π(X)`, so
-- path connectedness makes this inclusion
-- essentially surjective, and fullness and faithfulness are built into the one-object inclusion.
theorem fundamental_group_inclusion_is_equivalence (x : X) [PathConnectedSpace X] :
    Functor.IsEquivalence (fundamentalGroupInclusionFunctor x) :=
  inferInstance
