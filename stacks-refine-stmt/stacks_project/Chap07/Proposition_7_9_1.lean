import Mathlib
import stacks_project.Chap07.GSetForgetfulPoint

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory

section

variable (G : Type u) [Group G]

/- Domain-style sampling for Proposition 7.9.1:
- primary domain: sheaves on the jointly surjective site of `G`-sets and their recovery from the
  left regular `G`-set;
- sampled owner API:
  `Action.jointlySurjectiveTopology`,
  `GrothendieckTopology.yonedaEquiv`,
  `Action.ofMulAction`,
  `Functor.IsEquivalence`,
  `Functor.inv`,
  `Functor.asEquivalence`;
- primitive data: the source-facing functor `sheafSectionsOnLeftRegularFunctor`;
- derived API: the owner-level equivalence statement for
  `(Action.jointlySurjectiveTopology G).yoneda` and the identification of its canonical inverse
  with `sheafSectionsOnLeftRegularFunctor`;
- source/core/bridge triage:
  `source-facing`: the left-regular-sections functor from sheaves to `G`-sets;
  `core/canonical`: the site Yoneda functor together with the owner predicate
    `Functor.IsEquivalence`;
  `bridge/view`: the induced `MulAction` on `ℱ({}_G G)`, from which the bundled `Action` object is
    derived.

The public owner in this file remains `sheafSectionsOnLeftRegularFunctor`, while Proposition 7.9.1
itself is organized around the canonical owner `Functor.IsEquivalence` for the site Yoneda functor.
-/

/-- The jointly surjective topology `\mathcal T_G` on `G`-sets is subcanonical. -/
instance : (Action.jointlySurjectiveTopology G).Subcanonical := sorry

-- Proof sketch: pullback along the identity endomorphism is the identity map on sections. -/
/-- Pullback along right multiplication by `1` acts trivially on sections over the left regular
`G`-set. -/
private theorem sheafSectionsOnLeftRegular_map_one
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G 1)) =
      𝟙 (ℱ.obj.obj (op (Action.leftRegular G))) := by
  rw [gSetForgetfulPointLeftRegularRightMul_one]
  change ℱ.obj.map (𝟙 (op (Action.leftRegular G))) = 𝟙 (ℱ.obj.obj (op (Action.leftRegular G)))
  exact ℱ.obj.map_id (op (Action.leftRegular G))

-- Proof sketch: functoriality of the underlying presheaf identifies pullback along the composite
-- right multiplication map with the composite of the two pullback maps.
/-- Pullback along right multiplication turns multiplication in `G` into the induced left action on
sections over the left regular `G`-set. -/
private theorem sheafSectionsOnLeftRegular_map_mul
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) (g h : G) :
    ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G (g * h))) =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) ≫
        ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g)) := by
  rw [gSetForgetfulPointLeftRegularRightMul_mul]
  change
    ℱ.obj.map
        (op (gSetForgetfulPointLeftRegularRightMul G h) ≫
          op (gSetForgetfulPointLeftRegularRightMul G g)) =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) ≫
        ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
  exact
    ℱ.obj.map_comp
      (op (gSetForgetfulPointLeftRegularRightMul G h))
      (op (gSetForgetfulPointLeftRegularRightMul G g))

/-- The left action on sections over the left regular `G`-set induced by pullback along right
translations. -/
private instance sheafSectionsOnLeftRegularMulAction
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    MulAction G (ℱ.obj.obj (op (Action.leftRegular G))) where
  smul g := ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
  one_smul x := by
    change ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G 1)) x = x
    simpa using congrArg (fun f : End (ℱ.obj.obj (op (Action.leftRegular G))) ↦ f x)
      (sheafSectionsOnLeftRegular_map_one G ℱ)
  mul_smul g h x := by
    change ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G (g * h))) x =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
        (ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) x)
    simpa using congrArg (fun f : End (ℱ.obj.obj (op (Action.leftRegular G))) ↦ f x)
      (sheafSectionsOnLeftRegular_map_mul G ℱ g h)

/-- The equivariant map on left-regular sections induced by a sheaf morphism. -/
private def sheafSectionsOnLeftRegularMap
    {ℱ 𝒢 : Sheaf (Action.jointlySurjectiveTopology G) (Type v)} (η : ℱ ⟶ 𝒢) :
    Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ⟶
      Action.ofMulAction G (𝒢.obj.obj (op (Action.leftRegular G))) where
  hom := η.hom.app (op (Action.leftRegular G))
  comm g := by
    change
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g)) ≫
          η.hom.app (op (Action.leftRegular G)) =
        η.hom.app (op (Action.leftRegular G)) ≫
          𝒢.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
    exact η.hom.naturality (op (gSetForgetfulPointLeftRegularRightMul G g))

-- Proof sketch: evaluate the identity natural transformation at the left regular `G`-set. -/
/-- The left-regular sections construction sends identity morphisms of sheaves to identity
equivariant maps. -/
private theorem sheafSectionsOnLeftRegularFunctor_map_id
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    sheafSectionsOnLeftRegularMap G (𝟙 ℱ) =
      𝟙 (Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))) := by
  apply Action.hom_ext
  rfl

-- Proof sketch: evaluate the composite natural transformation at the left regular `G`-set and use
-- the functoriality of the sheaf morphism components.
/-- The left-regular sections construction preserves composition of sheaf morphisms. -/
private theorem sheafSectionsOnLeftRegularFunctor_map_comp
    {ℱ 𝒢 ℋ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    sheafSectionsOnLeftRegularMap G (η ≫ θ) =
      sheafSectionsOnLeftRegularMap G η ≫ sheafSectionsOnLeftRegularMap G θ := by
  apply Action.hom_ext
  rfl

/-- The functor sending a sheaf on the surjective site of `G`-sets to its `G`-set of sections on
the left regular object `{}_G G`. -/
def sheafSectionsOnLeftRegularFunctor :
    Sheaf (Action.jointlySurjectiveTopology G) (Type v) ⥤ Action (Type v) G where
  obj ℱ := Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))
  map := sheafSectionsOnLeftRegularMap G
  map_id := sheafSectionsOnLeftRegularFunctor_map_id G
  map_comp := fun η θ ↦ sheafSectionsOnLeftRegularFunctor_map_comp G η θ

-- Proof sketch: the surjective topology is subcanonical, so the functor `S ↦ Hom_G(-, S)` is the
-- canonical Yoneda functor `(Action.jointlySurjectiveTopology G).yoneda`. For any sheaf `ℱ`, the canonical map
-- `ℱ(U) → Hom_G(U, ℱ({}_G G))` sends a section to its translates along the maps `{}_G G → U`; the
-- orbit decompositions and Lemma 7.8.4 reduce bijectivity to the transitive case, where the sheaf
-- condition for the cover `{}_G G → U` identifies sections with stabilizer-invariant elements of
-- `ℱ({}_G G)`. This yields unit and counit isomorphisms exhibiting
-- `sheafSectionsOnLeftRegularFunctor G` as a quasi-inverse to `(Action.jointlySurjectiveTopology G).yoneda`.
/-- Proposition 7.9.1: the canonical Yoneda functor from `G`-sets to sheaves for the jointly
surjective topology on `G`-sets is an equivalence of categories, with inverse given by evaluation
on the left regular `G`-set `{}_G G`. -/
theorem jointlySurjectiveTopology_yoneda_isEquivalence :
    Functor.IsEquivalence
      ((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)) := by
  refine Functor.IsEquivalence.mk' (sheafSectionsOnLeftRegularFunctor G) ?_ ?_
  · sorry
  · sorry

attribute [instance] jointlySurjectiveTopology_yoneda_isEquivalence

/-- Companion bridge for Proposition 7.9.1: the canonical inverse functor attached to the
equivalence `(Action.jointlySurjectiveTopology G).yoneda` is the left-regular-sections functor. -/
theorem jointlySurjectiveTopology_yoneda_inv_eq_sheafSectionsOnLeftRegularFunctor :
    (((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)).inv) =
      sheafSectionsOnLeftRegularFunctor G := by
  sorry

end

end CategoryTheory
