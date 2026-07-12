import Mathlib
import StacksProject_2024.Chap06.Lemma_6_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped TopCat

universe u_1

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the ambient big-Zariski owner
-- `Scheme.zariskiTopology`. The source-faithful local owner here is a structure over `Over S`, with
-- inverse image on the small sheaf side expressed by `TopCat.Sheaf.pullback` and its composition
-- constraint compared by `TopCat.Sheaf.pullbackComp`.

/-- Lemma 34.3.20: source-facing structure for a sheaf on `(\mathit{Sch}/S)_{Zar}`. It assigns to each
object `T/S` a sheaf on the underlying topological space of `T`, together with inverse-image maps
for morphisms over `S`, compatible with composition and isomorphic for open immersions. -/
@[stacks 0213]
structure BigZariskiSheaf (S : Scheme.{u_1}) where
  /-- The sheaf attached to an object `T/S` of the big Zariski site. -/
  obj : ∀ T : Over S, TopCat.Sheaf (Type u_1) T.left.toTopCat
  /-- The inverse-image morphism attached to a morphism in the slice category `Over S`. -/
  pullbackMap : ∀ {T' T : Over S} (f : T' ⟶ T),
    (TopCat.Sheaf.pullback (Type u_1) f.left.base).obj (obj T) ⟶ obj T'
  /-- The pullback maps are compatible with composition after the canonical inverse-image
  comparison. -/
  comp : ∀ {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T),
    (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app
        (obj T) ≫
        pullbackMap (g ≫ f) =
      (TopCat.Sheaf.pullback (Type u_1) g.left.base).map (pullbackMap f) ≫
        pullbackMap g
  /-- The pullback map along an open immersion is an isomorphism. -/
  isIso_of_isOpenImmersion : ∀ {T' T : Over S} (f : T' ⟶ T) [IsOpenImmersion f.left],
    IsIso (pullbackMap f)

namespace BigZariskiSheaf

variable {S : Scheme.{u_1}}

/-- A big Zariski sheaf can be evaluated on an object `T/S` to recover the corresponding
sheaf on `T`. -/
instance instCoeFun :
    CoeFun (BigZariskiSheaf S)
      (fun _ ↦ ∀ T : Over S, TopCat.Sheaf (Type u_1) T.left.toTopCat) where
  coe 𝒜 := 𝒜.obj

variable (𝒜 : BigZariskiSheaf S)

/-- The pullback maps in a big Zariski sheaf satisfy the stated composition law. -/
theorem pullbackMap_comp {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T) :
    (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app
        (𝒜.obj T) ≫
        𝒜.pullbackMap (g ≫ f) =
      (TopCat.Sheaf.pullback (Type u_1) g.left.base).map (𝒜.pullbackMap f) ≫
        𝒜.pullbackMap g := sorry

/-- The pullback map of a big Zariski sheaf is an isomorphism along an open immersion. -/
theorem isIso_pullbackMap {T' T : Over S} (f : T' ⟶ T) [IsOpenImmersion f.left] :
    IsIso (𝒜.pullbackMap f) := sorry

/-- The source-facing compatibility package for the inverse-image maps of a big Zariski sheaf:
composition is respected through the canonical pullback comparison, and open immersions give
isomorphisms. -/
@[stacks 0213]
theorem pullbackMap_comp_spec :
    let comp := @BigZariskiSheaf.comp S 𝒜
    let isIso_of_isOpenImmersion := @BigZariskiSheaf.isIso_of_isOpenImmersion S 𝒜
    (∀ {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T),
        (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app
            (𝒜.obj T) ≫
            𝒜.pullbackMap (g ≫ f) =
          (TopCat.Sheaf.pullback (Type u_1) g.left.base).map (𝒜.pullbackMap f) ≫
            𝒜.pullbackMap g) ∧
      (∀ {T' T : Over S} (f : T' ⟶ T) [IsOpenImmersion f.left],
        IsIso (𝒜.pullbackMap f)) := sorry

end BigZariskiSheaf
end AlgebraicGeometry.Scheme
