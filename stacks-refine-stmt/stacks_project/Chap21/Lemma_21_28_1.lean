import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F : D ⥤ C) (G : C ⥤ D) (adj : F ⊣ G)

/-- The object property on the target category consisting of those objects for which the adjunction
unit `K ⟶ GF(K)` is an isomorphism. -/
abbrev unitIsomorphismProperty : ObjectProperty D :=
  fun K ↦ IsIso (adj.unit.app K)

-- Proof sketch: unfold `unitIsomorphismProperty`; membership is by definition that the chosen
-- adjunction unit `K ⟶ GF(K)` is an isomorphism.
/-- Membership in `unitIsomorphismProperty` means exactly that the adjunction unit
`K ⟶ GF(K)` is an isomorphism. -/
theorem mem_unitIsomorphismProperty_iff (K : D) :
    unitIsomorphismProperty F G adj K ↔ IsIso (adj.unit.app K) := sorry

/-- The full subcategory cut out by the unit-isomorphism condition `K ⟶ GF(K)`. -/
abbrev unitIsomorphismSubcategory :=
  (unitIsomorphismProperty F G adj).FullSubcategory

/-- The restriction of the left adjoint to the full subcategory on which the adjunction unit is an
isomorphism. -/
abbrev restrictedLeftAdjoint :
    unitIsomorphismSubcategory F G adj ⥤ C :=
  (unitIsomorphismProperty F G adj).ι ⋙ F

-- Proof sketch: the Stacks notion of “saturated” is retract-closure. If `K` is a retract of `L`
-- and the unit for `L` is an isomorphism, naturality of the adjunction unit shows that the unit
-- for `K` is a retract of an isomorphism, hence an isomorphism.
/-- Lemma 21.28.1 (1): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism form a saturated
subcategory, i.e. an object property stable under retracts. -/
theorem unitIsomorphismProperty_isStableUnderRetracts :
    (unitIsomorphismProperty F G adj).IsStableUnderRetracts := sorry

-- Proof sketch: for objects `K` and `L` in the unit-isomorphism subcategory, the adjunction gives
-- `Hom(FK, FL) ≃ Hom(K, GFL)`. Since the unit `L ⟶ GFL` is an isomorphism, composition with it
-- identifies the right-hand side with `Hom(K, L)`, giving bijectivity on homs.
/-- Lemma 21.28.1 (3): in the abstract adjunction `F ⊣ G` underlying the ringed-topos situation,
the restriction of the left adjoint to the full subcategory of objects satisfying
`K ⟶ GF(K)` is fully faithful. -/
theorem restrictedLeftAdjoint_bijective_on_homs
    (K L : unitIsomorphismSubcategory F G adj) :
    Function.Bijective
      ((restrictedLeftAdjoint F G adj).map :
        (K ⟶ L) → (F.obj K.obj ⟶ F.obj L.obj)) := sorry

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor C n)]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
variable [Pretriangulated C] [Pretriangulated D]
variable (F : D ⥤ C) (G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
variable (adj : F ⊣ G) [adj.IsTriangulated]

-- Proof sketch: `F` and `G` are exact functors of triangulated categories, so the unit natural
-- transformation is compatible with distinguished triangles and shifts. Applying the
-- two-out-of-three formalism to the unit maps shows that the unit-isomorphism condition is
-- triangulated; the associated full subcategory is therefore strictly full.
/-- Lemma 21.28.1 (2): in the abstract triangulated adjunction `F ⊣ G` underlying the
ringed-topos situation, the objects `K` for which the unit map `K ⟶ GF(K)` is an isomorphism
form a triangulated strictly full subcategory of the target category. -/
theorem unitIsomorphismProperty_isTriangulated :
    (unitIsomorphismProperty F G adj).IsTriangulated := sorry

end

end CategoryTheory
