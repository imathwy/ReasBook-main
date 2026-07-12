import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical separatedness owner
-- `AlgebraicGeometry.IsSeparated` and affine separatedness instances, but not this exact
-- affine-open section-ring criterion. The source-facing API below keeps the affine-pair
-- criterion around the canonical `IsSeparated` owner.

/-- The canonical ring map
`Γ(X, U) ⊗_ℤ Γ(X, V) → Γ(X, U ∩ V)` induced by restricting sections to the intersection. -/
def Scheme.sectionTensorToIntersection {X : Scheme.{u}} (U V : X.Opens) :
    TensorProduct ℤ (Γ(X, U) : Type u) (Γ(X, V) : Type u) →+*
      (Γ(X, U ⊓ V) : Type u) :=
  (Algebra.TensorProduct.productMap
    (CommRingCat.Hom.hom (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op)).toIntAlgHom
    (CommRingCat.Hom.hom
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op)).toIntAlgHom).toRingHom

variable {X S : Scheme.{u}}

/-- Helper predicate for affine neighborhoods over one affine open whose intersection has the
section-ring criterion used in Lemma 26.21.7. -/
structure Scheme.Hom.AffinePairInterSurjective
    (f : X ⟶ S) (x1 x2 : X) (U V : X.affineOpens) (W : S.affineOpens) : Prop where
  /-- The first point lies in the first affine open. -/
  mem_left : x1 ∈ (U : X.Opens)
  /-- The second point lies in the second affine open. -/
  mem_right : x2 ∈ (V : X.Opens)
  /-- The first affine open maps into the chosen affine open downstairs. -/
  le_left : (U : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens)
  /-- The second affine open maps into the chosen affine open downstairs. -/
  le_right : (V : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens)
  /-- The intersection is affine. -/
  inter_affine : IsAffineOpen ((U : X.Opens) ⊓ (V : X.Opens))
  /-- The canonical section-ring map to the intersection is surjective. -/
  section_surjective :
    Function.Surjective (Scheme.sectionTensorToIntersection (U : X.Opens) (V : X.Opens))

/-- Lemma 26.21.7 (1): if `f : X ⟶ S` is separated, then any two affine opens of `X` mapping
into a common affine open of `S` have affine intersection. -/
@[stacks 01KP]
theorem Scheme.Hom.isAffineOpen_inter_of_isSeparated
    (f : X ⟶ S) [IsSeparated f]
    (U V : X.affineOpens)
    (hcommon : ∃ W : S.affineOpens,
      (U : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens) ∧
        (V : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens)) :
    IsAffineOpen ((U : X.Opens) ⊓ (V : X.Opens)) := sorry

/-- Lemma 26.21.7 (2): under the same separatedness and common-affine-target hypotheses, the
canonical map
`Γ(X, U) ⊗_ℤ Γ(X, V) → Γ(X, U ∩ V)` is surjective. -/
@[stacks 01KP]
theorem Scheme.Hom.sectionTensorToIntersection_surjective_of_isSeparated
    (f : X ⟶ S) [IsSeparated f]
    (U V : X.affineOpens)
    (hcommon : ∃ W : S.affineOpens,
      (U : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens) ∧
        (V : X.Opens) ≤ (TopologicalSpace.Opens.map f.base).obj (W : S.Opens)) :
    Function.Surjective (Scheme.sectionTensorToIntersection (U : X.Opens) (V : X.Opens)) := sorry

/-- Lemma 26.21.7 (3): conversely, if any two points of `X` lying over a common point of `S`
admit affine neighborhoods mapping into a common affine open of `S`, with affine intersection and
surjective tensor-to-intersection section map, then `f` is separated. -/
@[stacks 01KP]
theorem Scheme.Hom.isSeparated_of_exists_affine_pair_inter_affine_and_surjective
    (f : X ⟶ S)
    (h : ∀ (x1 x2 : X) (s : S), f.base x1 = s → f.base x2 = s →
      ∃ (U V : X.affineOpens) (W : S.affineOpens),
        Scheme.Hom.AffinePairInterSurjective f x1 x2 U V W) :
    IsSeparated f := sorry

end AlgebraicGeometry
