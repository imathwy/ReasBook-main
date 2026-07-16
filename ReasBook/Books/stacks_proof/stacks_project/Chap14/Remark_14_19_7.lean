import stacks_proof.stacks_project.Chap14.Lemma_14_19_2
import stacks_proof.stacks_project.Chap14.Lemma_14_19_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 14.19.7:
- primary domain: truncated simplicial objects and the matching-family cone functor for the next
  degree;
- sampled owner-side declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `matchingFamilyFunctor`,
  `Functor.cones`,
  `StructuredArrow.mk`,
  `StructuredArrow.w`;
- best owner abstraction: the chapter owner for matching data is `matchingFamilyFunctor U`, whose
  points are cones on the structured-arrow matching diagram. This remark is a `bridge/view`: it
  gives the degeneracy family inside that owner and records that the face maps are the coordinate
  projections coming from the objects indexed by the cofaces `δ_i`;
- primitive data: an `n`-truncated simplicial object `U`, an object `T`, a morphism
  `f : T ⟶ U _⦋n⦌ₙ`, and a degeneracy index `j : Fin (n + 1)`;
- derived API: the canonical matching-family point determined by `f`, its coordinate projections,
  and in degree `0` the identification of those two coordinates with `(f, f)`.

Source/core/bridge triage:
- `source-facing`: the explicit tuple of maps obtained from the simplicial identities;
- `core/canonical`: `matchingFamilyFunctor U`;
- `bridge/view`: the remark identifies the source tuple with the owner-side matching-family point
  and exposes its coordinates through the face objects. -/

/-- The structured-arrow object corresponding to the `i`-th coface `δ_i : [n] ⟶ [n + 1]`. -/
abbrev matchingFaceObject {n : ℕ} (i : Fin (n + 2)) :
    matchingIndex n :=
  StructuredArrow.mk
    (show op ⦋n + 1⦌ ⟶
        (SimplexCategory.Truncated.inclusion n).op.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) from
      (SimplexCategory.δ i).op)

/-- The truncated simplex underlying a matching-diagram index object. -/
private abbrev matchingIndexSimplex {n : ℕ} (A : matchingIndex n) :
    SimplexCategory.Truncated n :=
  A.right.unop

/-- The simplex map underlying a morphism in the matching-diagram index category. -/
private abbrev matchingIndexRightHom {n : ℕ} {A B : matchingIndex n} (g : A ⟶ B) :
    matchingIndexSimplex B ⟶ matchingIndexSimplex A :=
  g.right.unop

/-- For an index object `α : [k] ⟶ [n + 1]` in the matching diagram, composing `α` with `σ_j`
gives the induced map `[k] ⟶ [n]`. -/
private abbrev matchingDegeneracyMap {n : ℕ} (j : Fin (n + 1))
    (A : matchingIndex n) :
    matchingIndexSimplex A ⟶ (⦋n⦌ₙ : SimplexCategory.Truncated n) :=
  Hom.tr (A.hom.unop ≫ SimplexCategory.σ j) (matchingIndexSimplex A).property (by simp)

private theorem matchingDegeneracyMap_naturality {n : ℕ} (j : Fin (n + 1))
    {A B : matchingIndex n} (g : A ⟶ B) :
    matchingIndexRightHom g ≫ matchingDegeneracyMap j A = matchingDegeneracyMap j B := by
  change Hom.tr ((matchingIndexRightHom g).hom ≫ A.hom.unop ≫ SimplexCategory.σ j) _ _ =
    Hom.tr (B.hom.unop ≫ SimplexCategory.σ j) _ _
  exact congrArg
    (fun k ↦ Hom.tr (k ≫ SimplexCategory.σ j) (matchingIndexSimplex B).property (by simp))
    (congrArg Quiver.Hom.unop (StructuredArrow.w g))

/-- Remark 14.19.7: the `j`-th degeneracy map on `T`-valued points of the matching-family model
for the degree-`n + 1` term is the canonical point of `matchingFamilyFunctor U` whose component at
an index object `α : [k] ⟶ [n + 1]` is obtained by precomposing `f` with `α ≫ σ_j`. -/
@[stacks 0188]
def matchingDegeneracyFamily {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (j : Fin (n + 1)) (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (matchingFamilyFunctor U).obj (op T) where
  app A := f ≫ U.map (matchingDegeneracyMap j A).op
  naturality := by
    intro A B g
    let h :=
      congrArg (fun k ↦ f ≫ U.map k)
        (congrArg Quiver.Hom.op (matchingDegeneracyMap_naturality j g))
    simpa [Functor.comp_map, Functor.const_obj_map, Category.assoc] using
      h.symm

/-- The `i`-th coordinate of the degeneracy family is the textbook map
`f ≫ U(δ_i ≫ σ_j)`. -/
theorem matchingDegeneracyFamily_app_matchingFaceObject {n : ℕ}
    (U : SimplicialObject.Truncated C n)
    {T : C} (i : Fin (n + 2)) (j : Fin (n + 1))
    (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (matchingDegeneracyFamily U j f).app (matchingFaceObject i) =
      f ≫ U.map (Hom.tr (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op := by
  simp [matchingDegeneracyFamily, matchingDegeneracyMap, matchingFaceObject, matchingIndexSimplex]

-- Proof sketch: when `n = 0` there is only one degeneracy index `j = 0`, and both composites
-- `δ_0 ≫ σ_0` and `δ_1 ≫ σ_0` are identities by the two parts of the third simplicial identity.
/-- In degree `0`, the two face projections of the explicit degeneracy family are both `f`. -/
theorem matchingDegeneracyFamily_zero (U : SimplicialObject.Truncated C 0) {T : C}
    (f : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (fun i : Fin 2 ↦ (matchingDegeneracyFamily U 0 f).app (matchingFaceObject i)) =
      fun _ : Fin 2 ↦ f := by
  funext i
  fin_cases i
  · rw [matchingDegeneracyFamily_app_matchingFaceObject]
    have hδ :
        (Hom.tr (SimplexCategory.δ 0 ≫ SimplexCategory.σ 0) :
          (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀) =
          𝟙 (⦋0⦌₀ : SimplexCategory.Truncated 0) := by
      simpa using congrArg
        (fun k ↦ (Hom.tr k : (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀))
        (show SimplexCategory.δ (Fin.castSucc 0) ≫ SimplexCategory.σ 0 = 𝟙 ⦋0⦌ from
          SimplexCategory.δ_comp_σ_self)
    simpa [hδ]
  · rw [matchingDegeneracyFamily_app_matchingFaceObject]
    have hδ :
        (Hom.tr (SimplexCategory.δ 1 ≫ SimplexCategory.σ 0) :
          (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀) =
          𝟙 (⦋0⦌₀ : SimplexCategory.Truncated 0) := by
      simpa using congrArg
        (fun k ↦ (Hom.tr k : (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀))
        (show SimplexCategory.δ (0 : Fin 1).succ ≫ SimplexCategory.σ 0 = 𝟙 ⦋0⦌ from
          SimplexCategory.δ_comp_σ_succ)
    simpa [hδ]

end CategoryTheory
