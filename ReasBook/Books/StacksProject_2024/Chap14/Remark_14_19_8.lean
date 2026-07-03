import StacksProject_2024.Chap14.Remark_14_19_7
import StacksProject_2024.Chap14.Remark_14_19_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open SimplexCategory
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe u

namespace CategoryTheory

/- Domain-style sampling for Remark 14.19.8:
- primary domain: one-step extensions of truncated simplicial sets, their matching objects, and
  representable presheaves on `Type`;
- sampled owner API:
  `SimplicialObject.Truncated.tilde`,
  `SimplicialObject.Truncated.tildeHomEquiv`,
  `matchingFamilyFunctor`,
  `Functor.RepresentableBy`,
  `Functor.RepresentableBy.uniqueUpToIso`,
  `Functor.ranObjObjIsoLimit`,
  `SimplexCategory.eq_comp_δ_of_not_surjective`;
- best owner abstraction: the canonical one-step extension `SimplicialObject.Truncated.tilde U`,
  whose universal property is `SimplicialObject.Truncated.tildeHomEquiv`; the explicit matching
  faces are only a source-facing top-degree model for the matching object represented by that
  extension;
- primitive data: the truncated simplicial set `U`, together with its explicit top-degree matching
  simplices;
- derived API: the inverse-to-restriction map into `tilde U`, and the explicit representability of
  the matching-family functor by the matching-face type.

Source/core/bridge triage:
- `source-facing`: the canonical `(n + 1)`-truncated simplicial set `\tilde U` and the inverse to
  restriction into it;
- `core/canonical`: `SimplicialObject.Truncated.tilde U` with
  `SimplicialObject.Truncated.tildeHomEquiv`;
- `bridge/view`: the explicit pair/subtype `simplicialMatchingFaces U`, which identifies the
  top-degree matching object represented by `\tilde U` through `matchingFamilyFunctor U`. -/

/-- The top simplex in `Δ≤n`. -/
private abbrev simplicialMatchingTopSimplex (n : ℕ) : SimplexCategory.Truncated n :=
  ⦋n⦌ₙ

/-- The predecessor simplex `[n]` regarded as an object of `Δ≤(n + 1)`. -/
private abbrev simplicialMatchingPredSimplex (n : ℕ) : SimplexCategory.Truncated (n + 1) :=
  ⟨SimplexCategory.mk n, Nat.le_succ n⟩

/-- The face map `d_i^(n + 1) : U_{n + 1} ⟶ U_n` written as a morphism in the truncated simplex
category. -/
private def simplicialMatchingFaceMap (n : ℕ) (i : Fin (n + 2)) :
    simplicialMatchingPredSimplex n ⟶ simplicialMatchingTopSimplex (n + 1) :=
  Hom.tr (SimplexCategory.δ i)

-- Proof sketch: if `i < j < n + 2`, then `i < n + 1`, so `i` determines a valid face index
-- `d_i^n`.
/-- The left-hand face index occurring in the matching-family relation. -/
private theorem simplicialMatchingLeftFaceIndex_isLt {n : ℕ} {i j : Fin (n + 2)}
    (hij : i < j) : i.1 < n + 1 := sorry

/-- The face index `i` in the relation `d_{j-1}^n(f_i) = d_i^n(f_j)`. -/
private def simplicialMatchingLeftFaceIndex {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) :
    Fin (n + 1) :=
  ⟨i.1, simplicialMatchingLeftFaceIndex_isLt hij⟩

-- Proof sketch: if `i < j < n + 2`, then `j` is positive and `j - 1 < n + 1`, so `j - 1`
-- determines the face index `d_{j-1}^n`.
/-- The right-hand face index occurring in the matching-family relation. -/
private theorem simplicialMatchingRightFaceIndex_isLt {n : ℕ} {i j : Fin (n + 2)}
    (hij : i < j) : j.1 - 1 < n + 1 := sorry

/-- The face index `j - 1` in the relation `d_{j-1}^n(f_i) = d_i^n(f_j)`. -/
private def simplicialMatchingRightFaceIndex {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) :
    Fin (n + 1) :=
  ⟨j.1 - 1, simplicialMatchingRightFaceIndex_isLt hij⟩

/-- The explicit matching-face object of Remark 14.19.8: for `n = 0` it is the pair of
`0`-simplices, while for `n + 1` it is the subtype of compatible `(n + 3)`-tuples of
`(n + 1)`-simplices. -/
def simplicialMatchingFaces {n : ℕ} (U : SSet.Truncated n) : Type u :=
  match n with
  | 0 =>
      Fin 2 → U.obj (op (simplicialMatchingTopSimplex 0))
  | m + 1 =>
      { f : Fin (m + 3) → U.obj (op (simplicialMatchingTopSimplex (m + 1))) //
          ∀ {i j : Fin (m + 3)}, (hij : i < j) →
            U.map (simplicialMatchingFaceMap m (simplicialMatchingRightFaceIndex hij)).op (f i) =
              U.map
                (simplicialMatchingFaceMap m (simplicialMatchingLeftFaceIndex hij)).op
                (f j) }

private def simplicialMatchingFaceValues {n : ℕ} (U : SSet.Truncated n)
    (f : simplicialMatchingFaces U) :
    Fin (n + 2) → U.obj (op (simplicialMatchingTopSimplex n)) := by
  match n with
  | 0 =>
      exact f
  | _ + 1 =>
      exact f.1

private abbrev matchingIndexSimplex {n : ℕ} (A : matchingIndex n) :
    SimplexCategory.Truncated n :=
  A.right.unop

private abbrev matchingIndexHom {n : ℕ} (A : matchingIndex n) :=
  A.hom.unop

private structure SimplicialMatchingFaceFactorization {n : ℕ} (A : matchingIndex n) where
  face : Fin (n + 2)
  map : (matchingIndexSimplex A).obj ⟶ ⦋n⦌
  fac : matchingIndexHom A = map ≫ SimplexCategory.δ face

private theorem matchingIndex_not_surjective {n : ℕ} (A : matchingIndex n) :
    ¬ Function.Surjective (matchingIndexHom A).toOrderHom := by
  intro hsurj
  have hle : n + 1 ≤ (matchingIndexSimplex A).obj.len := by
    letI : Epi (matchingIndexHom A) := (SimplexCategory.epi_iff_surjective).2 hsurj
    simpa using (SimplexCategory.len_le_of_epi (matchingIndexHom A))
  exact Nat.not_succ_le_self n (hle.trans (matchingIndexSimplex A).property)

private noncomputable def simplicialMatchingFaceFactorization {n : ℕ} (A : matchingIndex n) :
    SimplicialMatchingFaceFactorization A := by
  classical
  let h := SimplexCategory.eq_comp_δ_of_not_surjective (matchingIndexHom A)
    (matchingIndex_not_surjective A)
  let face := Classical.choose h
  let hmap := Classical.choose_spec h
  let map := Classical.choose hmap
  let fac := Classical.choose_spec hmap
  exact ⟨face, map, fac⟩

private abbrev simplicialMatchingChosenFace {n : ℕ} (A : matchingIndex n) : Fin (n + 2) :=
  (simplicialMatchingFaceFactorization A).face

private def simplicialMatchingChosenMap {n : ℕ} (A : matchingIndex n) :
    matchingIndexSimplex A ⟶ ⦋n⦌ₙ :=
  Hom.tr (simplicialMatchingFaceFactorization A).map (matchingIndexSimplex A).property (by simp)

private def simplicialMatchingHomToMatchingFamily
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (T ⟶ simplicialMatchingFaces U) → (matchingFamilyFunctor U).obj (op T) :=
  fun g ↦
      { app := fun A t ↦
          U.map (simplicialMatchingChosenMap A).op
            (simplicialMatchingFaceValues U (g t) (simplicialMatchingChosenFace A))
        naturality := by
          intro A B f
          ext t
          sorry }

private def simplicialMatchingMatchingFamilyToHom
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (matchingFamilyFunctor U).obj (op T) → (T ⟶ simplicialMatchingFaces U) :=
  match n with
  | 0 =>
      fun x ↦ fun t ↦ fun i ↦ x.app (CategoryTheory.matchingFaceObject i) t
  | _ + 1 =>
      fun x ↦
        fun t ↦
          ⟨fun i ↦ x.app (CategoryTheory.matchingFaceObject i) t, fun hij ↦ by sorry⟩

/- Remark 14.19.8: the explicit pair/subtype `simplicialMatchingFaces U` is a source-facing model
for the canonical matching object of `U`; its universal property is the owner-side Hom
equivalence for `matchingFamilyFunctor U`. -/
noncomputable def simplicialMatchingFaces_homEquiv
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (T ⟶ simplicialMatchingFaces U) ≃ (matchingFamilyFunctor U).obj (op T) where
  toFun := simplicialMatchingHomToMatchingFamily U T
  invFun := simplicialMatchingMatchingFamilyToHom U T
  left_inv := by
    intro g
    sorry
  right_inv := by
    intro x
    sorry

-- Proof sketch: the explicit tuple model is the source-facing presentation of the canonical
-- matching-family cone functor `matchingFamilyFunctor U`; the representability datum is obtained
-- from the universal Hom-equivalence above.
/-- The explicit matching-face object represents the canonical matching-family functor of `U`. -/
noncomputable def simplicialMatchingFaces_representableBy
    {n : ℕ} (U : SSet.Truncated n) :
    (matchingFamilyFunctor U).RepresentableBy (simplicialMatchingFaces U) where
  homEquiv := fun {X} ↦ simplicialMatchingFaces_homEquiv U X
  homEquiv_comp := by
    intro X X' f g
    sorry

private noncomputable def tildeTop_representableBy
    {n : ℕ} (U : SSet.Truncated n) :
    (matchingFamilyFunctor U).RepresentableBy
      ((SimplicialObject.Truncated.tilde U).obj
        (op (simplicialMatchingTopSimplex (n + 1)))) := by
  let Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op (simplicialMatchingTopSimplex (n + 1))
  let e :
      StructuredArrow Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ≌
        StructuredArrow ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
          (SimplexCategory.Truncated.inclusion n).op :=
    (StructuredArrow.post Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op
        (SimplexCategory.Truncated.inclusion (n + 1)).op).asEquivalence.trans
      (StructuredArrow.mapNatIso (Iso.refl _ :
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙
            (SimplexCategory.Truncated.inclusion (n + 1)).op ≅
          (SimplexCategory.Truncated.inclusion n).op))
  let w :
      e.functor ⋙
          StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U ≅
        StructuredArrow.proj Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙
          U :=
    Iso.refl _
  let hlim :=
    Limits.limit.isLimit
      (StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op ⋙ U)
  let hrep := Limits.IsLimit.representableBy hlim
  let eObj :
      ((SimplicialObject.Truncated.tilde U).obj
        (op (simplicialMatchingTopSimplex (n + 1)))) ≅
        (Limits.limit.cone
          (StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U)).pt :=
    ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ranObjObjIsoLimit U Y) ≪≫
      Limits.HasLimit.isoOfEquivalence e w
  simpa [matchingFamilyFunctor, SimplicialObject.Truncated.tilde] using
    hrep.ofIsoObj eObj

/-- The explicit matching-face model is canonically isomorphic to the top-degree term of the
one-step extension `\tilde U`. -/
noncomputable def simplicialMatchingFacesIsoTildeTop
    {n : ℕ} (U : SSet.Truncated n) :
    simplicialMatchingFaces U ≅
      (SimplicialObject.Truncated.tilde U).obj
        (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))) :=
  Functor.RepresentableBy.uniqueUpToIso
    (simplicialMatchingFaces_representableBy U)
    (tildeTop_representableBy U)

section Tilde

variable {n : ℕ} (U : SSet.Truncated n) (V : SSet.Truncated (n + 1))

/- Remark 14.19.8: the canonical one-step extension `\tilde U` of an `n`-truncated simplicial set
is the owner `SimplicialObject.Truncated.tilde U`. -/
#check (SimplicialObject.Truncated.tilde U : SSet.Truncated (n + 1))

/- Its universal property is the symmetric form of the canonical Hom-set equivalence
`U.tildeHomEquiv V`, whose inverse is the source map `Mor(sk_n V, U) → Mor(V, \tilde U)`. -/
#check (U.tildeHomEquiv V).symm

end Tilde

end CategoryTheory
