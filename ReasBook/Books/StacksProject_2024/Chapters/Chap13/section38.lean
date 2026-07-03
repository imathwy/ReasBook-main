import Mathlib
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_38_1 (from Chap13) -/
open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/- Domain-style sampling for Lemma 13.38.1:
- primary domain: Brown representability in triangulated categories, with the representability
  conclusion living in the Yoneda/preadditive-Yoneda interface;
- sampled owner declarations:
  `IsCompactlyGenerated`,
  `Functor.IsRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `whiskering_preadditiveYoneda`;
- best owner abstraction for the canonical representability layer:
  `Functor.IsRepresentable` on the underlying `Type`-valued functor;
- primitive data: the compact-generation hypothesis `hD`, the homologicality of `H`, and the
  product-preservation hypothesis `hprod`;
- derived API: the source-facing additive Yoneda isomorphism
  `∃ X, Nonempty (preadditiveYoneda.obj X ≅ H)` and the canonical representability companion for
  `H ⋙ forget AddCommGrpCat`;
- source/core/bridge triage:
  `source-facing`: `brown_representability`;
  `core/canonical`: `Functor.IsRepresentable (H ⋙ forget AddCommGrpCat)`;
  `bridge/view`: whiskering the additive Yoneda isomorphism along `forget AddCommGrpCat` and
  rewriting via `whiskering_preadditiveYoneda`.

The source theorem should stay in the additive `preadditiveYoneda` form, while downstream
adjunction arguments should use the canonical `Functor.IsRepresentable` companion. -/

-- Proof sketch: choose a compact generating family for `D`, build the standard Brown
-- approximation tower using all elements of `H` on the generators and then on successive kernels,
-- and take its homotopy colimit. Compactness identifies maps out of each generator into the
-- homotopy colimit with the colimit of the stagewise maps, giving an isomorphism on the
-- generating family. The full triangulated subcategory where `preadditiveYoneda.obj X ⟶ H` is an
-- isomorphism is closed under shifts, triangles, and direct sums, so the generating hypothesis
-- forces it to be all of `D`.
/-- Lemma 13.38.1: Brown representability for contravariant cohomological functors on a compactly
generated triangulated category with direct sums. If `H` sends direct sums to products, then
there exists an object `X` representing `H`, i.e. `preadditiveYoneda.obj X ≅ H`. -/
theorem brown_representability (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D)
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := sorry

/-- Canonical companion: Brown representability implies representability of the underlying
`Type`-valued presheaf, which is the owner abstraction used by adjoint-functor criteria. -/
theorem brown_representability_isRepresentable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D)
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  rcases brown_representability H hD hH hprod with ⟨X, ⟨e⟩⟩
  exact Functor.IsRepresentable.mk' <| by
    simpa [whiskering_preadditiveYoneda] using
      (Functor.isoWhiskerRight e (forget AddCommGrpCat) :
        preadditiveYoneda.obj X ⋙ forget AddCommGrpCat ≅ H ⋙ forget AddCommGrpCat)

end

end CategoryTheory

/-! ### Proposition_13_38_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D']
  [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']
  [HasCoproducts.{max u₁ v₁} D]
  (hD : IsCompactlyGenerated D)

/- Domain-style sampling for Proposition 13.38.2:
- primary domain: Brown representability and adjunction criteria for exact functors between
  triangulated categories;
- sampled owner declarations:
  `brown_representability_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`,
  `Adjunction.ofIsLeftAdjoint`,
  `Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `F.IsLeftAdjoint` for the left-adjoint existence statement and `F.rightAdjoint.IsTriangulated`
  for the exactness of the chosen right adjoint;
- primitive data: the functor `F`, the compact-generation hypothesis `hD`, exactness
  `[F.IsTriangulated]`, and coproduct preservation;
- derived API: the chosen adjunction `Adjunction.ofIsLeftAdjoint F`, its induced right-adjoint
  shift compatibility, and the resulting exactness instance on `F.rightAdjoint`.

Source/core/bridge triage:
- `source-facing`: the two theorems below, which keep the compact-generation hypothesis explicit;
- `core/canonical`: `brown_representability_isRepresentable`,
  `Functor.isLeftAdjoint_of_objwise_hom_isRepresentable`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the chosen adjunction `Adjunction.ofIsLeftAdjoint F` together with
  `Adjunction.rightAdjointCommShift` and `Adjunction.commShift_of_leftAdjoint`.
-/

-- Proof sketch: for each `Y : D'`, apply the canonical Brown-representability bridge
-- `brown_representability_isRepresentable` to the contravariant cohomological functor
-- `W ↦ Hom(F(W), Y)`. Exactness of `F` makes this functor homological, and preservation of direct
-- sums by `F` turns coproducts in `D` into products in `AddCommGrpCat`. The resulting objectwise
-- representability hypothesis is exactly the input for the owner criterion
-- `F.isLeftAdjoint_of_objwise_hom_isRepresentable`.
/-- Proposition 13.38.2: an exact functor from a compactly generated triangulated category that
preserves arbitrary direct sums is a left adjoint. The companion theorem
`exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated` records that the chosen
right adjoint is exact. -/
theorem exactFunctor_isLeftAdjoint_of_isCompactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    : F.IsLeftAdjoint := sorry

-- Proof sketch: apply `exactFunctor_isLeftAdjoint_of_isCompactlyGenerated` to obtain the chosen
-- adjunction `Adjunction.ofIsLeftAdjoint F`. The left adjoint is already exact by hypothesis, so
-- Lemma `13.7.1`, equivalently `Adjunction.isTriangulated_rightAdjoint`, gives that the right
-- adjoint is exact.
/-- The right adjoint produced by Brown representability is exact for an exact
coproduct-preserving functor out of a compactly generated triangulated category. -/
theorem exactFunctor_hasExactRightAdjoint_of_isCompactlyGenerated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max u₁ v₁), PreservesColimitsOfShape (Discrete J) F]
    : letI := exactFunctor_isLeftAdjoint_of_isCompactlyGenerated F
      let adj := Adjunction.ofIsLeftAdjoint F
      letI := adj.rightAdjointCommShift ℤ
      F.rightAdjoint.IsTriangulated := by
  letI := exactFunctor_isLeftAdjoint_of_isCompactlyGenerated F
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  letI := adj.rightAdjointCommShift ℤ
  letI := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

end

end CategoryTheory
