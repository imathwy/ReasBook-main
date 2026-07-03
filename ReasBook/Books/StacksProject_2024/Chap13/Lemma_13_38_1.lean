import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksProject_2024.Chap13.Definition_13_37_5

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
