import Mathlib
import StacksProject_2024.Chap04.Definition_4_42_3
import StacksProject_2024.Chap04.Lemma_4_35_10

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]

/- Domain-style sampling for Lemma 4.42.6:
- primary domain: representable morphisms of categories fibred in groupoids and the canonical
  diagonal morphism of a bundled fibred-in-groupoids owner over a fixed base;
- inspected owner-level declarations:
  `FibredInGroupoidsMor.IsRepresentable`,
  `FibredInGroupoidsMor.diagonalMor`,
  `FibredInGroupoidsOver.baseProjection`,
  `FibredInGroupoidsOver.IsRepresentable`;
- best owner abstraction: the ambient owner hom `ofFunctor (Over.forget U) ⟶ X` together with
  the canonical diagonal owner `FibredInGroupoidsMor.diagonalMor X.baseProjection`, rather than
  the redundant hom-type
  alias `FibredInGroupoidsMor`;
- primitive data: only the bundled owner `X : FibredInGroupoidsOver C`;
- derived API: the canonical projection `X.baseProjection` and the slice-level criterion
  `G.IsRepresentable`.

Source/core/bridge triage:
- `source-facing`: Lemma 4.42.6;
- `core/canonical`: `FibredInGroupoidsMor.IsRepresentable` for
  `FibredInGroupoidsMor.diagonalMor X.baseProjection`;
- `bridge/view`: the canonical projection `X.baseProjection` and the pairwise slice-morphism
  criterion over `C/U`. -/

-- Proof sketch: for `(1) → (2)`, fix `U` and `G : C/U ⥤ S`. To test representability of `G`,
-- pull back the diagonal along `(G, G') : C/U × C/V ⥤ S × S` for arbitrary `V` and `G'`,
-- using binary products in `C` and Lemma `4.31.11` together with Remark `4.35.8` to identify the
-- resulting representable pullback with `C/U ×_S C/V`. For `(2) → (1)`, start from a pair
-- `(G, G') : C/V ⥤ S × S`, apply representability to the first projection of
-- `C/V ×_{G, S, G'} C/V`, and then use Lemma `4.31.12` and Remark `4.35.8` to recover the
-- pullback of the diagonal.

/-- Lemma 4.42.6: for a category fibred in groupoids `X` over `C`, representability of its
canonical diagonal morphism is equivalent to representability of every morphism
`G : C/U ⟶ X` from a slice category. The left-hand side uses the canonical owner
`FibredInGroupoidsMor.diagonalMor X.baseProjection` directly, rather than the wrapper alias
`FibredInGroupoidsOver.baseProjectionDiagonalMor X`. -/
theorem representable_diagonal_iff_all_slice_morphisms_representable
    (X : FibredInGroupoidsOver C) :
    FibredInGroupoidsMor.IsRepresentable
        (FibredInGroupoidsMor.diagonalMor X.baseProjection) ↔
      ∀ {U : C} (G : ofFunctor (Over.forget U) ⟶ X),
        FibredInGroupoidsMor.IsRepresentable G := sorry

end CategoryTheory
