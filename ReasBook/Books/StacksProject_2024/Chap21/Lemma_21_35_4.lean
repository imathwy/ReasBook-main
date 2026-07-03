import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Domain-style sampling for Lemma 21.35.4:
- primary domain: triangulated functors on derived categories, especially exactness transported
  across adjunctions and opposite categories;
- sampled owner declarations:
  `Adjunction.isTriangulated_rightAdjoint`,
  `Functor.isTriangulated_of_op`,
  `Functor.op_isTriangulated_iff`,
  `SheafOfModules.RingedSite.derivedTensorProduct_isTriangulated`;
- best owner abstraction: the mathematical owners here are the generic triangulated-functor
  theorems `Adjunction.isTriangulated_rightAdjoint` and `Functor.isTriangulated_of_op`; the
  ringed-site input only supplies the ambient derived category and the source-facing realization of
  `- ⊗^L K` as the exact left adjoint from Definition `21.17.13`;
- primitive vs derived: the primitive data are a shift-compatible adjunction and, respectively, an
  opposite functor known to be triangulated; the exactness of the right adjoint and of the
  contravariant original functor are derived API, so they should not be restated as parallel local
  owner theorems.

Source/core/bridge triage:
- `source-facing`: Lemma 21.35.4 asserts exactness of derived internal Hom in each variable on the
  derived category of sheaves of modules over a ringed site;
- `core/canonical`: `Adjunction.isTriangulated_rightAdjoint` and `Functor.isTriangulated_of_op`;
- `bridge/view`: the ringed-site reading in which `- ⊗^L K` is the exact left adjoint and
  `R\mathcal H\!\mathit{om}(K,-)` or `R\mathcal H\!\mathit{om}(-,L)` are its source-facing
  second- and first-variable specializations.
-/

/- Lemma 21.35.4 (1): in the ringed-site setting, exactness of a chosen
`R\mathcal H\!\mathit{om}(K,-)` follows from the canonical theorem that a shift-compatible right
adjoint of a triangulated functor is triangulated. -/
recall Adjunction.isTriangulated_rightAdjoint

end

end SheafOfModules.RingedSite

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D]
variable [Limits.HasZeroObject D]
variable [Preadditive D]
variable [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated D]

/- Lemma 21.35.4 (2): exactness in the contravariant first variable is the opposite-category form
of exactness for a covariant triangulated functor, so the owner theorem is the canonical recall
`Functor.isTriangulated_of_op`. -/
recall Functor.isTriangulated_of_op

end

end CategoryTheory
