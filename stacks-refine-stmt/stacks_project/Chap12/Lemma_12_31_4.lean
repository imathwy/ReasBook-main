import Mathlib
import stacks_project.Chap12.Lemma_12_31_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe u

namespace CategoryTheory

namespace SequentialInverseSystem

local notation "AbSeq" => SequentialInverseSystem AddCommGrpCat

/- Domain-style sampling for Lemma 12.31.4 in the sequential inverse-system exactness domain:
- `source-facing`: a four-term exact sequence of sequential inverse systems and the induced exact
  tail sequence on inverse limits
- `core/canonical`: the finite exact-sequence owner `ComposableArrows.Exact` together with the
  chapter theorems `inverseLimit_shortExact_of_isMittagLeffler_left` and
  `inverseLimit_exact_and_mono_of_shortExact`
- `bridge/view`: the present theorem, which passes from an exact four-term composable-arrow object
  of towers to exactness of the tail sequence after applying inverse limit

Primitive data are the exact composable-arrow object `S : ComposableArrows AbSeq 3` and the
Mittag-Leffler condition on its leftmost term `S.left`. The tail inverse-limit sequence is
derived canonically as `δ₀ (S ⋙ lim)`, so the statement should use that owner-level
construction directly rather than reintroducing separate primitive morphism binders. -/

-- Proof sketch: let `Z_i = ker(C_i ⟶ D_i)` and `I_i = im(A_i ⟶ B_i)`. The short exact sequence
-- `0 ⟶ I_i ⟶ B_i ⟶ Z_i ⟶ 0` together with Lemma 12.31.3 yields surjectivity of
-- `\varprojlim B_i ⟶ \varprojlim Z_i`, and `\varprojlim Z_i` identifies with the kernel of
-- `\varprojlim C_i ⟶ \varprojlim D_i`.
/-- Lemma 12.31.4: let `A ⟶ B ⟶ C ⟶ D` be an exact sequence of sequential inverse systems of
abelian groups. If `A` is Mittag-Leffler, then the induced sequence on inverse limits
`\varprojlim B ⟶ \varprojlim C ⟶ \varprojlim D` is exact. -/
theorem inverseLimit_exact_of_four_term_exact_of_isMittagLeffler_left
    (S : ComposableArrows AbSeq 3)
    (hS : S.Exact)
    (hML : S.left.IsMittagLeffler) :
    (δ₀ (S ⋙ lim)).Exact := sorry

end SequentialInverseSystem

end CategoryTheory
