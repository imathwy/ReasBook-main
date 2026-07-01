import Mathlib
import stacks_project.Chap10.Definition_10_86_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Countable I]

local notation "AbelianGroupInverseSystem" => OrderDual I ⥤ AddCommGrpCat
local notation "invlim" => (lim : AbelianGroupInverseSystem ⥤ AddCommGrpCat)

-- Domain sampling:
-- * source-facing layer: this file proves inverse-limit exactness for short exact sequences of
--   abelian-group inverse systems.
-- * core/canonical owner: `CategoryTheory.Functor.IsMittagLeffler` on the underlying
--   `Type`-valued inverse system, recalled in `Definition_10_86_1`.
-- * relevant owner API sampled before refinement:
--   `CategoryTheory.Functor.IsMittagLeffler`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`,
--   `CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp`,
--   `CategoryTheory.Functor.IsMittagLeffler.toPreimages`.
-- Primitive data are only the short exact sequence and the owner Mittag-Leffler hypothesis on the
-- left term; stagewise image stabilization is derived bridge API from that owner abstraction.
--
-- Proof sketch: inverse limits of abelian groups are left exact, so only surjectivity of the map
-- on limits needs proof. For a compatible family in `(C_i)`, consider the inverse system of
-- fibres `E_i = g_i⁻¹(c_i)`; exactness makes each `E_i` nonempty, and the owner hypothesis
-- `(S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler` upgrades the induced set-valued inverse system
-- `(E_i)` to a Mittag-Leffler system via `Functor.IsMittagLeffler.toPreimages`. Lemma `10.86.3`
-- then gives a compatible family in the fibres, yielding a lift in `\varprojlim B_i`.
/-- Lemma 10.86.4: for a short exact sequence `0 ⟶ (A_i) ⟶ (B_i) ⟶ (C_i) ⟶ 0` of directed
inverse systems of abelian groups over a countable directed preorder `I`, if `(A_i)` is
Mittag-Leffler, then the induced sequence
`0 ⟶ \varprojlim_i A_i ⟶ \varprojlim_i B_i ⟶ \varprojlim_i C_i ⟶ 0`
is short exact. -/
theorem inverseSystem_limit_shortExact_of_countable_and_isMittagLeffler_left
    (S : ShortComplex AbelianGroupInverseSystem)
    (hS : S.ShortExact)
    (hML : (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler) :
    (S.map invlim).ShortExact := sorry
