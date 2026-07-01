import Mathlib
import stacks_project.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.87.10:
- primary domain: Milnor short exact sequences for sequential derived limits in derived categories
  of abelian categories;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.derivedLimitDifferenceMap`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `DerivedCategory.homologyFunctor`;
- best owner abstraction: the source-facing theorem should remain the Milnor short exact sequence
  for a chosen `IsDerivedLimit`, while the left term is canonically owned by
  `SequentialInverseSystem.firstDerivedLimit` on the tower of cohomology objects;
- primitive data: an abelian category `C` with countable products, the tower `Ksys`, the chosen
  derived-limit object `Klim`, and the witness `hKlim : IsDerivedLimit Ksys Klim`;
- derived API: the cohomology tower `Ksys ⋙ H p` and its owner-level Milnor term
  `(Ksys ⋙ H (p - 1)).firstDerivedLimit`.

Source/core/bridge triage:
- `source-facing`: the Milnor short exact sequence in degree `p`;
- `core/canonical`: `IsDerivedLimit`, `derivedLimitDifferenceMap`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the explicit cokernel presentation already packaged by
  `SequentialInverseSystem.firstDerivedLimit`. -/

section

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasCountableProducts C] [HasLimitsOfShape ℕᵒᵖ C]

local notation "DC" => DerivedCategory C
local notation "H" => DerivedCategory.homologyFunctor C

-- Proof sketch: start from the Milnor distinguished triangle defining `hKlim`, apply the
-- cohomology functor `H^p`, and read the relevant three-term segment of the resulting long exact
-- sequence. In any abelian category with countable products, the kernel of the Milnor difference
-- map is `lim_n H^p(K_n^•)` and its cokernel is the standard model for
-- `R^1 lim_n H^{p-1}(K_n^•)`.
/-- Lemma 15.87.10: if `Klim` is the chosen derived limit of a sequential inverse system
`(K_n^\bullet)_n` in `D(C)`, then the long exact cohomology sequence of the associated
distinguished triangle breaks into a short exact sequence
`0 \to R^1 \!\varprojlim_n H^{p-1}(K_n^\bullet) \to H^p(Klim) \to
\varprojlim_n H^p(K_n^\bullet) \to 0`, canonically realized as
`(Ksys ⋙ H (p - 1)).firstDerivedLimit`. -/
theorem derivedLimit_cohomology_shortExact
    (Ksys : SequentialInverseSystem DC) (Klim : DC) (hKlim : IsDerivedLimit Ksys Klim) (p : ℤ) :
    ∃ (ι : SequentialInverseSystem.firstDerivedLimit (Ksys ⋙ H (p - 1)) ⟶ (H p).obj Klim)
      (π : (H p).obj Klim ⟶ limit (Ksys ⋙ H p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end CategoryTheory
