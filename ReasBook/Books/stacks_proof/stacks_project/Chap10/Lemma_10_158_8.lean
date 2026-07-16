import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_158_5
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.8:
- primary domain: field extensions and the comparison between formal smoothness and the
  Stacks-project separability owner `Algebra.IsSeparableOver`;
- sampled owner declarations:
  `Algebra.formallySmooth_of_charZero`,
  `Algebra.isSeparableOver_of_formallySmooth`,
  `Algebra.formallySmooth_of_isSeparableOver`;
- best owner abstraction: the chapter owner pair `Algebra.IsSeparableOver k K` and
  `Algebra.FormallySmooth k K`, with characteristic assumptions used only when they add genuine
  mathematical content;
- primitive data: the field extension `K / k`;
- derived API: the characteristic-zero consequence and the bidirectional bridge between the two
  owner predicates.

Source/core/bridge triage:
- `source-facing`: the characteristic-zero formal-smoothness statement and the source's
  positive-characteristic equivalence;
- `core/canonical`: `Algebra.IsSeparableOver k K` and `Algebra.FormallySmooth k K`;
- `bridge/view`: `Algebra.formallySmooth_of_charZero`,
  `isSeparableOver_of_formallySmooth`, and `formallySmooth_of_isSeparableOver`.

The source states part `(2)` only in characteristic `p > 0`, but after Lemmas `10.158.5` and
`10.158.7` that hypothesis is redundant. The refined owner statement is therefore the
unconditional equivalence between the two chapter owners.
-/
/- Lemma 10.158.8 (1): if the characteristic of `k` is zero, then every field extension `K / k`
is formally smooth over `k`. This is Proposition `10.158.9 (3)`, now kept under the canonical
owner name `Algebra.formallySmooth_of_charZero`. -/
recall Algebra.formallySmooth_of_charZero

/-- Lemma 10.158.8 (2): for field extensions, formal smoothness over `k` is equivalent to
separability in the Stacks Project sense. In the source this is stated in characteristic `p > 0`,
but the characteristic hypothesis is redundant after Lemmas `10.158.5` and `10.158.7`. -/
@[stacks 0321]
theorem formallySmooth_iff_isSeparableOver :
    Algebra.FormallySmooth k K ↔ Algebra.IsSeparableOver k K := by
  constructor
  · intro h
    letI : Algebra.FormallySmooth k K := h
    exact Algebra.isSeparableOver_of_formallySmooth
  · intro h
    letI : Algebra.IsSeparableOver k K := h
    exact Algebra.formallySmooth_of_isSeparableOver

end

end Algebra
