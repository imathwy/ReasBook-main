import Mathlib
import stacks_project.Chap09.Definition_9_26_1
import stacks_project.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Lemma 10.158.7:
- primary domain: field extensions and the formal smoothness / separability interface over a base
  field;
- sampled owner declarations:
  `isPurelyTranscendental_iff_exists_algebraicIndependent`,
  `Algebra.FormallySmooth.of_algebraicIndependent`,
  `Algebra.FormallyEtale.of_isSeparable`,
  `Algebra.IsSeparableOver`;
- best owner abstraction: the canonical owner `Algebra.FormallySmooth k K`, with the source-facing
  chapter predicates `IsPurelyTranscendental` and `IsSeparableOver` treated as bridge inputs;
- primitive data: the field extension `K / k` together with the source-facing hypotheses
  `IsPurelyTranscendental k K`, `[Algebra.IsSeparable k K]`, or `[Algebra.IsSeparableOver k K]`;
- derived API: the formal smoothness conclusion and the low-priority instance exported from the
  source-facing theorem in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the three textbook implications in Lemma 10.158.7;
- `core/canonical`: `Algebra.FormallySmooth k K` and the exact mathlib owners
  `Algebra.FormallySmooth.of_algebraicIndependent` and
  `Algebra.FormallyEtale.of_isSeparable`;
- `bridge/view`: the chapter owners `IsPurelyTranscendental` and `IsSeparableOver`.
-/

/-- Lemma 10.158.7 (1): a purely transcendental field extension is formally smooth over the base
field. -/
theorem formallySmooth_of_purelyTranscendental
    (hK : IsPurelyTranscendental k K) :
    Algebra.FormallySmooth k K := by
  rcases isPurelyTranscendental_iff_exists_algebraicIndependent.mp hK with
    ⟨ι, x, hx, hx_top⟩
  exact Algebra.FormallySmooth.of_algebraicIndependent hx hx_top

/-- Lemma 10.158.7 (2): a separable algebraic field extension is formally smooth over the base
field. -/
theorem formallySmooth_of_isSeparable [Algebra.IsSeparable k K] :
    Algebra.FormallySmooth k K := by
  letI : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  infer_instance

/-- Lemma 10.158.7 (3): a separable field extension in the Stacks Project sense is formally smooth
over the base field. -/
-- Proof sketch: write `K` as the filtered union of its finitely generated intermediate
-- extensions; each such subextension is separably generated, hence formally smooth by parts (1)
-- and (2), and then pass to the filtered colimit criterion for formal smoothness of field
-- extensions.
theorem formallySmooth_of_isSeparableOver [IsSeparableOver k K] :
    Algebra.FormallySmooth k K := sorry

/-- Low-priority instance supplied by Lemma 10.158.7 (3). -/
@[instance low] instance [IsSeparableOver k K] : Algebra.FormallySmooth k K :=
  formallySmooth_of_isSeparableOver

end

end Algebra
