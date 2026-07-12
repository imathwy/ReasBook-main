import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Source/core/bridge triage for Lemma 9.26.5:
- primary domain: transcendence degree in towers of algebra extensions;
- sampled owner declarations: `Algebra.trdeg`, `IsTranscendenceBasis.cardinalMk_eq_trdeg`,
  `lift_trdeg_add_eq`, and `trdeg_add_eq`;
- best owner abstraction: `Algebra.trdeg`, with `trdeg_add_eq` as the canonical tower formula;
- primitive data: a tower `R → S → A` of commutative rings equipped with the faithful-scalar and
  no-zero-divisor hypotheses needed for the canonical additivity theorem;
- derived API: the Stacks field-extension statement is obtained from `trdeg_add_eq` by typeclass
  specialization;
- `source-facing`: additivity of transcendence degree in a tower of field extensions;
- `core/canonical`: `Algebra.trdeg` and its tower theorem `trdeg_add_eq`;
- `bridge/view`: the field-specialization of `trdeg_add_eq`;
- `layer`: `core/canonical`.

The source lemma adds no new mathematics beyond the canonical tower formula, so the file should
recall `trdeg_add_eq` directly instead of introducing a parallel local field-only wrapper.
-/

/-
Lemma 9.26.5: transcendence degree is additive in a tower. The Stacks field-extension statement is
the field specialization of the canonical mathlib theorem `trdeg_add_eq`.
-/
recall trdeg_add_eq (k : Type u) (K : Type v) [CommRing k] [CommRing K] [Algebra k K]
    [Nontrivial k] {L : Type v} [CommRing L] [NoZeroDivisors L] [Algebra k L] [Algebra K L]
    [FaithfulSMul k K] [FaithfulSMul K L] [IsScalarTower k K L] :
    Algebra.trdeg k K + Algebra.trdeg K L = Algebra.trdeg k L
