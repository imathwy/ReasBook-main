import Mathlib.RingTheory.Length
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Length

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-
Domain triage:
* primary domain: finite-length modules and module length over a ring;
* sampled owner API: `Module.length`, `Module.length_ne_top_iff`,
  `isFiniteLength_iff_isNoetherian_isArtinian`, and `IsNoetherian.finite`;
* core/canonical owner: `IsFiniteLength R M`;
* layer split: the hypothesis `Module.length R M < ⊤` is the source-facing formulation,
  `IsFiniteLength R M` is the owner abstraction, and `Module.Finite R M` is derived API via the
  Noetherian half of the owner theorem.
-/

/- Owner bridge: finite module length is canonically expressed by `IsFiniteLength R M`. -/
recall Module.length_ne_top_iff

/-- Lemma 10.52.2: if `Module.length R M < ⊤`, then `M` is a finite `R`-module. This is the
Stacks-project formulation; the equivalent owner predicate in mathlib is `IsFiniteLength R M`. -/
theorem module_finite_of_length_lt_top (h : Module.length R M < ⊤) : Module.Finite R M := by
  have hFiniteLength : IsFiniteLength R M := Module.length_ne_top_iff.mp h.ne
  have hNoetherian : IsNoetherian R M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hFiniteLength).1
  letI : IsNoetherian R M := hNoetherian
  exact Module.IsNoetherian.finite R M

end Length
