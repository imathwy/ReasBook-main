import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/- Domain-style sampling for Definition 9.26.9:
- primary domain: relative algebraic closures inside field extensions;
- sampled owner declarations:
  `algebraicClosure`,
  `mem_algebraicClosure_iff`,
  `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`,
  `IsAlgClosed.algebraicClosure_eq_bot_iff`;
- owner abstraction: the canonical proposition `algebraicClosure k K = ⊥`;
- primitive data: none locally, since the source notion is entirely determined by the canonical
  relative algebraic closure;
- derived API: the source-style pointwise characterization that every element of `K` algebraic
  over `k` comes from `k`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that `k` is algebraically closed in the extension `K`;
- `core/canonical`: the owner proposition `algebraicClosure k K = ⊥`;
- `bridge/view`: the companion elementwise characterization below.

The previous local class duplicated the owner proposition without adding mathematical data. The
refined file keeps the canonical proposition as the main entry and exposes only the source-facing
specification theorem as derived API. -/

/- Companion recall: the textbook algebraic closure of `k` in `K` is the canonical relative
algebraic closure `algebraicClosure k K`, namely the intermediate field of elements of `K`
algebraic over `k`. -/
recall algebraicClosure

/- Companion recall: membership in `algebraicClosure k K` is exactly algebraicity over `k`. -/
recall mem_algebraicClosure_iff

/- Definition 9.26.9: the base field `k` is algebraically closed in the extension `K` exactly
when its relative algebraic closure in `K` is the bottom intermediate field. This notion is
owned canonically by the proposition below. -/
#check (algebraicClosure k K = ⊥)

-- Proof sketch: use `mem_algebraicClosure_iff` together with `IntermediateField.mem_bot` to
-- convert equality with `⊥` into the textbook elementwise existence condition.
/-- The canonical proposition `algebraicClosure k K = ⊥` is equivalent to the textbook condition
that every element of `K` algebraic over `k` is the image of an element of `k`. -/
theorem algebraicClosure_eq_bot_iff :
    algebraicClosure k K = ⊥ ↔
      ∀ x : K, IsAlgebraic k x → ∃ y : k, algebraMap k K y = x := by
  constructor
  · intro h x hx
    exact IntermediateField.mem_bot.mp <|
      h ▸ mem_algebraicClosure_iff.mpr hx
  · intro h
    rw [eq_bot_iff]
    intro x hx
    exact IntermediateField.mem_bot.mpr <| h x (mem_algebraicClosure_iff.mp hx)
