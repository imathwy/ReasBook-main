import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Definition 3.2 is `source-facing` in the chapter subgradient API. The primitive mathematical
data already lives in Definition 3.1 as the predicate `is_subgradient_at`; the owner object
introduced here is the set-valued map `extendedRealSubdifferential`. Later normed/real-valued files only build
bridge/view APIs such as `strongDualSubdifferential` and `subdifferentialAt`, so this file keeps
just the owner set and its atomic membership/emptiness lemmas. -/

/-- Definition 3.2: the extendedRealSubdifferential `∂ f(x)` is the set of dual vectors `g ∈ E*` such that
`g` is a subgradient of `f` at `x` in the sense of Definition 3.1. Consequently, when
`x ∉ dom(f)`, this set is empty by definition. -/
def extendedRealSubdifferential (f : E → EReal) (x : E) : Set (Module.Dual ℝ E) :=
  is_subgradient_at f x

scoped[FirstOrderSubdifferential] notation "∂" f "(" x ")" => extendedRealSubdifferential f x

open scoped FirstOrderSubdifferential

-- Proof sketch: `extendedRealSubdifferential` is defined by collecting the subgradients from Definition 3.1,
-- so membership is exactly the predicate `is_subgradient_at`.
/-- Membership in the extendedRealSubdifferential means being a subgradient at the given point. -/
@[simp] lemma mem_subdifferential {f : E → EReal} {x : E} {g : Module.Dual ℝ E} :
    g ∈ ∂ f(x) ↔ is_subgradient_at f x g :=
  Iff.rfl

-- Proof sketch: extensionality on `g`; after rewriting membership with `mem_subdifferential`, the
-- hypothesis `x ∉ effective_domain f` makes the defining domain condition in
-- `is_subgradient_at` false, so both sides are empty.
/-- Outside the effective domain, the extendedRealSubdifferential is empty. -/
@[simp] theorem subdifferential_eq_empty_of_not_mem_effective_domain
    {f : E → EReal} {x : E} (hx : x ∉ effective_domain f) :
    ∂ f(x) = ∅ := by
  ext g
  change is_subgradient_at f x g ↔ False
  constructor
  · intro hg
    exact hx hg.1
  · intro hg
    exact False.elim hg

-- Proof sketch: if `g₁` and `g₂` satisfy all subgradient inequalities at `x`, then every convex
-- combination `t • g₁ + (1 - t) • g₂` satisfies the same inequalities by taking the same convex
-- combination of the two affine lower bounds; if `x ∉ effective_domain f`, the extendedRealSubdifferential is
-- empty, hence convex.
/-- The extendedRealSubdifferential `∂ f(x)` is a convex subset of the ambient dual space. -/
theorem convex_subdifferential (f : E → EReal) (x : E) :
    Convex ℝ (∂ f(x)) := sorry

end
