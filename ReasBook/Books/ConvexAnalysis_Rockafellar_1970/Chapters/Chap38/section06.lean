

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_38_6 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u

namespace Function

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [FiniteDimensional ℝ E] [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 38.6 states the sign-duality of the Chapter 38 inner product under
  convex and concave conjugation, together with invariance under passing to the closures of the
  two functions.
- `core/canonical`: the owners already present in the project are `Function.innerProduct`,
  `Function.HasInnerProduct`, the convex conjugate `f⋆`, the concave conjugate `g∗`, the
  concavity owner `g.IsConcave ℝ`, the Chapter 6 concave closure owner `concaveClosure g`, and
  the Chapter 2 closure owner `cl(·)`.
- `bridge/view`: the proof route goes through convex biconjugacy for `f` and for `-g`, while the
  public concave-side closure is kept in the canonical owner form `concaveClosure g` rather than a
  repeated sign-dual spelling.

Primary mathematical domain:
- Fenchel-type duality between convex and concave functions on a finite-dimensional real space
  equipped with a continuous linear self-pairing.

Domain-style sampling used here:
- `Function.innerProduct` and `Function.HasInnerProduct` from `Definition_38_5_2`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` from `Theorem_12_2`;
- the Chapter 6 concavity and concave-closure owners `Function.IsConcave` and `concaveClosure`
  from `Definition_6_30_2`;
- the Chapter 6 concave conjugate owner `concaveConjugate`, used through the source-facing
  notation `g∗`, from `Definition_6_30_4`.

Primitive data vs derived API:
- primitive inputs: a convex function `f : E → EReal`, a concave function `g : E → EReal`, and
  the source existence hypothesis `HasInnerProduct f g`;
- derived API: existence and value formulas for the conjugate pair and for the closure-normalized
  pair, with the concave closure written through the owner `concaveClosure g`.

Layer target: `bridge/view`. The lemma relates existing Chapter 38, Chapter 12, and Chapter 6
owners; it does not introduce a new owner notion.
-/

-- Proof sketch: compare the four extrema appearing in the source proof using Fenchel's
-- inequality, then identify the middle pair with the Chapter 38 existence criterion for the
-- conjugates. The biconjugacy bridges for `f` and `g` supply the closure-normalized comparison
-- needed to transfer existence from `⟪f, g⟫` to `⟪f⋆, g*⟫`.
/-- Lemma 38.6 (1): if the inner product of a convex function `f` and a concave function `g`
exists, then the inner product of the convex conjugate `f⋆` and the concave conjugate
`g∗` also exists. -/
theorem hasInnerProduct_convexConjugate_concaveConjugate
    {f g : E → EReal}
    (hf : f.IsConvex ℝ) (hg : g.IsConcave ℝ) (hfg : HasInnerProduct f g) :
    HasInnerProduct (f⋆ : E → EReal) (g∗ : E → EReal) := sorry

-- Proof sketch: once the conjugate inner product is known to exist, the same chain of Fenchel
-- inequalities shows that the common value of the conjugate extrema is the negative of the common
-- value defining `innerProduct f g`.
/-- Lemma 38.6 (2): under the same hypotheses, the conjugate inner product equals the negative of
the original one. -/
theorem innerProduct_convexConjugate_concaveConjugate_eq_neg
    {f g : E → EReal}
    (hf : f.IsConvex ℝ) (hg : g.IsConcave ℝ) (hfg : HasInnerProduct f g) :
    innerProduct (f⋆ : E → EReal) (g∗ : E → EReal) = -innerProduct f g := sorry

-- Proof sketch: replace `f⋆⋆` by `cl(f)` using convex biconjugacy and replace the concave
-- biconjugate side by the canonical Chapter 6 owner `concaveClosure g`, obtained by applying
-- convex biconjugacy to `-g`. Then apply the first clause to the conjugate pair and transport
-- existence back through those closure identifications.
/-- Lemma 38.6 (3): under the same hypotheses, the inner product of the convex closure `cl(f)` and
the concave closure `concaveClosure g` also exists. This is the canonical owner form of the
textbook statement involving `cl g`. -/
theorem hasInnerProduct_lowerSemicontinuousHull_concaveClosure
    {f g : E → EReal}
    (hf : f.IsConvex ℝ) (hg : g.IsConcave ℝ) (hfg : HasInnerProduct f g) :
    HasInnerProduct (cl(f)) (concaveClosure g) := sorry

-- Proof sketch: identify `cl(f)` with `f⋆⋆` and `concaveClosure g` with the concave biconjugate
-- side of `g`, apply the conjugate-value formula from the previous clauses twice, and simplify
-- the resulting double negation.
/-- Lemma 38.6 (4): the closure-normalized inner product coincides with the original one. This is
the canonical owner form of the textbook statement `⟨cl f, cl g⟩ = ⟨f, g⟩`, where the concave-side
closure is rendered by `concaveClosure g`. -/
theorem innerProduct_lowerSemicontinuousHull_concaveClosure_eq
    {f g : E → EReal}
    (hf : f.IsConvex ℝ) (hg : g.IsConcave ℝ) (hfg : HasInnerProduct f g) :
    innerProduct (cl(f)) (concaveClosure g) = innerProduct f g := sorry

end

end Function
