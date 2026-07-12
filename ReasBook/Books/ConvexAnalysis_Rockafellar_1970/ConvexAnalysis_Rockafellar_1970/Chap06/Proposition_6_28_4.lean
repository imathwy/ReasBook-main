import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_5
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2

universe u v w z

section

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {I : Sort v}
variable {α : Type z} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 6.28.4 states that the pointwise infimum of concave functions is
  concave.
- `core/canonical`: the chapter owner for global concavity is `Function.IsConcave` from
  Definition 6.30.2, and the canonical infimum closure owner is the set form
  `Function.IsConcave.sInf`.
- `bridge/view`: the indexed-family theorem `Function.IsConcave.iInf` is the `iInf` bridge form,
  while the proof route uses the upstream convex owner theorem `Function.IsConvex.iSup`.
- Primitive data vs derived API: for `iInf`, the family `f : I → E → WithTopBot α` and the
  concavity of each `f i` are primitive; for `sInf`, the primitive data are a set family
  `F : Set (E → WithTopBot α)` and its memberwise concavity.

Domain-style sampling used here:
- `Function.IsConcave` and `Function.IsConcave.convex_neg`;
- `Function.IsConvex`;
- `Function.IsConvex.iSup`;
- `WithTopBot.negOrderIso.map_iInf`.

Layer target: `source-facing`. The public closure owner is exposed on `Function.IsConcave`,
with `sInf` as canonical owner form and `iInf` as the indexed bridge surface.
-/

/-- Proposition 6.28.4 (owner method form): concavity is closed under pointwise indexed
infima. The source states this on `R^m`; the chapter's canonical whole-space owner for that
conclusion is `Function.IsConcave`, and the proof uses the existing convex-owner closure theorem
on the negated family. -/
theorem IsConcave.iInf
    {f : I → E → WithTopBot α}
    (hf : ∀ i, (f i).IsConcave 𝕜) :
    (⨅ i, f i).IsConcave 𝕜 := by
  have hneg_iInf_point (g : I → WithTopBot α) : -(⨅ i, g i) = ⨆ i, -g i := by
    exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iInf g)
  have hneg_iInf : -(⨅ i, f i) = ⨆ i, -f i := by
    ext x
    change -((⨅ i, f i) x) = (⨆ i, -f i) x
    simpa [iInf_apply, iSup_apply] using hneg_iInf_point (fun i ↦ f i x)
  change (-(⨅ i, f i)).IsConvex 𝕜
  rw [hneg_iInf]
  exact IsConvex.iSup (fun i ↦ (hf i).convex_neg)

/-- Proposition 6.28.4 (set-owner form): concavity is closed under pointwise set infima. This is
`Function.IsConcave.iInf` packaged on the intrinsic set-family owner `SupSet.sInf`, so downstream
items can use the canonical set form directly without introducing an auxiliary index type. -/
theorem IsConcave.sInf
    {F : Set (E → WithTopBot α)}
    (hF : ∀ f ∈ F, f.IsConcave 𝕜) :
    (SupSet.sInf F).IsConcave 𝕜 := by
  classical
  simpa [sInf_eq_iInf'] using
    (IsConcave.iInf (f := fun f : F ↦ (f : E → WithTopBot α))
      (hf := fun f ↦ hF f f.property))

end Function

end
