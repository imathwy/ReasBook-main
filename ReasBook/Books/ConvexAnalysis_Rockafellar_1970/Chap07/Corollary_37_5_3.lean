import ConvexAnalysis_Rockafellar_1970.Chap07.Corollary_37_5_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_37_3_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Proposition_36_5_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_4
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_5

noncomputable section

open scoped Rockafellar SetRel

universe u v

namespace Bifunction

section

variable {U : Type u} {V : Type v}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 37.5.3 identifies `∂KStar(0, 0)` with the saddle-points of `K`, and
  extracts the existence criterion `0 ∈ dom ∂ₛ KStar`.
- `core/canonical`: the relevant owners already exist upstream as
  `Bifunction.IsSaddlePoint`, the intrinsic strong-dual domain notation `dom∂ₛ`, and
  `SaddleFunction.dom`.
- `bridge/view`: this file therefore keeps only the zero-fiber and intrinsic-domain bridge
  theorems,
  with no local redefinition of the saddle subdifferential, graph relation, effective domain, or
  saddle-point set.

Primary mathematical domain:
- saddle-point existence via the conjugate saddle subdifferential.

Domain-style sampling used here:
- `Bifunction.mem_subdifferentialAt_iff_mem_subdifferentialAt_of_equivalent_lowerConjugate` from
  `Chap07.Theorem_37_5`;
- `Bifunction.mem_subdifferentialDomDual` from `Chap07.Definition_37_3_1`;
- `Bifunction.isSaddlePoint_iff_zero_mem_subdifferentialAt` from
  `Chap07.Proposition_36_5_2`;
- `Bifunction.subdifferentialGraphPairing` / notation `gphd[YU, YV](K)` from
  `Chap07.Corollary_37_5_1`;
- `Bifunction.ri_dom_subset_subdifferentialDomDual_of_isClosedProperConcaveConvex`
  from `Chap07.Theorem_37_4`.

Primitive data vs derived API:
- primitive source data: a saddle kernel `K` and a conjugate-side representative
  `KStar ∼ lowerConjugate K`;
- primitive owner data reused from upstream: `d(KStar ; 0, 0)`, `IsSaddlePoint K u v`,
  `dom∂ₛ KStar`, and `SaddleFunction.dom KStar`;
- derived API: the zero-fiber/saddle-point equivalence, the intrinsic-domain existence criterion,
  and
  the relative-interior existence consequence.

Layer target: `source-facing`, stated directly on the existing owners.
-/

-- Proof sketch: specialize Theorem 37.5 at the dual base point `(0, 0)`, then rewrite the
-- primal-side zero-subgradient clause by Proposition 36.5.2.
/-- Corollary 37.5.3, zero-fiber clause: if `KStar` is a conjugate saddle representative of `K`,
then membership in `∂KStar(0, 0)` is exactly the saddle-point condition for `K`. -/
theorem mem_subdifferentialAt_zero_iff_isSaddlePoint_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    {u : U} {v : V} :
    (u, v) ∈ d(KStar ; (0 : U), (0 : V) | U, V) ↔ IsSaddlePoint K u v := by
  sorry

-- Proof sketch: use `mem_subdifferentialDomDual` to rewrite `0 ∈ dom∂ₛ KStar` as nonemptiness of
-- `d(KStar ; 0, 0)`, then use the previous zero-fiber theorem to identify those witnesses with
-- saddle-points of `K`.
/-- Corollary 37.5.3, existence criterion: `K` has a saddle-point exactly when the origin lies in
the intrinsic strong-dual domain `dom∂ₛ KStar` of a conjugate saddle representative `KStar`. -/
theorem exists_isSaddlePoint_iff_zero_mem_subdifferentialDomDual_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K) :
    (∃ p : U × V, IsSaddlePoint K p.1 p.2) ↔
      (0 : U × V) ∈ dom∂ₛ KStar := by
  sorry

-- Proof sketch: Theorem 37.4 places `ri (dom KStar)` inside the domain of the saddle
-- subdifferential of `KStar`; the previous theorem then converts `0 ∈ dom∂ₛ KStar` into
-- existence of a saddle-point of `K`.
/-- Corollary 37.5.3, relative-interior consequence: if the origin lies in the relative interior
of the product domain of a closed proper concave-convex conjugate representative `KStar`, then
the original saddle kernel `K` has a saddle-point. -/
theorem exists_isSaddlePoint_of_zero_mem_ri_dom_of_equivalent_lowerConjugate
    {K KStar : U → V → EReal}
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hK_closed : SaddleFunction.IsClosed K)
    (hK_proper : SaddleFunction.IsProper K)
    (hKStar : KStar ∼ lowerConjugate K)
    (hKStar_shape : SaddleFunction.IsConcaveConvex ℝ KStar)
    (hKStar_closed : SaddleFunction.IsClosed KStar)
    (hKStar_proper : SaddleFunction.IsProper KStar)
    (hzero_ri : (0 : U × V) ∈ ri[ℝ](SaddleFunction.dom KStar)) :
    ∃ p : U × V, IsSaddlePoint K p.1 p.2 := by
  sorry

end

end Bifunction
