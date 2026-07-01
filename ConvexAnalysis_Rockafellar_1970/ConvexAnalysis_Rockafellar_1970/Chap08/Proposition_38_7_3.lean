import ConvexAnalysis_Rockafellar_1970.Chap08.Corollary_38_2_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Proposition_38_7_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_2

noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [HasLinearPairing U U ℝ] [HasContinuousPairing U U ℝ]
variable [HasLinearPairing X X ℝ] [HasContinuousPairing X X ℝ]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.3 states that the Chapter 38 infimal convolution of two
  closed convex co-finite bifunctions is again closed convex and co-finite, and that the adjoint
  commutes with this infimal convolution.
- `core/canonical`: the owner abstractions already present upstream are `Bifunction.IsClosedConvex`
  from Chapter 34, the pairing-generic owner `Bifunction.IsCofinite X U` from
  Proposition 38.7.2, the source-facing infimal convolution owner `F₁ D F₂`, and the adjoint
  owner `adjoint X U`, used here directly through the Chapter 6 scoped canonical source
  notation `F⋆`.
- `bridge/view`: this file is the bridge from the co-finite owner hypotheses to the already-owned
  common-`ri(dom)` infimal-convolution theorems of Section 38.2.

Primary mathematical domain:
- convex bifunction duality for infimal convolution in the finite-dimensional self-dual real
  setting.

Domain-style sampling used here:
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`;
- `Bifunction.IsCofinite X U` and
  `Bifunction.isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ`,
  `Bifunction.uncurry_isProper_of_isClosedConvex_of_isCofinite` from
  `Proposition_38_7_2`;
- `Bifunction.isClosedConvex_infimalConvolution_of_common_riDom` from
  `Corollary_38_2_1`;
- `Bifunction.adjointFunction_infimalConvolution_eq_infimalConvolution_\
adjointFunction_of_common_riDom` from `Theorem_38_2`.

Primitive data vs derived API:
- primitive inputs: bifunctions `F₁`, `F₂`;
- primitive owner hypotheses: `IsClosedConvex F₁`, `IsCofinite X U F₁`,
  `IsClosedConvex F₂`, `IsCofinite X U F₂`;
- derived API: closed-convexity and co-finiteness of `F₁ D F₂`, and the adjoint infimal
  convolution identity.

Layer target: `bridge/view`.
-/

variable {F₁ F₂ : U → X → WithBotTop ℝ}

/-- Bridge/view lemma: co-finite closed-convex bifunctions satisfy the common-relative-interior
qualification required by the Section 38.2 infimal-convolution theorems. -/
theorem common_riDom_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    (ri(dom F₁) ∩ ri(dom F₂)).Nonempty := by
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₁).1 hcof₁ with
    ⟨hdom₁, _⟩
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₂).1 hcof₂ with
    ⟨hdom₂, _⟩
  refine ⟨0, ?_⟩
  constructor <;> simp [hdom₁, hdom₂, intrinsicInterior, AffineSubspace.span_univ]

-- Proof sketch: Proposition 38.7.2 upgrades the co-finite hypotheses on `F₁` and `F₂` to the
-- common-relative-interior qualification owned here by
-- `common_riDom_of_isClosedConvex_of_isCofinite`, so Corollary 38.2.1 applies directly on the
-- canonical owner `IsClosedConvex`.
/-- Proposition 38.7.3, closed-convex clause in owner form: the infimal convolution of two closed
convex co-finite bifunctions is again closed convex. -/
theorem isClosedConvex_infimalConvolution_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    IsClosedConvex (F₁ D F₂) := by
  have hri :
      (ri(dom F₁) ∩ ri(dom F₂)).Nonempty :=
    common_riDom_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  simpa using
    isClosedConvex_infimalConvolution_of_common_riDom hF₁ hF₂ hri

-- Proof sketch: Proposition 38.7.2 upgrades the co-finite hypotheses in two ways: first to the
-- common-relative-interior qualification owned here by
-- `common_riDom_of_isClosedConvex_of_isCofinite`, and second to the graph-properness owner
-- `(Function.uncurry F).IsProper` via
-- `uncurry_isProper_of_isClosedConvex_of_isCofinite`. The exact adjoint identity then comes
-- directly from the qualified Section 38.2 theorem.
/-- Proposition 38.7.3, adjoint clause: under the same closed-convex co-finite hypotheses,
`(F₁ D F₂)⋆ = F₁⋆ D F₂⋆`. -/
theorem
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjoint_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂ := by
  have hri :
      (ri(dom F₁) ∩ ri(dom F₂)).Nonempty :=
    common_riDom_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  have hF₁_proper : (Function.uncurry F₁).IsProper :=
    uncurry_isProper_of_isClosedConvex_of_isCofinite hF₁ hcof₁
  have hF₂_proper : (Function.uncurry F₂).IsProper :=
    uncurry_isProper_of_isClosedConvex_of_isCofinite hF₂ hcof₂
  simpa using
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjointFunction_of_common_riDom
      hF₁.convex hF₁_proper hF₂.convex hF₂_proper hri

-- Proof sketch: first obtain `IsClosedConvex (F₁ D F₂)` from the preceding theorem and the
-- adjoint identity
-- `adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂` from the
-- local bridge theorem above. Then Proposition 38.7.2 characterizes co-finiteness by full primal
-- domain and full `dom (-F⋆)`, and those domain equalities are driven by the
-- same bridge
-- `common_riDom_of_isClosedConvex_of_isCofinite`.
/-- Proposition 38.7.3, co-finite clause in owner form: the infimal convolution of two closed
convex co-finite bifunctions is again co-finite. -/
theorem isCofinite_infimalConvolution_of_isClosedConvex_of_isCofinite
    (hF₁ : IsClosedConvex F₁) (hcof₁ : IsCofinite X U F₁)
    (hF₂ : IsClosedConvex F₂) (hcof₂ : IsCofinite X U F₂) :
    IsCofinite X U (F₁ D F₂) := by
  have hclosed : IsClosedConvex (F₁ D F₂) :=
    isClosedConvex_infimalConvolution_of_isClosedConvex_of_isCofinite hF₁ hcof₁ hF₂ hcof₂
  have hadj :
      adjoint X U (F₁ D F₂) = adjoint X U F₁ D adjoint X U F₂ :=
    adjointFunction_infimalConvolution_eq_infimalConvolution_adjoint_of_isClosedConvex_of_isCofinite
      hF₁ hcof₁ hF₂ hcof₂
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₁).1 hcof₁ with
    ⟨hdom₁, hdomAdj₁⟩
  rcases (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hF₂).1 hcof₂ with
    ⟨hdom₂, hdomAdj₂⟩
  change dom (-(adjoint X U F₁)) = Set.univ at hdomAdj₁
  change dom (-(adjoint X U F₂)) = Set.univ at hdomAdj₂
  have hF₁_slice_convex : ∀ u, (F₁ u).IsConvex ℝ := hF₁.convex.slice_uncurry
  have hF₂_slice_convex : ∀ u, (F₂ u).IsConvex ℝ := hF₂.convex.slice_uncurry
  have hdom : dom (F₁ D F₂) = Set.univ := by
    rw [dom_infimalConvolution_eq_inter hF₁_slice_convex hF₂_slice_convex, hdom₁, hdom₂,
      Set.univ_inter]
  refine (isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ hclosed).2 ?_
  refine ⟨hdom, ?_⟩
  change dom (-(adjoint X U (F₁ D F₂))) = Set.univ
  sorry

end

end Bifunction
