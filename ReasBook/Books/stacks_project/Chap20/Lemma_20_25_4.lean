import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 20.25.4:
- primary domain: compatibility between cohomological connecting morphisms, Čech cup products,
  and the total-complex sign rule;
- sampled owner declarations:
  `CategoryTheory.DeltaFunctor.connectingMorphism`,
  `AlgebraicGeometry.RingedSpace.ringedSpaceCechCohomologyConnectingMorphism`,
  `tensorObj_d_on_summand_eq`,
  `Functor.LaxMonoidal.μ`;
- best owner abstraction:
  `source-facing`: the signed boundary-cup compatibility relation itself;
  `core/canonical`: the connecting-morphism owners
    `CategoryTheory.DeltaFunctor.connectingMorphism` and
    `AlgebraicGeometry.RingedSpace.ringedSpaceCechCohomologyConnectingMorphism`, together with
    the total-complex differential formula `tensorObj_d_on_summand_eq` and the total Čech tensor
    comparison `Functor.LaxMonoidal.μ`;
  `bridge/view`: the theorem below, stated only in terms of the resulting boundary maps and cup
    pairings, without a parallel packaging wrapper.
- primitive data: the graded families `F₁`, `F₃`, `G₁`, `G₃`, `H` together with the two boundary
  maps and the two cup-product pairings.
- derived API: the signed boundary-cup compatibility statement below.

Source/core/bridge triage:
- `source-facing`: the textbook sign relation between the two ways of combining boundary maps and
  cup products;
- `core/canonical`: the chapter owners for connecting morphisms and total-complex tensor signs;
- `bridge/view`: this lemma, specialized to the source data and stated directly without a parallel
  setup wrapper.
-/

universe u

section

variable {F₁ F₃ G₁ G₃ H : ℕ → Type u}
variable [∀ k : ℕ, SMul ℤ (H k)]
variable
  (boundaryF : ∀ ⦃n : ℕ⦄, F₃ n → F₁ (n + 1))
  (boundaryG : ∀ ⦃m : ℕ⦄, G₁ m → G₃ (m + 1))
  (gamma₁ : ∀ ⦃n m : ℕ⦄, F₁ (n + 1) → G₁ m → H (n + m + 1))
  (gamma₃ : ∀ ⦃n m : ℕ⦄, F₃ n → G₃ (m + 1) → H (n + m + 1))

-- Proof sketch: in the source application, the comparison hypotheses identifying the abstract
-- boundary maps and cup products with the corresponding Čech and sheaf-cohomology constructions
-- are established upstream. After making those identifications, choose Čech cocycle
-- representatives for `a₃` and `b₁`, lift them to the middle terms of the two short exact
-- sequences, identify the resulting boundaries with representatives of `∂ a₃` and `∂ b₁`, and
-- apply the total-complex Leibniz rule
-- `d(α₂ ∪ β₂) = d α₂ ∪ β₂ + (-1)^n α₂ ∪ d β₂`.
/-- Lemma 20.25.4: after identifying the source boundary maps and cup products with the abstract
data `boundaryF`, `boundaryG`, `gamma₁`, and `gamma₃`, the pairing obtained from `γ₁` after taking
the boundary on the `\mathcal F`-side equals `(-1)^(n + 1)` times the pairing obtained from `γ₃`
after taking the boundary on the `\mathcal G`-side. -/
theorem gamma_boundary_cup_eq_signed_gamma_cup_boundary
    {n m : ℕ} (a₃ : F₃ n) (b₁ : G₁ m) :
    gamma₁ (boundaryF a₃) b₁ =
      ((-1 : ℤ) ^ (n + 1)) • gamma₃ a₃ (boundaryG b₁) := sorry

end
