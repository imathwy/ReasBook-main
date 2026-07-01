import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

/- Domain-style sampling for spectral spaces as directed inverse limits of finite sober spaces:
- primary domain: spectral spaces, preorder-indexed inverse systems in `TopCat`, and categorical
  limits;
- sampled owner declarations:
  `SpectralSpace`,
  `limit`,
  `CategoryTheory.orderDualEquivalence`,
  `spectralSpace_of_limit_finite_sober_inverse_system`;
- best owner abstraction: the inverse-system owner data are the preorder-dual diagram
  `F : Jᵒᵈ ⥤ TopCat` and the canonical limit object `limit F`, while spectrality itself is owned by
  `SpectralSpace`;
- primitive data: a directed preorder `J`, the inverse system `F`, finite `T₀` stage data, and a
  homeomorphism from `X` to `limit F`;
- derived API: stage quasi-sobriety from the finite `T₀` hypotheses, then spectrality of the limit
  via `spectralSpace_of_limit_finite_sober_inverse_system`.

Source/core/bridge triage:
- `source-facing`: the Stacks characterization of spectral spaces as directed inverse limits of
  finite sober spaces;
- `core/canonical`: `SpectralSpace`, the diagram `F : Jᵒᵈ ⥤ TopCat`, and the limit object
  `limit F`;
- `bridge/view`: the homeomorphism identifying `X` with that canonical limit.
-/

section

variable (X : Type u) [TopologicalSpace X]

-- Proof sketch: for the forward implication, use the Sierpinski-product embedding of
-- Lemma `5.23.13`, descend it to the directed system of finite-coordinate images indexed by the
-- source preorder, and identify `X` with the limit of that system. For the reverse implication,
-- derive quasi-sobriety of each finite `T₀` stage, apply
-- `spectralSpace_of_limit_finite_sober_inverse_system` from Lemma `5.23.12`, and transport the
-- resulting spectral structure across the given homeomorphism.
/-- Lemma 5.23.14: a topological space is spectral if and only if it is homeomorphic to the limit
of a directed inverse system of finite sober topological spaces. -/
theorem spectralSpace_iff_homeomorphic_directed_limit_finite_sober :
    SpectralSpace X ↔
      ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirectedOrder J)
        (F : Jᵒᵈ ⥤ TopCat.{u}) (_ : ∀ j : Jᵒᵈ, Finite (F.obj j))
        (_ : ∀ j : Jᵒᵈ, T0Space (F.obj j)),
        Nonempty (X ≃ₜ ↥(limit F)) := sorry

end
