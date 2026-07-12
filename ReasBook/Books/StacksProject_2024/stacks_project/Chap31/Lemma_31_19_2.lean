import StacksProject_2024.Chap10.«10_69_0_1_Core»

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Lemma 31.19.2 identifies the conormal algebra on an affine chart with the
  associated graded ring of the ideal cutting out the closed subscheme on that chart.
- `core/canonical`: the Chapter 10 owner `idealAssociatedGradedRing I`.
- `bridge/view`: the affine-open kernel ideal `ker(Γ(X, U) → Γ(Z, i ⁻¹ᵁ U))` and the resulting
  affine-local conormal algebra used by Lemmas 31.19.3 and 31.19.4.

The scheme-level owner `Scheme.ConormalAlgebra` is introduced elsewhere in Chapter 31. This file
keeps the affine chart model that the later affine comparison lemmas use directly.
-/

/-- The kernel ideal of the affine-open section map `Γ(X, U) → Γ(Z, i ⁻¹ᵁ U)`, used for an
immersion chart to cut out `Z ∩ U` inside `U`. -/
abbrev immersionAffineConormalIdeal
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) : Ideal (Γ(X, U)) :=
  RingHom.ker (i.app U).hom

/-- Lemma 31.19.2: on an affine chart `U ⊆ X` where an immersion `i : Z ⟶ X` is represented by
the closed subscheme cut out by the kernel ideal of the section map
`Γ(X, U) → Γ(Z, i ⁻¹ᵁ U)`, the affine chart of the conormal algebra is the associated graded ring
`⊕_{n ≥ 0} I^n / I^(n + 1)`. In the current project this affine-local bridge is recorded by the
canonical owner `idealAssociatedGradedRing I`. -/
abbrev immersionAffineConormalAlgebra
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) : Type u :=
  idealAssociatedGradedRing (immersionAffineConormalIdeal i U)

end

end AlgebraicGeometry
