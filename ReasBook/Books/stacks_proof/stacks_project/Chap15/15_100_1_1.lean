import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')

open scoped DerivedTensorWithAlgebra

/- Domain-style sampling for 15.100.1.1:
- primary domain: derived base change for internal Hom on derived module categories;
- sampled owner declarations:
  `Adjunction.rightAdjointUniq`,
  `ihom.adjunction`,
  `MonoidalCategory.tensorLeft`,
  `ihom`;
- best owner abstraction:
  `source-facing`: the base-change arrow
    `R\mathrm{Hom}_R(K, M) \otimes_R^{\mathbf L} R' \to
      R\mathrm{Hom}_{R'}(K \otimes_R^{\mathbf L} R', M \otimes_R^{\mathbf L} R')`;
  `core/canonical`: the right-adjoint uniqueness component comparing any right adjoint to
    left tensoring by `K ⊗[R]^L[R']` with the canonical internal-Hom right adjoint
    `ihom (K ⊗[R]^L[R'])`;
  `bridge/view`: the chapter notation `K ⊗[R]^L[R']`, which keeps the tensor factor in the
    source-facing base-change surface.
- primitive data: the ring map `R → R'`, the base-changed object `K ⊗[R]^L[R']`, the candidate
  right adjoint `G`, its adjunction witness `adj`, the target object `M`, and the ambient
  monoidal/closed structure on `D(R')`;
- derived API: the displayed target-ring internal-Hom codomain, obtained by the canonical
  right-adjoint uniqueness comparison.

Source/core/bridge triage:
- `source-facing`: the displayed internal-Hom base-change arrow;
- `core/canonical`: `adj.rightAdjointUniq (ihom.adjunction (K ⊗[R]^L[R']))`;
- `bridge/view`: this file keeps the displayed `⊗[R]^L[R']` presentation of the tensor factor
  in the codomain-rewrite morphism.
-/

/- Companion recalls: the source-facing base-change comparison is paired with the canonical
codomain rewrite obtained from right-adjoint uniqueness for internal Hom on `D(R')`. -/
recall Adjunction.rightAdjointUniq
recall ihom.adjunction
recall ihom

/- 15.100.1.1 is the bridge/view layer: it records the canonical codomain-rewrite morphism that
identifies a chosen right adjoint to tensoring by `K ⊗[R]^L[R']` with the target-ring internal
Hom object. This upgrades the previous hom-type-only surface to the actual comparison morphism. -/
/-- Helper for 15.100.1.1: any chosen right adjoint to tensoring by `K ⊗[R]^L[R']` is canonically
isomorphic to the internal-Hom functor `ihom (K ⊗[R]^L[R'])`. -/
noncomputable def derivedInternalHom_baseChange_rightAdjoint_iso
    [MonoidalCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorLeft (K ⊗[R]^L[R']) ⊣ G) :
    G ≅ ihom (K ⊗[R]^L[R']) :=
  -- The source-faithful route uses uniqueness of right adjoints for tensor-left by
  -- `K ⊗[R]^L[R']`, without unfolding the internal Hom.
  adj.rightAdjointUniq (ihom.adjunction (K ⊗[R]^L[R']))

/-- 15.100.1.1: the canonical base-change codomain comparison morphism from any chosen right
adjoint to tensoring by `K ⊗[R]^L[R']` to the target-ring internal-Hom object is the component of
the right-adjoint uniqueness isomorphism at `M`. -/
@[stacks 0E1X]
noncomputable def derivedInternalHom_baseChange_codomain_comparison
    [MonoidalCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorLeft (K ⊗[R]^L[R']) ⊣ G) (M : DModR') :
    G.obj M ⟶ (ihom (K ⊗[R]^L[R'])).obj M :=
  -- The displayed base-change arrow is the pointwise `hom` of the canonical functor isomorphism.
  ((derivedInternalHom_baseChange_rightAdjoint_iso (R := R) (R' := R') K G adj).app M).hom

/-- Helper for 15.100.1.1: the codomain comparison morphism is an isomorphism because it is the
component of a natural isomorphism. -/
theorem derivedInternalHom_baseChange_codomain_comparison_isIso
    [MonoidalCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorLeft (K ⊗[R]^L[R']) ⊣ G) (M : DModR') :
    IsIso (derivedInternalHom_baseChange_codomain_comparison (R := R) (R' := R') K G adj M) := by
  let e := (derivedInternalHom_baseChange_rightAdjoint_iso (R := R) (R' := R') K G adj).app M
  -- The comparison map is literally the `hom` field of the component isomorphism `e`.
  simpa [derivedInternalHom_baseChange_codomain_comparison, e] using
    (inferInstance : IsIso e.hom)

end

end CategoryTheory
