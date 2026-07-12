import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: the affine module-sheaf owner is `ModuleCat.tilde`, and the canonical affine
-- global-sections comparison is `tilde.isoTop`. This file keeps `tilde` as the public owner on
-- `Spec(R)` and adds the source-facing companion lemmas for Lemma 26.7.1.
/- Source/core/bridge triage:
- `source-facing`: the affine associated module sheaf `\widetilde M`, its functoriality in
  `M`, and the affine adjunction transpose against global sections on `Spec(R)`.
- `core/canonical`: `tilde.functor`, `tilde`, `tilde.adjunction`, `tilde.isoTop`, and
  `moduleSpecΓFunctor`.
- `bridge/view`: the quasi-coherence statement and the source-facing transpose formulas below. -/

section

variable (R : CommRingCat.{u}) (M : ModuleCat R)

/- Lemma 26.7.1 (1) and (2): on `Spec(R)`, the associated-module-sheaf construction
`M ↦ \mathcal F_M` is the canonical affine functor `M ↦ \widetilde M`, namely
`AlgebraicGeometry.tilde.functor R`. -/
recall tilde.functor
recall tilde

section

variable {N : ModuleCat R} (f : M ⟶ N)

/- Lemma 26.7.1 (2): a morphism `M ⟶ N` induces the canonical morphism
`\widetilde M ⟶ \widetilde N` via the affine associated-module functor. -/
#check ((tilde.functor R).map f : tilde M ⟶ tilde N)

end

/-- Lemma 26.7.1 (3): for an affine scheme `Spec(R)`, the sheaf `\widetilde M` is
quasi-coherent. -/
@[stacks 01I7]
theorem tildeIsQuasicoherent :
    (tilde M).IsQuasicoherent := by
  infer_instance

variable (ℱ : (Spec R).Modules)

/- Lemma 26.7.1 (4): the source-facing description of the affine adjunction transpose is the
specialization of the canonical unit formula `Adjunction.homEquiv_unit`, with affine comparison
isomorphism `tilde.isoTop M`. -/
recall tilde.adjunction
recall tilde.isoTop

@[simp] theorem tildeIsoTop_hom_eq_unit :
    (tilde.isoTop M).hom = (unit tilde.adjunction).app M := by
  rfl

/- Lemma 26.7.1 (4): the affine adjunction `\widetilde{(-)} \dashv \Gamma` on `Spec(R)` identifies
a morphism `\widetilde M ⟶ ℱ` with the induced map on global sections, precomposed with the
canonical affine global-sections comparison morphism `(tilde.isoTop M).hom`, equivalently the
unit morphism `M ⟶ Γ(Spec(R), \widetilde M)` whose isomorphism form is `tilde.isoTop M`. -/
@[stacks 01I7, simp]
theorem tildeAdjunction_homEquiv_apply
    (φ : tilde M ⟶ ℱ) :
    tilde.adjunction.homEquiv M ℱ φ =
      (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map φ := by
  simpa [tildeIsoTop_hom_eq_unit R M] using
    tilde.adjunction.homEquiv_unit φ

end

end AlgebraicGeometry
