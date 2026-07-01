import Mathlib
import stacks_project.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.24.1:
- primary domain: module-valued Čech resolutions on a ringed space, built from restriction to
  open subspaces and pushforward back to the ambient space;
- sampled owner declarations:
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `restrictedRingedSpaceModule`,
  `ringedSpaceModulePushforwardFromOpen`,
  `cechIntersection`;
- best owner abstraction: the ambient module category
  `SheafOfModules ((RingedSpace.ringCatSheaf X))` together with the chapter-level open-subspace
  owners `restrictedRingedSpaceModule` and `ringedSpaceModulePushforwardFromOpen`.

Primitive data is only the ringed space `X`, the open family `𝒰`, and the module `ℱ`. The
open-subspace structure-sheaf map and the low-level pullback/pushforward functors are derived
bridge data from that owner API, so they should not remain primitive public declarations in this
file.

Source/core/bridge triage:
- `source-facing`: `openCoverModuleCechTerm` and the existence of the Čech resolution;
- `core/canonical`: `ringedSpaceRingCatSheaf`, `restrictedRingedSpaceModule`,
  `ringedSpaceModulePushforwardFromOpen`, `cechIntersection`;
- `bridge/view`: `openCoverModuleCechTerm`, which applies the canonical open-subspace owners to
  Čech intersections. -/

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ModX" => SheafOfModules ((RingedSpace.ringCatSheaf X))

/-- The degree-`p` term expected in the module-valued Čech resolution of `ℱ` for the open cover
`𝒰`. -/
abbrev openCoverModuleCechTerm (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ) :
    ModX :=
  piObj fun σ : Fin (p + 1) → ι ↦
    (AlgebraicGeometry.ringedSpaceModulePushforwardFromOpen (cechIntersection 𝒰 σ)).obj
      (AlgebraicGeometry.restrictedRingedSpaceModule (cechIntersection 𝒰 σ) ℱ)

-- Proof sketch: form the usual Čech cochain complex of `ℱ` with respect to `𝒰`, whose
-- degree-`p` term is the product over all `(p + 1)`-fold intersections of the pushforward of the
-- restriction of `ℱ` from that intersection. The canonical augmentation from `ℱ` to this complex
-- is a quasi-isomorphism because `𝒰` is an open cover of `X`.
/-- Lemma 20.24.1: for a ringed space `X`, an open cover `𝒰`, and an `\mathcal O_X`-module
`\mathcal F`, there exists a cochain complex of `\mathcal O_X`-modules and a canonical
augmentation from `\mathcal F` whose degree-`p` term is the product of the pushforwards
`(j_{i_0 \ldots i_p})_* \mathcal F_{i_0 \ldots i_p}` over all `(p + 1)`-fold intersections of the
cover, and this augmentation is a quasi-isomorphism. -/
theorem openCoverModuleCechResolution_exists
    (𝒰 : ι → Opens X.carrier) (h𝒰 : IsOpenCover 𝒰) (ℱ : ModX) :
    ∃ (C : CochainComplex ModX ℕ)
      (η : (CochainComplex.single₀ ModX).obj ℱ ⟶ C)
      (e : ∀ p : ℕ, C.X p ≅ openCoverModuleCechTerm 𝒰 ℱ p),
        QuasiIso η := sorry

end AlgebraicGeometry.RingedSpace
