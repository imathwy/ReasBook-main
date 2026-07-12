import StacksProject_2024.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {K : Type u} [Field K] [Algebra k K]
variable {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k))

/- Refine triage:
* `source-facing`: Lemma 31.6.5 is the descent statement for weakly associated points under the
  field-extension projection `X_K → X`.
* `core/canonical`: the field-extension scheme is the pullback of `f` along `Spec.map`, and
  module pullback is the owner `Scheme.Modules.pullback`, used below through the Chapter 31
  pullback notation.
* `bridge/view`: `weaklyAssociatedAt` stays as a pointwise companion to the `weakAss` membership
  theorem. -/

local notation "ι" => Spec.map (CommRingCat.ofHom (algebraMap k K))
local notation "XK" => pullback f ι
local notation "π" => pullback.fst f ι
local notation:max π:max "^*" => Scheme.Modules.pullback π

/-- Lemma 31.6.5: let `K/k` be a field extension, let `X` be a scheme over `k`, and let
`\mathcal F` be a quasi-coherent `\mathcal O_X`-module. If `y ∈ X_K` is weakly associated to the
pullback `\mathcal F_K`, then its image in `X` is weakly associated to `\mathcal F`. -/
@[stacks 0CUC]
theorem mem_weakAss_of_mem_weakAss_pullback_fieldExtension
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (y : XK)
    (hy : y ∈ ((π^*).obj ℱ).weakAss) :
    π y ∈ ℱ.weakAss := sorry

/-- Lemma 31.6.5 in pointwise form: weak association on the field-extension pullback descends
along the projection `X_K → X`. -/
theorem weaklyAssociatedAt_of_pullback_fieldExtension
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (y : XK)
    (hy : ((π^*).obj ℱ).weaklyAssociatedAt y) :
    ℱ.weaklyAssociatedAt (π y) := by
  simpa [mem_weakAss_iff] using
    mem_weakAss_of_mem_weakAss_pullback_fieldExtension f ℱ y <|
      by simpa [mem_weakAss_iff] using hy

end AlgebraicGeometry.Scheme.Modules
