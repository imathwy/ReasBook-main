import Mathlib
import stacks_project.Chap18.Lemma_18_28_11
import stacks_project.Chap17.Lemma_17_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.17.10:
- primary domain: exact right-augmented sequences of `\mathcal O_X`-modules on a ringed space and
  preservation of that exactness under tensoring on the right;
- sampled owner declarations:
  `SheafOfModules.RingedSite.RightAugmentedExact`,
  `SheafOfModules.RingedSite.rightAugmentedExact_tensor_right_of_flat`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.isFlat_iff_stalkwise`;
- best owner abstraction: the ambient exactness package is already owned by
  `RightAugmentedExact`, while flatness remains owned by `IsFlat X.sheaf`; the target lemma should
  therefore be the ringed-space specialization of the owner theorem
  `rightAugmentedExact_tensor_right_of_flat`, not a second conjunction-shaped API;
- primitive data: the family `ℱ`, the differentials `d`, the augmentation `q`, and the single
  owner hypothesis `hExact : RightAugmentedExact ℱ d 𝒬 q`;
- derived API: the ringed-space recall/use of the owner theorem, plus the stalkwise flatness
  bridge theorem below.

Source/core/bridge triage:
- `source-facing`: the right-augmented exact sequence
  `\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`;
- `core/canonical`: `RightAugmentedExact`, `rightAugmentedExact_tensor_right_of_flat`,
  `sheafModuleTensorRightFunctor`, and `IsFlat X.sheaf`;
- `bridge/view`: the stalkwise flatness reformulation used only in the companion theorem.
-/

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (ℱ : ℕ → X.Modules)
variable (d : ∀ n : ℕ, ℱ (n + 1) ⟶ ℱ n)
variable {𝒬 𝒢 : X.Modules}
variable (q : ℱ 0 ⟶ 𝒬)

-- Proof sketch: this is the ringed-space specialization of the site-level owner theorem
-- `rightAugmentedExact_tensor_right_of_flat`.
/-- Lemma 17.17.10: if
`\cdots \to \mathcal F_2 \to \mathcal F_1 \to \mathcal F_0 \to \mathcal Q \to 0`
is an exact right-augmented sequence of flat `\mathcal O_X`-modules on a ringed space, then
tensoring on the right with any `\mathcal O_X`-module again yields an exact right-augmented
sequence. -/
theorem rightAugmentedExact_moduleTensorRight_of_isFlat
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : IsFlat X.sheaf 𝒬)
    (hflatℱ : ∀ n : ℕ, IsFlat X.sheaf (ℱ n)) :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := by
  letI : IsFlat X.sheaf 𝒬 := hflat𝒬
  letI : ∀ n : ℕ, IsFlat X.sheaf (ℱ n) := hflatℱ
  simpa using rightAugmentedExact_tensor_right_of_flat ℱ d q hExact

/-- Companion bridge: the stalkwise flatness hypotheses from the textbook formulation imply the
canonical flatness-owner hypotheses used by
`rightAugmentedExact_moduleTensorRight_of_isFlat`. -/
theorem rightAugmentedExact_moduleTensor_right_of_flat_stalkwise
    (hExact : RightAugmentedExact ℱ d 𝒬 q)
    (hflat𝒬 : ∀ x : X, 𝒬.flat_at x)
    (hflatℱ : ∀ n : ℕ, ∀ x : X, (ℱ n).flat_at x) :
    RightAugmentedExact
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).obj (ℱ n))
      (fun n ↦ (sheafModuleTensorRightFunctor 𝒢).map (d n))
      ((sheafModuleTensorRightFunctor 𝒢).obj 𝒬)
      ((sheafModuleTensorRightFunctor 𝒢).map q) := by
  simpa using
    rightAugmentedExact_moduleTensorRight_of_isFlat ℱ d q hExact
      ((SheafOfModules.isFlat_iff_stalkwise 𝒬).2 hflat𝒬)
      (fun n ↦ (SheafOfModules.isFlat_iff_stalkwise (ℱ n)).2 (hflatℱ n))

end AlgebraicGeometry.RingedSpace
