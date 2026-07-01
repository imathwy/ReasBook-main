import Mathlib
import stacks_project.Chap13.Definition_13_15_3
import stacks_project.Chap13.Lemma_13_14_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
variable [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
variable [Abelian 𝒜] [Abelian ℬ] [Abelian 𝒞]
variable [HasInjectiveResolutions 𝒜]
variable [HasDerivedCategory.{w} 𝒞]

variable (F : 𝒜 ⥤ ℬ)

variable (G : ℬ ⥤ 𝒞)
variable [F.Additive] [G.Additive]

local notation "QisA" => boundedBelowHomotopyQuasiIso 𝒜
local notation "QisB" => boundedBelowHomotopyQuasiIso ℬ
local notation "KplusF" => mapBoundedBelowHomotopyCategory F
local notation "KplusG" => mapBoundedBelowHomotopyCategoryToDerivedBelow G

/- Domain-style sampling for bounded-below Grothendieck-comparison morphisms:
- primary domain: composition comparisons for right derived functors on bounded-below homotopy and
  derived categories of abelian categories
- sampled owner declarations:
  `Functor.rightDerivedCompComparison`,
  `Functor.rightDerivedCompComparison_fac`,
  `mapBoundedBelowHomotopyCategory`,
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `HasInjectiveResolutions`
- best owner abstraction: the canonical comparison morphism
  `Functor.rightDerivedCompComparison`, specialized to the bounded-below source functors
- primitive data: the source category `𝒜` with injective resolutions, the additive functors `F`,
  `G`, and the three `HasRightDerivedFunctor` instances needed to form the comparison
- derived API: the acyclicity criterion asserting that this canonical comparison is an isomorphism
- layer targeted here: `bridge/view`; this lemma is the bounded-below source-facing criterion, not
  a new owner for the comparison morphism itself
-/

-- Proof sketch: for the forward implication, apply Leray's acyclicity lemma to an injective
-- resolution of each bounded-below complex of `𝒜`, using that every injective term is sent by
-- `F` to a `G`-acyclic object; this identifies the comparison map with an objectwise
-- quasi-isomorphism. For the converse, evaluate the comparison isomorphism on the degree-zero
-- complex of an injective object `I`; since `I` already computes `RF`, the comparison forces
-- `F.obj I` to compute the right derived functor of `G`, hence to be right acyclic.
namespace Functor

/-- Lemma 13.22.1 in bounded-below owner form: assume the canonical bounded-below right derived
functors of `F ⋙ G`, of `F` viewed in `D⁺(ℬ)`, and of `G` are defined. Then the canonical
comparison morphism
`rightDerivedCompComparison QisA QisB KplusF KplusG : R(G \circ F) ⟶ RG ∘ RF`
is an isomorphism if and only if, for every injective object `I` of `𝒜`, the object `F.obj I`
is right acyclic for the bounded-below right derived functor of `G`. -/
theorem rightDerivedCompComparison_isIso_iff
    [Functor.HasRightDerivedFunctor
      (KplusF ⋙ KplusG)
      QisA]
    [Functor.HasRightDerivedFunctor
      (KplusF ⋙
        (boundedBelowHomotopyQuasiIso ℬ).Q)
      QisA]
    [Functor.HasRightDerivedFunctor
      KplusG
      QisB] :
      IsIso (rightDerivedCompComparison QisA QisB KplusF KplusG) ↔
        ∀ (I : 𝒜) [Injective I],
          IsBoundedBelowRightAcyclicForAdditiveFunctor G (F.obj I) := sorry

end Functor

end

end CategoryTheory
