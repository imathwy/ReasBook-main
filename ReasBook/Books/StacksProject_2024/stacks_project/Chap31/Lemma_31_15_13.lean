import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Definition_17_25_6
import StacksProject_2024.Chap17.Lemma_17_21_1
import StacksProject_2024.Chap31.Definition_31_12_1
import StacksProject_2024.Chap31.Definition_31_13_1
import StacksProject_2024.Chap31.Definition_31_14_1
import StacksProject_2024.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat SheafOfModules.RingedSite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: Chapter 17/31 already owns the source-facing ingredients needed here: the top
-- exterior power `Λ^[r] ℱ`, the reflexive hull `reflexiveHull`, the effective Cartier divisor
-- associated sheaf `effectiveCartierDivisorAssociatedSheaf`, the ideal-sheaf owner
-- `closedImmersionIdealSubobject`, and the integral tensor-power notation `^⊗`.

section

variable {X Z : Scheme.{u}}
variable [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [MonoidalCategory X.toRingedSpace.Modules]
variable [BraidedCategory X.Modules]
variable [SymmetricCategory X.Modules] [MonoidalClosed X.Modules]

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertibleX" => (fun ℒ : ModX ↦ Functor.IsEquivalence (tensorRight ℒ))
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪X ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

/-- Helper for Lemma 31.15.13: the reflexive determinant line `(∧^r \mathcal F)^{**}` attached to
the rank-`r` exterior power of a coherent `\mathcal O_X`-module `\mathcal F`. -/
abbrev reflexiveTopExteriorPower (r : ℕ) (ℱ : ModX) : ModX :=
  reflexiveHull (Λ^[r] ℱ)

/-- Companion expansion for `reflexiveTopExteriorPower`. -/
theorem reflexiveTopExteriorPower_def (r : ℕ) (ℱ : ModX) :
    reflexiveTopExteriorPower r ℱ = reflexiveHull (Λ^[r] ℱ) :=
  rfl

/-- Helper for Lemma 31.15.13: on an integral locally Noetherian scheme whose stalks are regular
and whose topological Krull dimension is at most `2`, the reflexive determinant line attached to a
coherent module that is finite locally free of rank `r` on a nonempty open is invertible. -/
theorem isInvertible_reflexiveTopExteriorPower_of_nonempty_open_isFiniteLocallyFreeOfRank
    (r : ℕ) (ℱ : ModX) [ℱ.IsCoherent]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X ≤ 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)] :
    IsInvertibleX (reflexiveTopExteriorPower r ℱ) := sorry

/-- Lemma 31.15.13 (1): under the divisor-quotient hypotheses, the reflexive determinant line
`(\bigwedge^r \mathcal F)^{**}` is invertible. -/
@[stacks 0B3T]
theorem source_reflexiveTopExteriorPower_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward
    (i : Z ⟶ X)
    [IsEffectiveCartierDivisor i]
    [IsIntegral Z]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject i))]
    (ℱ ℱ' : ModX) (𝒢 : Z.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    [((RingedSpace.Hom.pushforward i.toShHom).obj 𝒢).IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (RingedSpace.Hom.pushforward i.toShHom).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact)
    [Epi ψ]
    (r s : ℕ)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    IsInvertibleX (reflexiveTopExteriorPower r ℱ) := sorry

/-- Lemma 31.15.13 (2): under the divisor-quotient hypotheses, the reflexive determinant line
`(\bigwedge^r \mathcal F')^{**}` is invertible. -/
@[stacks 0B3T]
theorem target_reflexiveTopExteriorPower_isInvertible_of_exact_to_effectiveCartierDivisor_pushforward
    (i : Z ⟶ X)
    [IsEffectiveCartierDivisor i]
    [IsIntegral Z]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject i))]
    (ℱ ℱ' : ModX) (𝒢 : Z.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    [((RingedSpace.Hom.pushforward i.toShHom).obj 𝒢).IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (RingedSpace.Hom.pushforward i.toShHom).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact)
    [Epi ψ]
    (r s : ℕ)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    IsInvertibleX (reflexiveTopExteriorPower r ℱ') := sorry

/-- Lemma 31.15.13 (3): under the divisor-quotient hypotheses, there exists
`k \in \{0,\ldots,\min(s,r)\}` such that `(\bigwedge^r \mathcal F')^{**}` is isomorphic to
`(\bigwedge^r \mathcal F)^{**} \otimes \mathcal O_X(D)^{\otimes k}`. -/
@[stacks 0B3T]
theorem exists_twist_iso_reflexiveTopExteriorPower_of_exact_to_effectiveCartierDivisor_pushforward
    (i : Z ⟶ X)
    [IsEffectiveCartierDivisor i]
    [IsIntegral Z]
    [Fact (EffectiveCartierIdeal (closedImmersionIdealSubobject i))]
    (ℱ ℱ' : ModX) (𝒢 : Z.Modules)
    [ℱ.IsCoherent] [ℱ'.IsCoherent]
    [((RingedSpace.Hom.pushforward i.toShHom).obj 𝒢).IsCoherent]
    (φ : ℱ ⟶ ℱ')
    (ψ : ℱ' ⟶ (RingedSpace.Hom.pushforward i.toShHom).obj 𝒢)
    (hφψ : φ ≫ ψ = 0)
    (hExact : (ShortComplex.mk φ ψ hφψ).Exact)
    [Epi ψ]
    (r s : ℕ)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : topologicalKrullDim X = 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ'.over U)]
    [SheafOfModules.IsFiniteLocallyFreeOfRank s 𝒢] :
    ∃ k : ℕ, k ≤ Nat.min s r ∧
      Nonempty
        (reflexiveTopExteriorPower r ℱ' ≅
          ((reflexiveTopExteriorPower r ℱ) ⊗ₘ
            (effectiveCartierDivisorAssociatedSheaf
              (closedImmersionIdealSubobject i) ^⊗ (k : ℤ)))) := sorry

end

end AlgebraicGeometry.Scheme.Modules
