import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme`; local
-- Chapter 30 precedent represents coherent subsheaves as `Subobject ℱ`, integral closed
-- subschemes as `X.IdealSheafData`, ideal sheaves as subobjects of the unit module, and direct
-- images along closed subschemes by `Scheme.Modules.pushforward`.

/-- Lemma 30.12.3: on a Noetherian scheme, every coherent `\mathcal O_X`-module has a finite
filtration by coherent submodules whose successive quotients are pushforwards of nonzero coherent
ideal sheaves on integral closed subschemes. The index `j : Fin m` records the source quotient
`\mathcal F_{j+1}/\mathcal F_j`. -/
@[stacks 01YF]
theorem exists_coherentSubobject_filtration_quotient_iso_pushforward_ideal
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ∃ (m : ℕ) (F : ℕ →o Subobject ℱ)
      (Z : Fin m → X.IdealSheafData)
      (I : (j : Fin m) →
        Subobject (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules))
      (e : (j : Fin m) →
        cokernel (Subobject.ofLE (F j.1) (F (j.1 + 1)) (F.monotone (Nat.le_succ j.1))) ≅
          (Scheme.Modules.pushforward (Z j).subschemeι).obj
            (Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)),
      ∃ (hBot : F 0 = ⊥) (hTop : F m = ⊤)
        (hFiltrationCoherent :
          ∀ n : ℕ, n ≤ m → ((F n : Subobject ℱ) : X.Modules).IsCoherent)
        (hIntegral : ∀ j : Fin m, IsIntegral (Z j).subscheme)
        (hIdealCoherent : ∀ j : Fin m,
          ((Subobject.underlying.obj (I j) : (Z j).subscheme.Modules)).IsCoherent),
        ∀ j : Fin m,
          I j ≠ (⊥ : Subobject
            (SheafOfModules.unit (Z j).subscheme.ringCatSheaf : (Z j).subscheme.Modules)) := sorry

end AlgebraicGeometry.Scheme.Modules
