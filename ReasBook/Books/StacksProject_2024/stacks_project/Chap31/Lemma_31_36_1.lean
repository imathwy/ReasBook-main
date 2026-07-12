import StacksProject_2024.Chap06.RingedSpaceModuleCore
import StacksProject_2024.Chap12.Aux_12_20_2_1
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap29.Definition_29_41_1
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` found only general module pullback and local-freeness
-- hints. Local Stacks files use `Scheme.Modules.pullback` for `f^*`, `IsBirational` and
-- `IsProper` for the available modification clauses, and finite locally free rank-one modules
-- as the scheme-module formulation of line-bundle quotients.

/-- A proper birational morphism whose pullback of `E` has a finite filtration with invertible
successive quotients, represented as finite locally free rank-one subquotients. -/
@[stacks 0AYP]
class ProperBirationalPullbackLineBundleQuotientFiltration
    {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] (f : X' ⟶ X) (E : X.Modules) :
    Prop where
  /-- The morphism is birational. -/
  isBirational : IsBirational f
  /-- The morphism is proper. -/
  isProper : IsProper f
  /-- The pulled-back module admits the requested finite filtration. -/
  exists_filtration :
    ∃ s : RelSeries {FG : Subobject ((Scheme.Modules.pullback f).obj E) ×
        Subobject ((Scheme.Modules.pullback f).obj E) |
      ∃ hFG : FG.1 ≤ FG.2,
        SheafOfModules.IsFiniteLocallyFreeOfRank 1
          (subobjectSubquotient hFG : X'.Modules)},
      s.head = ⊥ ∧ s.last = ⊤

/-- The pullback line-bundle quotient filtration property is equivalent to the source clauses:
birationality, properness, and existence of the finite filtration with rank-one quotients. -/
@[stacks 0AYP]
theorem properBirationalPullbackLineBundleQuotientFiltration_iff
    {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] (f : X' ⟶ X) (E : X.Modules) :
    ProperBirationalPullbackLineBundleQuotientFiltration f E ↔
      ∃ (_ : IsBirational f) (_ : IsProper f),
        ∃ s : RelSeries {FG : Subobject ((Scheme.Modules.pullback f).obj E) ×
            Subobject ((Scheme.Modules.pullback f).obj E) |
          ∃ hFG : FG.1 ≤ FG.2,
            SheafOfModules.IsFiniteLocallyFreeOfRank 1
              (subobjectSubquotient hFG : X'.Modules)},
          s.head = ⊥ ∧ s.last = ⊤ := sorry

/-- Lemma 31.36.1: let `X` be an integral scheme and let `\mathcal E` be a finite locally free
`\mathcal O_X`-module. There is an integral proper birational model `f : X' ⟶ X` such that
`f^*\mathcal E` admits a finite filtration whose successive quotients are invertible
`\mathcal O_{X'}`-modules, here represented as finite locally free rank-one quotients. -/
@[stacks 0AYP]
theorem exists_proper_birational_pullback_lineBundle_quotient_filtration
    (X : Scheme.{u}) [IsIntegral X] (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree E] :
    ∃ (X' : Scheme.{u}) (_ : IsIntegral X') (f : X' ⟶ X),
      ProperBirationalPullbackLineBundleQuotientFiltration f E := sorry

end AlgebraicGeometry.Scheme.Modules
