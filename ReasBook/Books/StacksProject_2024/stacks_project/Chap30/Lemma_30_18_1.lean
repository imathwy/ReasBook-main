import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap31.Definition_31_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`lean_leansearch` recalled the canonical scheme-morphism owners `IsProper`, `IsSeparated`, plus
`LocallyOfFiniteType` and `IsImmersion`. Local Chapter 29 precedent uses `Scheme.Hom.FiniteType f`
for finite-type morphisms; this file records `\mathbf P^n_S` directly through the lower-level
`Scheme.IsProjectiveBundle` owner over the finite free module, keeping the statement independent
of the Chapter 29 `ProjectiveSpaceOver` wrapper. The Stacks tag evidence is consistent: item tag
`0200` agrees with the source URL ending in `/tag/0200`.
-/

/-- A witness for the diagram in Chow's lemma: a scheme `X'`, a proper surjective morphism
`π : X' ⟶ X`, an immersion into a relative projective space over `S`, plus a dense open over which
`π` is an isomorphism. -/
@[stacks 0200]
structure ChowLemmaModification {X S : Scheme.{u}} (f : X ⟶ S) where
  n : ℕ
  P : Scheme.{u}
  p : P ⟶ S
  isProjectiveSpace :
    Scheme.IsProjectiveBundle p
      (SheafOfModules.free.{u} (ULift.{u} (Fin (n + 1))) : S.Modules)
  X' : Scheme.{u}
  π : X' ⟶ X
  i : X' ⟶ P
  isImmersion : IsImmersion i
  commutes : i ≫ p = π ≫ f
  proper : IsProper π
  surjective : Surjective π
  denseOpen : X.Opens
  denseOpenDense : Dense (denseOpen : Set X)
  isIsoOverDenseOpen : IsIso (π ∣_ denseOpen)

namespace ChowLemmaModification

variable {X S : Scheme.{u}} {f : X ⟶ S} (M : ChowLemmaModification f)

/-- The map from a Chow lemma modification to the original scheme is proper. -/
instance instIsProperPi : IsProper M.π :=
  M.proper

/-- The map from a Chow lemma modification to the original scheme is surjective. -/
instance instSurjectivePi : Surjective M.π :=
  M.surjective

end ChowLemmaModification

/-- Lemma 30.18.1: Chow's lemma for a separated finite-type morphism over a Noetherian scheme.
If `f : X ⟶ S` is separated, finite type, with `S` Noetherian, then after replacing `X` by a proper
surjective morphism `π : X' ⟶ X`, the scheme `X'` admits an immersion into some relative
projective space `\mathbf P^n_S` over `S`. Moreover `π` can be chosen to be an isomorphism over a
dense open subscheme of `X`. -/
@[stacks 0200]
theorem exists_projectiveSpaceImmersion_proper_surjective_of_separated_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] :
    Nonempty (ChowLemmaModification f) := sorry

end AlgebraicGeometry
