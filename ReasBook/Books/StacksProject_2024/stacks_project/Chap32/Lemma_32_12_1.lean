import StacksProject_2024.Chap30.Lemma_30_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners `IsProper`
-- and `IsImmersion`. Local Chapter 30 precedent represents `\mathbf P^n_S` by
-- `Scheme.IsProjectiveBundle` over the finite free module on `Fin (n + 1)`.

/-- A witness for the qcqs variant of Chow's lemma: a scheme `X'`, a proper surjective morphism
`π : X' ⟶ X`, and an immersion of `X'` into a relative projective space over `S` compatible with
the two maps to `S`. -/
@[stacks 0202]
structure ChowLemmaQcqsModification {X S : Scheme.{u}} (f : X ⟶ S) where
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

/-- Lemma 32.12.1: if `S` is quasi-compact and quasi-separated and `f : X ⟶ S` is separated
and of finite type, then there is a diagram
`X ← X' → \mathbf P^n_S → S` in which `X' ⟶ \mathbf P^n_S` is an immersion and
`π : X' ⟶ X` is proper and surjective. -/
@[stacks 0202]
theorem exists_projectiveSpaceImmersion_proper_surjective_of_separated_finiteType_qcqs
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    Nonempty (ChowLemmaQcqsModification f) := sorry

end AlgebraicGeometry
