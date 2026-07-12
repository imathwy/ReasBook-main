import Mathlib.FieldTheory.PurelyInseparable.Basic
import StacksProject_2024.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A finite purely inseparable lift of `K / k` whose upper extension becomes separably generated
over the lifted base field. -/
class IsPurelyInseparableLiftWithSeparablyGenerated
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (k' : Type w) [Field k'] [Algebra k k']
    (K' : Type (max v w)) [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] : Prop where
  /-- The top extension in the lift is finite. -/
  finiteDimensional_top : FiniteDimensional K K'
  /-- The top extension in the lift is purely inseparable. -/
  purelyInseparable_top : IsPurelyInseparable K K'
  /-- The base change in the lift is finite. -/
  finiteDimensional_base : FiniteDimensional k k'
  /-- The base change in the lift is purely inseparable. -/
  purelyInseparable_base : IsPurelyInseparable k k'
  /-- After the lift, the total extension is separably generated. -/
  separablyGenerated_top : IsSeparablyGenerated k' K'

-- Proof sketch: choose a separating transcendence basis after passing to the separable closure
-- decomposition from Lemma `9.14.6`. In positive characteristic, adjoin finitely many `p`th
-- roots to the base so that one step of the purely inseparable part descends into the separable
-- closure using Lemma `9.28.2`, reducing the inseparable degree. Induct on that degree.
/-- Lemma 10.42.4: for a finitely generated field extension `K/k`, there exist fields `k'` and
`K'` forming a commutative square of extensions over `k`, with `K' / K` and `k' / k` finite
purely inseparable and `K' / k'` separably generated. -/
theorem exists_purelyInseparable_lift_with_separablyGenerated
    [Algebra.EssFiniteType k K] :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v w)) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := sorry

end
