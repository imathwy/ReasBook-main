import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v w x

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain triage:
- primary domain: finitely generated field extensions, purely inseparable lifts, and reduced tensor
  products over fields;
- core/canonical owner: `Algebra.IsSeparableOver` for the separability side of the lifted
  extension;
- layer split: the lifted fields and tower maps are the source-facing primitive data, while the
  tensor-product map is a bridge/view used only to express the reduced presentation.
-/

-- Proof sketch: apply Lemma `10.42.4` to obtain finite purely inseparable extensions
-- `K' / K` and `k' / k` with `K' / k'` separably generated, then use Lemma `10.44.3` to upgrade
-- separably generatedness to the owner predicate `IsSeparableOver k' K'`.
/-- Lemma 10.45.3 (1): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that `K' / k'` is separable in the sense of
Definition `10.42.1 (2)`. -/
theorem exists_purelyInseparable_lift_with_separable_over
    [EssFiniteType k K] :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k')
      (K' : Type x) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        IsSeparableOver k' K' := sorry

-- Proof sketch: apply Lemma `10.42.4` to obtain the purely inseparable lifts, then invoke
-- Lemma `10.42.2` to identify `K'` with the compositum of the images of `k'` and `K`.
/-- Lemma 10.45.3 (2): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that `K'` is the compositum of the images of `k'`
and `K`. -/
theorem exists_purelyInseparable_lift_with_compositum_top
    [EssFiniteType k K] :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k')
      (K' : Type x) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        (IsScalarTower.toAlgHom k k' K').fieldRange ⊔
          (IsScalarTower.toAlgHom k K K').fieldRange = ⊤ := sorry

-- Proof sketch: apply Lemma `10.42.4` and the compositum description from Lemma `10.42.2`,
-- then use Lemma `10.36.19` to identify the reduced tensor product with a field. The canonical
-- tensor map is surjective onto the compositum, and its kernel is exactly the nilradical.
/-- Lemma 10.45.3 (3): for a finitely generated field extension `K / k`, there exist a finite
purely inseparable extension `K' / K` and a finite purely inseparable extension `k' / k`
equipped with compatible maps into `K'` such that the canonical `k'`-algebra map
`k' ⊗[k] K → K'` has kernel the nilradical and is surjective. -/
theorem exists_purelyInseparable_lift_with_reduced_tensor_presentation
    [EssFiniteType k K] :
    ∃ (k' : Type w) (_ : Field k') (_ : Algebra k k')
      (K' : Type x) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K')
      (_ : FiniteDimensional K K') (_ : IsPurelyInseparable K K')
      (_ : FiniteDimensional k k') (_ : IsPurelyInseparable k k'),
        let φ : k' ⊗[k] K →ₐ[k'] K' :=
          productLeftAlgHom (ofId k' K') (IsScalarTower.toAlgHom k K K')
        RingHom.ker φ.toRingHom = nilradical (k' ⊗[k] K) ∧ Function.Surjective φ := sorry

end
