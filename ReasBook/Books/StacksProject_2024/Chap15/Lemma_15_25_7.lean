import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

/- Domain-style sampling:
- primary domain: local commutative algebra over valuation rings, with source-facing conclusions in
  the canonical owners for essential finite presentation of algebras and finite presentation of
  modules;
- sampled owner declarations:
  `Algebra.EssFinitePresentation`,
  `Algebra.EssFiniteType.subalgebra`,
  `Algebra.EssFiniteType.submonoid`,
  `Algebra.EssFiniteType.isLocalization`,
  `Algebra.EssFinitePresentation.of_isLocalization`,
  `algebra_finitePresentation_of_finiteType_flat_over_valuationRing`,
  `Module.FinitePresentation`;
- best owner abstraction: `Algebra.EssFinitePresentation A B` for part (1), not an existential
  localization witness restated locally;
- primitive data: the valuation-ring base, the essentially-finite-type algebra `B`, the finite
  `B`-module `M`, and the flatness hypotheses;
- derived API: any explicit localization presentation of `B` by a finitely presented
  `A`-algebra. That witness belongs to the owner `Algebra.EssFinitePresentation` and should not
  remain the main public conclusion here.

Layering:
- `source-facing`: Lemma 15.25.7 itself;
- `core/canonical`: `Algebra.EssFinitePresentation` and `Module.FinitePresentation`;
- `bridge/view`: a chosen localization presentation of `B`, used only through the owner
  abstraction rather than as a parallel public API.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {B : Type v} [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]

-- Proof sketch: use the canonical finite-type subalgebra owner
-- `Algebra.EssFiniteType.subalgebra A B`, whose localization at
-- `Algebra.EssFiniteType.submonoid A B` is `B`. The ambient flat `A`-module `B` is torsion-free
-- by `flat_iff_isTorsionFree_of_valuationRing`, so the finite-type subalgebra is torsion-free,
-- hence flat, over `A`. Apply Lemma `15.25.6 (1)` to that finite-type model and then use
-- `Algebra.EssFinitePresentation.of_isLocalization`.
/-- Lemma 15.25.7 (1): if `A` is a valuation ring, `A → B` is essentially of finite type, and `B`
is flat over `A`, then `B` is essentially of finite presentation over `A`. -/
theorem algebra_essFinitePresentation_of_essFiniteType_flat_over_valuationRing [Module.Flat A B] :
    Algebra.EssFinitePresentation A B := sorry

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

-- Proof sketch: present `B` as a localization of a finite type polynomial algebra over `A`, view
-- `M` as a finite module over that finite type model, descend a finite generating set for the
-- kernel before localization, use the valuation-ring finite-presentation result for finite flat
-- modules over finite type algebras, and localize the resulting presentation.
/-- Lemma 15.25.7 (2): if `A` is a valuation ring, `A → B` is essentially of finite type, `M` is
a finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
theorem module_finitePresentation_of_essFiniteType_finite_flat_over_valuationRing
    [Module.Flat A M] : Module.FinitePresentation B M := sorry

end
