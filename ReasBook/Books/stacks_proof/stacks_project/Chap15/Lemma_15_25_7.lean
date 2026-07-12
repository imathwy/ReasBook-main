import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap15.Lemma_15_22_10

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

/-- Helper for Lemma 15.25.7: the canonical finite-type subalgebra inside an essentially
finite-type `A`-algebra stays flat over the valuation ring `A` when the ambient algebra is flat
over `A`. -/
lemma essFiniteType_subalgebra_flat_over_valuationRing [Module.Flat A B] :
    Module.Flat A (Algebra.EssFiniteType.subalgebra A B) := by
  let B₀ := Algebra.EssFiniteType.subalgebra A B
  have htorsB : Module.IsTorsionFree A B :=
    (flat_iff_isTorsionFree_of_valuationRing (A := A) (M := B)).mp inferInstance
  have htorsB₀ : Module.IsTorsionFree A B₀ := by
    -- Pull torsion-freeness back along the canonical inclusion `B₀ ↪ B`.
    exact Function.Injective.moduleIsTorsionFree
      (f := fun x : B₀ ↦ (x : B))
      Subtype.val_injective
      (fun a x ↦ rfl)
  -- Over a valuation ring, torsion-free and flat are equivalent.
  exact (flat_iff_isTorsionFree_of_valuationRing
    (A := A) (M := B₀)).mpr htorsB₀

-- Proof sketch: use the canonical finite-type subalgebra owner
-- `Algebra.EssFiniteType.subalgebra A B`, whose localization at
-- `Algebra.EssFiniteType.submonoid A B` is `B`. The ambient flat `A`-module `B` is torsion-free
-- by `flat_iff_isTorsionFree_of_valuationRing`, so the finite-type subalgebra is torsion-free,
-- hence flat, over `A`. Apply Lemma `15.25.6 (1)` to that finite-type model and then use
-- `Algebra.EssFinitePresentation.of_isLocalization`.
/-- Lemma 15.25.7 (1): if `A` is a valuation ring, `A → B` is essentially of finite type, and `B`
is flat over `A`, then `B` is essentially of finite presentation over `A`. -/
@[stacks 0GSE]
theorem algebra_essFinitePresentation_of_essFiniteType_flat_over_valuationRing [Module.Flat A B] :
    Algebra.EssFinitePresentation A B := by
  let B₀ := Algebra.EssFiniteType.subalgebra A B
  let T := Algebra.EssFiniteType.submonoid A B
  letI : Module.Flat A B₀ :=
    essFiniteType_subalgebra_flat_over_valuationRing (A := A) (B := B)
  -- TODO: once `Lemma_15_25_6` is available as a compiling prerequisite, apply its part `(1)` to
  -- the finite-type model `B₀` and conclude with
  -- `Algebra.EssFinitePresentation.of_isLocalization (R := A) (S := B) B₀ T`.
  sorry

/-- Helper for Lemma 15.25.7: localizing a finite free module over the canonical finite-type
subalgebra gives the corresponding finite free module over the localization target. -/
noncomputable def localized_pi_scalar_linearEquiv (n : ℕ) :
    LocalizedModule (Algebra.EssFiniteType.submonoid A B)
        (Fin n → Algebra.EssFiniteType.subalgebra A B) ≃ₗ[
          Localization (Algebra.EssFiniteType.submonoid A B)]
      (Fin n → Localization (Algebra.EssFiniteType.submonoid A B)) :=
  (LocalizedModule.equivTensorProduct (Algebra.EssFiniteType.submonoid A B)
      (Fin n → Algebra.EssFiniteType.subalgebra A B)).trans
    (TensorProduct.piScalarRight (Algebra.EssFiniteType.subalgebra A B)
      (Localization (Algebra.EssFiniteType.submonoid A B))
      (Localization (Algebra.EssFiniteType.submonoid A B)) (Fin n))

variable {M : Type w} [AddCommMonoid M] [Module B M] [Module.Finite B M]
variable [Module A M] [IsScalarTower A B M]

-- Proof sketch: present `B` as a localization of a finite type polynomial algebra over `A`, view
-- `M` as a finite module over that finite type model, descend a finite generating set for the
-- kernel before localization, use the valuation-ring finite-presentation result for finite flat
-- modules over finite type algebras, and localize the resulting presentation.
/-- Lemma 15.25.7 (2): if `A` is a valuation ring, `A → B` is essentially of finite type, `M` is
a finite `B`-module, and `M` is flat as an `A`-module, then `M` is finitely presented as a
`B`-module. -/
@[stacks 0GSE]
theorem module_finitePresentation_of_essFiniteType_finite_flat_over_valuationRing
    [Module.Flat A M] : Module.FinitePresentation B M := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  -- TODO: follow the source-faithful kernel-descent proof over the canonical localization model
  -- `B₀[T⁻¹] ≃ B`, where `B₀ := Algebra.EssFiniteType.subalgebra A B` and
  -- `T := Algebra.EssFiniteType.submonoid A B`: choose a finite free cover of `M` over the
  -- localization target, descend its kernel to a submodule of `Fin n → B₀` using
  -- `localized'gi.l_u_eq`, prove the descended quotient is an `A`-torsion-free finite
  -- `B₀`-module, apply Lemma `15.25.6 (2)`, and transport the localized finite presentation back
  -- across the canonical localization algebra equivalence.
  sorry

end
