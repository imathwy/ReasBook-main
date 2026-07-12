import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the residue-field point owner
-- `Scheme.fromSpecResidueField` and coproduct infrastructure, while local Chapter 29 precedent in
-- `29_54_0_1` confirms that the source-facing target here should be the subset-indexed coproduct
-- of the point spectra with structure map given by `Limits.Sigma.desc`.
--
-- Source/core/bridge triage:
-- - `source-facing`: the factorization criterion for a morphism whose image lands in `E`;
-- - `core/canonical`: the subset-indexed coproduct of residue-field spectra and its descent map;
-- - `bridge/view`: the existence of a factorization through that canonical morphism.

/-- The coproduct of the spectra of the residue fields of the points of `E ⊆ X`. -/
noncomputable def pointSpectrumCoproduct (X : Scheme.{u}) (E : Set X) : Scheme.{u} :=
  ∐ fun x : E ↦ Spec (CommRingCat.of (X.residueField x.1))

/-- The canonical morphism from the coproduct of the point spectra over `E` to `X`. -/
noncomputable def pointSpectrumCoproductTo (X : Scheme.{u}) (E : Set X) :
    pointSpectrumCoproduct X E ⟶ X :=
  Limits.Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)

/-- The canonical morphism from the point-spectrum coproduct over `E` is the coproduct descent map
built from the residue-field point morphisms. -/
theorem pointSpectrumCoproductTo_def (X : Scheme.{u}) (E : Set X) :
    pointSpectrumCoproductTo X E =
      Limits.Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) := rfl

/-- The `x`-th coproduct leg of `pointSpectrumCoproductTo X E` is the residue-field point morphism
associated to `x`. -/
@[simp, reassoc]
theorem pointSpectrumCoproductTo_ι (X : Scheme.{u}) (E : Set X) (x : E) :
    Limits.Sigma.ι
        (fun x : E ↦
          Spec (CommRingCat.of (X.residueField x.1))) x ≫
      pointSpectrumCoproductTo X E =
        X.fromSpecResidueField x.1 := by
  simpa [pointSpectrumCoproductTo_def] using
    (Limits.Sigma.ι_desc (fun x : E ↦ X.fromSpecResidueField x.1) x)

/-- Lemma 29.58.2: if `f : Y ⟶ X` is a morphism of schemes, `X` is locally Noetherian, there are
no nontrivial specializations among the elements of `E ⊆ X`, `Y` is reduced, and the set-theoretic
image of `f` is contained in `E`, then `f` factors through the canonical morphism from the
coproduct of the spectra of the residue fields of the points of `E` to `X`. -/
@[stacks 0H1N]
theorem exists_factorization_pointSpectrumCoproduct_of_range_subset
    {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Set X) [IsLocallyNoetherian X] [IsReduced Y]
    (hspecializes : ∀ ⦃x x' : X⦄, x ∈ E → x' ∈ E → x ⤳ x' → x = x')
    (himage : Set.range f ⊆ E) :
    ∃ g : Y ⟶ pointSpectrumCoproduct X E, g ≫ pointSpectrumCoproductTo X E = f := sorry

/-- Pointwise companion to Lemma 29.58.2: if a morphism from a reduced scheme sends every point
of `Y` into `E`, then it factors through the canonical residue-field coproduct over `E`. -/
theorem exists_factorization_pointSpectrumCoproduct_of_forall_mem
    {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Set X) [IsLocallyNoetherian X] [IsReduced Y]
    (hspecializes : ∀ ⦃x x' : X⦄, x ∈ E → x' ∈ E → x ⤳ x' → x = x')
    (hpoint : ∀ y : Y, f y ∈ E) :
    ∃ g : Y ⟶ pointSpectrumCoproduct X E, g ≫ pointSpectrumCoproductTo X E = f := by
  exact exists_factorization_pointSpectrumCoproduct_of_range_subset f E hspecializes
    (Set.range_subset_iff.2 hpoint)

end AlgebraicGeometry
