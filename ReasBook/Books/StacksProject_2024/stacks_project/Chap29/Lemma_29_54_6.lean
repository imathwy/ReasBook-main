import Mathlib
import StacksProject_2024.Chap29.Lemma_29_17_4
import StacksProject_2024.Chap29.Lemma_29_54_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

noncomputable section

-- Semantic recall / local analogue check: `lean_leansearch` surfaced mathlib's
-- `Scheme.Hom.normalizationCoprodIso`, while local Chapter 29 precedent packages the
-- source-facing scheme normalization as `Scheme.normalization` and `Scheme.normalizationTo`.
-- Chapter 29 packages the reduced induced irreducible-component subscheme by
-- `Scheme.irreducibleComponentSubscheme`.

/-- A reduced induced irreducible component inherits the finiteness condition on irreducible
components of quasi-compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensReducedInducedIrreducibleComponent
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (Z : irreducibleComponents X) :
    HasFiniteIrreducibleComponentsOnCompactOpens
      (X.irreducibleComponentSubscheme Z) := sorry

/-- Lemma 29.54.6: let `X` be a scheme such that every quasi-compact open has finitely many
irreducible components. If `Z_i` are the irreducible components of `X` with the reduced induced
scheme structure and `Z_i^ν ⟶ Z_i` are their normalizations, then the induced morphism
`∐ i, Z_i^ν ⟶ X` identifies this coproduct with the normalization `X^ν ⟶ X`. -/
@[stacks 0CDV]
theorem normalizationIsoCoproductIrreducibleComponentNormalizations
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [QuasiCompact (genericPointSpectrumCoproductTo X)]
    [QuasiSeparated (genericPointSpectrumCoproductTo X)]
    [∀ Z : irreducibleComponents X,
      QuasiCompact (genericPointSpectrumCoproductTo (X.irreducibleComponentSubscheme Z))]
    [∀ Z : irreducibleComponents X,
      QuasiSeparated (genericPointSpectrumCoproductTo (X.irreducibleComponentSubscheme Z))] :
    let componentScheme : irreducibleComponents X → Scheme.{u} :=
      X.irreducibleComponentSubscheme
    ∃ e :
        (∐ fun Z : irreducibleComponents X ↦
            (componentScheme Z).normalization) ≅ X.normalization,
      Limits.Sigma.desc (fun Z : irreducibleComponents X ↦
          (componentScheme Z).normalizationTo ≫
            X.irreducibleComponentSubschemeι Z) =
        e.hom ≫ X.normalizationTo := sorry

end

end Scheme
end AlgebraicGeometry
