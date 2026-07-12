import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

-- Semantic recall: this file is `source-facing` for the generic-point residue-field coproduct.
-- The public owner uses the actual generic-point set `genericPoints X`, and the file keeps the
-- coproduct object together with the canonical descent morphism built from
-- `Scheme.fromSpecResidueField`.

/-- The coproduct of the spectra of the residue fields of the generic points of `X`. -/
noncomputable def genericPointSpectrumCoproduct (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun η : genericPoints X ↦
    Spec (CommRingCat.of (X.residueField η.1))

/-- 29.54.0.1: the canonical morphism from the coproduct of the spectra of the residue fields of
the generic points of `X` to `X`. This formalizes the displayed map
`f : Y = ∐_{η ∈ X^(0)} Spec(κ(η)) ⟶ X`. -/
noncomputable def genericPointSpectrumCoproductTo (X : Scheme.{u}) :
    genericPointSpectrumCoproduct X ⟶ X :=
  Limits.Sigma.desc fun η : genericPoints X ↦
    X.fromSpecResidueField η.1

/-- The canonical morphism from the generic-point residue-field coproduct is the coproduct
descent map built from the residue-field morphisms of the generic points. -/
theorem genericPointSpectrumCoproductTo_def (X : Scheme.{u}) :
    genericPointSpectrumCoproductTo X =
      Limits.Sigma.desc (fun η : genericPoints X ↦ X.fromSpecResidueField η.1) := rfl

/-- The `η`-th coproduct leg of `genericPointSpectrumCoproductTo X` is the residue-field morphism
from the generic point `η`. -/
@[simp, reassoc]
theorem genericPointSpectrumCoproductTo_ι (X : Scheme.{u}) (η : genericPoints X) :
    Limits.Sigma.ι
        (fun η : genericPoints X ↦
          Spec (CommRingCat.of (X.residueField η.1))) η ≫
      genericPointSpectrumCoproductTo X =
        X.fromSpecResidueField η.1 := by
  simpa [genericPointSpectrumCoproductTo_def] using
    (Limits.Sigma.ι_desc (fun η : genericPoints X ↦ X.fromSpecResidueField η.1) η)

end
end AlgebraicGeometry
