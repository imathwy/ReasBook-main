import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

-- Semantic recall: `lean_leansearch` found the canonical owner `AlgebraicGeometry.IsAffineHom`,
-- and local source inspection confirmed that the current environment provides affine-open
-- `isoSpec` comparisons but not a global relative-`Spec` owner for sheaves of `\mathcal O_S`-
-- algebras. The source-faithful fallback is therefore the exact affine-open-cover equivalence
-- together with the canonical local `Spec` comparison over each affine open of the target.

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.11.3 (1): a morphism of schemes is affine if and only if the target admits an
affine open cover whose pullback pieces are affine. -/
@[stacks 01S8]
theorem isAffineHom_iff_exists_affineOpenCover :
    IsAffineHom f ↔
      ∃ 𝒰 : S.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsAffineOpen (f ⁻¹ᵁ (𝒰.U i)) := by
  constructor
  · intro _
    refine ⟨S.affineOpenCover, fun i ↦ ?_⟩
    simpa using (S.affineOpenCover.isAffine i).preimage f
  · rintro ⟨𝒰, h𝒰⟩
    refine HasAffineProperty.of_openCover (P := @IsAffineHom) 𝒰.openCover ?_
    intro i
    have : IsAffine ((𝒰.openCover.pullback₁ f).X i) := by
      simpa using h𝒰 i
    infer_instance

/- Lemma 29.11.3 (2): over each affine open `U ⊆ S`, the canonical local spectrum comparison for
`f` is exactly mathlib's source-faithful theorem `IsAffineOpen.SpecMap_appLE_fromSpec`; the source
statement here is its special case with `V = f ⁻¹ᵁ U` and `i = le_rfl`. -/
recall AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec
    {X S : Scheme.{u}} (f : X ⟶ S) {V : X.Opens} {U : S.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) :
    Spec.map (f.appLE U V i) ≫ hU.fromSpec = hV.fromSpec ≫ f

end

end AlgebraicGeometry
