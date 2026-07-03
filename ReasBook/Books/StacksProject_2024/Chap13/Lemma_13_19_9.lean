import Mathlib
import stacks_project.Chap13.Definition_13_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-above cochain complexes and compatible
  projective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ObjectProperty.ι`,
  `CochainComplex.minus`,
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.ProjectiveResolution`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (ProjectiveMinus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`; this is the
  projective dual of the direct short-complex formulation used for injective resolutions in
  Lemma `13.18.9`;
- primitive data here: a short exact sequence `S` of cochain complexes, the short exact resolving
  row in `ProjectiveMinus 𝒜`, the morphism from that underlying short complex to `S`, and the
  quasi-isomorphism witnesses on the three vertical components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `ProjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the projective-resolution diagram above a short exact sequence of cochain
  complexes, together with its existence theorems;
- `core/canonical`: `ShortComplex (ProjectiveMinus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, and `CochainComplex.ProjectiveResolution`;
- `bridge/view`: the prescribed-right-resolution specialization below.
-/

local notation "projMinusι" => MinusWithTermsIn.ι (isProjective 𝒜)

section

variable [EnoughProjectives 𝒜]

-- Proof sketch: fix the prescribed projective resolution of `C^•`, resolve `A^•` by projectives,
-- lift the map to `C^•` along the chosen resolution using the projective lifting machinery, and
-- then form the middle resolving complex so that the upper row is short exact and both squares
-- commute. The outer terms of the given short exact sequence are assumed bounded above so that
-- the outer columns are source-faithful projective resolutions, and the middle resolving complex
-- is then bounded above by extension-closure.
/-- Lemma 13.19.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
in an abelian category with enough projectives whose outer terms are bounded above, then it
extends to a commutative diagram whose vertical maps are projective resolutions and whose upper
row is again a short exact sequence of complexes. The middle term is bounded above because
bounded-above cochain complexes are closed under extensions. -/
theorem exists_projectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (hC : CochainComplex.minus 𝒜 S.X₃) :
    ∃ row : ShortComplex (ProjectiveMinus 𝒜), ∃ hom : row.map projMinusι ⟶ S,
      (row.map projMinusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ := sorry

-- Proof sketch: run the previous construction starting from the prescribed projective resolution
-- of `C^•`, using `ProjectiveResolution.minus` for the bounded-above right column, lifting the map
-- from the left resolution into that fixed right resolution, and then building the middle
-- resolving complex so that the upper row is short exact.
/-- Given a chosen projective resolution of the right complex, the diagram can be built with that
resolution as its right column, provided the left term of the short exact row is bounded above;
the right bounded-above hypothesis is already supplied by the chosen projective resolution. The
middle term is then bounded above by short exactness. -/
theorem exists_projectiveResolutionDiagram_of_shortExact_with_rightResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (P : ProjectiveResolution S.X₃) :
    ∃ (Q R : ProjectiveMinus 𝒜) (f : Q ⟶ R) (g : R ⟶ P.complex) (hfg : f ≫ g = 0)
      (φ : (ShortComplex.mk f g hfg).map projMinusι ⟶ S),
        φ.τ₃ = P.π ∧
          ((ShortComplex.mk f g hfg).map projMinusι).ShortExact ∧
          QuasiIso φ.τ₁ ∧
          QuasiIso φ.τ₂ := sorry

end

end CochainComplex
