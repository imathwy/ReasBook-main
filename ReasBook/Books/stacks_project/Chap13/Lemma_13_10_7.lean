import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "K" => HomotopyCategory 𝒜 (up ℤ)
local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.10.7:
- primary domain: distinguished triangles in the homotopy category of cochain complexes and their
  realization by degreewise split short exact sequences;
- inspected owner declarations:
  `distTriang (K)`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `Triangle.isoMk`;
- best owner abstraction: the canonical owner is the distinguished-triangle class `distTriang K`,
  while the degreewise split model is the bridge/view
  `CochainComplex.trianglehOfDegreewiseSplit`; comparison data should therefore be an ordinary
  triangle isomorphism, not a second local wrapper predicate;
- primitive data: a degreewise split short complex `0 ⟶ A ⟶ B' ⟶ C ⟶ 0` together with a triangle
  isomorphism whose first and third components are identities;
- derived API: distinguishedness of the target triangle and the equality of third morphisms follow
  from `hT` and the triangle-isomorphism commutativity, so they should not be stored as primitive
  public data.
- source/core/bridge triage:
  `source-facing`: the comparison theorem promised by Lemma 13.10.7;
  `core/canonical`: `distTriang K`;
  `bridge/view`: `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` together with
    `CochainComplex.trianglehOfDegreewiseSplit`.
-/

-- Proof sketch: use the characterization of distinguished triangles in `K(\mathcal A)` by
-- degreewise split triangles together with the explicit inverse-rotation of a cone triangle. The
-- proof in the text constructs a triangle `(A^•, W^•[-1], C^•, a', b', c)` from the cone of `c`,
-- then applies TR3 and the two-out-of-three lemma for morphisms of triangles to obtain an
-- isomorphism whose first and third components are identities.
/-- Lemma 13.10.7: if `(A^•, B^•, C^•, a, b, c)` is a distinguished triangle in
`K(\mathcal A)`, then it is isomorphic, through the identity on `A^•` and `C^•`, to a
distinguished triangle `(A^•, (B')^•, C^•, a', b', c)` coming from a degreewise split short exact
sequence `0 ⟶ A^n ⟶ (B')^n ⟶ C^n ⟶ 0` in every degree. -/
theorem distinguished_triangle_iso_to_degreewiseSplit
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang K) :
    ∃ (B' : CochainComplex 𝒜 ℤ) (f : A ⟶ B') (g : B' ⟶ C) (hfg : f ≫ g = 0)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting),
      ∃ e : Triangle.mk a b c ≅
          CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk f g hfg) σ,
        e.hom.hom₁ = 𝟙 ((Q).obj A) ∧
          e.hom.hom₃ = 𝟙 ((Q).obj C) := sorry

end

end CategoryTheory
