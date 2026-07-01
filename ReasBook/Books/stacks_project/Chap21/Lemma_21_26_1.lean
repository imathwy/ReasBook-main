import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Lemma 21.26.1:
- primary domain: distinguished triangles in the derived category of abelian groups coming from
  the canonical mapping-cocone triangle;
- inspected canonical declarations:
  `DerivedCategory.mappingCocone_triangle_distinguished`,
  `CochainComplex.mappingCocone.triangle`,
  `Triangle.isoMk`,
  `Pretriangulated.isomorphic_distinguished`;
- owner abstraction: `DerivedCategory.mappingCocone_triangle_distinguished`;
- primitive data: a morphism `β : IZY ⟶ IE` of cochain complexes and a comparison morphism
  `c : IX ⟶ mappingCocone β` whose image in the derived category is an isomorphism;
- derived API: transport of the canonical distinguished triangle along `asIso (Q.map c)`, and the
  induced canonical identification between two such comparison choices.

Source/core/bridge triage:
- `source-facing`: the Mayer-Vietoris triangle obtained by replacing `C(β)[-1]` with a quasi-isomorphic
  complex `IX`;
- `core/canonical`: `DerivedCategory.mappingCocone_triangle_distinguished`;
- `bridge/view`: the triangle isomorphism built from `asIso (Q.map c)`.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open DerivedCategory
open CochainComplex

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section

/-- The category of `\mathbf Z`-indexed cochain complexes of abelian groups. -/
private abbrev AbCochain :=
  CochainComplex AddCommGrpCat ℤ

/-- The unbounded derived category of abelian groups. -/
private abbrev AbDerived :=
  DerivedCategory AddCommGrpCat

-- Proof sketch: the standard triangle
-- `Q(C(\beta)[-1]) ⟶ Q(I(Z) \oplus I(Y)) ⟶ Q(I(E)) ⟶ Q(C(\beta)[-1])[1]`
-- is distinguished by `DerivedCategory.mappingCocone_triangle_distinguished β`. If
-- `Q(c)` is an isomorphism, transport that distinguished triangle across the induced triangle
-- isomorphism whose first component is `Q(c)` and whose other two components are identities.
/-- Lemma 21.26.1: if the canonical comparison map
`c^K_{X,Z,Y,E} : \mathcal I^\bullet(X) \to C(\beta)^\bullet[-1]` is an isomorphism in the derived
category of abelian groups, then the induced triangle
`R\Gamma(X,K) \to R\Gamma(Z,K) \oplus R\Gamma(Y,K) \to R\Gamma(E,K) \to R\Gamma(X,K)[1]`
is distinguished. Here the first arrow is the composite of the comparison map with the canonical
projection `C(\beta)^\bullet[-1] \to \mathcal I^\bullet(Z) \oplus \mathcal I^\bullet(Y)`. -/
theorem derived_mayer_vietoris_triangle_of_comparison_distinguished
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (Q.map c)] :
    Triangle.mk
        (Q.map (c ≫ mappingCocone.fst β))
        (Q.map β)
        ((Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫ (asIso (Q.map c)).inv⟦(1 : ℤ)⟧') ∈
      distTriang AbDerived := by
  let T : Triangle AbDerived :=
    Triangle.mk
      (Q.map (c ≫ mappingCocone.fst β))
      (Q.map β)
      ((Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫ (asIso (Q.map c)).inv⟦(1 : ℤ)⟧')
  let e : Q.obj IX ≅ Q.obj (mappingCocone β) := asIso (Q.map c)
  change T ∈ distTriang AbDerived
  refine isomorphic_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished β) _ ?_
  refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [T, e, Functor.map_comp]
  · simp [T]
  · simp [T, e]

-- Proof sketch: when both `Q(c₁)` and `Q(c₂)` are isomorphisms to the same mapping cocone, their
-- sources are canonically isomorphic in `D(\mathbf Z)` via
-- `asIso (Q.map c₁) ≪≫ (asIso (Q.map c₂)).symm`. Rewriting gives an isomorphism of the arrows
-- into the fixed target `Q(C(\beta)[-1])`.
/-- If two comparison maps into the same mapping cocone both become isomorphisms in
`D(\mathbf Z)`, then they determine isomorphic arrows into that fixed mapping cocone. This
records the common-target special case of the independence-of-resolution statement in the source.
-/
theorem comparison_choices_yield_isomorphic_arrows
    {IX₁ IX₂ IZY IE : AbCochain} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β)
    (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (Q.map c₁)] [IsIso (Q.map c₂)] :
    Q.map c₁ = ((asIso (Q.map c₁)) ≪≫ (asIso (Q.map c₂)).symm).hom ≫ Q.map c₂ := by
  simp

end
