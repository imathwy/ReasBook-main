import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic

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

open CategoryTheory Pretriangulated DerivedCategory CochainComplex

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section

/-- The category of `ℤ`-indexed cochain complexes of abelian groups. -/
local notation "AbCochain" => CochainComplex AddCommGrpCat ℤ

/-- The unbounded derived category of abelian groups. -/
local notation "DAb" => DerivedCategory AddCommGrpCat

/-- The Mayer-Vietoris triangle obtained by transporting the canonical mapping-cocone triangle
along a comparison quasi-isomorphism `c`. -/
noncomputable def derivedMayerVietorisTriangleOfComparison
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β) [IsIso (Q.map c)] :
    Triangle DAb :=
  Triangle.mk
    (Q.map (c ≫ mappingCocone.fst β))
    (Q.map β)
    ((Q.mapTriangle.obj (mappingCocone.triangle β)).mor₃ ≫ (asIso (Q.map c)).inv⟦(1 : ℤ)⟧')

/-- The comparison quasi-isomorphism identifies the source-facing Mayer-Vietoris triangle with
the canonical mapping-cocone triangle in the derived category of abelian groups. -/
noncomputable def derivedMayerVietorisTriangleOfComparisonIso
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β) [IsIso (Q.map c)] :
    derivedMayerVietorisTriangleOfComparison β c ≅ Q.mapTriangle.obj (mappingCocone.triangle β) :=
  let e : Q.obj IX ≅ Q.obj (mappingCocone β) := asIso (Q.map c)
  Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
    (by simp [derivedMayerVietorisTriangleOfComparison, e, Functor.map_comp])
    (by simp [derivedMayerVietorisTriangleOfComparison])
    (by simp [derivedMayerVietorisTriangleOfComparison, e])

@[simp]
theorem derivedMayerVietorisTriangleOfComparisonIso_hom₁
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β) [IsIso (Q.map c)] :
    (derivedMayerVietorisTriangleOfComparisonIso β c).hom.hom₁ = Q.map c := by
  simp [derivedMayerVietorisTriangleOfComparisonIso]

@[simp]
theorem derivedMayerVietorisTriangleOfComparisonIso_hom₂
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β) [IsIso (Q.map c)] :
    (derivedMayerVietorisTriangleOfComparisonIso β c).hom.hom₂ =
      𝟙 (Q.obj IZY) := by
  change 𝟙 ((derivedMayerVietorisTriangleOfComparison β c).obj₂) = 𝟙 (Q.obj IZY)
  rfl

@[simp]
theorem derivedMayerVietorisTriangleOfComparisonIso_hom₃
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β) [IsIso (Q.map c)] :
    (derivedMayerVietorisTriangleOfComparisonIso β c).hom.hom₃ =
      𝟙 (Q.obj IE) := by
  change 𝟙 ((derivedMayerVietorisTriangleOfComparison β c).obj₃) = 𝟙 (Q.obj IE)
  rfl

-- Proof sketch: the standard triangle
-- `Q(C(β)[-1]) ⟶ Q(I(Z) ⊞ I(Y)) ⟶ Q(I(E)) ⟶ Q(C(β)[-1])[1]`
-- is distinguished by `DerivedCategory.mappingCocone_triangle_distinguished β`. If
-- `Q(c)` is an isomorphism, transport that distinguished triangle across the induced triangle
-- isomorphism whose first component is `Q(c)` and whose other two components are identities.
/-- Lemma 21.26.1: if the canonical comparison map
`c^K_{X,Z,Y,E} : I(X) ⟶ C(β)[-1]` is an isomorphism in the derived category of abelian groups,
then the induced triangle
`RΓ(X, K) ⟶ RΓ(Z, K) ⊞ RΓ(Y, K) ⟶ RΓ(E, K) ⟶ RΓ(X, K)[1]`
is distinguished. Here the first arrow is the composite of the comparison map with the canonical
projection `C(β)[-1] ⟶ I(Z) ⊞ I(Y)`. -/
@[stacks 0F16]
theorem derived_mayer_vietoris_triangle_of_comparison_distinguished
    {IX IZY IE : AbCochain} (β : IZY ⟶ IE) (c : IX ⟶ mappingCocone β)
    [IsIso (Q.map c)] :
    derivedMayerVietorisTriangleOfComparison β c ∈ distTriang DAb := by
  exact isomorphic_distinguished _ (DerivedCategory.mappingCocone_triangle_distinguished β) _
    (derivedMayerVietorisTriangleOfComparisonIso β c)

/-- The canonical identification between two comparison choices whose images in the derived
category of abelian groups are isomorphisms to the same mapping cocone. -/
noncomputable def comparisonChoiceIso
    {IX₁ IX₂ IZY IE : AbCochain} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β)
    (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (Q.map c₁)] [IsIso (Q.map c₂)] :
    Q.obj IX₁ ≅ Q.obj IX₂ :=
  (asIso (Q.map c₁)) ≪≫ (asIso (Q.map c₂)).symm

-- Proof sketch: when both `Q(c₁)` and `Q(c₂)` are isomorphisms to the same mapping cocone, their
-- sources are canonically isomorphic in the derived category of abelian groups via
-- `asIso (Q.map c₁) ≪≫ (asIso (Q.map c₂)).symm`. Rewriting gives an isomorphism of the arrows
-- into the fixed target `Q(C(β)[-1])`.
/-- If two comparison maps into the same mapping cocone both become isomorphisms in
the derived category of abelian groups, then they determine isomorphic arrows into that fixed
mapping cocone. This
records the common-target special case of the independence-of-resolution statement in the source.
-/
theorem comparison_choices_yield_isomorphic_arrows
    {IX₁ IX₂ IZY IE : AbCochain} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β)
    (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (Q.map c₁)] [IsIso (Q.map c₂)] :
    Q.map c₁ = (comparisonChoiceIso β c₁ c₂).hom ≫ Q.map c₂ := by
  simp [comparisonChoiceIso]

@[simp, reassoc]
theorem comparisonChoiceIso_hom_comp
    {IX₁ IX₂ IZY IE : AbCochain} (β : IZY ⟶ IE)
    (c₁ : IX₁ ⟶ mappingCocone β)
    (c₂ : IX₂ ⟶ mappingCocone β)
    [IsIso (Q.map c₁)] [IsIso (Q.map c₂)] :
    (comparisonChoiceIso β c₁ c₂).hom ≫ Q.map c₂ = Q.map c₁ := by
  simp [comparisonChoiceIso]

end
