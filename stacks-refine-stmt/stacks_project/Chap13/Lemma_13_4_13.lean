import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe w v u

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.13:
- primary domain: distinguished triangles in a pretriangulated category, together with coproducts
  and the shift/coproduct comparison;
- sampled core/canonical declarations:
  `CategoryTheory.Pretriangulated.productTriangle`,
  `CategoryTheory.Pretriangulated.productTriangle_distinguished`,
  `CategoryTheory.Pretriangulated.triangleOpEquivalence`,
  `CategoryTheory.Pretriangulated.unop_distinguished`;
- best owner abstraction: the canonical core owner is `productTriangle`; the corresponding
  source-facing owner for this item should therefore be a project-level
  `CategoryTheory.Pretriangulated.coproductTriangle`. There is no exact upstream owner with the
  same minimal hypotheses: the opposite-category `productTriangle` route naturally lands in the
  auxiliary coproduct-of-shifts presentation and asks for coproducts of the shifted first terms.
  The source-facing owner here therefore stays local, with its distinguishedness theorem obtained
  as a `bridge/view` from the core product theorem in the opposite category, while the public
  target map stays in the intrinsic codomain `(∐ i, (T i).obj₁)⟦1⟧`;
- primitive-vs-derived split:
  primitive data are the family `T : I → Triangle D` and coproducts of the three object-families;
  derived API is the source-facing coproduct triangle together with its distinguishedness.

Source/core/bridge triage:
- `source-facing`: the owner `CategoryTheory.Pretriangulated.coproductTriangle T`;
- `core/canonical`: `productTriangle` and `productTriangle_distinguished`;
- `bridge/view`: opposite-category transport via `triangleOpEquivalence`, with
  `PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))` only as the comparison between the auxiliary
  coproduct-of-shifts presentation and the intrinsic shifted coproduct. The source-facing owner is
  not a duplicate wheel of the core owner, but the minimal-hypothesis bridge attached to it. -/

/- (1) The canonical owner for a family of distinguished triangles is
`CategoryTheory.Pretriangulated.productTriangle`. -/
#check CategoryTheory.Pretriangulated.productTriangle

/- (2) If a family of objects of a pre-triangulated category admits a coproduct, then the shifted
coproduct is canonically identified with the coproduct of the shifted family by the comparison
isomorphism `Limits.PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))`; this is a bridge from the
auxiliary coproduct-of-shifts presentation to the intrinsic codomain `(∐ i, X i)⟦1⟧`. -/
#check Limits.PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))

/- (3) The product of a family of distinguished triangles is distinguished. This is the canonical
theorem `CategoryTheory.Pretriangulated.productTriangle_distinguished`. -/
#check CategoryTheory.Pretriangulated.productTriangle_distinguished

/- (4) Distinguishedness transports back from triangles in the opposite category via
`CategoryTheory.Pretriangulated.unop_distinguished`. -/
#check CategoryTheory.Pretriangulated.unop_distinguished

end

namespace CategoryTheory.Pretriangulated

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- The coproduct of a family of triangles. -/
@[simps!]
def coproductTriangle (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : Triangle D :=
  Triangle.mk
    (Limits.Sigma.desc (fun i ↦ (T i).mor₁ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₂) i))
    (Limits.Sigma.desc (fun i ↦ (T i).mor₂ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₃) i))
    (Limits.Sigma.desc
      (fun i ↦ (T i).mor₃ ≫ (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧'))

/-- Companion bridge to the source-facing Stacks formula: after transporting the last morphism of
`coproductTriangle T` across the canonical shift/coproduct comparison, one recovers the
coproduct-of-shifts map `⨿ Tᵢ.obj₃ ⟶ ⨿ Tᵢ.obj₁⟦1⟧`. -/
@[reassoc, simp]
theorem coproductTriangle_mor₃_comp_preservesCoproductIso_hom (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)] :
    (coproductTriangle T).mor₃ ≫
        (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).hom =
      Limits.Sigma.desc
        (fun i ↦ (T i).mor₃ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₁⟦(1 : ℤ)⟧) i) := by
  apply Limits.Sigma.hom_ext
  intro i
  dsimp [coproductTriangle]
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
  rw [Category.assoc]
  congr 1
  have hhom :
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).hom =
        inv (sigmaComparison (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)))
  rw [hhom]
  exact
    map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁) i

end

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

-- Proof sketch: dualize the product argument for the core owner `productTriangle`, use the
-- universal property of the coproduct and the co-special form of Remark 13.4.4 to identify the
-- resulting source-facing owner `coproductTriangle T`, and transport distinguishedness back from
-- the opposite category.
/-- Lemma 13.4.13: clause (4) says that for a family of distinguished triangles in a
pre-triangulated category, if the coproducts of the first, second, and third terms exist, then
the coproduct triangle is distinguished. -/
lemma coproductTriangle_distinguished (T : I → Triangle D)
    (hT : ∀ i, T i ∈ distTriang D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    coproductTriangle T ∈ distTriang D := sorry

end

end CategoryTheory.Pretriangulated

end
