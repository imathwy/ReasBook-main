import StacksProject_2024.Chap13.Definition_13_37_5
import StacksProject_2024.Chap13.Lemma_13_37_2
import StacksProject_2024.Chap22.Lemma_22_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

noncomputable section

universe uR uA vA uB vB

section

variable {R : Type uR} [CommRing R]
variable {DA : Type uA} {DB : Type uB}
variable [Category.{vA} DA] [Category.{vB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [Linear R DA] [Linear R DB]
variable [HasCoproducts.{max uB vB} DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]
variable [IsTriangulated DB]

variable (derivedTensorWithN : DA ⥤ DB) (derivedHomFromN : DB ⥤ DA)
variable [derivedTensorWithN.CommShift ℤ]
variable [derivedTensorWithN.IsTriangulated]
variable [derivedTensorWithN.Linear R]
variable (Aunit : DA) (Bunit N : DB)

-- Semantic recall note: the local Chapter 13 API already provides the compact-object owner
-- `IsCompactObject`, the compact subcategory `D_c(D)`, the compact-generation owner
-- `IsCompactlyGenerated`, and the generator notions `IsWeakGenerator` and
-- `IsClassicalGenerator`.

omit [HasZeroObject DB] [HasCoproducts.{max uB vB} DB]
  [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB] [IsTriangulated DB] in
/-- If `N` is a weak generator, then vanishing of all shifted Homs out of `N` forces an object
to be zero. -/
theorem detectsZero_of_isWeakGenerator
    {N X : DB} (hNWeak : IsWeakGenerator N)
    (hX : ∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0) :
    IsZero X := by
  by_contra hXZero
  obtain ⟨n, f, hf⟩ := hNWeak hXZero
  exact hf (hX n f)

/-- Companion bridge for Remark 22.37.3 (1): classical generation of `N` on `D_c(DB)` and
ambient compact generation imply that the shifted Homs out of `N` detect zero objects of `DB`. -/
theorem detectsZero_of_compact_classicalGenerator
    (N : DB) (hNCompact : IsCompactObject N)
    (hDBCompactlyGenerated : IsCompactlyGenerated DB)
    (hNClassical : IsClassicalGenerator (⟨N, hNCompact⟩ : D_c(DB))) :
    ∀ X : DB, (∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0) → IsZero X := sorry

/-- Companion bridge for Remark 22.37.3 (2): if `RHom(N, B)` is compact in `DA`, then weak
generation of `N` in the compact subcategory upgrades to classical generation there. -/
theorem isClassicalGenerator_on_compactObjects_of_weakGenerator_on_compactObjects_of_compactRHomB
    (hNCompact : IsCompactObject N)
    (hBCompact : IsCompactObject Bunit)
    (hBClassical : IsClassicalGenerator (⟨Bunit, hBCompact⟩ : D_c(DB)))
    (hRHomBCompact : IsCompactObject (derivedHomFromN.obj Bunit))
    (hNWeakCompact : IsWeakGenerator (⟨N, hNCompact⟩ : D_c(DB))) :
    IsClassicalGenerator (⟨N, hNCompact⟩ : D_c(DB)) := sorry

/-- Remark 22.37.3 (1): in Lemma 22.37.2, the hypothesis that the shifted Homs out of
`N` detect zero objects of `D(B, d)` may be replaced by the condition that `N`, viewed as a
compact object, is a classical generator of the compact subcategory `D_compact(B, d)`. The
ambient compact-generation hypothesis records the standard compact generation of the derived
category used through Derived Categories, Proposition 13.37.6. -/
@[stacks 09SS]
theorem derivedTensorWithN_isEquivalence_of_compact_classicalGenerator_selfExt
    (hAdj : derivedTensorWithN ⊣ derivedHomFromN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hNCompact : IsCompactObject N)
    (hDBCompactlyGenerated : IsCompactlyGenerated DB)
    (hNClassical :
      IsClassicalGenerator (⟨N, hNCompact⟩ : D_c(DB)))
    (hRHomZero_implies_hom_zero :
      ∀ X : DB,
        IsZero (derivedHomFromN.obj X) →
          ∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (derivedTensorWithN_selfExtMap derivedTensorWithN Aunit N hTensorUnit k)) :
    derivedTensorWithN.IsEquivalence := sorry

/-- Remark 22.37.3 (2): if the right-derived internal Hom object `RHom(N, B)` is compact in
`D(A, d)`, then, in the same setup, it suffices to check that `N` is a weak generator of the
compact subcategory `D_compact(B, d)`. Here `Bunit` denotes the regular object `B` of `D(B, d)`;
its compactness and classical-generation hypotheses record the standard regular-generator facts
for this abstract derived-category surface. -/
@[stacks 09SS]
theorem derivedTensorWithN_isEquivalence_of_compact_weakGenerator_compactRHomB_selfExt
    (hAdj : derivedTensorWithN ⊣ derivedHomFromN)
    (hTensorUnit : derivedTensorWithN.obj Aunit ≅ N)
    (hNCompact : IsCompactObject N)
    (hBCompact : IsCompactObject Bunit)
    (hBClassical : IsClassicalGenerator (⟨Bunit, hBCompact⟩ : D_c(DB)))
    (hRHomBCompact : IsCompactObject (derivedHomFromN.obj Bunit))
    (hNWeakCompact : IsWeakGenerator (⟨N, hNCompact⟩ : D_c(DB)))
    (hRHomZero_implies_hom_zero :
      ∀ X : DB,
        IsZero (derivedHomFromN.obj X) →
          ∀ n : ℤ, ∀ f : N ⟶ X⟦n⟧, f = 0)
    (hSelfExt :
      ∀ k : ℤ,
        Function.Bijective
          (derivedTensorWithN_selfExtMap derivedTensorWithN Aunit N hTensorUnit k)) :
    derivedTensorWithN.IsEquivalence := sorry

end
