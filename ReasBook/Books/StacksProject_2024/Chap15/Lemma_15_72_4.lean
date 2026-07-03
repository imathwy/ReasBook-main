import stacks_project.Chap15.Lemma_15_72_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open MonoidalCategory
open MonoidalClosed
open BraidedCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
  [MonoidalCategory (CochainComplex (ModuleCat R) ℤ)]
  [BraidedCategory (CochainComplex (ModuleCat R) ℤ)]
  [MonoidalClosed (CochainComplex (ModuleCat R) ℤ)]
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for 15.72.4:
- primary domain: tensor-internal-Hom comparison morphisms for cochain complexes of `R`-modules;
- sampled owner declarations:
  `MonoidalClosed.curry`,
  `(ihom.ev M).app L`,
  `MonoidalClosed.pre f`;
- best owner abstraction: the source-facing morphism
  `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))` is the curried braiding/evaluation composite in the
  closed monoidal category of cochain complexes, so its canonical owner is `MonoidalClosed.curry`
  rather than a chapter-local reassembly through coevaluation and enriched composition;
- primitive data vs. derived API: the primitive owner data are the braiding and associator
  isomorphisms moving `M` past `K`, together with the evaluation map
  `M ⊗ (M ⟶[CpxR] L) ⟶ L`; the tensor-internal-Hom comparison is the derived curried morphism
  built from those owner maps;
- source/core/bridge triage:
  `source-facing`: the canonical morphism
    `K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
    and its functoriality;
  `core/canonical`: `MonoidalClosed.curry`, `(ihom.ev M).app L`, `MonoidalClosed.pre`,
    `(ihom M).map`, and `⊗ₘ`;
  `bridge/view`: none beyond the source-order presentation of the canonical comparison.
-/

/-- The uncurried braiding/evaluation composite whose transpose is the tensor-Hom comparison. -/
private noncomputable def module_complex_tensor_internal_hom_comparisonTranspose
    (K L M : CpxR) :
    M ⊗ (K ⊗ (M ⟶[CpxR] L)) ⟶ K ⊗ L :=
  (α_ M K (M ⟶[CpxR] L)).inv ≫
    (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
    (α_ K M (M ⟶[CpxR] L)).hom ≫
    K ◁ (ihom.ev M).app L

/-- Lemma 15.72.4: there is a canonical morphism
`K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L))`
of cochain complexes of `R`-modules. -/
noncomputable def module_complex_tensor_internal_hom_comparison
    (K L M : CpxR) :
    K ⊗ (M ⟶[CpxR] L) ⟶ (M ⟶[CpxR] (K ⊗ L)) :=
  curry (module_complex_tensor_internal_hom_comparisonTranspose K L M)

/-- Uncurrying the canonical tensor-Hom comparison recovers the braiding-evaluation composite used
to define it. -/
theorem module_complex_tensor_internal_hom_comparison_uncurry
    (K L M : CpxR) :
    uncurry (module_complex_tensor_internal_hom_comparison K L M) =
      (α_ M K (M ⟶[CpxR] L)).inv ≫
        (β_ M K).hom ▷ (M ⟶[CpxR] L) ≫
        (α_ K M (M ⟶[CpxR] L)).hom ≫
        K ◁ (ihom.ev M).app L := by
  simp [module_complex_tensor_internal_hom_comparison,
    module_complex_tensor_internal_hom_comparisonTranspose]

-- Proof sketch: uncurry both sides to the defining braiding/evaluation composite. Naturality then
-- follows from functoriality of `⊗ₘ`, naturality of the associator and braiding, and the
-- owner identities `MonoidalClosed.uncurry_pre_app` and `MonoidalClosed.uncurry_natural_right`.
/-- The tensor-Hom comparison is natural in the tensor factor and in both variables of the
internal-Hom term. -/
theorem module_complex_tensor_internal_hom_comparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : CpxR}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    CommSq
      (fK ⊗ₘ ((pre fM).app L₁ ≫ (ihom M₁).map fL))
      (module_complex_tensor_internal_hom_comparison K₁ L₁ M₂)
      (module_complex_tensor_internal_hom_comparison K₂ L₂ M₁)
      ((pre fM).app (K₁ ⊗ L₁) ≫ (ihom M₁).map (fK ⊗ₘ fL)) := sorry

end
