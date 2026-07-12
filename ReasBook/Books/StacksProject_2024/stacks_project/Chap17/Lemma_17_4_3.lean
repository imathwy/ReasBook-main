import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Sites.Monoidal
import StacksProject_2024.Chap06.Lemma_6_16_1
import StacksProject_2024.Chap17.Definition_17_23_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open TopCat TopCat.Presheaf TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules}
variable [MonoidalCategory X.Modules]

local notation "ModX" => X.Modules
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/- 
Domain-style sampling for tensor products of globally generated `\mathcal O_X`-modules:
- inspected owner declarations:
  `SheafOfModules.GeneratingSections`,
  `SheafOfModules.GeneratingSections.π`,
  `AlgebraicGeometry.generating_sections_iff_stalkwise_span_eq_top`,
  `tensorObj`,
  the local tensor notation `⊗ₘ`;
- best owner abstraction:
  `ℱ.GeneratingSections` is the canonical owner for global generating families, and the tensor
  product owner in the chapter/project ecosystem is the ambient monoidal tensor object
  `(tensorObj ℱ 𝒢 : ModX)`, written `ℱ ⊗ₘ 𝒢`;
- primitive data:
  two generating families `σ : ℱ.GeneratingSections` and `τ : 𝒢.GeneratingSections`;
- derived API:
  the tensor-specific bridge statements below, culminating in the induced owner-level tensor
  construction on generating families for `ℱ ⊗ₘ 𝒢`.

Source/core/bridge triage:
- `source-facing`: Lemma 17.4.3, asserting that the tensor product of two globally generated
  `\mathcal O_X`-modules is again globally generated;
- `core/canonical`: `ℱ.GeneratingSections`, `(tensorObj ℱ 𝒢 : ModX)`, and the stalkwise
  generation owner `AlgebraicGeometry.generating_sections_iff_stalkwise_span_eq_top`;
- `bridge/view`: the tensor-section construction, the stalk tensor-product comparison, and the
  stalkwise pure-tensor spanning statement.
-/

private noncomputable def tensorSection
    (s : ℱ.sections) (t : 𝒢.sections) : (ℱ ⊗ₘ 𝒢 : ModX).sections :=
  let η : SheafOfModules.unit X.ringCatSheaf ≅ 𝟙_ X.Modules :=
    SheafOfModules.unitIsoTensorUnit
  (ℱ ⊗ₘ 𝒢 : ModX).unitHomEquiv
    (η.hom ≫ (λ_ (𝟙_ X.Modules)).inv ≫
      ((η.inv ≫ ℱ.unitHomEquiv.symm s) ⊗ₘ (η.inv ≫ 𝒢.unitHomEquiv.symm t)))

/-- Helper for Lemma 17.4.3: pairwise pure tensors of two spanning families span the tensor
product. -/
lemma span_range_tmul_eq_top
    {R : Type*} [CommRing R]
    {ι κ : Type*}
    {M N : Type*}
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (a : ι → M) (b : κ → N)
    (ha : Submodule.span R (Set.range a) = ⊤)
    (hb : Submodule.span R (Set.range b) = ⊤) :
    Submodule.span R (Set.range fun ij : ι × κ ↦ a ij.1 ⊗ₜ[R] b ij.2) = ⊤ := by
  let S : Submodule R (TensorProduct R M N) :=
    Submodule.span R (Set.range fun ij : ι × κ ↦ a ij.1 ⊗ₜ[R] b ij.2)
  have hmem :
      ∀ m : M, m ∈ Submodule.span R (Set.range a) →
        ∀ n : N, n ∈ Submodule.span R (Set.range b) →
          TensorProduct.tmul R m n ∈ S := by
    intro m hm n hn
    exact Submodule.span_induction₂
      (p := fun x y _ _ ↦ TensorProduct.tmul R x y ∈ S)
      (fun m n hm_range hn_range ↦ by
        rcases hm_range with ⟨i, rfl⟩
        rcases hn_range with ⟨j, rfl⟩
        exact
          Submodule.subset_span (R := R)
            (s := Set.range fun ij : ι × κ ↦ TensorProduct.tmul R (a ij.1) (b ij.2))
            (by exact ⟨(i, j), rfl⟩))
      (fun n _ ↦ by
        simpa [S, TensorProduct.zero_tmul] using
          (show (0 : TensorProduct R M N) ∈ S from Submodule.zero_mem S))
      (fun m _ ↦ by
        simpa [S, TensorProduct.tmul_zero] using
          (show (0 : TensorProduct R M N) ∈ S from Submodule.zero_mem S))
      (fun x y z _ _ _ hxz hyz ↦ by
        simpa [TensorProduct.add_tmul] using Submodule.add_mem S hxz hyz)
      (fun x y z _ _ _ hxy hxz ↦ by
        simpa [TensorProduct.tmul_add] using Submodule.add_mem S hxy hxz)
      (fun r x y _ _ hxy ↦ by
        simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem S r hxy)
      (fun r x y _ _ hxy ↦ by
        simpa [TensorProduct.tmul_smul] using Submodule.smul_mem S r hxy)
      hm hn
  rw [← top_le_iff]
  intro z hz
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact Submodule.zero_mem S
  · intro m n
    exact hmem m (by simpa [ha]) n (by simpa [hb])
  · intro z₁ z₂ hz₁ hz₂
    exact Submodule.add_mem S hz₁ hz₂

/-- Helper for Lemma 17.4.3: the stalk of the tensor product module sheaf is canonically
isomorphic to the tensor product of the two stalk modules. -/
noncomputable def tensor_product_stalk_iso_local
    (ℱ 𝒢 : ModX) (x : X) :
    RingedSpace.stalkModuleCat (ℱ ⊗ₘ 𝒢 : ModX) x ≅
      RingedSpace.stalkModuleCat ℱ x ⊗ RingedSpace.stalkModuleCat 𝒢 x := sorry

/-- Helper for Lemma 17.4.3: under the local tensor-stalk comparison, the germ of a tensor section
becomes the pure tensor of the two corresponding germs. -/
lemma tensor_section_germ_eq_tmul
    (x : X) (s : ℱ.sections) (t : 𝒢.sections) :
    (tensor_product_stalk_iso_local (ℱ := ℱ) (𝒢 := 𝒢) x).hom
        (Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x ((tensorSection s t).1 (op ⊤))) =
      Γgerm ℱ.val.presheaf x (s.1 (op ⊤)) ⊗ₜ[X.presheaf.stalk x]
        Γgerm 𝒢.val.presheaf x (t.1 (op ⊤)) := by
  sorry

/-- Helper for Lemma 17.4.3: the tensor family built from two generating families spans every
stalk of the tensor product. -/
lemma tensor_generating_family_stalkwise_span_eq_top
    (σ : ℱ.GeneratingSections) (τ : 𝒢.GeneratingSections) :
    ∀ x : X,
      Submodule.span (X.presheaf.stalk x)
        (Set.range fun ij : σ.I × τ.I ↦
          Γgerm (ℱ ⊗ₘ 𝒢 : ModX).val.presheaf x
            ((tensorSection (σ.s ij.1) (τ.s ij.2)).1 (op ⊤))) = ⊤ := by
  sorry

namespace SheafOfModules.GeneratingSections

/-- Tensor two chosen generating families to obtain a generating family of the ambient tensor
product `ℱ ⊗ₘ 𝒢`. -/
noncomputable def tensor (σ : ℱ.GeneratingSections) (τ : 𝒢.GeneratingSections) :
    (ℱ ⊗ₘ 𝒢 : ModX).GeneratingSections where
  I := σ.I × τ.I
  s ij := tensorSection (σ.s ij.1) (τ.s ij.2)
  epi := by
    -- Route correction: the intended stalkwise closure route is now isolated into the three local
    -- tensor-stalk helper declarations above.
    sorry

end SheafOfModules.GeneratingSections

/-- Lemma 17.4.3: if two `\mathcal O_X`-modules are generated by global sections, then their
tensor product `ℱ ⊗ₘ 𝒢` is also generated by global sections. -/
theorem nonempty_generatingSections_tensor
    (hℱ : Nonempty ℱ.GeneratingSections) (h𝒢 : Nonempty 𝒢.GeneratingSections) :
    Nonempty ((ℱ ⊗ₘ 𝒢 : ModX).GeneratingSections) := by
  rcases hℱ with ⟨σ⟩
  rcases h𝒢 with ⟨τ⟩
  exact ⟨SheafOfModules.GeneratingSections.tensor σ τ⟩

end AlgebraicGeometry.RingedSpace
