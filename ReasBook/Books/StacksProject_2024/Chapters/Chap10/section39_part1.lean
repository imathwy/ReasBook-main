import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_39_1 (from Chap10) -/
universe u v

section module_flat

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Definition 10.39.1 (1): an `R`-module `M` is flat when tensoring with `M` preserves exact
sequences; the canonical mathlib predicate for this notion is `Module.Flat R M`. -/
recall Module.Flat

/- Companion recall: the textbook exact-sequence formulation of flatness is the canonical
equivalence `Module.Flat.iff_lTensor_preserves_shortComplex_exact`. -/
recall Module.Flat.iff_lTensor_preserves_shortComplex_exact

/- Definition 10.39.1 (2): an `R`-module `M` is faithfully flat when tensoring with `M`
preserves and reflects exact sequences; the canonical mathlib predicate for this notion is
`Module.FaithfullyFlat R M`. -/
recall Module.FaithfullyFlat

/- Companion recall: the textbook exact-sequence characterization of faithful flatness is the
canonical equivalence `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`. -/
recall Module.FaithfullyFlat.iff_exact_iff_lTensor_exact

end module_flat

section ring_hom_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- Definition 10.39.1 (3): a ring map `f : R →+* S` is flat when `S` is flat as an `R`-module;
the canonical mathlib predicate for this notion is `RingHom.Flat f`. -/
recall RingHom.Flat

/- Definition 10.39.1 (4): a ring map `f : R →+* S` is faithfully flat when `S` is faithfully flat
as an `R`-module; the canonical mathlib predicate for this notion is `RingHom.FaithfullyFlat f`. -/
recall RingHom.FaithfullyFlat

end ring_hom_flat

section algebra_flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Companion recall for Definition 10.39.1 (3): for the canonical algebra map, the textbook
wording "flat as an `R`-module" is exactly `RingHom.flat_algebraMap_iff`. -/
recall RingHom.flat_algebraMap_iff

/- Companion recall for Definition 10.39.1 (4): for the canonical algebra map, the textbook
wording "faithfully flat as an `R`-module" is exactly
`RingHom.faithfullyFlat_algebraMap_iff`. -/
recall RingHom.faithfullyFlat_algebraMap_iff

end algebra_flat

/-! ### Lemma_10_39_2 (from Chap10) -/
open TensorProduct LinearMap
open scoped TensorProduct

universe u v

namespace Ideal

/-
Domain triage: this file is `source-facing` for the flat-module intersection identity
`IM ∩ JM = (I ∩ J) M`. For the algebra specialization, the owner abstraction is the
`InfTopHom` on ideals induced by `Ideal.map (algebraMap R S)` under flatness. Primitive data:
the flat module/algebra structure. Derived API: the algebra-valued reformulation and the
bundled `InfTopHom` used by later finite-intersection arguments.
-/

section Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Flat R M]

/- The intersection of the images of two ideals on a flat module is the image of their
intersection. -/
-- Proof sketch: identify
-- `M → (R ⧸ I) ⊗[R] M × (R ⧸ J) ⊗[R] M`
-- with the tensor of `R → R ⧸ I × R ⧸ J`, use flatness to compute its kernel as the tensor of
-- `I ∩ J`, and then rewrite the resulting tensor-image as `(I ∩ J) • ⊤`.
/-- Lemma 10.39.2: for ideals `I` and `J` of a commutative ring `R` and a flat `R`-module `M`,
their images in `M` satisfy `IM ∩ JM = (I ∩ J)M`. -/
@[stacks 0BBY]
theorem smul_top_inf_smul_top_eq_inf_smul_top_of_flat (I J : Ideal R) :
    I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M) = (I ⊓ J) • (⊤ : Submodule R M) := by
  let f : R →ₗ[R] (R ⧸ I) × (R ⧸ J) := I.mkQ.prod J.mkQ
  let l : R ⊗[R] M ≃ₗ[R] M := TensorProduct.lid R M
  let e : ((R ⧸ I) × (R ⧸ J)) ⊗[R] M ≃ₗ[R]
      ((R ⧸ I) ⊗[R] M) × ((R ⧸ J) ⊗[R] M) :=
    prodLeft R R (R ⧸ I) (R ⧸ J) M
  have hmap :
      (e.toLinearMap.comp (f.rTensor M)).comp l.symm.toLinearMap =
        (mk R (R ⧸ I) M 1).prod (mk R (R ⧸ J) M 1) := by
    ext m <;> simp [f, l, e]
  have hker_tensor :
      ker (f.rTensor M) = range ((ker f).subtype.rTensor M) := by
    rw [← exact_iff]
    exact Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map f)
  have hker : LinearMap.ker f = I ⊓ J := by
    ext r
    simp [f, ker_prod]
  calc
    I • (⊤ : Submodule R M) ⊓ J • (⊤ : Submodule R M)
        = ker ((mk R (R ⧸ I) M 1).prod (mk R (R ⧸ J) M 1)) := by
            rw [ker_prod, ker_tensorProductMk, ker_tensorProductMk]
    _ = ker ((e.toLinearMap.comp (f.rTensor M)).comp l.symm.toLinearMap) := by
          rw [hmap]
    _ = (I ⊓ J) • (⊤ : Submodule R M) := by
          rw [ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.ker_comp, hker_tensor,
            ← range_comp, hker]
          simpa using Ideal.subtype_rTensor_range M (I ⊓ J)

end Module

section Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]

/-- For a flat `R`-algebra `S`, extension of ideals along `R → S` preserves binary intersections.

This is the algebra-valued specialization of Lemma 10.39.2, rewritten using
`Ideal.smul_top_eq_map`. -/
theorem map_inf_of_flat (I J : Ideal R) :
    Ideal.map (algebraMap R S) (I ⊓ J) =
      Ideal.map (algebraMap R S) I ⊓ Ideal.map (algebraMap R S) J := by
  have h :
      I • (⊤ : Submodule R S) ⊓ J • (⊤ : Submodule R S) = (I ⊓ J) • (⊤ : Submodule R S) :=
    smul_top_inf_smul_top_eq_inf_smul_top_of_flat I J
  apply Submodule.restrictScalars_injective R
  simpa [Ideal.smul_top_eq_map] using h.symm

/-- For a flat `R`-algebra `S`, ideal extension along `R → S` preserves finite intersections and
the top ideal. This is the owner abstraction used when later arguments need the ideal-extension
map as an `InfTopHom`. -/
def mapInfTopHom : InfTopHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := map_inf_of_flat
  map_top' := map_top _

@[simp] theorem mapInfTopHom_apply (I : Ideal R) :
    mapInfTopHom I = Ideal.map (algebraMap R S) I := rfl

end Algebra

end Ideal

/-! ### Lemma_10_39_3 (from Chap10) -/
open CategoryTheory Limits MonoidalCategory

universe u v

section

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Helper for Lemma 10.39.3: a filtered colimit of injective maps of types is injective. -/
theorem type_colimit_map_injective_of_app_injective
    {F G : J ⥤ Type (max u v)} (η : F ⟶ G)
    (hη : ∀ j, Function.Injective (η.app j)) :
    Function.Injective (colim.map η) := by
  intro x y hxy
  obtain ⟨i, x', y', rfl, rfl⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂ (colimit.isColimit F) x y
  have hxy' : colimit.ι G i (η.app i x') = colimit.ι G i (η.app i y') := by
    simpa using hxy
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (F := G) (colimit.isColimit G)
      (η.app i x') (η.app i y')).1 hxy'
  have hf' : η.app j (F.map f x') = η.app j (F.map f y') := by
    have hnatx : η.app j (F.map f x') = G.map f (η.app i x') := by
      simpa using congrFun (η.naturality f) x'
    have hnaty : η.app j (F.map f y') = G.map f (η.app i y') := by
      simpa using congrFun (η.naturality f) y'
    exact hnatx.trans (hf.trans hnaty.symm)
  apply Types.colimit_sound' f f
  exact hη j hf'

end

section

variable {R : Type u} [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- Helper for Lemma 10.39.3: tensoring a linear map on the right commutes with the transition
morphisms in a module diagram. -/
theorem lTensor_naturality
    {M M' N N' : ModuleCat.{u} R}
    (α : M ⟶ M') (f : N ⟶ N') :
    (α ▷ N) ≫ ModuleCat.ofHom (f.hom.lTensor M') =
      ModuleCat.ofHom (f.hom.lTensor M) ≫ (α ▷ N') := by
  -- Both sides identify with the canonical tensor-product map `TensorProduct.map α f`.
  apply ModuleCat.hom_ext
  change (f.hom.lTensor M').comp ((α ▷ N).hom) = ((α ▷ N').hom).comp (f.hom.lTensor M)
  rw [ModuleCat.hom_whiskerRight, ModuleCat.hom_whiskerRight]
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

/-- Helper for Lemma 10.39.3: a diagram morphism induces a natural transformation after tensoring
the codomain modules on the right by a fixed linear map. -/
def lTensor_natTrans
    (F : J ⥤ ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') :
    F ⋙ tensorRight N ⟶ F ⋙ tensorRight N' where
  app j := ModuleCat.ofHom (f.hom.lTensor (F.obj j))
  naturality _ _ g := lTensor_naturality (R := R) (F.map g) f

section

omit [IsFiltered J]

/-- Helper for Lemma 10.39.3: stagewise monomorphisms assemble into a monomorphism of natural
transformations. -/
theorem mono_natTrans_of_mono_app
    {X₁ X₂ : J ⥤ ModuleCat.{u} R} (φ : X₁ ⟶ X₂)
    (hmono : ∀ j, Mono (φ.app j)) :
    Mono φ := by
  -- The functor-category mono criterion is exactly stagewise monicity.
  letI : ∀ j, Mono (φ.app j) := hmono
  exact NatTrans.mono_of_mono_app φ

end

/-- Helper for Lemma 10.39.3: compatibility with a stagewise mono natural transformation induces a
mono map between filtered colimit cocone points in `ModuleCat`. -/
theorem ModuleCat.mono_of_isColimit_of_mono_app
    {X₁ X₂ : J ⥤ ModuleCat.{u} R}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (φ : X₁ ⟶ X₂) (f : c₁.pt ⟶ c₂.pt)
    (hf : ∀ j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j)
    (hmono : ∀ j, Mono (φ.app j)) :
    Mono f := by
  rw [ModuleCat.mono_iff_injective]
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := R)
  let c₁' : Cocone (X₁ ⋙ forget (ModuleCat.{u} R)) := (forget (ModuleCat.{u} R)).mapCocone c₁
  let c₂' : Cocone (X₂ ⋙ forget (ModuleCat.{u} R)) := (forget (ModuleCat.{u} R)).mapCocone c₂
  have hc₁' : IsColimit c₁' := by
    simpa [c₁'] using Limits.isColimitOfPreserves (forget (ModuleCat.{u} R)) hc₁
  have hc₂' : IsColimit c₂' := by
    simpa [c₂'] using Limits.isColimitOfPreserves (forget (ModuleCat.{u} R)) hc₂
  have hmono_fun : ∀ j, Function.Injective (φ.app j) := by
    intro j
    exact (ModuleCat.mono_iff_injective (φ.app j)).1 (hmono j)
  have hcompat_fun (j : J) (x : X₁.obj j) : f (c₁'.ι.app j x) = c₂'.ι.app j (φ.app j x) := by
    simpa [c₁', c₂'] using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (hf j)) x
  -- The underlying-set proof is the standard filtered-colimit injectivity argument.
  intro x₁ y₁ hxy
  obtain ⟨j, x₁', y₁', rfl, rfl⟩ : ∃ (j : J) (x₁' y₁' : X₁.obj j),
      x₁ = c₁'.ι.app j x₁' ∧ y₁ = c₁'.ι.app j y₁' := by
    obtain ⟨j, x₁', rfl⟩ := Types.jointly_surjective_of_isColimit hc₁' x₁
    obtain ⟨l, y₁', rfl⟩ := Types.jointly_surjective_of_isColimit hc₁' y₁
    exact ⟨_, _, _, congr_fun (c₁'.w (IsFiltered.leftToMax j l)).symm x₁',
      congr_fun (c₁'.w (IsFiltered.rightToMax j l)).symm y₁'⟩
  rw [hcompat_fun j x₁', hcompat_fun j y₁'] at hxy
  obtain ⟨k, α, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₂' _ _).1 hxy
  have hk' : φ.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α x₁') =
      φ.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α y₁') := by
    have hnatx :
        φ.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α x₁') =
          (X₂ ⋙ forget (ModuleCat.{u} R)).map α (φ.app j x₁') := by
      simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (φ.naturality α)) x₁'
    have hnaty :
        φ.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α y₁') =
          (X₂ ⋙ forget (ModuleCat.{u} R)).map α (φ.app j y₁') := by
      simpa using DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (φ.naturality α)) y₁'
    exact hnatx.trans (hk.trans hnaty.symm)
  have hmap : (X₁ ⋙ forget (ModuleCat.{u} R)).map α x₁' =
      (X₁ ⋙ forget (ModuleCat.{u} R)).map α y₁' := hmono_fun _ hk'
  have hxk : c₁'.ι.app j x₁' = c₁'.ι.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α x₁') := by
    exact congr_fun (c₁'.w α).symm x₁'
  have hyk : c₁'.ι.app j y₁' = c₁'.ι.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α y₁') := by
    exact congr_fun (c₁'.w α).symm y₁'
  have hι :
      c₁'.ι.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α x₁') =
        c₁'.ι.app k ((X₁ ⋙ forget (ModuleCat.{u} R)).map α y₁') := by
    rw [hmap]
  exact hxk.trans (hι.trans hyk.symm)

section

omit [IsFiltered J]

/-- Helper for Lemma 10.39.3: the tensorized cocone maps commute with tensoring by the chosen
linear map. -/
theorem lTensor_natTrans_colimit_compat
    (F : J ⥤ ModuleCat.{u} R) (c : Cocone F)
    {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
    (f : N →ₗ[R] N') :
    ∀ j,
      ((tensorRight (ModuleCat.of R N)).mapCocone c).ι.app j ≫ ModuleCat.ofHom (f.lTensor c.pt) =
        (lTensor_natTrans (R := R) F (ModuleCat.ofHom f)).app j ≫
          ((tensorRight (ModuleCat.of R N')).mapCocone c).ι.app j := by
  intro j
  -- This is exactly the naturality square for right tensoring by `f`.
  simpa [lTensor_natTrans] using
    lTensor_naturality (R := R) (c.ι.app j) (ModuleCat.ofHom f)

end

-- Proof sketch: first prove the chosen-colimit case using
-- `Module.Flat.iff_lTensor_preserves_shortComplex_exact`. Tensoring with a colimit commutes with
-- filtered colimits, and `ModuleCat R` satisfies `AB5`, so filtered colimits preserve exact short
-- complexes. The general colimit-cocone form then follows by transporting flatness across the
-- canonical isomorphism from any colimit cocone to `colimit F`.
/-- Lemma 10.39.3: if `c` is a colimit cocone of a filtered diagram of flat `R`-modules, then
its cocone point is a flat `R`-module. This is the canonical filtered-diagram formulation of the
source's directed-system statement. -/
theorem flat_of_isColimit_filtered_system
    (F : J ⥤ ModuleCat.{u} R) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R c.pt := by
  -- Use the injectivity criterion for flatness, so it suffices to preserve injective linear maps
  -- after tensoring with the cocone point.
  refine (Module.Flat.iff_lTensor_preserves_injective_linearMap' (R := R) (M := c.pt)).2 ?_
  intro N N' _ _ _ _ f hf
  let φ :
      F ⋙ tensorRight (ModuleCat.of R N) ⟶
        F ⋙ tensorRight (ModuleCat.of R N') :=
    lTensor_natTrans (R := R) F (ModuleCat.ofHom f)
  let cN : Cocone (F ⋙ tensorRight (ModuleCat.of R N)) := (tensorRight (ModuleCat.of R N)).mapCocone c
  let cN' : Cocone (F ⋙ tensorRight (ModuleCat.of R N')) :=
    (tensorRight (ModuleCat.of R N')).mapCocone c
  have hcN : IsColimit cN := by
    simpa [cN] using
      (Limits.isColimitOfPreserves (tensorRight (ModuleCat.of R N)) hc)
  have hcN' : IsColimit cN' := by
    simpa [cN'] using
      (Limits.isColimitOfPreserves (tensorRight (ModuleCat.of R N')) hc)
  have hφ_app : ∀ j, Mono (φ.app j) := by
    intro j
    rw [ModuleCat.mono_iff_injective]
    -- At each stage this is exactly the tensor of `f`, so stagewise flatness
    -- gives injectivity.
    simpa [φ] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := F.obj j) f hf
  have hcompat :
      ∀ j, cN.ι.app j ≫ ModuleCat.ofHom (f.lTensor c.pt) = φ.app j ≫ cN'.ι.app j := by
    intro j
    -- The tensorized cocone maps satisfy the same naturality square at each stage.
    simpa [cN, cN', φ] using lTensor_natTrans_colimit_compat (R := R) F c f j
  have hmono_tensor : Mono (ModuleCat.ofHom (f.lTensor c.pt)) := by
    -- Pass stagewise injectivity through the filtered colimit in `ModuleCat`.
    exact ModuleCat.mono_of_isColimit_of_mono_app
      (R := R) (J := J) cN cN' hcN hcN' φ (ModuleCat.ofHom (f.lTensor c.pt)) hcompat hφ_app
  -- Convert the categorical mono statement back to injectivity of the underlying linear map.
  exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom (f.lTensor c.pt))).1 hmono_tensor

/-- Filtered colimits of diagrams of flat modules carry the canonical flatness instance. -/
instance (F : J ⥤ ModuleCat.{u} R) [HasColimit F] [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R ↑(colimit F) := by
  simpa using flat_of_isColimit_filtered_system F (colimit.cocone F) (colimit.isColimit F)

end

/-! ### Lemma_10_39_4 (from Chap10) -/
/- Lemma 10.39.4: compositions of flat ring homomorphisms are flat. -/
recall RingHom.Flat.comp

/- Companion recall: compositions of faithfully flat ring homomorphisms are faithfully flat.
Mathlib packages this as stability under composition of `RingHom.FaithfullyFlat`. -/
recall RingHom.FaithfullyFlat.stableUnderComposition

/- Companion recall: if `R → R'` is flat and `M'` is a flat `R'`-module, then `M'` is flat as an
`R`-module. -/
recall Module.Flat.trans

/- Companion recall: if `R → R'` is faithfully flat and `M'` is a faithfully flat `R'`-module,
then `M'` is faithfully flat as an `R`-module. -/
recall Module.FaithfullyFlat.trans

/-! ### Lemma_10_39_5 (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.39.5, clause `(1)`: the flatness condition on the `R`-module `M` is the canonical
owner predicate `Module.Flat R M`. -/
recall Module.Flat

/- Lemma 10.39.5, clause `(2)`: flatness is exactly preservation of injective linear maps under
right tensoring. -/
recall Module.Flat.iff_rTensor_preserves_injective_linearMap

/- Lemma 10.39.5, clause `(3)`: flatness is equivalent to injectivity of `I.subtype.rTensor M`
for every ideal `I`; via `TensorProduct.lid`, this is the Stacks map `I ⊗[R] M → M`. -/
recall Module.Flat.iff_rTensor_injective'

/- Lemma 10.39.5, clause `(4)`: it suffices to test injectivity of the canonical map
`I ⊗[R] M → M` on finitely generated ideals `I`. -/
recall Module.Flat.iff_lift_lsmul_comp_subtype_injective

end
