import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.RingTheory.Flat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

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
