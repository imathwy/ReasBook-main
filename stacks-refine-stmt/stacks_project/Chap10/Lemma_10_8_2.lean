import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Limits

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

noncomputable section

section

variable {I : Type u} [Preorder I]
variable {R : Type v} [Ring R]
variable (F : I ⥤ ModuleCat.{u} R)

/-
Layering for this item:
* `source-facing`: the textbook quotient-model direct limit attached to a module-valued functor on a
  preorder, viewed as a cocone over `F`;
* `core/canonical`: `ModuleCat.directLimitDiagram`, `ModuleCat.directLimitCocone`, and
  `ModuleCat.directLimitIsColimit`;
* `bridge/view`: the objectwise identification of `F` with the canonical direct-limit diagram.
-/

local instance : DecidableEq I := Classical.decEq I

local notation "M" => fun i : I ↦ F.obj i

private abbrev moduleSystemMap (i j : I) (h : i ≤ j) :
    F.obj i →ₗ[R] F.obj j :=
  (F.map (homOfLE h)).hom

local notation "μ" => fun i j h ↦ moduleSystemMap F i j h

private instance : DirectedSystem (fun i ↦ F.obj i) (fun i j h ↦ moduleSystemMap F i j h) where
  map_self i x := by
    change ((F.map (𝟙 _)).hom) x = x
    exact congr(($((F.map_id _)) x))
  map_map := by
    intro i j k hij hjk x
    change ((F.map (homOfLE hjk)).hom) (((F.map (homOfLE hij)).hom) x) =
      ((F.map (homOfLE (hij.trans hjk))).hom) x
    simpa using congr(($((F.map_comp (homOfLE hij) (homOfLE hjk)).symm) x))

private def moduleSystemDiagramIso :
    F ≅ ModuleCat.directLimitDiagram M μ :=
  NatIso.ofComponents
    (fun _ ↦ Iso.refl _)
    (fun f ↦ by
      simpa using congrArg F.map (homOfLE_leOfHom f).symm)

local notation "M∞" => Module.DirectLimit M μ

local notation "of∞" => Module.DirectLimit.of R I M μ

/-- Lemma 10.8.2: the textbook quotient-model direct limit `(⨁ i, M_i) / Q`, implemented by
`Module.DirectLimit`, carries the canonical cocone over `F`. -/
noncomputable def module_system_cocone : Cocone F :=
  (Cocone.precompose (moduleSystemDiagramIso F).hom).obj
    (ModuleCat.directLimitCocone M μ)

/-- The structure map from stage `i` into the quotient-model direct limit is the canonical map
`Module.DirectLimit.of`. -/
@[simp] theorem module_system_cocone_ι_app (i : I) :
    (module_system_cocone F).ι.app i = ModuleCat.ofHom (of∞ i) := by
  rfl

/-- Lemma 10.8.2: the explicit quotient-model cocone `module_system_cocone F` is a colimit cocone,
so it has the universal property of the direct limit described in the source. -/
noncomputable def module_system_isColimit : IsColimit (module_system_cocone F) :=
  (IsColimit.precomposeHomEquiv (moduleSystemDiagramIso F) (ModuleCat.directLimitCocone M μ)).1
    (ModuleCat.directLimitIsColimit M μ)

/-- Companion bridge: the chosen categorical colimit `colimit F` is canonically isomorphic to the
explicit quotient-model direct limit `Module.DirectLimit`. -/
noncomputable def module_system_colimit_iso_moduleDirectLimit :
    colimit F ≅ ModuleCat.of R M∞ :=
  IsColimit.coconePointsIsoOfNatIso (colimit.isColimit F) (ModuleCat.directLimitIsColimit M μ)
    (moduleSystemDiagramIso F)

/-- Under `module_system_colimit_iso_moduleDirectLimit`, the chosen colimit structure map from
stage `i` identifies with the canonical map into `Module.DirectLimit`. -/
theorem module_system_colimit_iso_moduleDirectLimit_ι (i : I) :
    colimit.ι F i ≫ (module_system_colimit_iso_moduleDirectLimit F).hom =
      ModuleCat.ofHom (of∞ i) := by
  simpa using
    IsColimit.comp_coconePointsIsoOfNatIso_hom (colimit.isColimit F)
      (ModuleCat.directLimitIsColimit M μ) (moduleSystemDiagramIso F) i

end
