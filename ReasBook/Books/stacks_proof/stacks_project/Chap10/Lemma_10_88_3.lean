import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_88_2
import stacks_proof.stacks_project.Chap10.Lemma_10_11_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommMonoid M] [Module R M]
variable {N : Type u} [AddCommMonoid N] [Module R N]
variable {M' : Type u} [AddCommMonoid M'] [Module R M']

/-- Helper for Lemma 10.88.3: every `R`-module admits a filtered colimit presentation by finitely
presented stages. -/
lemma finite_presentation_stage_presentation
    {Q : Type u} [AddCommGroup Q] [Module R Q] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (pres : ColimitPresentation J (ModuleCat.of R Q)),
        ∀ j, Module.FinitePresentation R (pres.diag.obj j) := by
  -- Reuse the earlier owner theorem that every module is a filtered colimit of finitely presented
  -- modules and unpack the existential data it already provides.
  simpa [CategoryTheory.ObjectProperty.ind] using
    (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented
      (R := R) (M := ModuleCat.of R Q))

/-- Helper for Lemma 10.88.3: every tensor element over a filtered colimit module comes from some
finitely presented stage after tensoring on the left by a fixed module. -/
lemma exists_tensor_left_stage_lift
    {L : Type u} [AddCommGroup L] [Module R L]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of R Q))
    (x : L ⊗[R] Q) :
    ∃ (j : J) (xj : L ⊗[R] pres.diag.obj j), ((pres.ι.app j).hom.lTensor L) xj = x := by
  let T : ModuleCat R ⥤ ModuleCat R := MonoidalCategory.tensorLeft (ModuleCat.of R L)
  let tensorCocone : Cocone (pres.diag ⋙ T) := T.mapCocone pres.cocone
  -- Tensoring on the left preserves the filtered colimit presentation.
  have htensorCocone : IsColimit tensorCocone := by
    exact isColimitOfPreserves T pres.isColimit
  obtain ⟨j, xj, hxj⟩ :=
    Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget (ModuleCat R)) htensorCocone) x
  refine ⟨j, xj, ?_⟩
  -- Reinterpret the abstract colimit leg as the expected left-tensor map.
  simpa [tensorCocone, T, ModuleCat.hom_whiskerLeft] using hxj

/-- Helper for Lemma 10.88.3: if a tensor element becomes zero in the colimit after tensoring on
the left by a fixed module, then it is already zero at some later filtered stage. -/
lemma exists_later_stage_lTensor_eq_zero
    {L : Type u} [AddCommGroup L] [Module R L]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (pres : ColimitPresentation J (ModuleCat.of R Q))
    {j : J} {y : L ⊗[R] pres.diag.obj j}
    (hy : ((pres.ι.app j).hom.lTensor L) y = 0) :
    ∃ (j' : J) (w : j ⟶ j'), ((pres.diag.map w).hom.lTensor L) y = 0 := by
  let T : ModuleCat R ⥤ ModuleCat R := MonoidalCategory.tensorLeft (ModuleCat.of R L)
  let tensorCocone : Cocone (pres.diag ⋙ T) := T.mapCocone pres.cocone
  -- Tensoring on the left preserves filtered colimits, so equality in the colimit stabilizes.
  have htensorCocone : IsColimit tensorCocone := by
    exact isColimitOfPreserves T pres.isColimit
  have hy_eq :
      ((forget (ModuleCat R)).map (tensorCocone.ι.app j)) y =
        ((forget (ModuleCat R)).map (tensorCocone.ι.app j)) (0 : L ⊗[R] pres.diag.obj j) := by
    simpa [tensorCocone, T, ModuleCat.hom_whiskerLeft] using hy
  obtain ⟨j', w, hw⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget (ModuleCat R)) htensorCocone) y 0).1 hy_eq
  refine ⟨j', w, ?_⟩
  -- Translate the eventual equality in the underlying type back to the left-tensor map.
  simpa [T, ModuleCat.hom_whiskerLeft] using hw

-- Proof sketch: the forward implication is immediate from the definition. For the converse, write
-- an arbitrary `R`-module as a directed colimit of finitely presented modules and use that tensor
-- product commutes with directed colimits and those colimits are exact.
/-- Lemma 10.88.3: a map `g` dominates a map `f` if and only if it suffices to test the tensor
kernel inclusion `ker (f ⊗ 1_Q) ⊆ ker (g ⊗ 1_Q)` on finitely presented `R`-modules `Q`. -/
@[stacks 059C]
theorem dominates_iff_forall_finitePresentation
    (g : M →ₗ[R] M') (f : M →ₗ[R] N) :
    g.Dominates f ↔
      ∀ (Q : Type u) [AddCommMonoid Q] [Module R Q]
        [Module.FinitePresentation R Q],
        ker (f.rTensor Q) ≤ ker (g.rTensor Q) := by
  rw [dominates_iff]
  constructor
  · intro h Q _ _ _
    -- The forward implication is the defining kernel inclusion specialized to a finitely presented
    -- test module.
    exact h Q
  · intro h Q _ _
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
    letI : AddCommGroup M' := Module.addCommMonoidToAddCommGroup R (M := M')
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R (M := Q)
    -- For the converse, descend a kernel element to one finitely presented stage of a filtered
    -- colimit presentation of `Q`.
    obtain ⟨J, _, _, pres, hpres⟩ := finite_presentation_stage_presentation (R := R) (Q := Q)
    intro x hx
    obtain ⟨j, xj, hxj⟩ := exists_tensor_left_stage_lift (L := M) (pres := pres) x
    have hx_zero : (f.rTensor Q) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hι_comm :
        ((pres.ι.app j).hom.lTensor N).comp (f.rTensor (pres.diag.obj j)) =
          (f.rTensor Q).comp ((pres.ι.app j).hom.lTensor M) := by
      ext z y
      rfl
    have hy_zero :
        ((pres.ι.app j).hom.lTensor N) ((f.rTensor (pres.diag.obj j)) xj) = 0 := by
      -- Naturality identifies tensoring `f` after the stage map with tensoring the stage map after
      -- `f`, so the lifted element still dies in the colimit.
      have hι_comm_apply :
          ((pres.ι.app j).hom.lTensor N) ((f.rTensor (pres.diag.obj j)) xj) =
            (f.rTensor Q) (((pres.ι.app j).hom.lTensor M) xj) :=
        congrArg (fun k ↦ k xj) hι_comm
      rw [hι_comm_apply, hxj]
      exact hx_zero
    obtain ⟨j', w, hw_zero⟩ :=
      exists_later_stage_lTensor_eq_zero (L := N) (pres := pres) (j := j) hy_zero
    let xj' : M ⊗[R] pres.diag.obj j' := ((pres.diag.map w).hom.lTensor M) xj
    have hw_comm :
        ((pres.diag.map w).hom.lTensor N).comp (f.rTensor (pres.diag.obj j)) =
          (f.rTensor (pres.diag.obj j')).comp ((pres.diag.map w).hom.lTensor M) := by
      ext z y
      rfl
    have hxj'_zero : (f.rTensor (pres.diag.obj j')) xj' = 0 := by
      -- Route correction: instead of unfolding the filtered colimit, rewrite both composites as the
      -- same tensor-product map and read off the stagewise vanishing.
      have hw_comm_apply :
          ((pres.diag.map w).hom.lTensor N) ((f.rTensor (pres.diag.obj j)) xj) =
            (f.rTensor (pres.diag.obj j')) (((pres.diag.map w).hom.lTensor M) xj) :=
        congrArg (fun k ↦ k xj) hw_comm
      calc
        (f.rTensor (pres.diag.obj j')) xj'
            = ((pres.diag.map w).hom.lTensor N) ((f.rTensor (pres.diag.obj j)) xj) := by
                simpa [xj'] using hw_comm_apply.symm
        _ = 0 := hw_zero
    have hxj'_mem : xj' ∈ ker (f.rTensor (pres.diag.obj j')) := by
      simpa [LinearMap.mem_ker, xj'] using hxj'_zero
    letI : Module.FinitePresentation R (pres.diag.obj j') := hpres j'
    have hstage :
        ker (f.rTensor (pres.diag.obj j')) ≤ ker (g.rTensor (pres.diag.obj j')) :=
      h (pres.diag.obj j')
    have hg_stage_zero : (g.rTensor (pres.diag.obj j')) xj' = 0 := by
      simpa [LinearMap.mem_ker, xj'] using hstage hxj'_mem
    have hxj'_map : ((pres.ι.app j').hom.lTensor M) xj' = x := by
      -- Naturality of the cocone identifies the later-stage lift with the original tensor element.
      have hιw :
          (pres.ι.app j').hom.comp (pres.diag.map w).hom = (pres.ι.app j).hom := by
        simpa using congrArg ModuleCat.Hom.hom (pres.w w)
      have hιw_apply :
          ((pres.ι.app j').hom.lTensor M) (((pres.diag.map w).hom.lTensor M) xj) =
            ((pres.ι.app j).hom.lTensor M) xj := by
        calc
          ((pres.ι.app j').hom.lTensor M) (((pres.diag.map w).hom.lTensor M) xj)
              = (((pres.ι.app j').hom.comp (pres.diag.map w).hom).lTensor M) xj := by
                  simpa using
                    (LinearMap.lTensor_comp_apply (M := M) (f := (pres.diag.map w).hom)
                      (g := (pres.ι.app j').hom) (x := xj)).symm
          _ = ((pres.ι.app j).hom.lTensor M) xj := by
                simpa using congrArg (fun k ↦ k.lTensor M xj) hιw
      have hxj'_map_to_stage :
          ((pres.ι.app j').hom.lTensor M) xj' = ((pres.ι.app j).hom.lTensor M) xj := by
        simpa [xj'] using hιw_apply
      exact hxj'_map_to_stage.trans hxj
    have hg_comm :
        (g.rTensor Q).comp ((pres.ι.app j').hom.lTensor M) =
          ((pres.ι.app j').hom.lTensor M').comp (g.rTensor (pres.diag.obj j')) := by
      ext z y
      rfl
    have hxg_zero : (g.rTensor Q) x = 0 := by
      -- Push the stagewise vanishing of `g` forward along the cocone to the original module `Q`.
      have hg_comm_apply :
          (g.rTensor Q) (((pres.ι.app j').hom.lTensor M) xj') =
            ((pres.ι.app j').hom.lTensor M') ((g.rTensor (pres.diag.obj j')) xj') :=
        congrArg (fun k ↦ k xj') hg_comm
      calc
        (g.rTensor Q) x = (g.rTensor Q) (((pres.ι.app j').hom.lTensor M) xj') := by
          rw [← hxj'_map]
        _ = ((pres.ι.app j').hom.lTensor M') ((g.rTensor (pres.diag.obj j')) xj') := hg_comm_apply
        _ = 0 := by
          rw [hg_stage_zero]
          simpa using LinearMap.map_zero ((pres.ι.app j').hom.lTensor M')
    simpa [LinearMap.mem_ker] using hxg_zero

end

end LinearMap
