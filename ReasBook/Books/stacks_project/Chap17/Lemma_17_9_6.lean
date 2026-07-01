import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap17.Lemma_17_9_5

open CategoryTheory Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.9.6:
- primary domain: support of finite-type `\mathcal O_X`-modules on a ringed space and its local
  vanishing criterion;
- inspected owner declarations:
  `moduleSupport`,
  `mem_moduleSupport_iff`,
  `exists_open_neighborhood_restriction_isZero_of_stalk_isZero`,
  `TopCat.Presheaf.germ_exist`;
- best owner abstraction: the source-facing owner remains `moduleSupport`; the local-zero
  neighborhood comes from Lemma `17.9.5`, while sectionwise vanishing on smaller opens is derived
  through the canonical evaluation functor and the standard stalk-representation theorem, instead
  of a bespoke restriction wrapper;
- primitive data: a ringed space `X`, a module sheaf `ℱ : X.Modules`, and the finite-type owner
  `[ℱ.IsFiniteType]`;
- derived API: closedness of `moduleSupport ℱ`.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that the support of a finite-type module sheaf is closed;
- `core/canonical`: `moduleSupport` together with `IsZero (ℱ.over U)` on a neighborhood;
- `bridge/view`: `mem_moduleSupport_iff`, `TopCat.Presheaf.germ_exist`, and
  `SheafOfModules.evaluation`, which turn local zero sheaves into sectionwise vanishing of stalk
  representatives. -/

-- Proof sketch: if `x` is outside the support, then the stalk `ℱ_x` is zero. Lemma `17.9.5`
-- gives an open neighbourhood `U` of `x` on which `ℱ|_U` is the zero sheaf. Evaluating that zero
-- sheaf on any smaller open `W ⊆ U` shows every restricted local section vanishes. Any stalk
-- element at a point of `U` is represented by such a local section, so every stalk on `U` is
-- zero. Thus the
-- complement of the support is open.
/-- Lemma 17.9.6: if `ℱ` is a finite type `\mathcal O_X`-module on a ringed space `X`, then the
support of `ℱ` is closed. -/
theorem isClosed_moduleSupport_of_isFiniteType
    {X : RingedSpace.{u}} (ℱ : X.Modules)
    [ℱ.IsFiniteType] :
    IsClosed (moduleSupport ℱ) := by
  let F := PresheafOfModules.presheaf ℱ.val
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hx_not_mem : x ∉ moduleSupport ℱ := by
    simpa [Set.mem_compl_iff] using hx
  have hx_subsingleton : Subsingleton ↑(RingedSpace.stalkModuleCat ℱ x) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnontrivial
    rcases (nontrivial_iff_exists_ne (0 : ↑(RingedSpace.stalkModuleCat ℱ x))).1 hnontrivial with
      ⟨m, hm⟩
    exact hx_not_mem ((mem_moduleSupport_iff ℱ x).2 ⟨m, hm⟩)
  have hx_zero : IsZero (RingedSpace.stalkModuleCat ℱ x) :=
    (ModuleCat.isZero_iff_subsingleton).2 hx_subsingleton
  rcases exists_open_neighborhood_restriction_isZero_of_stalk_isZero ℱ x hx_zero with
    ⟨U, hxU, hU_zero⟩
  refine Filter.mem_of_superset (U.2.mem_nhds hxU) fun y hyU ↦ ?_
  have hy_not_mem : y ∉ moduleSupport ℱ := by
    intro hy_mem
    rcases (mem_moduleSupport_iff ℱ y).1 hy_mem with ⟨m, hm⟩
    obtain ⟨V, hyV, s, hs⟩ := TopCat.Presheaf.germ_exist F y m
    let W : Opens X := V ⊓ U
    let yW : W := ⟨y, ⟨hyV, hyU⟩⟩
    let t : ℱ.val.obj (op W) := F.map (homOfLE inf_le_left).op s
    let evalW :=
      SheafOfModules.evaluation (X.ringCatSheaf.over U)
        (op <| Over.mk (homOfLE inf_le_right : W ⟶ U))
    letI : evalW.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    have hW_zero :
        IsZero (evalW.obj (ℱ.over U)) :=
      Functor.map_isZero evalW hU_zero
    have hW_subsingleton : Subsingleton (ℱ.val.obj (op W)) := by
      simpa [SheafOfModules.over, SheafOfModules.pushforward, SheafOfModules.evaluation, W] using
        (ModuleCat.isZero_iff_subsingleton.1 hW_zero)
    have ht_zero : t = 0 := hW_subsingleton.elim _ _
    have hm_zero : m = 0 := by
      calc
        m = TopCat.Presheaf.germ F V y hyV s := hs.symm
        _ = TopCat.Presheaf.germ F W y yW.2 t := by
          rw [show t = F.map (homOfLE inf_le_left).op s by rfl]
          symm
          exact TopCat.Presheaf.germ_res_apply F (homOfLE inf_le_left) y yW.2 s
        _ = 0 := by
          rw [ht_zero]
          change (TopCat.Presheaf.germ F W y yW.2).hom 0 = 0
          exact (TopCat.Presheaf.germ F W y yW.2).hom.map_zero
    exact hm hm_zero
  simpa [Set.mem_compl_iff] using hy_not_mem

end AlgebraicGeometry
