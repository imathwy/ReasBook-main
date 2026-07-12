import Mathlib
import StacksProject_2024.Chap19.Definition_19_2_4
import StacksProject_2024.Chap19.«19_2_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open Ordinal.ToType

universe u

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 19.2.5: a family of stages indexed by a type of cardinality
strictly smaller than `α.cof` is dominated by one stage of `α`. -/
lemma existsStageDominatingSmallFamily
    {S : Type u} {α : Ordinal.{u}} (hS : Cardinal.mk S < α.cof) (ι : S → α.ToType) :
    ∃ j : α.ToType, ∀ s : S, ι s ≤ j := by
  -- The supremum of fewer than `α.cof` many ordinals below `α` is still below `α`.
  let j : α.ToType := Ordinal.ToType.mk
    ⟨⨆ s : S, (ι s : Ordinal),
      Ordinal.iSup_lt_of_lt_cof hS fun s ↦
        (show (ι s : Ordinal) < α from (ι s).toOrd.2)⟩
  refine ⟨j, ?_⟩
  intro s
  -- Each chosen stage lies below that supremum stage.
  have hle : (ι s).toOrd ≤ j.toOrd := by
    exact
      show (ι s : Ordinal) ≤ j.toOrd from by
        simpa [j] using Ordinal.le_iSup (fun s : S ↦ (ι s : Ordinal)) s
  simpa [j] using Ordinal.ToType.mk.monotone hle

/-- Helper for Proposition 19.2.5: every element of a colimit of `R`-modules is represented by
an element of some stage. -/
lemma moduleCatColimitHasStageRepresentative (α : Ordinal.{u}) (B : α.ToType ⥤ ModuleCat R)
    (z : colimit B) :
    ∃ j : α.ToType, ∃ x : B.obj j, ((colimit.ι B j).hom) x = z := by
  letI : PreservesFilteredColimits (forget (ModuleCat.{u} R)) := by infer_instance
  let e : ((forget (ModuleCat.{u} R)).obj (colimit B)) ≅
      colimit (B ⋙ forget (ModuleCat.{u} R)) :=
    preservesColimitIso (forget (ModuleCat.{u} R)) B
  -- First represent the forgotten colimit element in the filtered colimit of underlying types.
  let z' : colimit (B ⋙ forget (ModuleCat.{u} R)) := e.hom z
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective' z'
  refine ⟨j, x, ?_⟩
  have hmor :
      (forget (ModuleCat.{u} R)).map (colimit.ι B j) ≫ e.hom =
        colimit.ι (B ⋙ forget (ModuleCat.{u} R)) j := by
    simpa using ι_preservesColimitIso_hom (G := forget (ModuleCat.{u} R)) (F := B) (j := j)
  have hstage :
      e.hom (((colimit.ι B j).hom) x) = z' := by
    calc
      e.hom (((colimit.ι B j).hom) x) = colimit.ι (B ⋙ forget (ModuleCat.{u} R)) j x := by
        simpa [CategoryTheory.types_comp_apply] using congrArg (fun f ↦ f x) hmor
      _ = z' := hx
  -- Applying the inverse comparison isomorphism recovers an honest stage representative of `z`.
  simpa [e, z'] using congrArg e.inv hstage

/-- Helper for Proposition 19.2.5: in a transfinite tower of monomorphisms of `R`-modules, each
stage map into the colimit is itself a monomorphism. -/
lemma colimitIota_mono_of_monoTower (α : Ordinal.{u}) (B : α.ToType ⥤ ModuleCat R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)) (j : α.ToType) :
    Mono (colimit.ι B j) := by
  -- Compare equality in the module colimit after forgetting to the filtered colimit of types.
  refine (ModuleCat.mono_iff_injective _).2 ?_
  intro x y hxy
  let F : α.ToType ⥤ Type u := B ⋙ forget (ModuleCat.{u} R)
  let e : ((forget (ModuleCat.{u} R)).obj (colimit B)) ≅ colimit F :=
    preservesColimitIso (forget (ModuleCat.{u} R)) B
  have hmor :
      (forget (ModuleCat.{u} R)).map (colimit.ι B j) ≫ e.hom = colimit.ι F j := by
    simpa [F] using ι_preservesColimitIso_hom (G := forget (ModuleCat.{u} R)) (F := B) (j := j)
  have hxy' : colimit.ι F j x = colimit.ι F j y := by
    -- Apply the comparison isomorphism to move the equality into the canonical `Type` colimit.
    apply (e.hom.injective_iff).mp
    simpa [CategoryTheory.types_comp_apply] using congrArg e.hom hxy
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.colimit_eq_iff (F := F)).1 hxy'
  have hfg' : F.map f x = F.map f y := by
    simpa [Subsingleton.elim f g] using hfg
  -- Since `α.ToType` is thin, both comparison maps to the common upper stage agree, and the
  -- mono transition map cancels that common image equality.
  exact (ModuleCat.mono_iff_injective _).1 (hB f) <| by
    simpa [F] using hfg'

/-- Helper for Proposition 19.2.5: the comparison map on Hom-sets is injective for a mono
ordinal tower of `R`-modules. -/
lemma colimitPost_injective_of_monoTower (α : Ordinal.{u}) (B : α.ToType ⥤ ModuleCat R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)) :
    Function.Injective (colimit.post B (coyoneda.obj (op (ModuleCat.of R M)))) := by
  -- Reduce both colimit elements to stage representatives in the Hom-colimit.
  intro x y hxy
  obtain ⟨i, f, rfl⟩ := Types.jointly_surjective' x
  obtain ⟨j, g, rfl⟩ := Types.jointly_surjective' y
  let k : α.ToType := max i j
  let fi : i ⟶ k := homOfLE (le_max_left i j)
  let gj : j ⟶ k := homOfLE (le_max_right i j)
  have hcolim :
      f ≫ B.map fi ≫ colimit.ι B k = g ≫ B.map gj ≫ colimit.ι B k := by
    -- Rewrite both images in the comparison map to the common upper stage `k`.
    calc
      f ≫ B.map fi ≫ colimit.ι B k = f ≫ colimit.ι B i := by
        simpa [Category.assoc] using congrArg (fun t ↦ f ≫ t) (colimit.w B fi)
      _ = g ≫ colimit.ι B j := by
        simpa using (colimit_post_coyoneda_ι_app (ModuleCat.of R M) B i f).trans hxy |>.trans
          (colimit_post_coyoneda_ι_app (ModuleCat.of R M) B j g).symm
      _ = g ≫ B.map gj ≫ colimit.ι B k := by
        simpa [Category.assoc] using congrArg (fun t ↦ g ≫ t) (colimit.w B gj).symm
  have hstage :
      f ≫ B.map fi = g ≫ B.map gj := by
    exact (cancel_mono (colimit.ι B k)).1 hcolim
  -- Equality at the common upper stage is exactly the filtered-colimit equality criterion.
  exact (Types.FilteredColimit.colimit_eq_iff
      (F := B ⋙ coyoneda.obj (op (ModuleCat.of R M)))).2 ⟨k, fi, gj, hstage⟩

/-- Helper for Proposition 19.2.5: if every element of `M` maps into the range of the `j`-th
stage coprojection, then the map to the colimit factors through stage `j`. -/
lemma factorThroughStage_of_comap_eq_top (α : Ordinal.{u}) (B : α.ToType ⥤ ModuleCat R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f))
    {j : α.ToType} (f : ModuleCat.of R M ⟶ colimit B)
    (hTop : Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom) = ⊤) :
    ∃ g : ModuleCat.of R M ⟶ B.obj j, g ≫ colimit.ι B j = f := by
  let hιinj :
      Function.Injective (colimit.ι B j).hom :=
    (ModuleCat.mono_iff_injective _).1
      (colimitIota_mono_of_monoTower (R := R) α B hB j)
  let eRange : B.obj j ≃ₗ[R] LinearMap.range (colimit.ι B j).hom :=
    LinearEquiv.ofInjective (colimit.ι B j).hom hιinj
  let fRange : M →ₗ[R] LinearMap.range (colimit.ι B j).hom :=
    LinearMap.codRestrict (LinearMap.range (colimit.ι B j).hom) f.hom fun x ↦ by
      -- The top-comap hypothesis says exactly that every `f x` already lies in the stage range.
      have hx : x ∈ Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom) := by
        simpa [hTop]
      exact hx
  let g : ModuleCat.of R M ⟶ B.obj j := ModuleCat.ofHom (eRange.symm.toLinearMap.comp fRange)
  refine ⟨g, ?_⟩
  -- The chosen map lands in the range by construction, and `eRange.symm` converts that range
  -- element back to the unique stage element mapping to `f x`.
  ext x
  have hx :
      ((colimit.ι B j).hom) (eRange.symm (fRange x)) = f.hom x := by
    have happly :
        eRange (eRange.symm (fRange x)) = fRange x := by
      exact eRange.apply_symm_apply (fRange x)
    exact congrArg Subtype.val happly
  simpa [g, fRange, LinearMap.comp_apply] using hx

/-- Helper for Proposition 19.2.5: the comparison map on Hom-sets is surjective once the number
of submodules of `M` is strictly smaller than the cofinality of `α`. -/
lemma colimitPost_surjective_of_submodule_cardinal_lt_cof (α : Ordinal.{u})
    (hα : Cardinal.mk (Submodule R M) < α.cof) (B : α.ToType ⥤ ModuleCat R)
    (hB : ∀ ⦃i j : α.ToType⦄ (f : i ⟶ j), Mono (B.map f)) :
    Function.Surjective (colimit.post B (coyoneda.obj (op (ModuleCat.of R M)))) := by
  classical
  intro f
  let preimageStage : α.ToType → Submodule R M := fun j ↦
    Submodule.comap f.hom (LinearMap.range (colimit.ι B j).hom)
  have hpreimage_mono : Monotone preimageStage := by
    intro i j hij
    refine Submodule.comap_mono ?_
    intro z hz
    rcases hz with ⟨x, rfl⟩
    refine ⟨(B.map (homOfLE hij)).hom x, ?_⟩
    -- Naturality of the colimit coprojections identifies the smaller-stage image inside the
    -- larger one.
    simpa [Category.assoc] using congrArg (fun t ↦ t x) (colimit.w B (homOfLE hij))
  have hx_mem_some_stage : ∀ x : M, ∃ j : α.ToType, x ∈ preimageStage j := by
    intro x
    obtain ⟨j, y, hy⟩ :=
      moduleCatColimitHasStageRepresentative (R := R) α B (f.hom x)
    refine ⟨j, ?_⟩
    exact hy ▸ LinearMap.mem_range_self _ _
  have hrange_lt : Cardinal.mk (Set.range preimageStage) < α.cof := by
    refine lt_of_le_of_lt ?_ hα
    exact Cardinal.mk_le_of_injective (f := fun Q : Set.range preimageStage ↦ Q.1) fun _ _ h ↦
      Subtype.ext h
  let representative : Set.range preimageStage → α.ToType := fun Q ↦ Classical.choose Q.2
  have hrepresentative :
      ∀ Q : Set.range preimageStage, preimageStage (representative Q) = Q.1 := by
    intro Q
    exact Classical.choose_spec Q.2
  obtain ⟨j0, hj0⟩ :=
    existsStageDominatingSmallFamily (S := Set.range preimageStage) (α := α) hrange_lt
      representative
  have htop : preimageStage j0 = ⊤ := by
    rw [Submodule.eq_top_iff]
    intro x
    rcases hx_mem_some_stage x with ⟨j, hxj⟩
    let Q : Set.range preimageStage := ⟨preimageStage j, ⟨j, rfl⟩⟩
    have hleQ : preimageStage j ≤ preimageStage j0 := by
      calc
        preimageStage j = preimageStage (representative Q) := by
          symm
          simpa [Q] using hrepresentative Q
        _ ≤ preimageStage j0 := hpreimage_mono (hj0 Q)
    exact hleQ hxj
  obtain ⟨g, hg⟩ :=
    factorThroughStage_of_comap_eq_top (R := R) (M := M) α B hB f htop
  refine ⟨colimit.ι (B ⋙ coyoneda.obj (op (ModuleCat.of R M))) j0 g, ?_⟩
  -- A stage factorization is exactly a preimage of the comparison map under the coprojection.
  simpa [hg] using colimit_post_coyoneda_ι_app (ModuleCat.of R M) B j0 g

/-- Proposition 19.2.5: if the cofinality of `α` is strictly larger than the cardinality of the
set of `R`-submodules of `M`, then `M` is `α`-small with respect to injections, i.e. with
respect to monomorphisms in `ModuleCat R`. -/
theorem moduleCat_is_alpha_small_wrt_monomorphisms_of_submodule_cardinal_lt_cof
    (α : Ordinal.{u}) (hα : Cardinal.mk (Submodule R M) < α.cof) :
    is_alpha_small_wrt (ModuleCat.of R M) (MorphismProperty.monomorphisms (ModuleCat R)) α := by
  intro B hB
  have hbij :
      Function.Bijective (colimit.post B (coyoneda.obj (op (ModuleCat.of R M)))) := by
    refine ⟨?_, ?_⟩
    · exact colimitPost_injective_of_monoTower (R := R) (M := M) α B hB
    · exact colimitPost_surjective_of_submodule_cardinal_lt_cof
        (R := R) (M := M) α hα B hB
  letI : IsIso (colimit.post B (coyoneda.obj (op (ModuleCat.of R M)))) :=
    (isIso_iff_bijective _).2 hbij
  -- Route correction: once the comparison map itself is an isomorphism, the generic owner lemma
  -- `preservesColimit_of_isIso_post` finishes directly without an extra cocone-transport layer.
  exact preservesColimit_of_isIso_post (F := B) (G := coyoneda.obj (op (ModuleCat.of R M)))

end

end CategoryTheory
