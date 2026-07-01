import Mathlib
import stacks_project.Chap17.Definition_17_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.5.3:
- primary domain: support of sheaves of rings on a topological space, detected stalkwise by the
  germ of the global unit section;
- sampled owner declarations:
  `ringSheafSupport`,
  `abelianSheafSupport`,
  `mem_abelianSheafSupport_iff`,
  `TopCat.Presheaf.stalk`,
  `TopCat.Presheaf.Γgerm`;
- best owner abstraction:
  the source-facing owner is `ringSheafSupport`, the thin ring-sheaf bridge to the chapter’s core
  additive owner `abelianSheafSupport`;
- primitive data:
  a sheaf of rings `ℱ` on `X`;
- derived API:
  the unit-germ criterion for membership in `ringSheafSupport ℱ` and the resulting closedness
  statement.

Source/core/bridge triage:
- `source-facing`: `ringSheafSupport` and Lemma 17.5.3 for a sheaf of rings;
- `core/canonical`: `abelianSheafSupport`;
- `bridge/view`: the forgetful additive sheaf `ringToAddSheaf ℱ` and the stalk comparison induced
  by `forget₂ RingCat AddCommGrpCat`. -/

private abbrev ringToAddSheaf (ℱ : X.Sheaf RingCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ

private abbrev ringToAddPresheaf (ℱ : X.Sheaf RingCat.{u}) : X.Presheaf AddCommGrpCat.{u} :=
  ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat

private noncomputable abbrev ringStalkAddIso (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x ≅
      (forget₂ RingCat AddCommGrpCat).obj (TopCat.Presheaf.stalk ℱ.presheaf x) := by
  change TopCat.Presheaf.stalk (ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat) x ≅ _
  exact Limits.colimit.isoColimitCocone
    ⟨_, Limits.isColimitOfPreserves
      (forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf))⟩

-- Proof sketch: the support owner is `abelianSheafSupport` of the underlying additive sheaf. Its
-- stalk is nonzero exactly when the stalk of rings is nontrivial, which is equivalent to the germ
-- of the global unit section being nonzero.
/-- For a sheaf of rings, membership in `ringSheafSupport` is equivalent to nonvanishing of the
germ of the global unit section. -/
theorem mem_ringSheafSupport_iff_one_germ_ne_zero
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    x ∈ ringSheafSupport ℱ ↔
      ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0 := by
  change x ∈ abelianSheafSupport (ringToAddSheaf ℱ) ↔ _
  rw [mem_abelianSheafSupport_iff]
  change ¬ IsZero (TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) ↔
    ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0
  constructor
  · intro hx hzero
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) :=
      subsingleton_of_zero_eq_one (show (0 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) = 1 by
        simpa using hzero.symm)
    have hsubAdd : Subsingleton ↑(TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) := by
      let e := (ringStalkAddIso ℱ x).addCommGroupIsoToAddEquiv.toEquiv
      letI : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := hsubRing
      exact e.subsingleton
    exact hx ((AddCommGrpCat.isZero_iff_subsingleton).2 hsubAdd)
  · intro hx
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    intro hsub
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := by
      let e := (ringStalkAddIso ℱ x).addCommGroupIsoToAddEquiv.toEquiv
      letI : Subsingleton ↑(TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) := hsub
      exact e.symm.subsingleton
    exact hx <| by
      letI : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := hsubRing
      exact Subsingleton.elim _ _

-- Proof sketch: if the unit germ vanishes at `x`, then by the stalk criterion there is an open
-- neighbourhood on which the unit section restricts to zero. Hence the unit germ vanishes at every
-- point of that neighbourhood, so the complement of the support is open.
/-- Lemma 17.5.3: for a topological space `X`, the support of a sheaf of rings on `X` is closed. -/
theorem isClosed_ringSheafSupport
    (ℱ : X.Sheaf RingCat.{u}) :
    IsClosed (ringSheafSupport ℱ) := by
  change IsClosed (abelianSheafSupport (ringToAddSheaf ℱ))
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hzero : ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    by_contra h
    exact hx ((mem_ringSheafSupport_iff_one_germ_ne_zero ℱ x).2 h)
  have hzero' :
      ℱ.presheaf.germ ⊤ x True.intro (1 : ℱ.presheaf.obj (op ⊤)) =
        ℱ.presheaf.germ ⊤ x True.intro 0 := by
    simpa [TopCat.Presheaf.Γgerm] using hzero
  obtain ⟨W, hxW, iW, iTop, hW⟩ := ℱ.presheaf.germ_eq x
    (show x ∈ (⊤ : Opens X) from True.intro)
    (show x ∈ (⊤ : Opens X) from True.intro)
    (1 : ℱ.presheaf.obj (op ⊤)) 0 hzero'
  have hWzero : ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    simpa using hW
  refine Filter.mem_of_superset (IsOpen.mem_nhds W.2 hxW) fun y hyW hySupport ↦ ?_
  have hyZero : ℱ.presheaf.Γgerm y (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    have hΓ :
        ℱ.presheaf.germ W y hyW (ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤))) =
          ℱ.presheaf.Γgerm y (1 : ℱ.presheaf.obj (op ⊤)) := by
      change ℱ.presheaf.germ W y hyW (ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤))) =
        ℱ.presheaf.germ ⊤ y True.intro (1 : ℱ.presheaf.obj (op ⊤))
      exact ℱ.presheaf.germ_res_apply iW y hyW (1 : ℱ.presheaf.obj (op ⊤))
    rw [← hΓ, hWzero]
    exact map_zero _
  exact (mem_ringSheafSupport_iff_one_germ_ne_zero ℱ y).1 hySupport hyZero

end

end TopCat.Sheaf
