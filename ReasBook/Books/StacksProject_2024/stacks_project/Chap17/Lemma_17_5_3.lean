import Mathlib
import StacksProject_2024.Chap17.Lemma_17_5_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open AlgebraicGeometry

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}

private abbrev toAddSheaf (ℱ : X.Sheaf RingCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ

private theorem subsingleton_addStalk_of_subsingleton_ringStalk
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) →
      Subsingleton ↑(TopCat.Presheaf.stalk (ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat) x) := by
  intro hsub
  let e :=
    (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).addCommGroupIsoToAddEquiv.toEquiv
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  exact congrArg e (hsub.elim a' b')

private theorem subsingleton_ringStalk_of_subsingleton_addStalk
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    Subsingleton ↑(TopCat.Presheaf.stalk (ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat) x) →
      Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := by
  intro hsub
  let e :=
    (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).addCommGroupIsoToAddEquiv.toEquiv
  refine ⟨fun a b ↦ ?_⟩
  exact e.injective (hsub.elim (e a) (e b))

/- Domain-style sampling for Lemma 17.5.3:
- primary domain: support of sheaves of rings on a topological space, detected stalkwise by the
  germ of the global unit section;
- sampled owner declarations:
  `ringSheafSupport`,
  `abelianSheafSupport`,
  `mem_abelianSheafSupport_iff`,
  `CategoryTheory.preservesColimitIso`,
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
- `bridge/view`: the canonical stalk comparison
  `preservesColimitIso (forget₂ RingCat AddCommGrpCat) ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)`,
  relating the ring stalk to the stalk of the underlying additive presheaf. -/

-- Proof sketch: the support owner is `abelianSheafSupport` of the underlying additive sheaf. Its
-- stalk is nonzero exactly when the stalk of rings is nontrivial, which is equivalent to the germ
-- of the global unit section being nonzero.
/-- For a sheaf of rings, membership in `ringSheafSupport` is equivalent to nonvanishing of the
germ of the global unit section. -/
theorem mem_ringSheafSupport_iff_one_germ_ne_zero
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    x ∈ ringSheafSupport ℱ ↔
      ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0 := by
  change x ∈ abelianSheafSupport (toAddSheaf ℱ) ↔ _
  rw [mem_abelianSheafSupport_iff]
  change ¬ IsZero (TopCat.Presheaf.stalk (ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat) x) ↔
    ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0
  constructor
  · intro hx hzero
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) :=
      subsingleton_of_zero_eq_one (show (0 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) = 1 by
        simpa using hzero.symm)
    exact hx ((AddCommGrpCat.isZero_iff_subsingleton).2
      (subsingleton_addStalk_of_subsingleton_ringStalk ℱ x hsubRing))
  · intro hx
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    intro hsub
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) :=
      subsingleton_ringStalk_of_subsingleton_addStalk ℱ x hsub
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
  let Fadd : X.Sheaf AddCommGrpCat.{u} :=
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ
  let oneSection : Fadd.presheaf.obj (op ⊤) := (1 : ℱ.presheaf.obj (op ⊤))
  let α (x : X) :=
    (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).addCommGroupIsoToAddEquiv
  have hα_germ_eval (x : X) :
      α x (ℱ.presheaf.germ ⊤ x True.intro (1 : ℱ.presheaf.obj (op ⊤))) =
        Fadd.presheaf.germ ⊤ x True.intro oneSection := by
    let j : (OpenNhds x)ᵒᵖ := op ⟨⊤, True.intro⟩
    have hmor :
        (forget₂ RingCat AddCommGrpCat).map (colimit.ι ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) j) ≫
          (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
            ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).hom =
        colimit.ι (((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) ⋙ forget₂ RingCat AddCommGrpCat) j :=
      ι_preservesColimitIso_hom
        (forget₂ RingCat AddCommGrpCat) ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) j
    have hmor_apply := congrArg (fun f ↦ f oneSection) hmor
    rw [show α x =
      (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
        ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).addCommGroupIsoToAddEquiv by rfl]
    rw [Iso.addCommGroupIsoToAddEquiv_apply]
    have hmor_apply' :
        (AddCommGrpCat.Hom.hom
            (preservesColimitIso (forget₂ RingCat AddCommGrpCat)
              ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf)).hom)
            (((ConcreteCategory.hom
              ((forget₂ RingCat AddCommGrpCat).map
                (colimit.ι ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) j))) oneSection)) =
        (ConcreteCategory.hom
          (colimit.ι (((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) ⋙ forget₂ RingCat AddCommGrpCat) j))
          oneSection := by
              simpa [ConcreteCategory.comp_apply] using hmor_apply
    have hgerm_eval :
        (ConcreteCategory.hom (ℱ.presheaf.germ ⊤ x True.intro)) (1 : ℱ.presheaf.obj (op ⊤)) =
          (ConcreteCategory.hom
            ((forget₂ RingCat AddCommGrpCat).map
              (colimit.ι ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf) j))) oneSection := by
      rfl
    rw [hgerm_eval]
    exact hmor_apply'
  have hα_germ (x : X) :
      α x (1 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) =
        Fadd.presheaf.germ ⊤ x True.intro oneSection := by
    calc
      α x (1 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) =
          α x (ℱ.presheaf.germ ⊤ x True.intro (1 : ℱ.presheaf.obj (op ⊤))) := by
            exact congrArg (α x) ((ℱ.presheaf.germ ⊤ x True.intro).hom.map_one.symm)
      _ = Fadd.presheaf.germ ⊤ x True.intro oneSection := hα_germ_eval x
  have hsupport :
      ringSheafSupport ℱ =
        Subtype.val '' abelianSheafSectionSupport Fadd oneSection := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, show x ∈ (⊤ : Opens X) from True.intro⟩, ?_, rfl⟩
      rw [mem_abelianSheafSectionSupport_iff]
      have hx' :
          (1 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) ≠ 0 := by
        simpa [TopCat.Presheaf.Γgerm] using
          (mem_ringSheafSupport_iff_one_germ_ne_zero ℱ x).1 hx
      intro hzero
      apply hx'
      apply (α x).injective
      rw [hα_germ x]
      exact hzero.trans (α x).map_zero.symm
    · rintro ⟨x, hx, rfl⟩
      have hx' :
          (1 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) ≠ 0 := by
        intro hzero
        apply hx
        rw [← hα_germ x]
        calc
          α x (1 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) = α x 0 :=
            congrArg (α x) hzero
          _ = 0 := (α x).map_zero
      exact (mem_ringSheafSupport_iff_one_germ_ne_zero ℱ x).2 <| by
        simpa [TopCat.Presheaf.Γgerm] using hx'
  rw [hsupport]
  exact isClosed_univ.isClosedMap_subtype_val _
    (show IsClosed (abelianSheafSectionSupport Fadd oneSection) from
      isClosed_abelianSheafSectionSupport oneSection)

end

end TopCat.Sheaf
