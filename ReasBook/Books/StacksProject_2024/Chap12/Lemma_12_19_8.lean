import stacks_project.Chap12.Lemma_12_19_7

open CategoryTheory
open CategoryTheory.Limits

universe v u v₁ u₁

noncomputable section

namespace CategoryTheory
namespace FilteredObject.Hom

/-
Source/core/bridge triage for Lemma 12.19.8:
- source-facing: closure and non-closure properties of strict filtered morphisms under composition
- core/canonical owner: `FilteredObject.Hom.Strict`
- bridge/view: the mono/epi characterizations from Lemma `12.19.7`
-/

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable [HasEqualizers C]

private theorem imageSubobject_comp_eq_map_of_mono [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = Subobject.mk ((imageSubobject f).arrow ≫ g) := by
      simpa using (Limits.imageSubobject_mono ((imageSubobject f).arrow ≫ g))
    _ = (Subobject.map g).obj (Subobject.mk (imageSubobject f).arrow) := by
      rw [Subobject.map_mk]
    _ = (Subobject.map g).obj (imageSubobject f) := by
      rw [Subobject.mk_arrow]

private theorem imageSubobject_comp_eq_of_epi [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
        (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

-- Proof sketch: use the explicit two-step filtration on a two-dimensional vector space, together
-- with the induced filtration on a line and the quotient filtration on the quotient by a basis
-- vector, to obtain strict maps whose nonzero composite fails the strictness equality.
/-- Lemma 12.19.8 (1): in general, the composite of strict morphisms of filtered objects need not
be strict. -/
theorem strict_comp_not_in_general :
    ¬ ∀ {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {A B C : FilteredObject 𝒜}
        (f : A ⟶ B) (g : B ⟶ C), Strict f → Strict g → Strict (f ≫ g) := by
  sorry

variable {A B D : FilteredObject C}

private theorem map_inf_eq_of_strict_mono (g : B ⟶ D) [Mono g.hom] (hg : Strict g)
    (x : Subobject B.obj) (i : ℤ) :
    (Subobject.map g.hom).obj (x ⊓ B.filtration i) =
      (Subobject.map g.hom).obj x ⊓ D.filtration i := by
  have hgi : B.filtration i = (Subobject.pullback g.hom).obj (D.filtration i) := by
    exact congrArg (fun F ↦ F i) ((strict_iff_induced_filtration_of_mono g).1 hg)
  rw [hgi, Subobject.inf_map]
  rw [show (Subobject.map g.hom).obj ((Subobject.pullback g.hom).obj (D.filtration i)) =
      Subobject.mk g.hom ⊓ D.filtration i by
        simpa [Subobject.inf_def] using
          (Subobject.inf_eq_map_pullback' (MonoOver.mk g.hom) (D.filtration i)).symm]
  have hx : (Subobject.map g.hom).obj x ≤ Subobject.mk g.hom := by
    induction x using Subobject.ind
    rename_i X m hm
    simpa [Subobject.map_mk] using
      (Subobject.mk_le_mk_of_comm m (by simp) :
        Subobject.mk (m ≫ g.hom) ≤ Subobject.mk g.hom)
  calc
    (Subobject.map g.hom).obj x ⊓ (Subobject.mk g.hom ⊓ D.filtration i)
        = ((Subobject.map g.hom).obj x ⊓ Subobject.mk g.hom) ⊓ D.filtration i := by
            simp [inf_assoc]
    _ = (Subobject.map g.hom).obj x ⊓ D.filtration i := by
            simp [inf_eq_left.mpr hx]

private theorem quotient_comp_eq_quotient_of_quotient [Balanced C] (f : A ⟶ B) (g : B ⟶ D)
    (i : ℤ) : A.filtration.quotient (f.hom ≫ g.hom) i =
      (A.filtration.quotient f.hom).quotient g.hom i := by
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    DecreasingFiltration.quotient_eq_imageSubobject_comp]
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  simpa [Category.assoc] using
    (CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction
      ((A.filtration i).arrow ≫ f.hom) g.hom)

-- Proof sketch: strictness of `f` identifies `g (f(F^p A))` with
-- `g (f(A) ∩ F^p B)`; injectivity of `g.hom` turns this into the intersection of the image of the
-- composite with `g(F^p B)`, and strictness of `g` rewrites `g(F^p B)` as `F^p C ∩ image g`.
/-- Lemma 12.19.8 (2): if `g` is injective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_mono [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Mono g.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = imageSubobject ((A.filtration i).arrow ≫ f.hom ≫ g.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject ((A.filtration i).arrow ≫ f.hom)) := by
            simpa [Category.assoc] using
              (imageSubobject_comp_eq_map_of_mono ((A.filtration i).arrow ≫ f.hom) g.hom)
    _ = (Subobject.map g.hom).obj (A.filtration.quotient f.hom i) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom ⊓ B.filtration i) := by
            rw [(strict_iff_quotient_eq_inf f).1 hf i]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom) ⊓ D.filtration i := by
            simpa using map_inf_eq_of_strict_mono g hg (imageSubobject f.hom) i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
            rw [← imageSubobject_comp_eq_map_of_mono f.hom g.hom]

-- Proof sketch: rewrite the preimage of `F^p C` under `g ∘ f` as the preimage under `f` of
-- `F^p B + ker g` using strictness of `g`; surjectivity of `f.hom` lets the pullback of this sum
-- split as the sum of the pullbacks, and strictness of `f` identifies the pullback of `F^p B`
-- with `F^p A + ker f`, which collapses to `F^p A + ker (g ≫ f)`.
/-- Lemma 12.19.8 (3): if `f` is surjective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_epi [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Epi f.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = (A.filtration.quotient f.hom).quotient g.hom i :=
            quotient_comp_eq_quotient_of_quotient f g i
    _ = B.filtration.quotient g.hom i := by
          have hfi : A.filtration.quotient f.hom = B.filtration := by
            simpa using ((strict_iff_quotient_filtration_of_epi f).1 hf).symm
          rw [hfi]
    _ = imageSubobject g.hom ⊓ D.filtration i := by
          exact (strict_iff_quotient_eq_inf g).1 hg i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
          rw [imageSubobject_comp_eq_of_epi f.hom g.hom]

end FilteredObject.Hom
end CategoryTheory
