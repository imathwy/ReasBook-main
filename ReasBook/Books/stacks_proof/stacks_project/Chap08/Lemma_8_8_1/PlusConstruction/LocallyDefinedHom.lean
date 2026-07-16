import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.LocalEqualityQuotient

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: for objects `x` over `U`, `y` over `V`,
and a base arrow `f : U ⟶ V`, the presheaf of local representatives of morphisms `x ⟶ y`
lying over `f`.  Over a test object `T ⟶ U`, this is the ordinary Hom presheaf from `x|_T` to
`(f|_T)^* y`. -/
noncomputable abbrev locallyDefinedHomPresheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) :
    (Over (X.p.obj x))ᵒᵖ ⥤ Type vX :=
  (canonicalFiberPseudofunctor X.p).presheafHom
    (Functor.Fiber.mk (p := X.p) (a := x) rfl)
    (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
      (Functor.Fiber.mk (p := X.p) (a := y) rfl))

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: the same locally-defined-Hom presheaf viewed
in the saturated Type universe where the concrete plus construction has the required cover-shape
limits. -/
noncomputable abbrev locallyDefinedHomSaturatedPresheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) :
    (Over (X.p.obj x))ᵒᵖ ⥤ Type (max vX (max u v)) :=
  locallyDefinedHomPresheaf X f ⋙
    (CategoryTheory.uliftFunctor.{max u v, vX} : Type vX ⥤ Type (max vX (max u v)))

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: the type of locally defined morphisms from
`x` to `y`, packaged as a base arrow together with a plus-section of the corresponding local
representative presheaf.  This is only the Hom-object surface; composition and the fibred
category structure are separate obligations. -/
noncomputable abbrev locallyDefinedHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x y : X.S) :
    Type (max v (max vX (max u v))) :=
  Σ f : X.p.obj x ⟶ X.p.obj y,
    ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).obj
      (op (Over.mk (𝟙 (X.p.obj x))))

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: a base cover of `U` regarded as the
corresponding cover of the terminal object `U ⟶ U` in the slice site.  This keeps the concrete
plus construction aligned with the source text's cover notation `{U_i ⟶ U}`. -/
noncomputable def identitySliceCoverOfBaseCover {U : C} (S : J.Cover U) :
    (J.over U).Cover (Over.mk (𝟙 U)) :=
  ⟨(Sieve.overEquiv (Over.mk (𝟙 U))).symm S.1,
    GrothendieckTopology.overEquiv_symm_mem_over J (Over.mk (𝟙 U)) S.1 S.condition⟩

/-- The base cover underlying a cover of the identity object in a slice site. -/
noncomputable def baseCoverOfIdentitySliceCover {U : C}
    (S : (J.over U).Cover (Over.mk (𝟙 U))) : J.Cover U :=
  ⟨Sieve.overEquiv (Over.mk (𝟙 U)) S.1, (J.mem_over_iff S.1).1 S.condition⟩

/-- A refinement of covers in the identity slice induces the corresponding refinement of the
underlying base covers. -/
noncomputable def baseCoverOfIdentitySliceCoverHom {U : C}
    {S T : (J.over U).Cover (Over.mk (𝟙 U))} (h : S ⟶ T) :
    baseCoverOfIdentitySliceCover (J := J) S ⟶
      baseCoverOfIdentitySliceCover (J := J) T :=
  homOfLE (by
    intro Y f hf
    have hs : (S : Sieve (Over.mk (𝟙 U)))
        (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)) := by
      simpa using (Sieve.overEquiv_iff (Y := Over.mk (𝟙 U))
        (S : Sieve (Over.mk (𝟙 U))) f).1 hf
    have ht : (T : Sieve (Over.mk (𝟙 U)))
        (Over.homMk f : Over.mk (f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)) :=
      (leOfHom h) _ hs
    exact (Sieve.overEquiv_iff (Y := Over.mk (𝟙 U))
      (T : Sieve (Over.mk (𝟙 U))) f).2 ht)

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.1: a representative of a locally defined
morphism with fixed base arrow.  It is a cover of the identity object in the slice together with
a matching family for the representative Hom presheaf.  Unwinding `Meq`, this is exactly the
source datum `(cover, local morphisms, overlap compatibility)`. -/
structure LocallyDefinedHomRepresentativeOver
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) where
  /-- The cover on which the morphism is defined, expressed in the slice site over `p x`. -/
  cover : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))
  /-- Compatible local representatives over the cover. -/
  family : Meq (locallyDefinedHomSaturatedPresheaf X f) cover

namespace LocallyDefinedHomRepresentativeOver

/-- The source cover underlying a slice-cover representative. -/
noncomputable def baseCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    J.Cover (X.p.obj x) :=
  baseCoverOfIdentitySliceCover (J := J) α.cover

/-- A refinement of fixed-base representatives induces a refinement of their underlying base
covers. -/
noncomputable def baseCoverHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    {α β : LocallyDefinedHomRepresentativeOver (J := J) X f}
    (h : α.cover ⟶ β.cover) :
    α.baseCover ⟶ β.baseCover :=
  baseCoverOfIdentitySliceCoverHom (J := J) h

/-- The plus-section represented by a raw locally-defined morphism representative. -/
noncomputable def toPlusSection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).obj
      (op (Over.mk (𝟙 (X.p.obj x)))) :=
  GrothendieckTopology.Plus.mk α.family

/-- Refine a raw locally-defined morphism representative to a finer cover.  This is the formal
version of replacing `{U_i}` by a common refinement in the source proof. -/
noncomputable def refine
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover) :
    LocallyDefinedHomRepresentativeOver (J := J) X f where
  cover := W
  family := α.family.refine h

@[simp]
theorem refine_cover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover) :
    (α.refine h).cover = W :=
  rfl

@[simp]
theorem refine_family_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover) (I : W.Arrow) :
    (α.refine h).family I =
      α.family ⟨I.Y, I.f, (leOfHom h) _ I.hf⟩ :=
  rfl

/-- Refining a raw representative does not change the plus-section it represents. -/
theorem refine_toPlusSection
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover) :
    (α.refine h).toPlusSection = α.toPlusSection := by
  change GrothendieckTopology.Plus.mk (α.family.refine h) =
    GrothendieckTopology.Plus.mk α.family
  exact (GrothendieckTopology.Plus.eq_mk_iff_exists (J := J.over (X.p.obj x))
    (P := locallyDefinedHomSaturatedPresheaf X f) (α.family.refine h) α.family).2
      ⟨W, 𝟙 W, h, by ext I; rfl⟩

/-- Restrict a raw representative along a morphism in the source slice.  This is the formal
version of pulling a locally-defined morphism back to a refinement of the cover. -/
noncomputable def pullbackFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {V : Over (X.p.obj x)} (k : V ⟶ Over.mk (𝟙 (X.p.obj x))) :
    Meq (locallyDefinedHomSaturatedPresheaf X f) (((J.over (X.p.obj x)).pullback k).obj α.cover) :=
  α.family.pullback k

@[simp]
theorem pullbackFamily_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {V : Over (X.p.obj x)} (k : V ⟶ Over.mk (𝟙 (X.p.obj x)))
    (I : (((J.over (X.p.obj x)).pullback k).obj α.cover).Arrow) :
    α.pullbackFamily k I =
      α.family ⟨I.Y, I.f ≫ k, I.hf⟩ :=
  rfl

/-- Restrict a raw representative to a base arrow `V ⟶ p(x)`, viewed as an object of the source
slice. -/
noncomputable def pullbackFamilyAlongBase
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {V : C} (h : V ⟶ X.p.obj x) :
    Meq (locallyDefinedHomSaturatedPresheaf X f)
      (((J.over (X.p.obj x)).pullback
        (Over.homMk (U := Over.mk h) (V := Over.mk (𝟙 (X.p.obj x))) h (by simp) :
        Over.mk h ⟶ Over.mk (𝟙 (X.p.obj x)))).obj α.cover) :=
  α.pullbackFamily
    (Over.homMk (U := Over.mk h) (V := Over.mk (𝟙 (X.p.obj x))) h (by simp))

/-- On each member of its cover, a raw representative restricts to the corresponding
`toPlus` image. -/
theorem toPlusSection_restrict_eq_toPlus
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (I : α.cover.Arrow) :
    ((J.over (X.p.obj x)).toPlus (locallyDefinedHomSaturatedPresheaf X f)).app
        (op I.Y) (α.family I) =
      ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).map
        I.f.op α.toPlusSection := by
  exact GrothendieckTopology.Plus.toPlus_apply α.cover α.family I

/-- Pulling back a represented plus-section is represented by pulling back the raw matching
family. -/
theorem toPlusSection_pullback_eq_mk
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {V : Over (X.p.obj x)} (k : V ⟶ Over.mk (𝟙 (X.p.obj x))) :
    ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).map
        k.op α.toPlusSection =
      GrothendieckTopology.Plus.mk (α.pullbackFamily k) := by
  exact GrothendieckTopology.Plus.res_mk_eq_mk_pullback α.family k

/-- Every plus-section for a fixed base arrow is represented by a raw locally-defined morphism
representative.  This packages `GrothendieckTopology.Plus.exists_rep` in the notation of the
source proof. -/
theorem toPlusSection_surjective
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (s :
      ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).obj
        (op (Over.mk (𝟙 (X.p.obj x))))) :
    ∃ α : LocallyDefinedHomRepresentativeOver (J := J) X f,
      α.toPlusSection = s := by
  obtain ⟨S, t, ht⟩ :=
    GrothendieckTopology.Plus.exists_rep
      (J := J.over (X.p.obj x))
      (P := locallyDefinedHomSaturatedPresheaf X f) s
  refine ⟨⟨S, t⟩, ?_⟩
  exact ht.symm

/-- Source stage 2.2 for fixed base arrow: two representatives are equivalent exactly when they
agree after passing to a common refinement of their covers. -/
def Equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α β : LocallyDefinedHomRepresentativeOver (J := J) X f) : Prop :=
  ∃ (W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x))))
    (hα : W ⟶ α.cover) (hβ : W ⟶ β.cover),
      α.family.refine hα = β.family.refine hβ

/-- The common-refinement equivalence is exactly equality of the represented plus-sections. -/
theorem toPlusSection_eq_iff_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α β : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    α.toPlusSection = β.toPlusSection ↔ Equivalent (J := J) α β := by
  exact GrothendieckTopology.Plus.eq_mk_iff_exists α.family β.family

/-- A refinement of a raw representative is equivalent to the original representative. -/
theorem refine_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover) :
    Equivalent (J := J) (α.refine h) α :=
  (toPlusSection_eq_iff_equivalent (J := J) (α.refine h) α).1
    (refine_toPlusSection (J := J) α h)

/-- The fixed-base representative equivalence is reflexive. -/
theorem equivalent_refl
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    Equivalent (J := J) α α := by
  exact (toPlusSection_eq_iff_equivalent (J := J) α α).1 rfl

/-- The fixed-base representative equivalence is symmetric. -/
theorem equivalent_symm
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    {α β : LocallyDefinedHomRepresentativeOver (J := J) X f}
    (h : Equivalent (J := J) α β) :
    Equivalent (J := J) β α := by
  exact (toPlusSection_eq_iff_equivalent (J := J) β α).1
    ((toPlusSection_eq_iff_equivalent (J := J) α β).2 h).symm

/-- The fixed-base representative equivalence is transitive; this is the plus-colimit version of
the source proof's separatedness argument on triple common refinements. -/
theorem equivalent_trans
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    {α β γ : LocallyDefinedHomRepresentativeOver (J := J) X f}
    (hαβ : Equivalent (J := J) α β) (hβγ : Equivalent (J := J) β γ) :
    Equivalent (J := J) α γ := by
  exact (toPlusSection_eq_iff_equivalent (J := J) α γ).1
    (((toPlusSection_eq_iff_equivalent (J := J) α β).2 hαβ).trans
      ((toPlusSection_eq_iff_equivalent (J := J) β γ).2 hβγ))

/-- The setoid on fixed-base raw representatives. -/
def setoid
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) :
    Setoid (LocallyDefinedHomRepresentativeOver (J := J) X f) where
  r := Equivalent (J := J)
  iseqv := ⟨equivalent_refl (J := J), equivalent_symm (J := J),
    equivalent_trans (J := J)⟩

/-- For a fixed base arrow, the quotient of raw local representatives by common refinement is
exactly the corresponding plus-section type. -/
noncomputable def quotientEquivPlusSection
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) :
    _root_.Quotient (setoid (J := J) X f) ≃
      ((J.over (X.p.obj x)).plusObj (locallyDefinedHomSaturatedPresheaf X f)).obj
        (op (Over.mk (𝟙 (X.p.obj x)))) where
  toFun :=
    _root_.Quot.lift (fun α : LocallyDefinedHomRepresentativeOver (J := J) X f =>
      α.toPlusSection) (by
        intro α β h
        exact (toPlusSection_eq_iff_equivalent (J := J) α β).2 h)
  invFun := fun s =>
    _root_.Quotient.mk (setoid (J := J) X f)
      (Classical.choose (toPlusSection_surjective (J := J) (X := X) (x := x) (y := y)
        (f := f) s))
  left_inv := by
    intro q
    induction q using _root_.Quot.inductionOn with
    | h α =>
        apply _root_.Quotient.sound
        exact (toPlusSection_eq_iff_equivalent (J := J)
          (Classical.choose (toPlusSection_surjective (J := J) (X := X) (x := x)
            (y := y) (f := f) α.toPlusSection)) α).1
          (Classical.choose_spec (toPlusSection_surjective (J := J) (X := X) (x := x)
            (y := y) (f := f) α.toPlusSection))
  right_inv := by
    intro s
    exact Classical.choose_spec
      (toPlusSection_surjective (J := J) (X := X) (x := x) (y := y) (f := f) s)

end LocallyDefinedHomRepresentativeOver

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.1: a raw locally-defined morphism
representative from `x` to `y`, including its base arrow. -/
structure LocallyDefinedHomRepresentative
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x y : X.S) where
  /-- The base arrow of the locally-defined morphism. -/
  base : X.p.obj x ⟶ X.p.obj y
  /-- The cover and compatible local morphisms over this base arrow. -/
  representative : LocallyDefinedHomRepresentativeOver (J := J) X base

namespace LocallyDefinedHomRepresentative

/-- Send a raw locally-defined morphism representative to the plus-packaged Hom surface. -/
noncomputable def toLocallyDefinedHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y) :
    locallyDefinedHom (J := J) X x y :=
  ⟨α.base, α.representative.toPlusSection⟩

@[simp]
theorem toLocallyDefinedHom_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y) :
    α.toLocallyDefinedHom.1 = α.base :=
  rfl

end LocallyDefinedHomRepresentative

namespace LocallyDefinedHomRepresentativeOver

/-- Rebase a fixed-base locally-defined morphism representative along an equality of displayed
base arrows.  This is only transport; it lets arbitrary-base representative equalities be reduced
to the fixed-base common-refinement relation used in the source proof. -/
noncomputable def castBase
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f f' : X.p.obj x ⟶ X.p.obj y} (h : f = f')
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    LocallyDefinedHomRepresentativeOver (J := J) X f' := by
  cases h
  exact α

@[simp]
theorem castBase_rfl
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    castBase (J := J) (rfl : f = f) α = α :=
  rfl

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomRepresentative

/-- Every plus-packaged locally-defined morphism admits a raw representative. -/
theorem toLocallyDefinedHom_surjective
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (s : locallyDefinedHom (J := J) X x y) :
    ∃ α : LocallyDefinedHomRepresentative (J := J) X x y,
      α.toLocallyDefinedHom = s := by
  rcases s with ⟨f, sf⟩
  obtain ⟨αf, hαf⟩ :=
    LocallyDefinedHomRepresentativeOver.toPlusSection_surjective (J := J) (X := X) (x := x)
      (y := y) (f := f) sf
  refine ⟨⟨f, αf⟩, ?_⟩
  cases hαf
  rfl

/-- Source stage 2.2 for arbitrary base arrows: two raw locally-defined morphisms represent the
same plus-packaged morphism exactly when their images in `locallyDefinedHom` are equal.  The
fixed-base common-refinement criterion above is the concrete test after the base arrows are
identified. -/
def Equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α β : LocallyDefinedHomRepresentative (J := J) X x y) : Prop :=
  α.toLocallyDefinedHom = β.toLocallyDefinedHom

/-- Equivalent raw representatives have the same base arrow. -/
theorem equivalent_base_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {α β : LocallyDefinedHomRepresentative (J := J) X x y}
    (h : Equivalent (J := J) α β) :
    α.base = β.base :=
  congrArg Sigma.fst h

/-- If two representatives have the same displayed base arrow, equality in the plus-packaged
Hom surface is exactly common-refinement equivalence of their fixed-base representatives. -/
theorem sameBase_toLocallyDefinedHom_eq_iff
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α β : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    (toLocallyDefinedHom (J := J)
        ({ base := f, representative := α } :
          LocallyDefinedHomRepresentative (J := J) X x y) =
      toLocallyDefinedHom (J := J)
        ({ base := f, representative := β } :
          LocallyDefinedHomRepresentative (J := J) X x y)) ↔
      LocallyDefinedHomRepresentativeOver.Equivalent (J := J) α β := by
  change (⟨f, α.toPlusSection⟩ : locallyDefinedHom (J := J) X x y) =
      ⟨f, β.toPlusSection⟩ ↔
    LocallyDefinedHomRepresentativeOver.Equivalent (J := J) α β
  constructor
  · intro h
    have hs : α.toPlusSection = β.toPlusSection :=
      eq_of_heq (Sigma.ext_iff.1 h).2
    exact
      (LocallyDefinedHomRepresentativeOver.toPlusSection_eq_iff_equivalent (J := J) α β).1 hs
  · intro h
    have hs : α.toPlusSection = β.toPlusSection :=
      (LocallyDefinedHomRepresentativeOver.toPlusSection_eq_iff_equivalent (J := J) α β).2 h
    exact Sigma.ext rfl (heq_of_eq hs)

/-- Arbitrary-base representative equivalence is exactly a displayed-base equality plus the
fixed-base common-refinement equivalence after transporting along that base equality.  This is the
dependent bookkeeping form of source stage 2.2. -/
theorem equivalent_iff_exists_base_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α β : LocallyDefinedHomRepresentative (J := J) X x y) :
    Equivalent (J := J) α β ↔
      ∃ hbase : α.base = β.base,
        LocallyDefinedHomRepresentativeOver.Equivalent (J := J)
          (LocallyDefinedHomRepresentativeOver.castBase (J := J) hbase α.representative)
          β.representative := by
  constructor
  · intro h
    let hbase : α.base = β.base := equivalent_base_eq (J := J) h
    refine ⟨hbase, ?_⟩
    cases α with
    | mk f a =>
      cases β with
      | mk g b =>
        dsimp at hbase h ⊢
        cases hbase
        exact (sameBase_toLocallyDefinedHom_eq_iff (J := J) a b).1 h
  · rintro ⟨hbase, heq⟩
    cases α with
    | mk f a =>
      cases β with
      | mk g b =>
        dsimp at hbase heq ⊢
        cases hbase
        exact (sameBase_toLocallyDefinedHom_eq_iff (J := J) a b).2 heq

/-- The raw-representative equality relation is reflexive. -/
theorem equivalent_refl
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y) :
    Equivalent (J := J) α α :=
  rfl

/-- The raw-representative equality relation is symmetric. -/
theorem equivalent_symm
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {α β : LocallyDefinedHomRepresentative (J := J) X x y}
    (h : Equivalent (J := J) α β) :
    Equivalent (J := J) β α :=
  h.symm

/-- The raw-representative equality relation is transitive. -/
theorem equivalent_trans
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {α β γ : LocallyDefinedHomRepresentative (J := J) X x y}
    (hαβ : Equivalent (J := J) α β) (hβγ : Equivalent (J := J) β γ) :
    Equivalent (J := J) α γ :=
  hαβ.trans hβγ

/-- The setoid of raw representatives whose quotient is the plus-packaged Hom type. -/
def setoid
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x y : X.S) :
    Setoid (LocallyDefinedHomRepresentative (J := J) X x y) where
  r := Equivalent (J := J)
  iseqv := ⟨equivalent_refl (J := J), equivalent_symm (J := J),
    equivalent_trans (J := J)⟩

/-- The source-cover used for composing raw locally-defined morphisms: intersect the cover for
`α` with the pullback of the source cover for `β` along the base arrow of `α`.  This is the
formal cover corresponding to `T_{ij} = U_i ×_V V_j` in the source proof. -/
noncomputable def compositionCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x))) :=
  α.cover ⊓
    identitySliceCoverOfBaseCover (J := J)
      (((J.pullback f).obj β.baseCover))

/-- A member of the composition cover is in the cover for the first morphism. -/
def compositionCoverToLeft
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    α.cover.Arrow :=
  ⟨I.Y, I.f, I.hf.1⟩

@[simp]
theorem compositionCoverToLeft_f
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (compositionCoverToLeft (J := J) α β I).f = I.f :=
  rfl

/-- A member of the composition cover maps, after the base arrow of the first morphism, into the
source cover for the second morphism. -/
def compositionCoverToRightBase
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    β.baseCover.Arrow :=
  ⟨I.Y.left, I.Y.hom ≫ f, by
    have hbase :
        (((J.pullback f).obj β.baseCover) : Sieve (X.p.obj x)) I.Y.hom := by
      have hslice :
          ((identitySliceCoverOfBaseCover (J := J) (((J.pullback f).obj β.baseCover)) :
              (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))) : Sieve
                (Over.mk (𝟙 (X.p.obj x)))) I.f := I.hf.2
      have hconverted :=
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj x)))
          (((J.pullback f).obj β.baseCover) : Sieve (X.p.obj x)) I.f).1 hslice
      convert hconverted using 1
      simpa using I.f.w.symm
    exact hbase⟩

@[simp]
theorem compositionCoverToRightBase_f
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (compositionCoverToRightBase (J := J) α β I).f = I.Y.hom ≫ f :=
  rfl

/-- A member of the composition cover determines a member of the second morphism's slice cover,
after applying the first base arrow. -/
def compositionCoverToRight
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    β.cover.Arrow := by
  let q : I.Y.left ⟶ X.p.obj y := I.Y.hom ≫ f
  let Y₀ : Over (X.p.obj y) := Over.mk (q ≫ 𝟙 (X.p.obj y))
  let θ₀ : Y₀ ⟶ Over.mk (𝟙 (X.p.obj y)) := Over.homMk q
  have hbase : (β.baseCover : Sieve (X.p.obj y)) q :=
    (compositionCoverToRightBase (J := J) α β I).hf
  have hθ₀ : (β.cover : Sieve (Over.mk (𝟙 (X.p.obj y)))) θ₀ := by
    simpa [q, Y₀, θ₀] using (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj y)))
      (β.cover : Sieve (Over.mk (𝟙 (X.p.obj y)))) q).1 hbase
  let θ : Over.mk q ⟶ Y₀ := Over.homMk (𝟙 I.Y.left) (by simp [q, Y₀])
  exact ⟨Over.mk q, θ ≫ θ₀, β.cover.1.downward_closed hθ₀ θ⟩

@[simp]
theorem compositionCoverToRight_left
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (compositionCoverToRight (J := J) α β I).Y.left = I.Y.left :=
  rfl

@[simp]
theorem compositionCoverToRight_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (compositionCoverToRight (J := J) α β I).Y.hom = I.Y.hom ≫ f :=
  rfl

/-- The quotient of raw locally-defined representatives by the source equality relation is
equivalent to the plus-packaged Hom surface.  This is the formal version of "以后直接把 locally
defined morphism 看成该等价类" from the source-style draft. -/
noncomputable def quotientEquivLocallyDefinedHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x y : X.S) :
    _root_.Quotient (setoid (J := J) X x y) ≃ locallyDefinedHom (J := J) X x y where
  toFun :=
    _root_.Quot.lift (fun α : LocallyDefinedHomRepresentative (J := J) X x y =>
      α.toLocallyDefinedHom) (by
        intro α β h
        exact h)
  invFun := fun s =>
    _root_.Quotient.mk (setoid (J := J) X x y)
      (Classical.choose (toLocallyDefinedHom_surjective (J := J) (X := X) (x := x) (y := y) s))
  left_inv := by
    intro q
    induction q using _root_.Quot.inductionOn with
    | h α =>
        apply _root_.Quotient.sound
        exact (Classical.choose_spec
          (toLocallyDefinedHom_surjective (J := J) (X := X) (x := x) (y := y)
            α.toLocallyDefinedHom))
  right_inv := by
    intro s
    exact Classical.choose_spec
      (toLocallyDefinedHom_surjective (J := J) (X := X) (x := x) (y := y) s)

end LocallyDefinedHomRepresentative

namespace LocallyDefinedHomRepresentativeOver

/-- Owner-correct alias for the source-cover used to compose fixed-base raw representatives. -/
noncomputable abbrev compositionCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x))) :=
  LocallyDefinedHomRepresentative.compositionCover (J := J) α β

/-- Owner-correct alias for the projection from the composition cover to the first cover. -/
abbrev compositionCoverToLeft
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    α.cover.Arrow :=
  LocallyDefinedHomRepresentative.compositionCoverToLeft (J := J) α β I

/-- Owner-correct alias for the projection from the composition cover to the base cover of the
second morphism. -/
abbrev compositionCoverToRightBase
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    β.baseCover.Arrow :=
  LocallyDefinedHomRepresentative.compositionCoverToRightBase (J := J) α β I

/-- Owner-correct alias for the projection from the composition cover to the second slice cover. -/
abbrev compositionCoverToRight
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    β.cover.Arrow :=
  LocallyDefinedHomRepresentative.compositionCoverToRight (J := J) α β I

/-- The local representative contributed by the first morphism on a member of the composition
cover. -/
abbrev compositionLeftLocal
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (locallyDefinedHomSaturatedPresheaf X f).obj
      (op (compositionCoverToLeft (J := J) α β I).Y) :=
  α.family (compositionCoverToLeft (J := J) α β I)

/-- The local representative contributed by the second morphism on a member of the composition
cover. -/
abbrev compositionRightLocal
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (locallyDefinedHomSaturatedPresheaf X g).obj
      (op (compositionCoverToRight (J := J) α β I).Y) :=
  β.family (compositionCoverToRight (J := J) α β I)

/-- A relation in the composition cover induces the corresponding relation in the first cover. -/
def compositionCoverLeftRelation
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    (compositionCoverToLeft (J := J) α β ((compositionCover (J := J) α β).shape.fst R)).Relation
      (compositionCoverToLeft (J := J) α β ((compositionCover (J := J) α β).shape.snd R)) :=
  { R.r with }

/-- The compatibility condition of the first raw representative, specialized to a relation of the
composition cover. -/
theorem compositionLeftLocal_condition
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    (locallyDefinedHomSaturatedPresheaf X f).map R.r.g₁.op
        (compositionLeftLocal (J := J) α β ((compositionCover (J := J) α β).shape.fst R)) =
      (locallyDefinedHomSaturatedPresheaf X f).map R.r.g₂.op
        (compositionLeftLocal (J := J) α β ((compositionCover (J := J) α β).shape.snd R)) :=
  α.family.condition
    (GrothendieckTopology.Cover.Relation.mk'
      (compositionCoverLeftRelation (J := J) α β R))

set_option linter.unnecessarySimpa false in
/-- The first matching condition with `ULift` removed and the base arrows normalized to the common
overlap object. -/
theorem compositionLeftLocal_condition_down
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionLeftLocal (J := J) α β R.fst).down
        R.r.g₁.left R.r.Z.hom R.r.Z.hom
        (by simpa using R.r.g₁.w)
        (by simpa using R.r.g₁.w) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionLeftLocal (J := J) α β R.snd).down
        R.r.g₂.left R.r.Z.hom R.r.Z.hom
        (by simpa using R.r.g₂.w)
        (by simpa using R.r.g₂.w) := by
  have hα := congrArg ULift.down (compositionLeftLocal_condition (J := J) α β R)
  dsimp [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf] at hα
  simpa using hα

/-- A relation in the composition cover induces a relation in the base cover underlying the
second representative. -/
def compositionCoverRightBaseRelation
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    (compositionCoverToRightBase (J := J) α β
        ((compositionCover (J := J) α β).shape.fst R)).Relation
      (compositionCoverToRightBase (J := J) α β
        ((compositionCover (J := J) α β).shape.snd R)) where
  Z := R.r.Z.left
  g₁ := R.r.g₁.left
  g₂ := R.r.g₂.left
  w := by
    have hwLeft :
        R.r.g₁.left ≫ ((compositionCover (J := J) α β).shape.fst R).f.left =
          R.r.g₂.left ≫ ((compositionCover (J := J) α β).shape.snd R).f.left :=
      by
        simpa using
          (congrArg
            (fun e : R.r.Z ⟶ Over.mk (𝟙 (X.p.obj x)) => e.left) R.r.w)
    have hfst :
        ((compositionCover (J := J) α β).shape.fst R).f.left =
          ((compositionCover (J := J) α β).shape.fst R).Y.hom := by
      simpa using ((compositionCover (J := J) α β).shape.fst R).f.w
    have hsnd :
        ((compositionCover (J := J) α β).shape.snd R).f.left =
          ((compositionCover (J := J) α β).shape.snd R).Y.hom := by
      simpa using ((compositionCover (J := J) α β).shape.snd R).f.w
    simp only [LocallyDefinedHomRepresentative.compositionCoverToRightBase_f]
    calc
      R.r.g₁.left ≫ (((compositionCover (J := J) α β).shape.fst R).Y.hom ≫ f)
          = (R.r.g₁.left ≫ ((compositionCover (J := J) α β).shape.fst R).f.left) ≫ f := by
              rw [hfst]
              simp [Category.assoc]
      _ = (R.r.g₂.left ≫ ((compositionCover (J := J) α β).shape.snd R).f.left) ≫ f := by
              rw [hwLeft]
      _ = R.r.g₂.left ≫ (((compositionCover (J := J) α β).shape.snd R).Y.hom ≫ f) := by
              rw [hsnd]
              simp [Category.assoc]

/-- A relation in the composition cover induces the corresponding relation in the slice cover
underlying the second representative. -/
def compositionCoverRightRelation
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    (compositionCoverToRight (J := J) α β
        ((compositionCover (J := J) α β).shape.fst R)).Relation
      (compositionCoverToRight (J := J) α β
        ((compositionCover (J := J) α β).shape.snd R)) where
  Z := Over.mk (R.r.Z.hom ≫ f)
  g₁ := Over.homMk R.r.g₁.left (by
    simp only [LocallyDefinedHomRepresentative.compositionCoverToRight_hom]
    simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w)
  g₂ := Over.homMk R.r.g₂.left (by
    simp only [LocallyDefinedHomRepresentative.compositionCoverToRight_hom]
    simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w)
  w := by
    ext
    have h₁ :
        R.r.g₁.left ≫ R.fst.Y.hom = R.r.Z.hom := by
      simpa using R.r.g₁.w
    have h₂ :
        R.r.g₂.left ≫ R.snd.Y.hom = R.r.Z.hom := by
      simpa using R.r.g₂.w
    have hf₁ :
        (compositionCoverToRight (J := J) α β R.fst).f.left =
          R.fst.Y.hom ≫ f := by
      simp [LocallyDefinedHomRepresentative.compositionCoverToRight]
    have hf₂ :
        (compositionCoverToRight (J := J) α β R.snd).f.left =
          R.snd.Y.hom ≫ f := by
      simp [LocallyDefinedHomRepresentative.compositionCoverToRight]
    simpa [hf₁, hf₂, Category.assoc] using
      (congrArg (fun h => h ≫ f) h₁).trans
        (congrArg (fun h => h ≫ f) h₂).symm

/-- The compatibility condition of the second raw representative, specialized to a relation of the
composition cover. -/
theorem compositionRightLocal_condition
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    (locallyDefinedHomSaturatedPresheaf X g).map
        (compositionCoverRightRelation (J := J) α β R).g₁.op
        (compositionRightLocal (J := J) α β ((compositionCover (J := J) α β).shape.fst R)) =
      (locallyDefinedHomSaturatedPresheaf X g).map
        (compositionCoverRightRelation (J := J) α β R).g₂.op
        (compositionRightLocal (J := J) α β ((compositionCover (J := J) α β).shape.snd R)) :=
  β.family.condition
    (GrothendieckTopology.Cover.Relation.mk'
      (compositionCoverRightRelation (J := J) α β R))

set_option linter.unnecessarySimpa false in
/-- The second matching condition with `ULift` removed and the pulled-back right-cover arrows
normalized to the common overlap object. -/
theorem compositionRightLocal_condition_down
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionRightLocal (J := J) α β R.fst).down
        R.r.g₁.left (R.r.Z.hom ≫ f) (R.r.Z.hom ≫ f)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionRightLocal (J := J) α β R.snd).down
        R.r.g₂.left (R.r.Z.hom ≫ f) (R.r.Z.hom ≫ f)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w) := by
  have hβ := congrArg ULift.down (compositionRightLocal_condition (J := J) α β R)
  dsimp [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf] at hβ
  simpa [compositionCoverRightRelation, Category.assoc] using hβ

set_option backward.isDefEq.respectTransparency false in
/-- The comparison identifying the target of the first local morphism with the source of the
second local morphism on a member of the composition cover. -/
noncomputable def compositionMiddleIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.obj
        (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := y) rfl)) ≅
      ((canonicalFiberPseudofunctor X.p).map
          ((I.Y.hom ≫ f).op.toLoc)).toFunctor.obj
        (Functor.Fiber.mk (p := X.p) (a := y) rfl) :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp' f.op.toLoc I.Y.hom.op.toLoc
        ((I.Y.hom ≫ f).op.toLoc) (by rfl))).app
      (Functor.Fiber.mk (p := X.p) (a := y) rfl)).symm

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the middle comparison isomorphism to an overlap depends only on the common
overlap object, not on which side of the relation it came from. -/
theorem compositionMiddleIso_pullHom_condition
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionMiddleIso (J := J) α β R.fst).hom
        R.r.g₁.left R.r.Z.hom (R.r.Z.hom ≫ f)
        (by simpa using R.r.g₁.w)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionMiddleIso (J := J) α β R.snd).hom
        R.r.g₂.left R.r.Z.hom (R.r.Z.hom ≫ f)
        (by simpa using R.r.g₂.w)
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  have h₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_inv_of_fac
    (F := Fp) f R.fst.Y.hom R.r.g₁.left R.r.Z.hom (by simpa using R.r.g₁.w) yF
  have h₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_inv_of_fac
    (F := Fp) f R.snd.Y.hom R.r.g₂.left R.r.Z.hom (by simpa using R.r.g₂.w) yF
  trans (Fp.mapComp' f.op.toLoc R.r.Z.hom.op.toLoc
      (f.op.toLoc ≫ R.r.Z.hom.op.toLoc) (by simp)).inv.toNatTrans.app yF
  · simpa [Fp, yF, compositionMiddleIso, Category.assoc] using h₁
  · symm
    simpa [Fp, yF, compositionMiddleIso, Category.assoc] using h₂

set_option backward.isDefEq.respectTransparency false in
/-- The comparison identifying the target of the second local morphism with the target required
for the composite base arrow. -/
noncomputable def compositionTargetIso
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map
        ((I.Y.hom ≫ f).op.toLoc)).toFunctor.obj
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := z) rfl)) ≅
      ((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.obj
        (((canonicalFiberPseudofunctor X.p).map (f ≫ g).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := z) rfl)) :=
  ((Cat.Hom.toNatIso
      ((canonicalFiberPseudofunctor X.p).mapComp g.op.toLoc
        ((I.Y.hom ≫ f).op.toLoc))).app
      (Functor.Fiber.mk (p := X.p) (a := z) rfl)).symm ≪≫
    eqToIso (by simp [Category.assoc]) ≪≫
      (Cat.Hom.toNatIso
        ((canonicalFiberPseudofunctor X.p).mapComp (f ≫ g).op.toLoc I.Y.hom.op.toLoc)).app
        (Functor.Fiber.mk (p := X.p) (a := z) rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The target comparison morphism used in the local composite, written as the source-faithful
two-step comparison that first restricts the `f`-comparison and then applies the `g,f`
comparison under the local base. -/
noncomputable def compositionTargetHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map
        ((I.Y.hom ≫ f).op.toLoc)).toFunctor.obj
        (((canonicalFiberPseudofunctor X.p).map g.op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := z) rfl)) ⟶
      ((canonicalFiberPseudofunctor X.p).map I.Y.hom.op.toLoc).toFunctor.obj
        (((canonicalFiberPseudofunctor X.p).map (f ≫ g).op.toLoc).toFunctor.obj
          (Functor.Fiber.mk (p := X.p) (a := z) rfl)) :=
  let Fp := canonicalFiberPseudofunctor X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  (Fp.mapComp' f.op.toLoc I.Y.hom.op.toLoc ((I.Y.hom ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
      ((Fp.map g.op.toLoc).toFunctor.obj zF) ≫
    (Fp.map I.Y.hom.op.toLoc).toFunctor.map
      ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the target comparison morphism to an overlap depends only on the common overlap
object. -/
theorem compositionTargetHom_pullHom_condition
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (R : (compositionCover (J := J) α β).Relation) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionTargetHom (J := J) α β R.fst)
        R.r.g₁.left (R.r.Z.hom ≫ f) R.r.Z.hom
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w)
        (by simpa using R.r.g₁.w) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (compositionTargetHom (J := J) α β R.snd)
        R.r.g₂.left (R.r.Z.hom ≫ f) R.r.Z.hom
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w)
        (by simpa using R.r.g₂.w) := by
  let Fp := canonicalFiberPseudofunctor X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  let gzF : X.p.Fiber (X.p.obj y) := (Fp.map g.op.toLoc).toFunctor.obj zF
  let φ₁ := (Fp.mapComp' f.op.toLoc R.fst.Y.hom.op.toLoc
    ((R.fst.Y.hom ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app gzF
  let ψ₁ := (Fp.map R.fst.Y.hom.op.toLoc).toFunctor.map
    ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)
  let φ₂ := (Fp.mapComp' f.op.toLoc R.snd.Y.hom.op.toLoc
    ((R.snd.Y.hom ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app gzF
  let ψ₂ := (Fp.map R.snd.Y.hom.op.toLoc).toFunctor.map
    ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)
  have hsplit₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := Fp) φ₁ ψ₁ R.r.g₁.left (R.r.Z.hom ≫ f) R.r.Z.hom R.r.Z.hom
    (by simpa [φ₁, Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w)
    (by simpa [φ₁] using R.r.g₁.w) (by simpa [φ₁] using R.r.g₁.w)
  have hsplit₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := Fp) φ₂ ψ₂ R.r.g₂.left (R.r.Z.hom ≫ f) R.r.Z.hom R.r.Z.hom
    (by simpa [φ₂, Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w)
    (by simpa [φ₂] using R.r.g₂.w) (by simpa [φ₂] using R.r.g₂.w)
  have h₁a :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Fp) φ₁
        R.r.g₁.left (R.r.Z.hom ≫ f) R.r.Z.hom
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₁.w)
        (by simpa using R.r.g₁.w) =
      (Fp.mapComp' f.op.toLoc R.r.Z.hom.op.toLoc
        (f.op.toLoc ≫ R.r.Z.hom.op.toLoc) (by simp)).hom.toNatTrans.app gzF := by
    simpa [φ₁, Fp, gzF, Category.assoc] using
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_of_fac
        (F := Fp) f R.fst.Y.hom R.r.g₁.left R.r.Z.hom (by simpa using R.r.g₁.w) gzF
  have h₁b :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Fp) ψ₁
        R.r.g₁.left R.r.Z.hom R.r.Z.hom
        (by simpa using R.r.g₁.w) (by simpa using R.r.g₁.w) =
      (Fp.map R.r.Z.hom.op.toLoc).toFunctor.map
        ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF) := by
    simpa [ψ₁, Fp, zF] using
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map_of_fac
        (F := Fp) R.fst.Y.hom R.r.g₁.left R.r.Z.hom (by simpa using R.r.g₁.w)
        ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)
  have h₂a :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Fp) φ₂
        R.r.g₂.left (R.r.Z.hom ≫ f) R.r.Z.hom
        (by simpa [Category.assoc] using congrArg (fun h => h ≫ f) R.r.g₂.w)
        (by simpa using R.r.g₂.w) =
      (Fp.mapComp' f.op.toLoc R.r.Z.hom.op.toLoc
        (f.op.toLoc ≫ R.r.Z.hom.op.toLoc) (by simp)).hom.toNatTrans.app gzF := by
    simpa [φ₂, Fp, gzF, Category.assoc] using
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapComp'_hom_of_fac
        (F := Fp) f R.snd.Y.hom R.r.g₂.left R.r.Z.hom (by simpa using R.r.g₂.w) gzF
  have h₂b :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Fp) ψ₂
        R.r.g₂.left R.r.Z.hom R.r.Z.hom
        (by simpa using R.r.g₂.w) (by simpa using R.r.g₂.w) =
      (Fp.map R.r.Z.hom.op.toLoc).toFunctor.map
        ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF) := by
    simpa [ψ₂, Fp, zF] using
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map_of_fac
        (F := Fp) R.snd.Y.hom R.r.g₂.left R.r.Z.hom (by simpa using R.r.g₂.w)
        ((Fp.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app zF)
  simp only [compositionTargetHom]
  rw [hsplit₁, hsplit₂]
  simp only [Fp, zF, gzF, φ₁, ψ₁, φ₂, ψ₂] at h₁a h₁b h₂a h₂b ⊢
  rw [h₁a, h₁b, h₂a, h₂b]

set_option backward.isDefEq.respectTransparency false in
/-- The local morphism on one member of the composition cover, obtained by composing the two
local representatives with the canonical pseudofunctor comparison isomorphisms. -/
noncomputable def compositionLocal
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (locallyDefinedHomSaturatedPresheaf X (f ≫ g)).obj (op I.Y) :=
  ULift.up
    ((compositionLeftLocal (J := J) α β I).down ≫
      (compositionMiddleIso (J := J) α β I).hom ≫
      (compositionRightLocal (J := J) α β I).down ≫
      compositionTargetHom (J := J) α β I)

/-- The explicit compatibility condition required for the locally defined composites to form a
matching family on the composition cover.  This is the formal statement of the source proof's
overlap check for `b_j ∘ a_i`. -/
def compositionLocalCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) : Prop :=
  ∀ R : (compositionCover (J := J) α β).Relation,
    (locallyDefinedHomSaturatedPresheaf X (f ≫ g)).map R.r.g₁.op
        (compositionLocal (J := J) α β ((compositionCover (J := J) α β).shape.fst R)) =
      (locallyDefinedHomSaturatedPresheaf X (f ≫ g)).map R.r.g₂.op
        (compositionLocal (J := J) α β ((compositionCover (J := J) α β).shape.snd R))

set_option linter.unnecessarySimpa false in
set_option backward.isDefEq.respectTransparency false in
/-- The local composites form a matching family on the composition cover. -/
theorem compositionLocalCompatible_holds
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    compositionLocalCompatible (J := J) α β := by
  intro R
  apply ULift.ext
  dsimp [locallyDefinedHomSaturatedPresheaf, locallyDefinedHomPresheaf, compositionLocal]
  let Fp := canonicalFiberPseudofunctor X.p
  let L₁ := (compositionLeftLocal (J := J) α β R.fst).down
  let M₁ := (compositionMiddleIso (J := J) α β R.fst).hom
  let N₁ := (compositionRightLocal (J := J) α β R.fst).down
  let T₁ := compositionTargetHom (J := J) α β R.fst
  let L₂ := (compositionLeftLocal (J := J) α β R.snd).down
  let M₂ := (compositionMiddleIso (J := J) α β R.snd).hom
  let N₂ := (compositionRightLocal (J := J) α β R.snd).down
  let T₂ := compositionTargetHom (J := J) α β R.snd
  have hg₁ : R.r.g₁.left ≫ R.fst.Y.hom = R.r.Z.hom := by simpa using R.r.g₁.w
  have hg₂ : R.r.g₂.left ≫ R.snd.Y.hom = R.r.Z.hom := by simpa using R.r.g₂.w
  have hg₁f : R.r.g₁.left ≫ R.fst.Y.hom ≫ f = R.r.Z.hom ≫ f := by
    simpa [Category.assoc] using congrArg (fun h => h ≫ f) hg₁
  have hg₂f : R.r.g₂.left ≫ R.snd.Y.hom ≫ f = R.r.Z.hom ≫ f := by
    simpa [Category.assoc] using congrArg (fun h => h ≫ f) hg₂
  have hsplit₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp₄
    (F := Fp) L₁ M₁ N₁ T₁ R.r.g₁.left R.r.Z.hom R.r.Z.hom
    (R.r.Z.hom ≫ f) (R.r.Z.hom ≫ f) R.r.Z.hom
    hg₁ hg₁ hg₁f hg₁f hg₁
  have hsplit₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp₄
    (F := Fp) L₂ M₂ N₂ T₂ R.r.g₂.left R.r.Z.hom R.r.Z.hom
    (R.r.Z.hom ≫ f) (R.r.Z.hom ≫ f) R.r.Z.hom
    hg₂ hg₂ hg₂f hg₂f hg₂
  rw [hsplit₁, hsplit₂]
  have hL := compositionLeftLocal_condition_down (J := J) α β R
  have hM := compositionMiddleIso_pullHom_condition (J := J) α β R
  have hN := compositionRightLocal_condition_down (J := J) α β R
  have hT := compositionTargetHom_pullHom_condition (J := J) α β R
  simp only [Fp, L₁, M₁, N₁, T₁, L₂, M₂, N₂, T₂] at hL hM hN hT ⊢
  rw [hL, hM, hN, hT]

/-- The matching family of local composites, once the overlap compatibility has been proved. -/
noncomputable def compositionFamilyOfCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (h : compositionLocalCompatible (J := J) α β) :
    Meq (locallyDefinedHomSaturatedPresheaf X (f ≫ g))
      (compositionCover (J := J) α β) :=
  ⟨fun I => compositionLocal (J := J) α β I, h⟩

/-- The raw fixed-base composite of two locally-defined representatives, conditional on the
explicit matching-family compatibility. -/
noncomputable def composeOverOfCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (h : compositionLocalCompatible (J := J) α β) :
    LocallyDefinedHomRepresentativeOver (J := J) X (f ≫ g) where
  cover := compositionCover (J := J) α β
  family := compositionFamilyOfCompatible (J := J) α β h

/-- The matching family of local composites. -/
noncomputable def compositionFamily
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    Meq (locallyDefinedHomSaturatedPresheaf X (f ≫ g))
      (compositionCover (J := J) α β) :=
  compositionFamilyOfCompatible (J := J) α β
    (compositionLocalCompatible_holds (J := J) α β)

@[simp]
theorem compositionFamily_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    compositionFamily (J := J) α β I = compositionLocal (J := J) α β I :=
  rfl

/-- The raw fixed-base composite of two locally-defined representatives. -/
noncomputable def composeOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    LocallyDefinedHomRepresentativeOver (J := J) X (f ≫ g) :=
  composeOverOfCompatible (J := J) α β
    (compositionLocalCompatible_holds (J := J) α β)

@[simp]
theorem composeOverOfCompatible_eq_composeOver
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (h : compositionLocalCompatible (J := J) α β) :
    composeOverOfCompatible (J := J) α β h = composeOver (J := J) α β :=
  rfl

@[simp]
theorem composeOver_cover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    (composeOver (J := J) α β).cover = compositionCover (J := J) α β :=
  rfl

@[simp]
theorem composeOver_family
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    (composeOver (J := J) α β).family = compositionFamily (J := J) α β :=
  rfl

@[simp]
theorem composeOver_family_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) α β).Arrow) :
    (composeOver (J := J) α β).family I = compositionLocal (J := J) α β I :=
  rfl

/-- Refining the first representative induces a refinement of the composite cover. -/
noncomputable def compositionCoverRefineLeftHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    compositionCover (J := J) (α.refine h) β ⟶ compositionCover (J := J) α β :=
  homOfLE (by
    intro Y k hk
    exact ⟨(leOfHom h) _ hk.1, hk.2⟩)

/-- On the cover induced by refining the first representative, the composite family is exactly the
refinement of the original composite family. -/
theorem composeOver_refine_left_family_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    (I : (compositionCover (J := J) (α.refine h) β).Arrow) :
    (composeOver (J := J) (α.refine h) β).family I =
      (composeOver (J := J) α β).family
        ⟨I.Y, I.f, (leOfHom (compositionCoverRefineLeftHom (J := J) α h β)) _ I.hf⟩ :=
  rfl

/-- Refining the first representative does not change the represented composite. -/
theorem composeOver_refine_left_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {W : (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))}
    (h : W ⟶ α.cover)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    Equivalent (J := J) (composeOver (J := J) (α.refine h) β)
      (composeOver (J := J) α β) :=
  ⟨compositionCover (J := J) (α.refine h) β, 𝟙 _,
    compositionCoverRefineLeftHom (J := J) α h β, by
      ext I
      exact composeOver_refine_left_family_apply (J := J) α h β I⟩

/-- Refining the second representative induces a refinement of the composite cover. -/
noncomputable def compositionCoverRefineRightHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    {W : (J.over (X.p.obj y)).Cover (Over.mk (𝟙 (X.p.obj y)))}
    (h : W ⟶ β.cover) :
    compositionCover (J := J) α (β.refine h) ⟶ compositionCover (J := J) α β :=
  homOfLE (by
    intro Y k hk
    refine ⟨hk.1, ?_⟩
    have hb : (β.refine h).baseCover ⟶ β.baseCover := baseCoverHom (J := J) h
    exact (leOfHom ((J.pullback f).map hb)) _ hk.2)

/-- On the cover induced by refining the second representative, the composite family is exactly the
refinement of the original composite family. -/
theorem composeOver_refine_right_family_apply
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    {W : (J.over (X.p.obj y)).Cover (Over.mk (𝟙 (X.p.obj y)))}
    (h : W ⟶ β.cover)
    (I : (compositionCover (J := J) α (β.refine h)).Arrow) :
    (composeOver (J := J) α (β.refine h)).family I =
      (composeOver (J := J) α β).family
        ⟨I.Y, I.f, (leOfHom (compositionCoverRefineRightHom (J := J) α β h)) _ I.hf⟩ :=
  rfl

/-- Refining the second representative does not change the represented composite. -/
theorem composeOver_refine_right_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g)
    {W : (J.over (X.p.obj y)).Cover (Over.mk (𝟙 (X.p.obj y)))}
    (h : W ⟶ β.cover) :
    Equivalent (J := J) (composeOver (J := J) α (β.refine h))
      (composeOver (J := J) α β) :=
  ⟨compositionCover (J := J) α (β.refine h), 𝟙 _,
    compositionCoverRefineRightHom (J := J) α β h, by
      ext I
      exact composeOver_refine_right_family_apply (J := J) α β h I⟩

/-- Fixed-base composite respects equivalence in the first representative.  This formalizes the
source proof's common-refinement argument
`U_i ×_U U'_{i'} ×_V V_j`, with the second representative held fixed. -/
theorem composeOver_equivalent_left
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    {α α' : LocallyDefinedHomRepresentativeOver (J := J) X f}
    (hα : Equivalent (J := J) α α')
    (β : LocallyDefinedHomRepresentativeOver (J := J) X g) :
    Equivalent (J := J) (composeOver (J := J) α β) (composeOver (J := J) α' β) := by
  rcases hα with ⟨W, h, h', hW⟩
  have hleft := composeOver_refine_left_equivalent (J := J) α h β
  have hright := composeOver_refine_left_equivalent (J := J) α' h' β
  have hmid :
      Equivalent (J := J) (composeOver (J := J) (α.refine h) β)
        (composeOver (J := J) (α'.refine h') β) := by
    apply (toPlusSection_eq_iff_equivalent (J := J)
      (composeOver (J := J) (α.refine h) β)
      (composeOver (J := J) (α'.refine h') β)).1
    change GrothendieckTopology.Plus.mk (compositionFamily (J := J) (α.refine h) β) =
      GrothendieckTopology.Plus.mk (compositionFamily (J := J) (α'.refine h') β)
    congr 1
    ext I
    have hI := congrArg
      (fun m : Meq (locallyDefinedHomSaturatedPresheaf X f) W =>
        m (compositionCoverToLeft (J := J) (α.refine h) β I)) hW
    dsimp [compositionFamily, compositionFamilyOfCompatible, compositionLocal,
      compositionLeftLocal, compositionMiddleIso, compositionRightLocal, compositionCoverToRight,
      compositionTargetHom] at hI ⊢
    rw [hI]
    rfl
  exact equivalent_trans (J := J) (equivalent_symm (J := J) hleft)
    (equivalent_trans (J := J) hmid hright)

/-- Fixed-base composite respects equivalence in the second representative.  This is the
right-hand version of the source proof's common-refinement argument
`U_i ×_U U'_{i'} ×_V V_j ×_V V'_{j'}`. -/
theorem composeOver_equivalent_right
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f)
    {β β' : LocallyDefinedHomRepresentativeOver (J := J) X g}
    (hβ : Equivalent (J := J) β β') :
    Equivalent (J := J) (composeOver (J := J) α β) (composeOver (J := J) α β') := by
  rcases hβ with ⟨W, h, h', hW⟩
  have hleft := composeOver_refine_right_equivalent (J := J) α β h
  have hright := composeOver_refine_right_equivalent (J := J) α β' h'
  have hmid :
      Equivalent (J := J) (composeOver (J := J) α (β.refine h))
        (composeOver (J := J) α (β'.refine h')) := by
    apply (toPlusSection_eq_iff_equivalent (J := J)
      (composeOver (J := J) α (β.refine h))
      (composeOver (J := J) α (β'.refine h'))).1
    change GrothendieckTopology.Plus.mk (compositionFamily (J := J) α (β.refine h)) =
      GrothendieckTopology.Plus.mk (compositionFamily (J := J) α (β'.refine h'))
    congr 1
    ext I
    have hI := congrArg
      (fun m : Meq (locallyDefinedHomSaturatedPresheaf X g) W =>
        m (compositionCoverToRight (J := J) α (β.refine h) I)) hW
    dsimp [compositionFamily, compositionFamilyOfCompatible, compositionLocal,
      compositionRightLocal] at hI ⊢
    rw [hI]
    rfl
  exact equivalent_trans (J := J) (equivalent_symm (J := J) hleft)
    (equivalent_trans (J := J) hmid hright)

/-- Fixed-base composite respects simultaneous equivalence of representatives. -/
theorem composeOver_respects_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {f : X.p.obj x ⟶ X.p.obj y} {g : X.p.obj y ⟶ X.p.obj z}
    {α α' : LocallyDefinedHomRepresentativeOver (J := J) X f}
    {β β' : LocallyDefinedHomRepresentativeOver (J := J) X g}
    (hα : Equivalent (J := J) α α') (hβ : Equivalent (J := J) β β') :
    Equivalent (J := J) (composeOver (J := J) α β)
      (composeOver (J := J) α' β') :=
  equivalent_trans (J := J) (composeOver_equivalent_left (J := J) hα β)
    (composeOver_equivalent_right (J := J) α' hβ)

end LocallyDefinedHomRepresentativeOver

namespace LocallyDefinedHomRepresentative

/-- The explicit overlap condition needed to compose two arbitrary raw representatives. -/
abbrev compositionLocalCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z) : Prop :=
  LocallyDefinedHomRepresentativeOver.compositionLocalCompatible (J := J)
    α.representative β.representative

/-- The raw composite of two arbitrary locally-defined representatives, conditional on the
explicit overlap compatibility. -/
noncomputable def composeOfCompatible
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z)
    (h : compositionLocalCompatible (J := J) α β) :
    LocallyDefinedHomRepresentative (J := J) X x z where
  base := α.base ≫ β.base
  representative :=
    LocallyDefinedHomRepresentativeOver.composeOverOfCompatible (J := J)
      α.representative β.representative h

/-- The raw composite of two arbitrary locally-defined representatives. -/
noncomputable def compose
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z) :
    LocallyDefinedHomRepresentative (J := J) X x z where
  base := α.base ≫ β.base
  representative :=
    LocallyDefinedHomRepresentativeOver.composeOver (J := J)
      α.representative β.representative

@[simp]
theorem composeOfCompatible_eq_compose
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z)
    (h : compositionLocalCompatible (J := J) α β) :
    composeOfCompatible (J := J) α β h = compose (J := J) α β :=
  rfl

@[simp]
theorem compose_representative
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z) :
    (compose (J := J) α β).representative =
      LocallyDefinedHomRepresentativeOver.composeOver (J := J)
        α.representative β.representative :=
  rfl

@[simp]
theorem compose_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z) :
    (compose (J := J) α β).base = α.base ≫ β.base :=
  rfl

@[simp]
theorem composeOfCompatible_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z)
    (h : compositionLocalCompatible (J := J) α β) :
    (composeOfCompatible (J := J) α β h).base = α.base ≫ β.base :=
  rfl

/-- Raw locally-defined composition is independent of the chosen representatives.  After the
displayed base arrows are identified, this is exactly the fixed-base common-refinement theorem. -/
theorem compose_respects_equivalent
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    {α α' : LocallyDefinedHomRepresentative (J := J) X x y}
    {β β' : LocallyDefinedHomRepresentative (J := J) X y z}
    (hα : Equivalent (J := J) α α') (hβ : Equivalent (J := J) β β') :
    Equivalent (J := J) (compose (J := J) α β) (compose (J := J) α' β') := by
  cases α with
  | mk f a =>
    cases α' with
    | mk f' a' =>
      cases β with
      | mk g b =>
        cases β' with
        | mk g' b' =>
          dsimp [Equivalent, toLocallyDefinedHom] at hα hβ ⊢
          have hf : f = f' := congrArg Sigma.fst hα
          have hg : g = g' := congrArg Sigma.fst hβ
          cases hf
          cases hg
          have ha : LocallyDefinedHomRepresentativeOver.Equivalent (J := J) a a' :=
            (sameBase_toLocallyDefinedHom_eq_iff (J := J) a a').1 hα
          have hb : LocallyDefinedHomRepresentativeOver.Equivalent (J := J) b b' :=
            (sameBase_toLocallyDefinedHom_eq_iff (J := J) b b').1 hβ
          exact
            (sameBase_toLocallyDefinedHom_eq_iff (J := J)
              (LocallyDefinedHomRepresentativeOver.composeOver (J := J) a b)
              (LocallyDefinedHomRepresentativeOver.composeOver (J := J) a' b')).2
              (LocallyDefinedHomRepresentativeOver.composeOver_respects_equivalent
                (J := J) ha hb)

end LocallyDefinedHomRepresentative

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: an ordinary total-category morphism
`a : x ⟶ y` factors uniquely through the chosen cartesian arrow
`(p(a))^* y ⟶ y`, giving a vertical morphism from `x` to `(p(a))^* y`.  This is the
strict representative used for the trivial-cover locally-defined morphism `G²(a)` in the
source proof. -/
noncomputable def ordinaryHomToPullbackFiberHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    Functor.Fiber.mk (p := X.p) (a := x) rfl ⟶
      (((canonicalFiberPseudofunctor X.p).map (X.p.map a).op.toLoc).toFunctor.obj
        (Functor.Fiber.mk (p := X.p) (a := y) rfl)) := by
  let hc := canonicalPullbackChoice X.p
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  have hcart : X.p.IsStronglyCartesian (X.p.map a) (hc.map (X.p.map a) yF) :=
    hc.isStronglyCartesian (X.p.map a) yF
  have haLift : X.p.IsHomLift (𝟙 (X.p.obj x) ≫ X.p.map a) a := by
    simp
  haveI hcartI : X.p.IsStronglyCartesian (X.p.map a) (hc.map (X.p.map a) yF) := hcart
  haveI haLiftI : X.p.IsHomLift (𝟙 (X.p.obj x) ≫ X.p.map a) a := haLift
  let H := @Functor.IsStronglyCartesian.universal_property C X.S _ _ X.p
    (X.p.obj x) (X.p.obj y) ((hc.obj (X.p.map a) yF).1) y
    (X.p.map a) (hc.map (X.p.map a) yF) hcart
    (X.p.obj x) x (𝟙 (X.p.obj x)) (𝟙 (X.p.obj x) ≫ X.p.map a)
    rfl a haLiftI
  let χ := Classical.choose H
  have hχ : X.p.IsHomLift (𝟙 (X.p.obj x)) χ ∧
      χ ≫ hc.map (X.p.map a) yF = a :=
    (Classical.choose_spec H).1
  refine ⟨χ, ?_⟩
  simpa [hc, yF] using hχ.1

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: the vertical factor from
`ordinaryHomToPullbackFiberHom` composes with the chosen cartesian pullback arrow back to the
original morphism. -/
theorem ordinaryHomToPullbackFiberHom_fac
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    (ordinaryHomToPullbackFiberHom X a).1 ≫
      (canonicalPullbackChoice X.p).map (X.p.map a)
        (Functor.Fiber.mk (p := X.p) (a := y) rfl) = a := by
  unfold ordinaryHomToPullbackFiberHom
  dsimp only []
  let hc := canonicalPullbackChoice X.p
  let yF : X.p.Fiber (X.p.obj y) := Functor.Fiber.mk (p := X.p) (a := y) rfl
  have hcart : X.p.IsStronglyCartesian (X.p.map a) (hc.map (X.p.map a) yF) :=
    hc.isStronglyCartesian (X.p.map a) yF
  have haLift : X.p.IsHomLift (𝟙 (X.p.obj x) ≫ X.p.map a) a := by
    simp
  haveI hcartI : X.p.IsStronglyCartesian (X.p.map a) (hc.map (X.p.map a) yF) := hcart
  haveI haLiftI : X.p.IsHomLift (𝟙 (X.p.obj x) ≫ X.p.map a) a := haLift
  let H := @Functor.IsStronglyCartesian.universal_property C X.S _ _ X.p
    (X.p.obj x) (X.p.obj y) ((hc.obj (X.p.map a) yF).1) y
    (X.p.map a) (hc.map (X.p.map a) yF) hcart
    (X.p.obj x) x (𝟙 (X.p.obj x)) (𝟙 (X.p.obj x) ≫ X.p.map a)
    rfl a haLiftI
  exact (Classical.choose_spec H).1.2

theorem ordinaryHomToPullbackFiberHom_id_fac
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    (ordinaryHomToPullbackFiberHom X (𝟙 x)).1 ≫
      (canonicalPullbackChoice X.p).map (X.p.map (𝟙 x))
        (Functor.Fiber.mk (p := X.p) (a := x) rfl) = 𝟙 x :=
  ordinaryHomToPullbackFiberHom_fac X (𝟙 x)

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: the raw representative of
`G²(a) = (p(a), {id}, a)` before passing to the plus quotient. -/
noncomputable def ordinaryHomToRepresentativeOver
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    LocallyDefinedHomRepresentativeOver (J := J) X (X.p.map a) where
  cover := ⊤
  family :=
    Meq.mk ⊤
      (ULift.up
        (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
          (ordinaryHomToPullbackFiberHom X a)))

@[simp]
theorem ordinaryHomToRepresentativeOver_cover
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    (ordinaryHomToRepresentativeOver (J := J) X a).cover = ⊤ :=
  rfl

theorem ordinaryHomToRepresentativeOver_family_apply
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y)
    (I : (ordinaryHomToRepresentativeOver (J := J) X a).cover.Arrow) :
    (ordinaryHomToRepresentativeOver (J := J) X a).family I =
      (locallyDefinedHomSaturatedPresheaf X (X.p.map a)).map I.f.op
        (ULift.up
          (((canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv)
            (ordinaryHomToPullbackFiberHom X a))) :=
  rfl

namespace LocallyDefinedHomRepresentativeOver

/-- The source cover for `id_x` followed by a fixed representative refines the representative's
original cover.  This is the cover-theoretic part of the left identity law; the remaining
morphism equality is the identity-pullback coherence calculation. -/
noncomputable def compositionCoverLeftIdentityHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    compositionCover (J := J) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) α ⟶
      α.cover :=
  homOfLE (by
    intro Y k hk
    let q : Y.left ⟶ X.p.obj x := k.left
    let Y0 : Over (X.p.obj x) := Over.mk (q ≫ 𝟙 (X.p.obj x))
    let θ0 : Y0 ⟶ Over.mk (𝟙 (X.p.obj x)) := Over.homMk q
    have hpull : (((J.pullback (X.p.map (𝟙 x))).obj α.baseCover) :
        Sieve (X.p.obj x)) q := by
      have hslice :
          ((identitySliceCoverOfBaseCover (J := J)
              (((J.pullback (X.p.map (𝟙 x))).obj α.baseCover)) :
              (J.over (X.p.obj x)).Cover (Over.mk (𝟙 (X.p.obj x)))) :
              Sieve (Over.mk (𝟙 (X.p.obj x)))) k := hk.2
      exact
        (Sieve.overEquiv_symm_iff
          (Y := Over.mk (𝟙 (X.p.obj x)))
          ((((J.pullback (X.p.map (𝟙 x))).obj α.baseCover) :
            Sieve (X.p.obj x))) k).1 hslice
    have hbase : (α.baseCover : Sieve (X.p.obj x)) q := by
      change (α.baseCover : Sieve (X.p.obj x)) (q ≫ X.p.map (𝟙 x)) at hpull
      simpa [q] using hpull
    have hθ0 : (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) θ0 := by
      simpa [q, Y0, θ0] using
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) q).1 hbase
    let θ : Y ⟶ Y0 := Over.homMk (𝟙 Y.left) (by simpa [q, Y0] using k.w)
    have hθ : θ ≫ θ0 = k := by
      ext
      exact Category.id_comp k.left
    simpa [hθ] using α.cover.1.downward_closed hθ0 θ)

/-- The source cover for a fixed representative followed by `id_y` refines the representative's
original cover.  This is the cover-theoretic part of the right identity law. -/
noncomputable def compositionCoverRightIdentityHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    compositionCover (J := J) α (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)) ⟶
      α.cover :=
  homOfLE (by
    intro Y k hk
    exact hk.1)

/-- Conversely, the original cover refines the source cover for `id_x` followed by a fixed
representative.  Together with `compositionCoverLeftIdentityHom`, this records that the left
identity composite uses the same cover up to pullback along the identity base map. -/
noncomputable def compositionCoverLeftIdentityInvHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    α.cover ⟶
      compositionCover (J := J) (ordinaryHomToRepresentativeOver (J := J) X (𝟙 x)) α :=
  homOfLE (by
    intro Y k hk
    refine ⟨?_, ?_⟩
    · trivial
    · let Y₀ : Over (X.p.obj x) := Over.mk (k.left ≫ 𝟙 (X.p.obj x))
      let θ : Y₀ ⟶ Y := Over.homMk (𝟙 Y.left) (by simpa [Y₀] using k.w.symm)
      have hθ : θ ≫ k =
          (Over.homMk k.left :
            Over.mk (k.left ≫ 𝟙 (X.p.obj x)) ⟶
              Over.mk (𝟙 (X.p.obj x))) := by
        ext
        exact Category.id_comp k.left
      have hkcanon :
          (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x))))
            (Over.homMk k.left :
              Over.mk (k.left ≫ 𝟙 (X.p.obj x)) ⟶
                Over.mk (𝟙 (X.p.obj x))) := by
        simpa [hθ] using α.cover.1.downward_closed hk θ
      have hbase : (α.baseCover : Sieve (X.p.obj x)) k.left := by
        exact
          (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj x)))
            (α.cover : Sieve (Over.mk (𝟙 (X.p.obj x)))) k.left).2 hkcanon
      have hpull : (((J.pullback (X.p.map (𝟙 x))).obj α.baseCover) :
          Sieve (X.p.obj x)) k.left := by
        change (α.baseCover : Sieve (X.p.obj x)) (k.left ≫ X.p.map (𝟙 x))
        simpa using hbase
      exact
        (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 (X.p.obj x)))
          ((((J.pullback (X.p.map (𝟙 x))).obj α.baseCover) :
            Sieve (X.p.obj x))) k).2 hpull)

/-- Conversely, the original cover refines the source cover for a fixed representative followed
by `id_y`. -/
noncomputable def compositionCoverRightIdentityInvHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    {f : X.p.obj x ⟶ X.p.obj y}
    (α : LocallyDefinedHomRepresentativeOver (J := J) X f) :
    α.cover ⟶
      compositionCover (J := J) α (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)) :=
  homOfLE (by
    intro Y k hk
    refine ⟨hk, ?_⟩
    have hbase :
        ((ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)).baseCover :
          Sieve (X.p.obj y)) (k.left ≫ f) := by
      change
        ((Sieve.overEquiv (Over.mk (𝟙 (X.p.obj y))))
          (⊤ : Sieve (Over.mk (𝟙 (X.p.obj y))))) (k.left ≫ f)
      exact
        (Sieve.overEquiv_iff (Y := Over.mk (𝟙 (X.p.obj y)))
          (⊤ : Sieve (Over.mk (𝟙 (X.p.obj y)))) (k.left ≫ f)).2 trivial
    have hpull : (((J.pullback f).obj
        (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)).baseCover) :
        Sieve (X.p.obj x)) k.left := by
      change
        ((ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)).baseCover :
          Sieve (X.p.obj y)) (k.left ≫ f)
      exact hbase
    exact
      (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 (X.p.obj x)))
        ((((J.pullback f).obj
          (ordinaryHomToRepresentativeOver (J := J) X (𝟙 y)).baseCover) :
          Sieve (X.p.obj x))) k).2 hpull)

end LocallyDefinedHomRepresentativeOver

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: an ordinary morphism as a raw
locally-defined morphism representative. -/
noncomputable def ordinaryHomToRepresentative
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    LocallyDefinedHomRepresentative (J := J) X x y where
  base := X.p.map a
  representative := ordinaryHomToRepresentativeOver (J := J) X a

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: the map on morphisms for the canonical
functor from the old fibred category to the locally-defined-Hom surface.  It is the source proof's
`G²(a) = (p(a), {id}, a)`, first built as a raw representative and then sent to the concrete
plus construction. -/
noncomputable def ordinaryHomToLocallyDefinedHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    locallyDefinedHom (J := J) X x y :=
  (ordinaryHomToRepresentative (J := J) X a).toLocallyDefinedHom

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.5: the base arrow of the locally-defined
morphism associated to an ordinary morphism is the original projected base arrow. -/
@[simp]
theorem ordinaryHomToLocallyDefinedHom_base
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    (ordinaryHomToLocallyDefinedHom (J := J) X a).1 = X.p.map a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The raw representative of an ordinary morphism presents the same plus-section as
`ordinaryHomToLocallyDefinedHom`. -/
theorem ordinaryHomToRepresentative_toLocallyDefinedHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S} (a : x ⟶ y) :
    (ordinaryHomToRepresentative (J := J) X a).toLocallyDefinedHom =
      ordinaryHomToLocallyDefinedHom (J := J) X a := by
  rfl

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.4: the locally-defined identity morphism,
represented by the ordinary identity through `ordinaryHomToLocallyDefinedHom`. -/
noncomputable def locallyDefinedHomId
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    locallyDefinedHom (J := J) X x x :=
  ordinaryHomToLocallyDefinedHom (J := J) X (𝟙 x)

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.4: the locally-defined identity lies over the
identity base morphism. -/
@[simp]
theorem locallyDefinedHomId_base
    (X : FibredCategoryOver.{u, v, uX, vX} C) (x : X.S) :
    (locallyDefinedHomId (J := J) X x).1 = 𝟙 (X.p.obj x) := by
  simp [locallyDefinedHomId]

namespace LocallyDefinedHom

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.4: choose a raw representative for a
plus-packaged locally-defined morphism.  This is only a representative-choice bridge; the
source-faithful category laws still require proving that the composite below is independent of
representatives. -/
noncomputable def chooseRepresentative
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y) :
    LocallyDefinedHomRepresentative (J := J) X x y :=
  Classical.choose
    (LocallyDefinedHomRepresentative.toLocallyDefinedHom_surjective
      (J := J) (X := X) (x := x) (y := y) a)

/-- The chosen raw representative presents the original plus-packaged locally-defined morphism. -/
theorem chooseRepresentative_spec
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y) :
    (chooseRepresentative (J := J) a).toLocallyDefinedHom = a :=
  Classical.choose_spec
    (LocallyDefinedHomRepresentative.toLocallyDefinedHom_surjective
      (J := J) (X := X) (x := x) (y := y) a)

/-- The chosen representative has the same displayed base arrow as the plus-packaged morphism. -/
theorem chooseRepresentative_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y) :
    (chooseRepresentative (J := J) a).base = a.1 := by
  simpa [LocallyDefinedHomRepresentative.toLocallyDefinedHom] using
    congrArg Sigma.fst (chooseRepresentative_spec (J := J) a)

/-- Helper for Chap08 Lemma 8 8 1, source stage 2.4: compose plus-packaged locally-defined
morphisms by choosing raw representatives and composing them on the source-text cover
`U_i ×_V V_j`.  The next proof obligation is the representative-independence theorem identifying
this with any other choice. -/
noncomputable def comp
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (b : locallyDefinedHom (J := J) X y z) :
    locallyDefinedHom (J := J) X x z :=
  (LocallyDefinedHomRepresentative.compose
    (J := J) (chooseRepresentative (J := J) a)
    (chooseRepresentative (J := J) b)).toLocallyDefinedHom

/-- The base arrow of the locally-defined composite is the composite of the base arrows. -/
@[simp]
theorem comp_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (b : locallyDefinedHom (J := J) X y z) :
    (comp (J := J) a b).1 = a.1 ≫ b.1 := by
  dsimp [comp, LocallyDefinedHomRepresentative.toLocallyDefinedHom]
  rw [chooseRepresentative_base (J := J) a, chooseRepresentative_base (J := J) b]

/-- The chosen-representative definition of composition agrees with composing any chosen raw
representatives of the two plus-packaged locally-defined morphisms.  This is the quotient bridge
used to reduce later identity and associativity checks to explicit common-refinement proofs. -/
theorem comp_eq_of_representatives
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (a : locallyDefinedHom (J := J) X x y)
    (b : locallyDefinedHom (J := J) X y z)
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z)
    (hα : α.toLocallyDefinedHom = a)
    (hβ : β.toLocallyDefinedHom = b) :
    comp (J := J) a b =
      (LocallyDefinedHomRepresentative.compose (J := J) α β).toLocallyDefinedHom := by
  dsimp [comp]
  exact LocallyDefinedHomRepresentative.compose_respects_equivalent (J := J)
    ((chooseRepresentative_spec (J := J) a).trans hα.symm)
    ((chooseRepresentative_spec (J := J) b).trans hβ.symm)

/-- Special case of `comp_eq_of_representatives` when the two inputs are already presented by
raw representatives. -/
theorem comp_toLocallyDefinedHom
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y z : X.S}
    (α : LocallyDefinedHomRepresentative (J := J) X x y)
    (β : LocallyDefinedHomRepresentative (J := J) X y z) :
    comp (J := J) α.toLocallyDefinedHom β.toLocallyDefinedHom =
      (LocallyDefinedHomRepresentative.compose (J := J) α β).toLocallyDefinedHom :=
  comp_eq_of_representatives (J := J)
    α.toLocallyDefinedHom β.toLocallyDefinedHom α β rfl rfl

/-- Base-arrow form of the left identity law for locally-defined composition. -/
theorem id_comp_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y) :
    (comp (J := J) (locallyDefinedHomId (J := J) X x) a).1 = a.1 := by
  simp

/-- Base-arrow form of the right identity law for locally-defined composition. -/
theorem comp_id_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {x y : X.S}
    (a : locallyDefinedHom (J := J) X x y) :
    (comp (J := J) a (locallyDefinedHomId (J := J) X y)).1 = a.1 := by
  simp

/-- Base-arrow form of associativity for locally-defined composition. -/
theorem assoc_base
    {X : FibredCategoryOver.{u, v, uX, vX} C} {w x y z : X.S}
    (a : locallyDefinedHom (J := J) X w x)
    (b : locallyDefinedHom (J := J) X x y)
    (c : locallyDefinedHom (J := J) X y z) :
    (comp (J := J) (comp (J := J) a b) c).1 =
      (comp (J := J) a (comp (J := J) b c)).1 := by
  calc
    (comp (J := J) (comp (J := J) a b) c).1 = (a.1 ≫ b.1) ≫ c.1 := by
      rw [comp_base, comp_base]
    _ = a.1 ≫ b.1 ≫ c.1 := by
      rw [Category.assoc]
    _ = (comp (J := J) a (comp (J := J) b c)).1 := by
      rw [comp_base, comp_base]

end LocallyDefinedHom

/-- Helper for Chap08 Lemma 8 8 1, source stage 2: for a fixed base arrow, the canonical map from
local representatives to their plus construction is a local isomorphism in the source slice site.
This is the arbitrary-base-arrow analogue of
`localEqualityQuotient_saturatedPresheafHom_toPlus_W`. -/
theorem locallyDefinedHomSaturatedPresheaf_toPlus_W
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y) :
    (J.over (X.p.obj x)).W
      ((J.over (X.p.obj x)).toPlus (locallyDefinedHomSaturatedPresheaf X f)) := by
  let P := locallyDefinedHomSaturatedPresheaf X f
  haveI : (J.over (X.p.obj x)).WEqualsLocallyBijective (Type (max vX (max u v))) :=
    @CategoryTheory.Functor.large_type_WEqualsLocallyBijective.{max u v, v, vX}
      (Over (X.p.obj x)) inferInstance (J.over (X.p.obj x)) inferInstance
  haveI : Presheaf.IsLocallyInjective (J.over (X.p.obj x))
      ((J.over (X.p.obj x)).toPlus P) :=
    CategoryTheory.Functor.toPlus_isLocallyInjective_type (L := J.over (X.p.obj x)) P
  haveI : Presheaf.IsLocallySurjective (J.over (X.p.obj x))
      ((J.over (X.p.obj x)).toPlus P) :=
    CategoryTheory.Functor.toPlus_isLocallySurjective_type (L := J.over (X.p.obj x)) P
  exact GrothendieckTopology.W_of_isLocallyBijective (J.over (X.p.obj x))
    ((J.over (X.p.obj x)).toPlus P)

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source stage 2: if the representative Hom presheaf for a
fixed base arrow is separated, its plus construction is a sheaf. -/
theorem locallyDefinedHomSaturatedPresheaf_plus_isSheaf_of_separated
    (X : FibredCategoryOver.{u, v, uX, vX} C) {x y : X.S}
    (f : X.p.obj x ⟶ X.p.obj y)
    (hsep : Presieve.IsSeparated (J.over (X.p.obj x))
      (locallyDefinedHomPresheaf X f)) :
    Presheaf.IsSheaf (J.over (X.p.obj x))
      ((J.over (X.p.obj x)).plusObj
        (locallyDefinedHomSaturatedPresheaf X f)) := by
  apply GrothendieckTopology.Plus.isSheaf_of_sep
  intro V S s t h
  apply ULift.ext
  exact Presieve.IsSeparatedFor.ext (hsep (S : Sieve V) S.condition) (by
    intro W g hg
    exact congrArg ULift.down (h ⟨W, g, hg⟩))

namespace LocalEqualityQuotientTotal

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source stage 2 after the first quotient: for every base arrow
between two total objects, the plus construction of the corresponding locally-defined-Hom
presheaf is already a sheaf.  This is the arbitrary-base-arrow version of the source proof's
statement that the second stage sheafifies separated morphism presheaves. -/
theorem localEqualityQuotient_locallyDefinedHom_plus_isSheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C)
    {x y : LocalEqualityQuotientTotal (J := J) X}
    (f : (projection (J := J) X).obj x ⟶ (projection (J := J) X).obj y) :
    Presheaf.IsSheaf (J.over ((projection (J := J) X).obj x))
      ((J.over ((projection (J := J) X).obj x)).plusObj
        (locallyDefinedHomSaturatedPresheaf
          (FibredCategoryOver.ofFunctor (projection (J := J) X)) f)) := by
  apply GrothendieckTopology.Plus.isSheaf_of_sep
  intro V S s t h
  apply ULift.ext
  let F := canonicalFiberPseudofunctor (projection (J := J) X)
  let xF : (projection (J := J) X).Fiber ((projection (J := J) X).obj x) :=
    Functor.Fiber.mk (p := projection (J := J) X) (a := x) rfl
  let yF : (projection (J := J) X).Fiber ((projection (J := J) X).obj y) :=
    Functor.Fiber.mk (p := projection (J := J) X) (a := y) rfl
  exact Presieve.IsSeparatedFor.ext
    (localEqualityQuotient_presheafHom_isSeparated
      (J := J) X xF ((F.map f.op.toLoc).toFunctor.obj yF)
      (S : Sieve V) S.condition)
    (by
      intro W g hg
      exact congrArg ULift.down (h ⟨W, g, hg⟩))

/-- Helper for Chap08 Lemma 8 8 1: the first local-equality quotient as a fibred category. -/
abbrev fibredCategory (X : FibredCategoryOver C) : FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor (projection (J := J) X)

/-- Helper for Chap08 Lemma 8 8 1: the functor from the original total category to the first
quotient total category. -/
def toQuotientFunctor (X : FibredCategoryOver C) :
    X.S ⥤ LocalEqualityQuotientTotal (J := J) X where
  obj x := ofObj J X x
  map {x y} f := homMk J X f
  map_id x := by simp
  map_comp f g := by simp

/-- Helper for Chap08 Lemma 8 8 1: the first quotient functor as a based functor over the site
base. -/
def toQuotientBasedFunctor (X : FibredCategoryOver C) :
    X.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor (projection (J := J) X) where
  toFunctor := toQuotientFunctor (J := J) X
  w := by
    rfl

/-- Helper for Chap08 Lemma 8 8 1: the quotient functor preserves strongly cartesian arrows.
This is source step 1.5 packaged as a based-functor property. -/
theorem toQuotientBasedFunctor_preservesStronglyCartesian
    (X : FibredCategoryOver C) :
    (toQuotientBasedFunctor (J := J) X).PreservesStronglyCartesian := by
  intro x y φ hφ
  simpa using homMk_isStronglyCartesian (J := J) X φ hφ

/-- Helper for Chap08 Lemma 8 8 1: local equality of source morphisms becomes literal equality
after applying the quotient functor. -/
theorem toQuotientFunctor_map_eq_of_locallyEqual
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) :
    (toQuotientFunctor (J := J) X).map f =
      (toQuotientFunctor (J := J) X).map g :=
  (homMk_eq_iff_locallyEqual (J := J) X).2 h

/-- Helper for Chap08 Lemma 8 8 1: the canonical morphism from a fibred category to its first
local-equality quotient. -/
abbrev toFibredCategory (X : FibredCategoryOver C) :
    X ⟶ fibredCategory (J := J) X :=
  FibredCategoryMor.ofBasedFunctor
    (toQuotientBasedFunctor (J := J) X)
    (toQuotientBasedFunctor_preservesStronglyCartesian (J := J) X)

/-- Helper for Chap08 Lemma 8 8 1: the quotient functor is locally essentially surjective on
objects.  Objects are unchanged, but the proof is phrased using the canonical pullback choice of
the quotient fibred category, so it works with the owner-level definition rather than a chosen
strict pullback model. -/
theorem toQuotient_locallyEssentiallySurjectiveOnObjects
    (X : FibredCategoryOver.{u, v, uX, vX} C) :
    FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J
      (toFibredCategory (J := J) X) := by
  intro U y
  refine ⟨⊤, ?_⟩
  intro I
  let yI := I.f ^*[canonicalPullbackChoice (projection (J := J) X)] y
  refine ⟨⟨yI.1.obj, yI.2⟩, ?_⟩
  change Nonempty (((toFibredCategory (J := J) X).toHom.fiberFunctor I.Y).obj
    ⟨yI.1.obj, yI.2⟩ ≅ yI)
  cases yI with
  | mk obj h =>
    cases obj
    exact ⟨Iso.refl _⟩

end LocalEqualityQuotientTotal
end FibredCategoryMor

end CategoryTheory
