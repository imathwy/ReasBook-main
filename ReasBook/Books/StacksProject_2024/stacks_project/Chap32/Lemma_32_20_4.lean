import StacksProject_2024.stacks_project.Chap32.Lemma_32_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` confirmed the canonical scheme-morphism owners
-- `IsSeparated`, `IsProper`, `IsFinite`, and `Etale`. Local Section 32.20 precedent supplies
-- `FinitePresentationOver`, `finitePresentationStalkGluingCategory`, and base change through
-- `FinitePresentationOver.baseChange`.

namespace FinitePresentationOver

/-- The concrete `Over`-object obtained by base changing a finite-presentation object. -/
abbrev baseChangeOverObject {T T' : Scheme.{u}} (f : T' ⟶ T)
    (X : FinitePresentationOver T) : Over T' :=
  (Over.pullback f).obj X.obj

/-- The concrete `Over`-morphism obtained by base changing a morphism between
finite-presentation objects. -/
abbrev baseChangeOverHom {T T' : Scheme.{u}} (f : T' ⟶ T)
    {X Y : FinitePresentationOver T} (a : X ⟶ Y) :
    baseChangeOverObject f X ⟶ baseChangeOverObject f Y :=
  (Over.pullback f).map ((inclusion T).map a)

/-- Restrict a finite-presentation object over an open subscheme to a smaller open, retaining
only the concrete `Over`-object. -/
abbrev restrictOverObject {S : Scheme.{u}} {W U' : S.Opens}
    (hWU' : W ≤ U') (X : FinitePresentationOver U'.toScheme) : Over W.toScheme :=
  baseChangeOverObject (S.homOfLE hWU') X

/-- Restrict a morphism between finite-presentation objects over an open subscheme to a smaller
open, retaining only the concrete `Over`-morphism. -/
abbrev restrictOverHom {S : Scheme.{u}} {W U' : S.Opens}
    (hWU' : W ≤ U') {X Y : FinitePresentationOver U'.toScheme} (a : X ⟶ Y) :
    restrictOverObject hWU' X ⟶ restrictOverObject hWU' Y :=
  baseChangeOverHom (S.homOfLE hWU') a

/-- The underlying morphism of schemes associated to a morphism in a finite-presentation
over-category. -/
abbrev underlyingHom {T : Scheme.{u}} {X Y : FinitePresentationOver T} (a : X ⟶ Y) :
    X.obj.left ⟶ Y.obj.left :=
  ((inclusion T).map a).left

end FinitePresentationOver

/-- Lemma 32.20.4 (1): if the two components corresponding to a finitely presented morphism
`f'` over an open neighbourhood `U'` are separated, then after shrinking `U'` around `s` and still
containing `U`, the restriction of `f'` is separated. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isSeparated_of_gluingObject_isSeparated
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty (FinitePresentationOver.baseChangeOverObject toU' X' ≅ G.snd.obj))
    (hopen : IsSeparated (Comma.hom G.fst.obj))
    (hstalk : IsSeparated (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- Lemma 32.20.4 (2): if the two components corresponding to a finitely presented morphism
`f'` over an open neighbourhood `U'` are proper, then after shrinking `U'` around `s` and still
containing `U`, the restriction of `f'` is proper. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isProper_of_gluingObject_isProper
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty (FinitePresentationOver.baseChangeOverObject toU' X' ≅ G.snd.obj))
    (hopen : IsProper (Comma.hom G.fst.obj))
    (hstalk : IsProper (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- Lemma 32.20.4 (3): if the two components corresponding to a finitely presented morphism
`f'` over an open neighbourhood `U'` are finite, then after shrinking `U'` around `s` and still
containing `U`, the restriction of `f'` is finite. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isFinite_of_gluingObject_isFinite
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty (FinitePresentationOver.baseChangeOverObject toU' X' ≅ G.snd.obj))
    (hopen : IsFinite (Comma.hom G.fst.obj))
    (hstalk : IsFinite (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- Lemma 32.20.4 (4): if the two components corresponding to a finitely presented morphism
`f'` over an open neighbourhood `U'` are étale, then after shrinking `U'` around `s` and still
containing `U`, the restriction of `f'` is étale. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_etale_of_gluingObject_etale
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    (X' : FinitePresentationOver U'.toScheme)
    (G : finitePresentationStalkGluingCategory S U s)
    (hOpenIso : Nonempty (FinitePresentationOver.restrictOverObject hUU' X' ≅ G.fst.obj))
    (hStalkIso : Nonempty (FinitePresentationOver.baseChangeOverObject toU' X' ≅ G.snd.obj))
    (hopen : Etale (Comma.hom G.fst.obj))
    (hstalk : Etale (Comma.hom G.snd.obj)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale (FinitePresentationOver.restrictOverObject hWU' X').hom := sorry

/-- Lemma 32.20.4 (5): if the two component morphisms corresponding to a morphism `a` over an
open neighbourhood `U'` are separated, then after shrinking `U'` around `s` and still containing
`U`, the restriction of `a` is separated. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isSeparated_of_gluingMorphism_isSeparated
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃ (e₁ : FinitePresentationOver.baseChangeOverObject toU' X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject toU' X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom toU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsSeparated (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsSeparated (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsSeparated
          (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- Lemma 32.20.4 (6): if the two component morphisms corresponding to a morphism `a` over an
open neighbourhood `U'` are proper, then after shrinking `U'` around `s` and still containing
`U`, the restriction of `a` is proper. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isProper_of_gluingMorphism_isProper
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃ (e₁ : FinitePresentationOver.baseChangeOverObject toU' X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject toU' X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom toU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsProper (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsProper (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsProper
          (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- Lemma 32.20.4 (7): if the two component morphisms corresponding to a morphism `a` over an
open neighbourhood `U'` are finite, then after shrinking `U'` around `s` and still containing
`U`, the restriction of `a` is finite. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_isFinite_of_gluingMorphism_isFinite
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃ (e₁ : FinitePresentationOver.baseChangeOverObject toU' X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject toU' X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom toU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : IsFinite (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : IsFinite (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        IsFinite
          (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

/-- Lemma 32.20.4 (8): if the two component morphisms corresponding to a morphism `a` over an
open neighbourhood `U'` are étale, then after shrinking `U'` around `s` and still containing
`U`, the restriction of `a` is étale. -/
@[stacks 0EY3]
theorem existsOpenNeighborhood_etale_of_gluingMorphism_etale
    (S : Scheme.{u}) (U U' : S.Opens) [QuasiCompact U.ι]
    (s : S) (hsU : s ∉ (U : Set S)) (hUU' : U ≤ U') (hsU' : s ∈ (U' : Set S))
    (toU' : Spec (S.presheaf.stalk s) ⟶ U'.toScheme)
    (htoU' : toU' ≫ U'.ι = S.fromSpecStalk s)
    {X₁ X₂ : FinitePresentationOver U'.toScheme} (a : X₁ ⟶ X₂)
    {G₁ G₂ : finitePresentationStalkGluingCategory S U s} (α : G₁ ⟶ G₂)
    (hOpenComm : ∃ (e₁ : FinitePresentationOver.restrictOverObject hUU' X₁ ≅ G₁.fst.obj)
        (e₂ : FinitePresentationOver.restrictOverObject hUU' X₂ ≅ G₂.fst.obj),
      FinitePresentationOver.restrictOverHom hUU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion U.toScheme).map α.fst ≫ e₂.inv)
    (hStalkComm : ∃ (e₁ : FinitePresentationOver.baseChangeOverObject toU' X₁ ≅ G₁.snd.obj)
        (e₂ : FinitePresentationOver.baseChangeOverObject toU' X₂ ≅ G₂.snd.obj),
      FinitePresentationOver.baseChangeOverHom toU' a =
        e₁.hom ≫ (FinitePresentationOver.inclusion (Spec (S.presheaf.stalk s))).map α.snd ≫
          e₂.inv)
    (hopen : Etale (FinitePresentationOver.underlyingHom α.fst))
    (hstalk : Etale (FinitePresentationOver.underlyingHom α.snd)) :
    ∃ (W : S.Opens) (hUW : U ≤ W) (hWU' : W ≤ U'),
      s ∈ (W : Set S) ∧
        Etale
          (FinitePresentationOver.restrictOverHom hWU' a).left := sorry

end AlgebraicGeometry
