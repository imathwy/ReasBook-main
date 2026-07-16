import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.SharedCore

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

/-- Helper for Chap08 Lemma 8 8 1: two total-category morphisms with the same source and target
are locally equal when they have the same base arrow and become equal after precomposition with a
cover of the source by the chosen cartesian pullback arrows. This is the source-text relation
used in the first quotient stage. -/
def locallyEqual (X : FibredCategoryOver C) {x y : X.S} (f g : x ⟶ y) : Prop :=
  X.p.map f = X.p.map g ∧
    ∃ S : J.Cover (X.p.obj x),
      ∀ I : S.Arrow,
        (canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f =
          (canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g

/-- Helper for Chap08 Lemma 8 8 1: the sieve of arrows on the source over which two morphisms
become strictly equal after precomposition by the chosen cartesian pullback arrow.  This packages
the source proof's repeated "after refining the cover" argument into a genuine sieve. -/
def equalRestrictionSieve (X : FibredCategoryOver C) {x y : X.S} (f g : x ⟶ y) :
    Sieve (X.p.obj x) where
  arrows Y u :=
    (canonicalPullbackChoice X.p).map u
          (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f =
      (canonicalPullbackChoice X.p).map u
          (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g
  downward_closed := by
    intro Y Z u hu v
    let hc := canonicalPullbackChoice X.p
    let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
    have hfac :
        (hc.pullbackCompComponentIso u v xF).hom.1 ≫
            hc.map v (hc.obj u xF) ≫ hc.map u xF =
          hc.map (v ≫ u) xF := by
      simpa using hc.pullbackCompComponentIso_fac u v xF
    calc
      hc.map (v ≫ u) xF ≫ f
          = ((hc.pullbackCompComponentIso u v xF).hom.1 ≫
                hc.map v (hc.obj u xF) ≫ hc.map u xF) ≫ f := by
              rw [hfac]
      _ = (hc.pullbackCompComponentIso u v xF).hom.1 ≫
            hc.map v (hc.obj u xF) ≫ (hc.map u xF ≫ f) := by
              simp [Category.assoc]
      _ = (hc.pullbackCompComponentIso u v xF).hom.1 ≫
            hc.map v (hc.obj u xF) ≫ (hc.map u xF ≫ g) := by
              rw [hu]
      _ = ((hc.pullbackCompComponentIso u v xF).hom.1 ≫
                hc.map v (hc.obj u xF) ≫ hc.map u xF) ≫ g := by
              simp [Category.assoc]
      _ = hc.map (v ≫ u) xF ≫ g := by
              rw [hfac]

/-- Helper for Chap08 Lemma 8 8 1: local equality is equivalent to equality of base arrows plus
the covering property of the strict-equality restriction sieve. -/
theorem locallyEqual_iff_equalRestrictionSieve_mem
    (X : FibredCategoryOver C) {x y : X.S} (f g : x ⟶ y) :
    locallyEqual (J := J) X f g ↔
      X.p.map f = X.p.map g ∧ equalRestrictionSieve X f g ∈ J (X.p.obj x) := by
  constructor
  · rintro ⟨hbase, S, hS⟩
    refine ⟨hbase, J.superset_covering ?_ S.condition⟩
    intro Y u hu
    exact hS ⟨Y, u, hu⟩
  · rintro ⟨hbase, hcover⟩
    refine ⟨hbase, ⟨equalRestrictionSieve X f g, hcover⟩, ?_⟩
    intro I
    exact I.hf

/-- Helper for Chap08 Lemma 8 8 1: local equality is reflexive. -/
theorem locallyEqual_refl (X : FibredCategoryOver C) {x y : X.S} (f : x ⟶ y) :
    locallyEqual (J := J) X f f := by
  refine ⟨rfl, ⊤, ?_⟩
  intro I
  rfl

/-- Helper for Chap08 Lemma 8 8 1: local equality is symmetric. -/
theorem locallyEqual_symm
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) :
    locallyEqual (J := J) X g f := by
  rcases h with ⟨hbase, S, hS⟩
  refine ⟨hbase.symm, S, ?_⟩
  intro I
  exact (hS I).symm

/-- Helper for Chap08 Lemma 8 8 1: local equality is transitive, after refining the two covers by
their intersection. -/
theorem locallyEqual_trans
    (X : FibredCategoryOver C) {x y : X.S} {f g h : x ⟶ y}
    (hfg : locallyEqual (J := J) X f g)
    (hgh : locallyEqual (J := J) X g h) :
    locallyEqual (J := J) X f h := by
  rcases hfg with ⟨hbasefg, Sfg, hSfg⟩
  rcases hgh with ⟨hbasegh, Sgh, hSgh⟩
  refine ⟨hbasefg.trans hbasegh, Sfg ⊓ Sgh, ?_⟩
  intro I
  let Ifg : Sfg.Arrow := ⟨I.Y, I.f, I.hf.1⟩
  let Igh : Sgh.Arrow := ⟨I.Y, I.f, I.hf.2⟩
  exact (hSfg Ifg).trans (hSgh Igh)

/-- Helper for Chap08 Lemma 8 8 1: local equality defines the setoid on each Hom type used by
the first quotient stage. -/
def localEqualitySetoid (X : FibredCategoryOver C) (x y : X.S) : Setoid (x ⟶ y) where
  r := locallyEqual (J := J) X
  iseqv := ⟨locallyEqual_refl (J := J) X, locallyEqual_symm (J := J) X,
    locallyEqual_trans (J := J) X⟩

/-- Helper for Chap08 Lemma 8 8 1: local equality is stable under postcomposition.  This is the
easy half of the source-text assertion that `b ∼ b'` implies
`a ∘ b ∘ c ∼ a ∘ b' ∘ c`. -/
theorem locallyEqual_comp_right
    (X : FibredCategoryOver C) {x y z : X.S} {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) (a : y ⟶ z) :
    locallyEqual (J := J) X (f ≫ a) (g ≫ a) := by
  rcases h with ⟨hbase, S, hS⟩
  refine ⟨?_, S, ?_⟩
  · simp [Functor.map_comp, hbase]
  · intro I
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ a) (hS I)

/-- Helper for Chap08 Lemma 8 8 1: local equality is stable under precomposition.  The proof
pulls the witnessing cover back along the base map of the precomposing arrow, then factors through
the chosen cartesian pullback of the original source object. -/
theorem locallyEqual_comp_left
    (X : FibredCategoryOver C) {w x y : X.S} (a : w ⟶ x) {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) :
    locallyEqual (J := J) X (a ≫ f) (a ≫ g) := by
  rcases h with ⟨hbase, S, hS⟩
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let wF : X.p.Fiber (X.p.obj w) := Functor.Fiber.mk (p := X.p) (a := w) rfl
  refine ⟨?_, S.pullback (X.p.map a), ?_⟩
  · simp [Functor.map_comp, hbase]
  · intro I
    let φ : (hc.obj I.f wF).1 ⟶ x := hc.map I.f wF ≫ a
    have hφLift : X.p.IsHomLift (I.f ≫ X.p.map a) φ := by
      exact
        @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ I.f (X.p.map a)
          (hc.map I.f wF) a
          ((hc.isStronglyCartesian I.f wF).toIsHomLift)
          (IsHomLift.map X.p a)
    let ψ : (hc.obj (I.f ≫ X.p.map a) xF).1 ⟶ x :=
      hc.map (I.f ≫ X.p.map a) xF
    have hψStrong : X.p.IsStronglyCartesian (I.f ≫ X.p.map a) ψ :=
      hc.isStronglyCartesian (I.f ≫ X.p.map a) xF
    letI : X.p.IsHomLift (I.f ≫ X.p.map a) φ := hφLift
    letI : X.p.IsStronglyCartesian (I.f ≫ X.p.map a) ψ := hψStrong
    obtain ⟨χ, hχ, _⟩ :=
      Functor.IsStronglyCartesian.universal_property X.p (I.f ≫ X.p.map a) ψ
        (𝟙 I.Y) (I.f ≫ X.p.map a) (by simp) φ
    have hχfac : χ ≫ ψ = φ := hχ.2
    have hlocal := hS (GrothendieckTopology.Cover.Arrow.base I)
    calc
      hc.map I.f wF ≫ (a ≫ f)
          = (hc.map I.f wF ≫ a) ≫ f := by simp [Category.assoc]
      _ = (χ ≫ ψ) ≫ f := by rw [hχfac]
      _ = χ ≫ (ψ ≫ f) := by simp [Category.assoc]
      _ = χ ≫ (ψ ≫ g) := by
            exact congrArg (fun k ↦ χ ≫ k) hlocal
      _ = (χ ≫ ψ) ≫ g := by simp [Category.assoc]
      _ = (hc.map I.f wF ≫ a) ≫ g := by rw [hχfac]
      _ = hc.map I.f wF ≫ (a ≫ g) := by simp [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 1: the full compatibility with two-sided composition used to
define composition on the first quotient category. -/
theorem locallyEqual_comp
    (X : FibredCategoryOver C) {w x y z : X.S} (c : w ⟶ x) {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) (a : y ⟶ z) :
    locallyEqual (J := J) X ((c ≫ f) ≫ a) ((c ≫ g) ≫ a) :=
  locallyEqual_comp_right (J := J) X (locallyEqual_comp_left (J := J) X c h) a

/-- Helper for Chap08 Lemma 8 8 1: local equality can be cancelled after postcomposition with a
strongly cartesian morphism, provided the two arrows have the same base map.  This is the source
proof's injectivity argument for cartesian arrows in the first quotient category. -/
theorem locallyEqual_of_comp_right_stronglyCartesian
    (X : FibredCategoryOver C) {z x y : X.S} {φ : x ⟶ y}
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) {f g : z ⟶ x}
    (hbase : X.p.map f = X.p.map g)
    (hcomp : locallyEqual (J := J) X (f ≫ φ) (g ≫ φ)) :
    locallyEqual (J := J) X f g := by
  rcases hcomp with ⟨_, S, hS⟩
  let hc := canonicalPullbackChoice X.p
  let zF : X.p.Fiber (X.p.obj z) := Functor.Fiber.mk (p := X.p) (a := z) rfl
  refine ⟨hbase, S, ?_⟩
  intro I
  let lf : (hc.obj I.f zF).1 ⟶ x := hc.map I.f zF ≫ f
  let lg : (hc.obj I.f zF).1 ⟶ x := hc.map I.f zF ≫ g
  have hlf : X.p.IsHomLift (I.f ≫ X.p.map f) lf := by
    exact
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ I.f (X.p.map f)
        (hc.map I.f zF) f
        ((hc.isStronglyCartesian I.f zF).toIsHomLift)
        (IsHomLift.map X.p f)
  have hglift : X.p.IsHomLift (X.p.map f) g := by
    rw [hbase]
    exact IsHomLift.map X.p g
  have hlg : X.p.IsHomLift (I.f ≫ X.p.map f) lg := by
    exact
      @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ I.f (X.p.map f)
        (hc.map I.f zF) g
        ((hc.isStronglyCartesian I.f zF).toIsHomLift)
        hglift
  letI : X.p.IsStronglyCartesian (X.p.map φ) φ := hφ
  letI : X.p.IsHomLift (I.f ≫ X.p.map f) lf := hlf
  letI : X.p.IsHomLift (I.f ≫ X.p.map f) lg := hlg
  change lf = lg
  apply IsStronglyCartesian.ext X.p (X.p.map φ) φ (I.f ≫ X.p.map f)
  dsimp [lf, lg]
  simpa [Category.assoc] using hS I

/-- Helper for Chap08 Lemma 8 8 1: a strongly cartesian structure can be rebased along another
base arrow lifted by the same total-category morphism.  This is the small owner/API bridge needed
because the source proof freely identifies the displayed base map of a lift with the actual
projection of the representing arrow. -/
theorem isStronglyCartesian_rebase_of_isHomLift
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    {R S₀ R' S₁ : C} {x y : S} {f : R ⟶ S₀} {f' : R' ⟶ S₁}
    {φ : x ⟶ y}
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsHomLift f' φ) :
    p.IsStronglyCartesian f' φ := by
  have hφLift : p.IsHomLift f φ := hφ.toIsHomLift
  have hdom : p.obj x = R := IsHomLift.domain_eq p f φ
  have hcod : p.obj y = S₀ := IsHomLift.codomain_eq p f φ
  have hdom' : p.obj x = R' := IsHomLift.domain_eq p f' φ
  have hcod' : p.obj y = S₁ := IsHomLift.codomain_eq p f' φ
  subst hdom
  subst hcod
  subst hdom'
  subst hcod'
  have hf : f = p.map φ :=
    @IsHomLift.eq_of_isHomLift C S _ _ p x y f φ hφLift
  have hf' : f' = p.map φ :=
    @IsHomLift.eq_of_isHomLift C S _ _ p x y f' φ hφ'
  subst hf
  subst hf'
  exact hφ

/-- Helper for Chap08 Lemma 8 8 1: the Hom type of the first-stage quotient category. -/
abbrev localEqualityQuotientHom (J : GrothendieckTopology C)
    (X : FibredCategoryOver C) (x y : X.S) :=
  _root_.Quotient (localEqualitySetoid (J := J) X x y)

/-- Helper for Chap08 Lemma 8 8 1: locally equal arrows have the same image in the first-stage
quotient Hom type. -/
theorem localEqualityQuotientHom_eq_of_locallyEqual
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (h : locallyEqual (J := J) X f g) :
    _root_.Quotient.mk (localEqualitySetoid (J := J) X x y) f =
      _root_.Quotient.mk (localEqualitySetoid (J := J) X x y) g :=
  _root_.Quotient.sound h

/-- Helper for Chap08 Lemma 8 8 1: equality in the first-stage quotient Hom type is exactly
local equality of representatives. -/
theorem locallyEqual_of_localEqualityQuotientHom_eq
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (h :
      _root_.Quotient.mk (localEqualitySetoid (J := J) X x y) f =
        _root_.Quotient.mk (localEqualitySetoid (J := J) X x y) g) :
    locallyEqual (J := J) X f g :=
  _root_.Quotient.exact h

/-- Helper for Chap08 Lemma 8 8 1: object wrapper for the first quotient category.  Objects are
unchanged, but a wrapper avoids changing the existing category structure on `X.S`. -/
structure LocalEqualityQuotientTotal (J : GrothendieckTopology C) (X : FibredCategoryOver C) where
  /-- The underlying object of the original total category. -/
  obj : X.S

namespace LocalEqualityQuotientTotal

instance (X : FibredCategoryOver C) : CoeOut (LocalEqualityQuotientTotal J X) X.S :=
  ⟨LocalEqualityQuotientTotal.obj⟩

/-- Helper for Chap08 Lemma 8 8 1: the image of an original object in the first quotient total
category. -/
abbrev ofObj (J : GrothendieckTopology C) (X : FibredCategoryOver C) (x : X.S) :
    LocalEqualityQuotientTotal J X :=
  ⟨x⟩

/-- Helper for Chap08 Lemma 8 8 1: the first quotient category.  Composition is induced from the
original total category using the two-sided compatibility of local equality with composition. -/
instance (X : FibredCategoryOver C) : Category (LocalEqualityQuotientTotal (J := J) X) where
  Hom x y := localEqualityQuotientHom J X x.obj y.obj
  id x := _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj x.obj) (𝟙 x.obj)
  comp {x y z} f g :=
    _root_.Quotient.liftOn₂ f g
      (fun f' g' =>
        _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj z.obj) (f' ≫ g'))
      (by
        intro f₁ g₁ f₂ g₂ hf hg
        change locallyEqual (J := J) X f₁ f₂ at hf
        change locallyEqual (J := J) X g₁ g₂ at hg
        apply _root_.Quotient.sound
        exact
          locallyEqual_trans (J := J) X
            (locallyEqual_comp_right (J := J) X hf g₁)
            (locallyEqual_comp_left (J := J) X f₂ hg))
  id_comp {x y} f := by
    refine _root_.Quotient.inductionOn f ?_
    intro f'
    change
      _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj y.obj) (𝟙 x.obj ≫ f') =
        _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj y.obj) f'
    simp
  comp_id {x y} f := by
    refine _root_.Quotient.inductionOn f ?_
    intro f'
    change
      _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj y.obj) (f' ≫ 𝟙 y.obj) =
        _root_.Quotient.mk (localEqualitySetoid (J := J) X x.obj y.obj) f'
    simp
  assoc {w x y z} f g h := by
    refine _root_.Quotient.inductionOn₃ f g h ?_
    intro f' g' h'
    change
      _root_.Quotient.mk (localEqualitySetoid (J := J) X w.obj z.obj) ((f' ≫ g') ≫ h') =
        _root_.Quotient.mk (localEqualitySetoid (J := J) X w.obj z.obj) (f' ≫ g' ≫ h')
    simp [Category.assoc]

/-- Helper for Chap08 Lemma 8 8 1: the projection functor of the first quotient category to the
base category. -/
def projection (X : FibredCategoryOver C) :
    LocalEqualityQuotientTotal (J := J) X ⥤ C where
  obj x := X.p.obj x.obj
  map {x y} f :=
    _root_.Quotient.liftOn f (fun f' => X.p.map f') (by
      intro f₁ f₂ h
      exact h.1)
  map_id x := by
    change X.p.map (𝟙 x.obj) = 𝟙 (X.p.obj x.obj)
    simp
  map_comp {x y z} f g := by
    refine _root_.Quotient.inductionOn₂ f g ?_
    intro f' g'
    change X.p.map (f' ≫ g') = X.p.map f' ≫ X.p.map g'
    simp [Functor.map_comp]

/-- Helper for Chap08 Lemma 8 8 1: the quotient class of an original morphism. -/
abbrev homMk (J : GrothendieckTopology C) (X : FibredCategoryOver C) {x y : X.S} (f : x ⟶ y) :
    ofObj J X x ⟶ ofObj J X y :=
  _root_.Quotient.mk (localEqualitySetoid (J := J) X x y) f

/-- Helper for Chap08 Lemma 8 8 1: the projection sends a quotient representative to the base
map of the representative. -/
@[simp]
theorem projection_map_homMk
    (X : FibredCategoryOver C) {x y : X.S} (f : x ⟶ y) :
    (projection (J := J) X).map (homMk J X f) = X.p.map f :=
  rfl

/-- Helper for Chap08 Lemma 8 8 1: quotient representatives compose as expected. -/
@[simp]
theorem homMk_comp
    (X : FibredCategoryOver C) {x y z : X.S} (f : x ⟶ y) (g : y ⟶ z) :
    homMk J X f ≫ homMk J X g =
      homMk J X (f ≫ g) :=
  rfl

/-- Helper for Chap08 Lemma 8 8 1: the identity in the quotient is represented by the original
identity. -/
@[simp]
theorem homMk_id (X : FibredCategoryOver C) (x : X.S) :
    homMk J X (𝟙 x) = 𝟙 (ofObj J X x) :=
  rfl

/-- Helper for Chap08 Lemma 8 8 1: equality of quotient representatives is local equality of the
original morphisms. -/
theorem homMk_eq_iff_locallyEqual
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y} :
    homMk J X f = homMk J X g ↔ locallyEqual (J := J) X f g :=
  ⟨fun h ↦ _root_.Quotient.exact h, fun h ↦ _root_.Quotient.sound h⟩

/-- Helper for Chap08 Lemma 8 8 1: equality in the first quotient can be checked by the
covering strict-equality restriction sieve.  This is the quotient-facing form of the source proof's
"locally equal iff equal after quotienting" bookkeeping. -/
theorem homMk_eq_iff_equalRestrictionSieve_mem
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y} :
    homMk J X f = homMk J X g ↔
      X.p.map f = X.p.map g ∧ equalRestrictionSieve X f g ∈ J (X.p.obj x) := by
  rw [homMk_eq_iff_locallyEqual, locallyEqual_iff_equalRestrictionSieve_mem]

/-- Helper for Chap08 Lemma 8 8 1: if the strict-equality restriction sieve covers, then the two
representatives define the same arrow in the first quotient. -/
theorem homMk_eq_of_equalRestrictionSieve_mem
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (hcover : equalRestrictionSieve X f g ∈ J (X.p.obj x)) :
    homMk J X f = homMk J X g :=
  (homMk_eq_iff_equalRestrictionSieve_mem (J := J) X).2 ⟨hbase, hcover⟩

/-- Helper for Chap08 Lemma 8 8 1, source step 1.7: if a cover of the source makes the chosen
pullback restrictions of two representatives equal in the first quotient, then the original
representatives are equal in the first quotient.  This is the first-stage separatedness argument:
the local quotient equalities provide covering strict-equality sieves, and transitivity of the
topology combines them into one cover of the original source. -/
theorem homMk_eq_of_cover_homMk_eq
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (S : J.Cover (X.p.obj x))
    (hS : ∀ I : S.Arrow,
      homMk J X
          ((canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f) =
        homMk J X
          ((canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g)) :
    homMk J X f = homMk J X g := by
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  refine homMk_eq_of_equalRestrictionSieve_mem (J := J) X hbase ?_
  let R := equalRestrictionSieve X f g
  change R ∈ J (X.p.obj x)
  refine J.transitive S.condition R ?_
  intro Y u hu
  let I : S.Arrow := ⟨Y, u, hu⟩
  have hIq :
      homMk J X (hc.map I.f xF ≫ f) =
        homMk J X (hc.map I.f xF ≫ g) := hS I
  have hIcover :
      equalRestrictionSieve X (hc.map I.f xF ≫ f) (hc.map I.f xF ≫ g) ∈
        J (X.p.obj (hc.obj I.f xF).1) :=
    ((homMk_eq_iff_equalRestrictionSieve_mem (J := J) X).1 hIq).2
  let e : X.p.obj (hc.obj I.f xF).1 = I.Y := (hc.obj I.f xF).2
  have hIpull :
      (equalRestrictionSieve X (hc.map I.f xF ≫ f) (hc.map I.f xF ≫ g)).pullback
          (eqToHom e.symm) ∈ J I.Y :=
    J.pullback_stable (eqToHom e.symm) hIcover
  refine J.superset_covering ?_ hIpull
  intro Z v hv
  change R (v ≫ I.f)
  dsimp [R, equalRestrictionSieve] at hv ⊢
  let sourceF : X.p.Fiber (X.p.obj (hc.obj I.f xF).1) :=
    Functor.Fiber.mk (p := X.p) (a := (hc.obj I.f xF).1) rfl
  let localMap : (hc.obj (v ≫ eqToHom e.symm) sourceF).1 ⟶ (hc.obj I.f xF).1 :=
    hc.map (v ≫ eqToHom e.symm) sourceF
  let iter : (hc.obj (v ≫ eqToHom e.symm) sourceF).1 ⟶ x :=
    localMap ≫ hc.map I.f xF
  have hlocal : iter ≫ f = iter ≫ g := by
    dsimp [iter, localMap]
    simpa [Category.assoc] using hv
  have hcartI :
      X.p.IsStronglyCartesian (eqToHom e ≫ I.f) (hc.map I.f xF) := by
    have hlift : X.p.IsHomLift (eqToHom e ≫ I.f) (hc.map I.f xF) := by
      subst e
      simpa using (hc.isStronglyCartesian I.f xF).toIsHomLift
    exact
      isStronglyCartesian_rebase_of_isHomLift X.p
        (hc.isStronglyCartesian I.f xF) hlift
  have hiterStrongRaw :
      X.p.IsStronglyCartesian
        ((v ≫ eqToHom e.symm) ≫ (eqToHom e ≫ I.f)) iter := by
    let gbase : X.p.obj (hc.obj I.f xF).1 ⟶ X.p.obj x := eqToHom e ≫ I.f
    letI : X.p.IsStronglyCartesian (v ≫ eqToHom e.symm) localMap :=
      hc.isStronglyCartesian (v ≫ eqToHom e.symm) sourceF
    letI : X.p.IsStronglyCartesian gbase (hc.map I.f xF) := hcartI
    have hcomp :
        X.p.IsStronglyCartesian
          ((v ≫ eqToHom e.symm) ≫ gbase) (localMap ≫ hc.map I.f xF) := by
      infer_instance
    simpa [iter, gbase] using hcomp
  have hiterStrong : X.p.IsStronglyCartesian (v ≫ I.f) iter := by
    simpa [Category.assoc] using hiterStrongRaw
  let chosen : (hc.obj (v ≫ I.f) xF).1 ⟶ x := hc.map (v ≫ I.f) xF
  have hchosenLift : X.p.IsHomLift (v ≫ I.f) chosen :=
    (hc.isStronglyCartesian (v ≫ I.f) xF).toIsHomLift
  letI : X.p.IsStronglyCartesian (v ≫ I.f) iter := hiterStrong
  letI : X.p.IsHomLift (v ≫ I.f) chosen := hchosenLift
  obtain ⟨χ, hχ, _⟩ :=
    Functor.IsStronglyCartesian.universal_property X.p (v ≫ I.f) iter
      (𝟙 Z) (v ≫ I.f) (by simp) chosen
  have hχfac : χ ≫ iter = chosen := hχ.2
  calc
    chosen ≫ f = (χ ≫ iter) ≫ f := by rw [hχfac]
    _ = χ ≫ (iter ≫ f) := by simp [Category.assoc]
    _ = χ ≫ (iter ≫ g) := by rw [hlocal]
    _ = (χ ≫ iter) ≫ g := by simp [Category.assoc]
    _ = chosen ≫ g := by rw [hχfac]

/-- Helper for Chap08 Lemma 8 8 1, source step 1.7 in relation form: local equality in the first
quotient descends from a cover of local quotient equalities. -/
theorem locallyEqual_of_cover_homMk_eq
    (X : FibredCategoryOver C) {x y : X.S} {f g : x ⟶ y}
    (hbase : X.p.map f = X.p.map g)
    (S : J.Cover (X.p.obj x))
    (hS : ∀ I : S.Arrow,
      homMk J X
          ((canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ f) =
        homMk J X
          ((canonicalPullbackChoice X.p).map I.f
              (Functor.Fiber.mk (p := X.p) (a := x) rfl) ≫ g)) :
    locallyEqual (J := J) X f g :=
  (homMk_eq_iff_locallyEqual (J := J) X).1
    (homMk_eq_of_cover_homMk_eq (J := J) X hbase S hS)

/-- Helper for Chap08 Lemma 8 8 1, source step 1.7 for arbitrary quotient morphisms: in the
first local-equality quotient category, equality can be checked after precomposition by a covering
family of chosen pullback arrows. -/
theorem eq_of_cover_comp_homMk_eq
    (X : FibredCategoryOver C) {x y : X.S}
    (a b : ofObj J X x ⟶ ofObj J X y)
    (hbase : (projection (J := J) X).map a = (projection (J := J) X).map b)
    (S : J.Cover (X.p.obj x))
    (hS : ∀ I : S.Arrow,
      homMk J X
          ((canonicalPullbackChoice X.p).map I.f
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ a =
        homMk J X
          ((canonicalPullbackChoice X.p).map I.f
            (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ b) :
    a = b := by
  refine
    _root_.Quotient.inductionOn₂
      (motive := fun a b =>
        (projection (J := J) X).map a = (projection (J := J) X).map b →
          (∀ I : S.Arrow,
            homMk J X
                ((canonicalPullbackChoice X.p).map I.f
                  (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ a =
              homMk J X
                ((canonicalPullbackChoice X.p).map I.f
                  (Functor.Fiber.mk (p := X.p) (a := x) rfl)) ≫ b) →
            a = b)
      a b ?_ hbase hS
  intro f g hbase hS
  change homMk J X f = homMk J X g
  have hbase' : X.p.map f = X.p.map g := hbase
  refine homMk_eq_of_cover_homMk_eq (J := J) X hbase' S ?_
  intro I
  simpa [homMk_comp] using hS I

/-- Helper for Chap08 Lemma 8 8 1: a representative of a strongly cartesian morphism remains
strongly cartesian in the first local-equality quotient category. -/
theorem homMk_isStronglyCartesian
    (X : FibredCategoryOver C) {x y : X.S} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian (X.p.map φ) φ) :
    (projection (J := J) X).IsStronglyCartesian (X.p.map φ) (homMk J X φ) := by
  refine { toIsHomLift := ?_, universal_property' := ?_ }
  · change (projection (J := J) X).IsHomLift
      ((projection (J := J) X).map (homMk J X φ)) (homMk J X φ)
    infer_instance
  · intro z g α hα
    refine
      _root_.Quotient.inductionOn
        (motive := fun α =>
          (projection (J := J) X).IsHomLift (g ≫ X.p.map φ) α →
            ∃! χ : z ⟶ ofObj J X x,
              (projection (J := J) X).IsHomLift g χ ∧ χ ≫ homMk J X φ = α)
        α ?_ hα
    intro α' hα
    have hαbase :
        g ≫ X.p.map φ = X.p.map α' := by
      let αq : z ⟶ ofObj J X y := homMk J X α'
      have hαq : (projection (J := J) X).IsHomLift (g ≫ X.p.map φ) αq := hα
      simpa [αq] using
        (@IsHomLift.eq_of_isHomLift C (LocalEqualityQuotientTotal J X) _ _
          (projection (J := J) X) z (ofObj J X y) (g ≫ X.p.map φ) αq hαq)
    have hαlift : X.p.IsHomLift (g ≫ X.p.map φ) α' := by
      rw [hαbase]
      exact IsHomLift.map X.p α'
    letI : X.p.IsStronglyCartesian (X.p.map φ) φ := hφ
    letI : X.p.IsHomLift (g ≫ X.p.map φ) α' := hαlift
    obtain ⟨β, hβ, hβuniq⟩ :=
      IsStronglyCartesian.universal_property X.p (X.p.map φ) φ
        g (g ≫ X.p.map φ) rfl α'
    refine ⟨homMk J X β, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hβbase : g = X.p.map β := by
          let βz : z.obj ⟶ x := β
          have hβz : X.p.IsHomLift g βz := hβ.1
          simpa [βz] using
            (@IsHomLift.eq_of_isHomLift C X.S _ _ X.p z.obj x g βz hβz)
        rw [hβbase]
        change (projection (J := J) X).IsHomLift
          ((projection (J := J) X).map (homMk J X β)) (homMk J X β)
        infer_instance
      · simp [homMk_comp, hβ.2]
    · intro χ hχ
      refine
        _root_.Quotient.inductionOn
          (motive := fun χ =>
            ((projection (J := J) X).IsHomLift g χ ∧
                χ ≫ homMk J X φ = homMk J X α') →
              χ = homMk J X β)
          χ ?_ hχ
      intro γ hχ
      change homMk J X γ = homMk J X β
      have hβbase : g = X.p.map β := by
        let βz : z.obj ⟶ x := β
        have hβz : X.p.IsHomLift g βz := hβ.1
        simpa [βz] using
          (@IsHomLift.eq_of_isHomLift C X.S _ _ X.p z.obj x g βz hβz)
      have hγbase : g = X.p.map γ := by
        let γq : z ⟶ ofObj J X x := homMk J X γ
        have hγq : (projection (J := J) X).IsHomLift g γq := hχ.1
        simpa [γq] using
          (@IsHomLift.eq_of_isHomLift C (LocalEqualityQuotientTotal J X) _ _
            (projection (J := J) X) z (ofObj J X x) g γq hγq)
      have hbaseγβ : X.p.map γ = X.p.map β :=
        hγbase.symm.trans hβbase
      have hcompγβ : locallyEqual (J := J) X (γ ≫ φ) (β ≫ φ) := by
        rw [← homMk_eq_iff_locallyEqual (J := J) X]
        simpa [homMk_comp, hβ.2] using hχ.2
      exact
        (homMk_eq_iff_locallyEqual (J := J) X).2
          (locallyEqual_of_comp_right_stronglyCartesian
            (J := J) X hφ hbaseγβ hcompγβ)

/-- Helper for Chap08 Lemma 8 8 1: the preceding representative result, stated with the external
base arrow of a hom-lift. -/
theorem homMk_isStronglyCartesian_of_isStronglyCartesian
    (X : FibredCategoryOver C) {R S : C} {x y : X.S} {f : R ⟶ S} (φ : x ⟶ y)
    (hφ : X.p.IsStronglyCartesian f φ) :
    (projection (J := J) X).IsStronglyCartesian f (homMk J X φ) := by
  have hφLift : X.p.IsHomLift f φ := hφ.toIsHomLift
  have hφMap : X.p.IsStronglyCartesian (X.p.map φ) φ :=
    isStronglyCartesian_rebase_of_isHomLift X.p hφ (IsHomLift.map X.p φ)
  have hqMap :
      (projection (J := J) X).IsStronglyCartesian
        ((projection (J := J) X).map (homMk J X φ)) (homMk J X φ) := by
    simpa using homMk_isStronglyCartesian (J := J) X φ hφMap
  have hqLift : (projection (J := J) X).IsHomLift f (homMk J X φ) := by
    refine IsHomLift.of_fac' (projection (J := J) X) f (homMk J X φ)
      (IsHomLift.domain_eq X.p f φ) (IsHomLift.codomain_eq X.p f φ) ?_
    simpa using IsHomLift.fac' X.p f φ
  exact isStronglyCartesian_rebase_of_isHomLift (projection (J := J) X) hqMap hqLift

/-- Helper for Chap08 Lemma 8 8 1, source step 1.7 with arbitrary cartesian local pullbacks:
the local arrows used to test equality in the first quotient may be any strongly cartesian lifts
over the covering arrows, not only the explicit representatives chosen from the original
fibred category. -/
theorem eq_of_cover_comp_stronglyCartesian_eq
    (X : FibredCategoryOver C) {x y : X.S}
    (a b : ofObj J X x ⟶ ofObj J X y)
    (hbase : (projection (J := J) X).map a = (projection (J := J) X).map b)
    (S : J.Cover (X.p.obj x))
    (z : S.Arrow → LocalEqualityQuotientTotal J X)
    (φ : ∀ I : S.Arrow, z I ⟶ ofObj J X x)
    (hφ : ∀ I : S.Arrow, (projection (J := J) X).IsStronglyCartesian I.f (φ I))
    (hS : ∀ I : S.Arrow, φ I ≫ a = φ I ≫ b) :
    a = b := by
  refine eq_of_cover_comp_homMk_eq (J := J) X a b hbase S ?_
  intro I
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber (X.p.obj x) := Functor.Fiber.mk (p := X.p) (a := x) rfl
  let ψ : ofObj J X (hc.obj I.f xF).1 ⟶ ofObj J X x :=
    homMk J X (hc.map I.f xF)
  have hψStrong :
      (projection (J := J) X).IsStronglyCartesian I.f ψ :=
    homMk_isStronglyCartesian_of_isStronglyCartesian
      (J := J) X (hc.map I.f xF) (hc.isStronglyCartesian I.f xF)
  letI : (projection (J := J) X).IsStronglyCartesian I.f (φ I) := hφ I
  letI : (projection (J := J) X).IsHomLift I.f ψ := hψStrong.toIsHomLift
  obtain ⟨χ, hχ, _⟩ :=
    Functor.IsStronglyCartesian.universal_property (projection (J := J) X) I.f (φ I)
      (𝟙 I.Y) I.f (by simp) ψ
  have hχfac : χ ≫ φ I = ψ := hχ.2
  calc
    ψ ≫ a = (χ ≫ φ I) ≫ a := by rw [hχfac]
    _ = χ ≫ (φ I ≫ a) := by simp [Category.assoc]
    _ = χ ≫ (φ I ≫ b) := by rw [hS I]
    _ = (χ ≫ φ I) ≫ b := by simp [Category.assoc]
    _ = ψ ≫ b := by rw [hχfac]

/-- Helper for Chap08 Lemma 8 8 1, source step 1.7 in standard-fiber form: two vertical
morphisms in a fiber of the first quotient are equal if a covering family of cartesian pullbacks
makes their ambient composites equal. -/
theorem fiberHom_eq_of_cover_comp_stronglyCartesian_eq
    (X : FibredCategoryOver C) {U : C}
    {x y : (projection (J := J) X).Fiber U}
    (a b : x ⟶ y)
    (S : J.Cover U)
    (z : S.Arrow → LocalEqualityQuotientTotal J X)
    (φ : ∀ I : S.Arrow, z I ⟶ x.1)
    (hφ : ∀ I : S.Arrow, (projection (J := J) X).IsStronglyCartesian I.f (φ I))
    (hS : ∀ I : S.Arrow, φ I ≫ a.1 = φ I ≫ b.1) :
    a = b := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  subst hx
  apply Functor.Fiber.hom_ext
  change a.1 = b.1
  haveI haLift : (projection (J := J) X).IsHomLift
      (𝟙 ((projection (J := J) X).obj x)) a.1 := a.2
  haveI hbLift : (projection (J := J) X).IsHomLift
      (𝟙 ((projection (J := J) X).obj x)) b.1 := b.2
  have ha :=
    IsHomLift.fac' (projection (J := J) X)
      (𝟙 ((projection (J := J) X).obj x)) a.1
  have hb :=
    IsHomLift.fac' (projection (J := J) X)
      (𝟙 ((projection (J := J) X).obj x)) b.1
  have hbase : (projection (J := J) X).map a.1 = (projection (J := J) X).map b.1 :=
    ha.trans hb.symm
  exact
    eq_of_cover_comp_stronglyCartesian_eq
      (J := J) X a.1 b.1 hbase S z φ hφ hS

/-- Helper for Chap08 Lemma 8 8 1: the first local-equality quotient projection is fibred.
This is source step 1.6. -/
instance projection_isFibered (X : FibredCategoryOver C) :
    (projection (J := J) X).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x R f
  let hc := canonicalPullbackChoice X.p
  let xF : X.p.Fiber ((projection (J := J) X).obj x) :=
    Functor.Fiber.mk (p := X.p) (a := x.obj) rfl
  let φ : (hc.obj f xF).1 ⟶ x.obj := hc.map f xF
  refine ⟨ofObj J X (hc.obj f xF).1, homMk J X φ, ?_⟩
  exact homMk_isStronglyCartesian_of_isStronglyCartesian
    (J := J) X φ (hc.isStronglyCartesian f xF)

/-- Helper for Chap08 Lemma 8 8 1: separatedness of the first quotient Hom presheaf at the
identity object of a slice site, stated as an extensionality lemma for a covering family. -/
theorem localEqualityQuotient_presheafHom_identity_ext
    (X : FibredCategoryOver C) {U : C}
    (x y : (projection (J := J) X).Fiber U)
    (S : J.Cover U)
    {s t :
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).obj
        (op (Over.mk (𝟙 U)))}
    (h : ∀ I : S.Arrow,
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map
          (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op s =
        ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map
          (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op t) :
    s = t := by
  let F := canonicalFiberPseudofunctor (projection (J := J) X)
  let e := F.presheafHomObjHomEquiv (M := x) (N := y)
  let a : x ⟶ y := e.symm s
  let b : x ⟶ y := e.symm t
  have ha : e a = s := Equiv.apply_symm_apply e s
  have hb : e b = t := Equiv.apply_symm_apply e t
  have hab : a = b := by
    let hcQ := canonicalPullbackChoice (projection (J := J) X)
    refine fiberHom_eq_of_cover_comp_stronglyCartesian_eq (J := J) X a b S
      (fun I ↦ (hcQ.obj (I.f ≫ 𝟙 U) x).1)
      (fun I ↦ hcQ.map (I.f ≫ 𝟙 U) x)
      ?_ ?_
    · intro I
      have hstrong :
          (projection (J := J) X).IsStronglyCartesian
            (I.f ≫ 𝟙 U) (hcQ.map (I.f ≫ 𝟙 U) x) :=
        hcQ.isStronglyCartesian (I.f ≫ 𝟙 U) x
      have hlift :
          (projection (J := J) X).IsHomLift I.f (hcQ.map (I.f ≫ 𝟙 U) x) := by
        simpa using hstrong.toIsHomLift
      exact isStronglyCartesian_rebase_of_isHomLift
        (projection (J := J) X) hstrong hlift
    · intro I
      have hI₀ :
          ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map
              (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op (e a) =
            ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map
              (Over.homMk I.f : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U)).op (e b) := by
        rw [ha, hb]
        exact h I
      have hI₁ :
          ((canonicalFiberPseudofunctor (projection (J := J) X)).map
              (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map a =
            ((canonicalFiberPseudofunctor (projection (J := J) X)).map
              (I.f ≫ 𝟙 U).op.toLoc).toFunctor.map b := by
        rw [← presheafHom_map_identitySlice_hom
              (p := projection (J := J) X) I.f x y a,
            ← presheafHom_map_identitySlice_hom
              (p := projection (J := J) X) I.f x y b]
        exact hI₀
      change
        hcQ.map (I.f ≫ 𝟙 U) x ≫ a.1 =
          hcQ.map (I.f ≫ 𝟙 U) x ≫ b.1
      have hmap :
          (hcQ.pullbackFunctor (I.f ≫ 𝟙 U)).map a =
            (hcQ.pullbackFunctor (I.f ≫ 𝟙 U)).map b := by
        simpa [F, canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor] using hI₁
      have hunder :=
        congrArg
          (fun k : (hcQ.pullbackFunctor (I.f ≫ 𝟙 U)).obj x ⟶
              (hcQ.pullbackFunctor (I.f ≫ 𝟙 U)).obj y =>
            k.1 ≫ hcQ.map (I.f ≫ 𝟙 U) y)
          hmap
      simpa [PullbackChoice.pullbackFunctor_map_fac] using hunder
  calc
    s = e a := ha.symm
    _ = e b := by rw [hab]
    _ = t := hb

/-- Helper for Chap08 Lemma 8 8 1: the first quotient Hom presheaf is separated for covers of
the identity object in the slice site.  This is the formal `Presieve.IsSeparatedFor` form of the
source proof's step 1.7 for the basic slice cover. -/
theorem localEqualityQuotient_presheafHom_identity_isSeparatedFor
    (X : FibredCategoryOver C) {U : C}
    (x y : (projection (J := J) X).Fiber U)
    (S : J.Cover U) :
    Presieve.IsSeparatedFor
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y)
      (((Sieve.overEquiv (Over.mk (𝟙 U))).symm (S : Sieve U)) : Presieve (Over.mk (𝟙 U))) := by
  intro fam s t hs ht
  refine localEqualityQuotient_presheafHom_identity_ext (J := J) X x y S ?_
  intro I
  let fI : Over.mk (I.f ≫ 𝟙 U) ⟶ Over.mk (𝟙 U) := Over.homMk I.f
  have hfI : ((Sieve.overEquiv (Over.mk (𝟙 U))).symm (S : Sieve U)) fI := by
    rw [Sieve.overEquiv_symm_iff]
    exact I.hf
  exact (hs fI hfI).trans (ht fI hfI).symm

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source step 1.7 for arbitrary slice objects: two sections of
the first-quotient Hom presheaf that agree on a covering sieve of a slice object are equal.  The
proof transports the covering sieve along `Sieve.overEquiv`, applies the identity-slice
separatedness theorem over the slice object's source, and uses
`Pseudofunctor.overMapCompPresheafHomIso` to compare the two restriction pictures. -/
theorem localEqualityQuotient_presheafHom_ext
    (X : FibredCategoryOver C) {U : C}
    (x y : (projection (J := J) X).Fiber U)
    (V : Over U) (S : Sieve V) (hS : S ∈ (J.over U) V)
    {s t : ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).obj (op V)}
    (h : ∀ ⦃W : Over U⦄ (f : W ⟶ V), S f →
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map f.op s =
        ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y).map f.op t) :
    s = t := by
  obtain ⟨V₀, q, rfl⟩ := V.mk_surjective
  let F := canonicalFiberPseudofunctor (projection (J := J) X)
  let R : J.Cover V₀ :=
    ⟨Sieve.overEquiv (Over.mk q) S, (J.mem_over_iff S).1 hS⟩
  let xq : (projection (J := J) X).Fiber V₀ := (F.map q.op.toLoc).toFunctor.obj x
  let yq : (projection (J := J) X).Fiber V₀ := (F.map q.op.toLoc).toFunctor.obj y
  apply (F.presheafHomObjHomEquiv (M := xq) (N := yq)).injective
  refine localEqualityQuotient_presheafHom_identity_ext (J := J) X xq yq R ?_
  intro I
  let k : Over.mk (I.f ≫ 𝟙 V₀) ⟶ Over.mk (𝟙 V₀) := Over.homMk I.f
  let kq : (Over.map q).obj (Over.mk (I.f ≫ 𝟙 V₀)) ⟶ Over.mk q :=
    (Over.map q).map k ≫ (overMapIdentitySliceIso q).hom
  have hkq : S kq := by
    have h0 : S (Over.homMk I.f : Over.mk (I.f ≫ q) ⟶ Over.mk q) :=
      (Sieve.overEquiv_iff (Y := Over.mk q) S I.f).1 I.hf
    let a : (Over.map q).obj (Over.mk (I.f ≫ 𝟙 V₀)) ⟶ Over.mk (I.f ≫ q) :=
      Over.homMk (𝟙 I.Y) (by simp)
    have h1 : S (a ≫ (Over.homMk I.f : Over.mk (I.f ≫ q) ⟶ Over.mk q)) :=
      S.downward_closed h0 a
    have heq : a ≫ (Over.homMk I.f : Over.mk (I.f ≫ q) ⟶ Over.mk q) = kq := by
      ext
      simp [a, kq, k, overMapIdentitySliceIso]
    rwa [← heq]
  have hst : (F.presheafHom x y).map kq.op s = (F.presheafHom x y).map kq.op t :=
    h kq hkq
  let i := F.overMapCompPresheafHomIso x y q
  have hs_nat :
      (F.presheafHom xq yq).map k.op
        ((i.hom.app (op (Over.mk (𝟙 V₀))))
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)) =
      (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀))))
        (((Over.map q).op ⋙ F.presheafHom x y).map k.op
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)) := by
    simpa [i] using
      (congr_fun (i.hom.naturality k.op)
        ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)).symm
  have ht_nat :
      (F.presheafHom xq yq).map k.op
        ((i.hom.app (op (Over.mk (𝟙 V₀))))
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)) =
      (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀))))
        (((Over.map q).op ⋙ F.presheafHom x y).map k.op
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)) := by
    simpa [i] using
      (congr_fun (i.hom.naturality k.op)
        ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)).symm
  have hs_comp :
      (((Over.map q).op ⋙ F.presheafHom x y).map k.op
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)) =
        (F.presheafHom x y).map kq.op s := by
    change (F.presheafHom x y).map (((Over.map q).map k).op)
        ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s) =
      (F.presheafHom x y).map kq.op s
    rw [← FunctorToTypes.map_comp_apply]
    rfl
  have ht_comp :
      (((Over.map q).op ⋙ F.presheafHom x y).map k.op
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)) =
        (F.presheafHom x y).map kq.op t := by
    change (F.presheafHom x y).map (((Over.map q).map k).op)
        ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t) =
      (F.presheafHom x y).map kq.op t
    rw [← FunctorToTypes.map_comp_apply]
    rfl
  have hs_id :
      F.presheafHomObjHomEquiv s =
        (i.hom.app (op (Over.mk (𝟙 V₀))))
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s) := by
    exact (overMapCompPresheafHomIso_hom_app_identitySlice F q s).symm
  have ht_id :
      F.presheafHomObjHomEquiv t =
        (i.hom.app (op (Over.mk (𝟙 V₀))))
          ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t) := by
    exact (overMapCompPresheafHomIso_hom_app_identitySlice F q t).symm
  change
    (F.presheafHom xq yq).map k.op (F.presheafHomObjHomEquiv s) =
      (F.presheafHom xq yq).map k.op (F.presheafHomObjHomEquiv t)
  calc
    (F.presheafHom xq yq).map k.op (F.presheafHomObjHomEquiv s)
        = (F.presheafHom xq yq).map k.op
            ((i.hom.app (op (Over.mk (𝟙 V₀))))
              ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)) :=
          congrArg (fun z => (F.presheafHom xq yq).map k.op z) hs_id
    _ = (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀))))
          (((Over.map q).op ⋙ F.presheafHom x y).map k.op
            ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op s)) := hs_nat
    _ = (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀)))) ((F.presheafHom x y).map kq.op s) := by
          rw [hs_comp]
    _ = (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀)))) ((F.presheafHom x y).map kq.op t) := by
          rw [hst]
    _ = (i.hom.app (op (Over.mk (I.f ≫ 𝟙 V₀))))
          (((Over.map q).op ⋙ F.presheafHom x y).map k.op
            ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)) := by
          rw [ht_comp]
    _ = (F.presheafHom xq yq).map k.op
            ((i.hom.app (op (Over.mk (𝟙 V₀))))
              ((F.presheafHom x y).map (overMapIdentitySliceIso q).hom.op t)) := ht_nat.symm
    _ = (F.presheafHom xq yq).map k.op (F.presheafHomObjHomEquiv t) :=
          congrArg (fun z => (F.presheafHom xq yq).map k.op z) ht_id.symm

/-- Helper for Chap08 Lemma 8 8 1: the first quotient Hom presheaf is separated for every
covering sieve on every slice object. -/
theorem localEqualityQuotient_presheafHom_isSeparatedFor
    (X : FibredCategoryOver C) {U : C}
    (x y : (projection (J := J) X).Fiber U)
    (V : Over U) (S : Sieve V) (hS : S ∈ (J.over U) V) :
    Presieve.IsSeparatedFor
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y)
      (S : Presieve V) := by
  intro fam s t hs ht
  refine localEqualityQuotient_presheafHom_ext (J := J) X x y V S hS ?_
  intro W f hf
  exact (hs f hf).trans (ht f hf).symm

/-- Helper for Chap08 Lemma 8 8 1: after quotienting by local equality, all Hom presheaves of
the resulting fibred category are separated on the relevant slice sites. -/
theorem localEqualityQuotient_presheafHom_isSeparated
    (X : FibredCategoryOver C) {U : C}
    (x y : (projection (J := J) X).Fiber U) :
    Presieve.IsSeparated (J.over U)
      ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y) := by
  intro V S hS
  exact localEqualityQuotient_presheafHom_isSeparatedFor (J := J) X x y V S hS

/-- Helper for Chap08 Lemma 8 8 1, source stage 2 at the Hom-presheaf level: the Hom presheaf
of the first quotient, viewed in a type universe large enough to contain the slice-cover shapes.
The `ULift` is a bookkeeping bridge for Lean's concrete plus construction; mathematically it is
the same set-valued Hom presheaf. -/
noncomputable abbrev localEqualityQuotient_saturatedPresheafHom
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (projection (J := J) X).Fiber U) :
    (Over U)ᵒᵖ ⥤ Type (max vX (max u v)) :=
  ((canonicalFiberPseudofunctor (projection (J := J) X)).presheafHom x y) ⋙
    (CategoryTheory.uliftFunctor.{max u v, vX} : Type vX ⥤ Type (max vX (max u v)))

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap08 Lemma 8 8 1, source stage 2 at the Hom-presheaf level: since the first
quotient Hom presheaf is separated, its plus construction is already a sheaf.  This formalizes
the presheaf part of the source proof's "locally defined morphisms" stage without yet pretending
that the total category of those morphisms has been built. -/
theorem localEqualityQuotient_saturatedPresheafHom_plus_isSheaf
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (projection (J := J) X).Fiber U) :
    Presheaf.IsSheaf (J.over U)
      ((J.over U).plusObj
        (localEqualityQuotient_saturatedPresheafHom (J := J) X x y)) := by
  apply GrothendieckTopology.Plus.isSheaf_of_sep
  intro V S s t h
  apply ULift.ext
  exact Presieve.IsSeparatedFor.ext
    (localEqualityQuotient_presheafHom_isSeparated
      (J := J) X x y (S : Sieve V) S.condition)
    (by
      intro W f hf
      exact congrArg ULift.down (h ⟨W, f, hf⟩))

/-- Helper for Chap08 Lemma 8 8 1, source stage 2 at the Hom-presheaf level: after the same
universe saturation, the canonical map from the first quotient Hom presheaf to its plus
construction is a local isomorphism in the slice topology. -/
theorem localEqualityQuotient_saturatedPresheafHom_toPlus_W
    (X : FibredCategoryOver.{u, v, uX, vX} C) {U : C}
    (x y : (projection (J := J) X).Fiber U) :
    (J.over U).W
      ((J.over U).toPlus
        (localEqualityQuotient_saturatedPresheafHom (J := J) X x y)) := by
  let P := localEqualityQuotient_saturatedPresheafHom (J := J) X x y
  haveI : (J.over U).WEqualsLocallyBijective (Type (max vX (max u v))) :=
    @CategoryTheory.Functor.large_type_WEqualsLocallyBijective.{max u v, v, vX}
      (Over U) inferInstance (J.over U) inferInstance
  haveI : Presheaf.IsLocallyInjective (J.over U) ((J.over U).toPlus P) :=
    CategoryTheory.Functor.toPlus_isLocallyInjective_type (L := J.over U) P
  haveI : Presheaf.IsLocallySurjective (J.over U) ((J.over U).toPlus P) :=
    CategoryTheory.Functor.toPlus_isLocallySurjective_type (L := J.over U) P
  exact GrothendieckTopology.W_of_isLocallyBijective (J.over U) ((J.over U).toPlus P)

end LocalEqualityQuotientTotal
end FibredCategoryMor

end CategoryTheory

