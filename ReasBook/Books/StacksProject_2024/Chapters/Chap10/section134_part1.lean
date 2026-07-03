import Mathlib
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_134_1 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe u v w x

noncomputable section

namespace Algebra.Extension

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: naive cotangent complexes attached to polynomial presentations of algebras;
* sampled owner declarations:
  - `Algebra.Extension.cotangentComplex`, the canonical conormal-to-cotangent-space map;
  - `Algebra.Extension.H1Cotangent`, which treats the naive cotangent complex through this
    extension-level owner;
  - `CochainComplex.of` in the cochain convention and `ChainComplex.mk'` in the chain convention
    for two-term complexes.
* best owner abstraction: the primitive data are the extension `P : Algebra.Extension A B` and its
  canonical map `P.cotangentComplex`; the two-term chain complex is derived from that owner data,
  not additional primitive structure tied to one polynomial presentation.
* layer triage:
  - `source-facing`: the naive cotangent complex `NL_{B/A}` of a chosen polynomial presentation;
  - `core/canonical`: `P.cotangentComplex` for `P : Algebra.Extension A B`;
  - `bridge/view`: the chain-complex packaging placing `P.Cotangent` in degree `1` and
    `P.CotangentSpace` in degree `0`.

Definition 10.134.1 is therefore refined to the extension-level owner construction, which
specializes to the source's polynomial-presentation complex without keeping a parallel duplicate
definition. -/
/-- Definition 10.134.1: the naive cotangent complex attached to an `A`-extension `P → B` is the
two-term chain complex with the degree-`1` term canonically represented by
`ULift P.Cotangent = ULift (I / I²)`,
`P.CotangentSpace = B ⊗[P.Ring] Ω[P.Ring⁄A]` in degree `0`, and differential the canonical
cotangent map `P.cotangentComplex`. -/
def naiveCotangentChainComplex (P : Extension.{w} A B) :
    ChainComplex (ModuleCat.{max v w} B) ℕ :=
  ChainComplex.mk'
    (ModuleCat.of.{max v w} B P.CotangentSpace)
    (ModuleCat.of.{max v w} B (ULift.{v, w} P.Cotangent))
    (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
    (fun {_ _} _ ↦ ⟨ModuleCat.of.{max v w} B PUnit, 0, zero_comp⟩)

/-- Restricting scalars along `R → B` carries the naive cotangent complex of `P` to the same
two-term chain complex viewed in `ModuleCat R`. This is the canonical bridge/view used when a
comparison lives over a smaller base ring. -/
noncomputable abbrev naiveCotangentChainComplexRestrictScalars
    (P : Extension.{w} A B) (R : Type x) [CommRing R] [Algebra R B] :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex (down ℕ)).obj
    P.naiveCotangentChainComplex

/-- The differential in degrees `1 → 0` of `P.naiveCotangentChainComplex` is
`ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap)`. -/
theorem naiveCotangentChainComplex_d_1_0 (P : Extension.{w} A B) :
    P.naiveCotangentChainComplex.d 1 0 =
      ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) := by
  simp [naiveCotangentChainComplex]

/-- All higher differentials of `P.naiveCotangentChainComplex` vanish. -/
theorem naiveCotangentChainComplex_d_succ_succ (P : Extension.{w} A B) (n : ℕ) :
    P.naiveCotangentChainComplex.d (n + 2) (n + 1) = 0 := by
  rw [naiveCotangentChainComplex, ChainComplex.mk'_d]
  simp

/-- All higher differentials also vanish after restricting scalars on the naive cotangent
complex. -/
theorem naiveCotangentChainComplexRestrictScalars_d_succ_succ
    (P : Extension.{w} A B) (R : Type x) [CommRing R] [Algebra R B] (n : ℕ) :
    (P.naiveCotangentChainComplexRestrictScalars R).d (n + 2) (n + 1) = 0 := by
  simp [naiveCotangentChainComplexRestrictScalars, naiveCotangentChainComplex_d_succ_succ]
  rfl

section

variable {A' : Type x} [CommRing A'] [Algebra A' B] [Algebra A A'] [IsScalarTower A A' B]

/-- An extension morphism induces the canonical chain map on naive cotangent complexes. -/
noncomputable def naiveCotangentChainMap
    {P : Extension.{w} A B} {Q : Extension.{w} A' B} (f : P.Hom Q) :
    P.naiveCotangentChainComplex ⟶ Q.naiveCotangentChainComplex :=
  ChainComplex.mkHom _ _
    (ModuleCat.ofHom (CotangentSpace.map f))
    (ModuleCat.ofHom
      (((ULift.moduleEquiv : ULift Q.Cotangent ≃ₗ[B] Q.Cotangent).symm.toLinearMap) ∘ₗ
        Cotangent.map f ∘ₗ
          (ULift.moduleEquiv : ULift P.Cotangent ≃ₗ[B] P.Cotangent).toLinearMap))
    (by
      ext x
      rcases x with ⟨x⟩
      simpa [naiveCotangentChainComplex, LinearMap.comp_assoc] using
        LinearMap.congr_fun (CotangentSpace.map_comp_cotangentComplex f).symm x)
    (by
      intro n _
      refine ⟨0, ?_⟩
      rw [naiveCotangentChainComplex_d_succ_succ Q n, naiveCotangentChainComplex_d_succ_succ P n]
      simp)

end

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension.{w} A B) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{max v w} B PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{max v w} B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{max v w} B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{max v w} B PUnit, 0, zero_comp⟩
  simpa [naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{max v w} B P.CotangentSpace)
      (ModuleCat.of.{max v w} B (ULift.{v, w} P.Cotangent))
      (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{w} A B) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{w} A B) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

/-- The chain map on naive cotangent complexes induced by the identity extension morphism is the
identity. -/
theorem naiveCotangentChainMap_id
    (P : Extension.{w} A B) :
    Extension.naiveCotangentChainMap (.id P) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (.id P)) =
        ModuleCat.ofHom (LinearMap.id : P.CotangentSpace →ₗ[B] P.CotangentSpace)
      congr
      exact Extension.CotangentSpace.map_id
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (.id P) x) : ULift P.Cotangent) = ULift.up x
          congr 1
          simp
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ P i
          ext x
          exact Subsingleton.elim _ _

/-- Composition of extension morphisms is respected by the induced chain maps on naive cotangent
complexes. -/
theorem naiveCotangentChainMap_comp
    {P Q T : Extension.{w} A B} (f : P.Hom Q) (g : Q.Hom T) :
    Extension.naiveCotangentChainMap (g.comp f) =
      Extension.naiveCotangentChainMap f ≫ Extension.naiveCotangentChainMap g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change ModuleCat.ofHom (CotangentSpace.map (g.comp f)) =
        ModuleCat.ofHom ((CotangentSpace.map g).restrictScalars B ∘ₗ CotangentSpace.map f)
      congr
      exact Extension.CotangentSpace.map_comp f g
  | succ i =>
      cases i with
      | zero =>
          ext x
          rcases x with ⟨x⟩
          change (ULift.up (Cotangent.map (g.comp f) x) : ULift T.Cotangent) =
            ULift.up (Cotangent.map g (Cotangent.map f x))
          simp [Cotangent.map_comp]
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ T i
          ext x
          exact Subsingleton.elim _ _

end

end Algebra.Extension

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

attribute [local instance] HasDerivedCategory.standard

/- Domain triage:
* primary domain: the canonical naive cotangent complex `NL_{B/A}` attached to the canonical
  presentation `A[B] → B`;
* sampled owner declarations:
  - `Generators.self`, the canonical self-presentation of `B` over `A`;
  - `Algebra.Extension.naiveCotangentChainComplex`, the Chapter 10 owner for the two-term chain
    representative of a presentationwise naive cotangent complex;
  - `DerivedCategory.Q.obj`, the canonical passage from a cochain complex to its object of the
    derived category.
* best owner abstraction: the primitive data are only the algebra map `A → B`; the source-facing
  owner is the canonical self-presentation chain complex itself, while passage to `D(B)` is
  derived bridge/view data.
* layer triage:
  - `source-facing`: the chain complex `NL_{B/A}` in homological degrees `1` and `0`;
  - `core/canonical`: `naiveCotangent A B`;
  - `bridge/view`: `naiveCotangentObject A B`.

Definition 10.134.1 should therefore make the algebra-level self-presentation chain complex the
main owner, with the derived-category object kept only as a companion bridge for later chapters.
-/
/-- Definition 10.134.1: the naive cotangent complex `NL_{B/A}` of the algebra map `A → B` is the
canonical self-presentation two-term chain complex. -/
noncomputable abbrev naiveCotangent :
    ChainComplex (ModuleCat B) ℕ :=
  (Generators.self A B).toExtension.naiveCotangentChainComplex

end

end Algebra

namespace CommRingCat.Hom

section

variable {A B : CommRingCat.{u}}

attribute [local instance] HasDerivedCategory.standard

/-- The naive cotangent complex of a commutative-ring morphism `f : A ⟶ B`, written `NL(f)`, is
the Chapter 10 chain-complex owner `NL_{B⁄A}` for the algebra structure induced by `f`. -/
noncomputable abbrev naiveCotangent (f : A ⟶ B) :
    ChainComplex (ModuleCat B) ℕ := by
  let _ : Algebra A B := f.hom.toAlgebra
  exact Algebra.naiveCotangent A B

end

end CommRingCat.Hom

namespace NaiveCotangent

scoped notation "NL_{" B "⁄" A "}" => Algebra.naiveCotangent A B
scoped[NaiveCotangent] notation:max "NL(" f ")" => CommRingCat.Hom.naiveCotangent f

end NaiveCotangent

open scoped NaiveCotangent

namespace Algebra

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

attribute [local instance] HasDerivedCategory.standard

/-- The derived-category object represented by the canonical self-presentation complex
`NL_{B/A}`. This is the bridge/view companion of the chain-complex owner, not the primary owner
itself. -/
noncomputable abbrev naiveCotangentObject : DerivedCategory (ModuleCat B) :=
  DerivedCategory.Q.obj ((NL_{B⁄A}).extend embeddingDownNat)

end

end Algebra

namespace CommRingCat.Hom

section

variable {A B : CommRingCat.{u}}

attribute [local instance] HasDerivedCategory.standard

/-- The derived-category object represented by the chain complex `NL(f)`. This is the map-level
bridge/view companion used when later arguments take place in `D(B)`. -/
noncomputable abbrev naiveCotangentObject (f : A ⟶ B) :
    DerivedCategory (ModuleCat B) :=
  DerivedCategory.Q.obj ((NL(f)).extend embeddingDownNat)

end

end CommRingCat.Hom

/-! ### Lemma_10_134_2 (from Chap10) -/
open Algebra
open Algebra.Generators
open Algebra.Extension

universe w w' w'' u v u' v' u'' v''

section General

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {R' : Type u'} {S' : Type v'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {ι : Type w} {ι' : Type w'} {ι'' : Type w''}

variable (P : Generators R S ι) (P' : Generators R' S' ι') (P'' : Generators R'' S'' ι'')

variable [Algebra S S']

/- Lemma 10.134.2 (1) is a `source-facing` existence claim whose canonical owner is
`Generators.defaultHom`. For two presentations in the commutative square, the distinguished
morphism of presentations is already provided upstream. -/
#check (Generators.defaultHom P P' : P.Hom P')

variable [Algebra R R'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

variable {P P'} (f g : P.Hom P')

/- Lemma 10.134.2 (2) is exactly the owner homotopy identity
`Extension.CotangentSpace.map_sub_map` applied to `f.toExtensionHom` and `g.toExtensionHom`. -/
#check
  (Extension.CotangentSpace.map_sub_map (f.toExtensionHom) (g.toExtensionHom) :
    CotangentSpace.map f.toExtensionHom - CotangentSpace.map g.toExtensionHom =
      (let d := P'.toExtension.cotangentComplex
       d.restrictScalars S) ∘ₗ f.toExtensionHom.sub g.toExtensionHom)

/- Lemma 10.134.2 (3) is exactly the owner homotopy identity
`Extension.Cotangent.map_sub_map` applied to `f.toExtensionHom` and `g.toExtensionHom`. -/
#check
  (Extension.Cotangent.map_sub_map (f.toExtensionHom) (g.toExtensionHom) :
    Cotangent.map f.toExtensionHom - Cotangent.map g.toExtensionHom =
      f.toExtensionHom.sub g.toExtensionHom ∘ₗ P.toExtension.cotangentComplex)

/- Lemma 10.134.2 (4) is the canonical presentation-independence theorem
`Extension.H1Cotangent.map_eq` specialized to presentation morphisms. -/
#check
  (Extension.H1Cotangent.map_eq f.toExtensionHom g.toExtensionHom :
    Extension.H1Cotangent.map f.toExtensionHom = Extension.H1Cotangent.map g.toExtensionHom)

variable [Algebra S' S''] [Algebra S S'']
variable [Algebra R R''] [Algebra R' R''] [Algebra R' S''] [Algebra R S'']
variable [IsScalarTower R' R'' S''] [IsScalarTower R R'' S''] [IsScalarTower R R' R'']
variable [IsScalarTower R' S' S''] [IsScalarTower S S' S'']

variable {P''} (h : P'.Hom P'')

/- Lemma 10.134.2 (5) is the owner functoriality statement
`Extension.H1Cotangent.map_comp` specialized to presentation morphisms. -/
#check
  (Extension.H1Cotangent.map_comp f.toExtensionHom h.toExtensionHom :
    Extension.H1Cotangent.map (h.toExtensionHom.comp f.toExtensionHom) =
      (Extension.H1Cotangent.map h.toExtensionHom).restrictScalars S ∘ₗ
        Extension.H1Cotangent.map f.toExtensionHom)

end General

section FixedBase

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {ι' : Type w'}
variable (P : Generators R S ι) (P' : Generators R S ι')

/- Lemma 10.134.2 (6) is recalled canonically by `Generators.H1Cotangent.equiv`. -/
#check
  (Generators.H1Cotangent.equiv P P' :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent)

/- Lemma 10.134.2 (7) is recalled canonically by `Generators.equivH1Cotangent`. -/
#check (P.equivH1Cotangent : P.toExtension.H1Cotangent ≃ₗ[S] H1Cotangent R S)

end FixedBase

namespace Algebra.Generators

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {ι' : Type w'}
variable {P : Generators R S ι} {P' : Generators R S ι'}

-- Proof sketch: both sides are maps on `H¹(L_{S/R})`; after rewriting the left-hand side using
-- `Extension.H1Cotangent.map_comp`, `Extension.H1Cotangent.map_eq` identifies the composite with
-- the canonical comparison map coming directly from `P`.
/-- Lemma 10.134.2: the canonical comparison with `Algebra.H1Cotangent R S` is functorial in
morphisms of presentations. -/
theorem equivH1Cotangent_naturality (f : P.Hom P') :
    P'.equivH1Cotangent.toLinearMap ∘ₗ Extension.H1Cotangent.map f.toExtensionHom =
      P.equivH1Cotangent.toLinearMap := by
  apply LinearMap.ext
  intro x
  change
    Extension.H1Cotangent.map (Generators.defaultHom P' (Generators.self R S)).toExtensionHom
        (Extension.H1Cotangent.map f.toExtensionHom x) =
      Extension.H1Cotangent.map (Generators.defaultHom P (Generators.self R S)).toExtensionHom x
  simpa [Generators.Hom.toExtensionHom_comp] using
    DFunLike.congr_fun
      (Extension.H1Cotangent.map_eq
        (((Generators.defaultHom P' (Generators.self R S)).comp f).toExtensionHom)
        ((Generators.defaultHom P (Generators.self R S)).toExtensionHom)) x

end

end Algebra.Generators

/-! ### Lemma_10_134_3 (from Chap10) -/
open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/- Domain triage:
* primary domain: naive cotangent complexes attached to polynomial presentations of an
  `A`-algebra `B`;
* sampled owner declarations:
  - `Algebra.naiveCotangent`, the canonical owner `NL_{B⁄A}`;
  - `Algebra.Generators.self`, the canonical self-presentation underlying `NL_{B⁄A}`;
  - `Algebra.Generators.defaultHom`, the canonical comparison between two presentations of the
    same algebra;
  - `Algebra.Extension.toKaehler`, the canonical map from the degree-`0` term of a presentation
    complex to `Ω[B⁄A]`.
* best owner abstraction: the source-facing public statement should be about the canonical owner
  `NL_{B⁄A}`. A chosen polynomial algebra structure is bridge/view data used only to compare that
  owner with a presentation whose algebra map is bijective.
* primitive vs. derived:
  - primitive data: the algebra map `A → B` and, for the polynomial case, a chosen equivalence
    `MvPolynomial ι A ≃ₐ[A] B`;
  - derived API: the presentationwise naive cotangent complexes and the homotopy comparison
    between different presentations.
* layer triage:
  - `source-facing`: the homotopy equivalence `NL_{B⁄A} ≃ single₀ Ω[B⁄A]` for polynomial
    `A`-algebras;
  - `core/canonical`: `Algebra.naiveCotangent A B`;
  - `bridge/view`: the chosen polynomial presentation and the generic bijective-presentation
    comparison below.
-/

private abbrev LiftCotangent (P : Extension.{u} A B) :=
  ULift P.Cotangent

private noncomputable abbrev liftCotangentEquiv
    (P : Extension.{u} A B) :
    LiftCotangent P ≃ₗ[B] P.Cotangent :=
  ULift.moduleEquiv

private noncomputable def liftCotangentMap
    {P Q : Extension.{u} A B} (f : P.Hom Q) :
    LiftCotangent P →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ
    Cotangent.map f ∘ₗ (liftCotangentEquiv P).toLinearMap

private noncomputable def liftCotangentHomotopyMap
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
    P.CotangentSpace →ₗ[B] LiftCotangent Q :=
  (liftCotangentEquiv Q).symm.toLinearMap ∘ₗ f.sub g

private theorem liftCotangentMap_id
    (P : Extension.{u} A B) :
    liftCotangentMap (.id P) = LinearMap.id := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap]

private theorem liftCotangentMap_comp
    {P Q T : Extension.{u} A B} (f : P.Hom Q) (g : Q.Hom T) :
    liftCotangentMap (g.comp f) =
      (liftCotangentMap g).restrictScalars B ∘ₗ liftCotangentMap f := by
  ext x
  rcases x with ⟨x⟩
  simp [liftCotangentMap, Cotangent.map_comp, LinearMap.comp_assoc]

private theorem naiveCotangent_rel10 : (ComplexShape.down ℕ).Rel 1 0 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_rel21 : (ComplexShape.down ℕ).Rel 2 1 := by
  simp [ComplexShape.down]

private theorem naiveCotangent_not_rel0 (j : ℕ) : ¬ (ComplexShape.down ℕ).Rel 0 j := by
  simp [ComplexShape.down]

private noncomputable def naiveCotangentChainComplexXIsoPUnit
    (P : Extension.{u} A B) (i : ℕ) :
    P.naiveCotangentChainComplex.X (i + 2) ≅ ModuleCat.of.{u} B PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{u} B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{u} B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{u} B PUnit, 0, zero_comp⟩
  simpa [naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of.{u} B P.CotangentSpace)
      (ModuleCat.of.{u} B (LiftCotangent P))
      (ModuleCat.ofHom (P.cotangentComplex ∘ₗ (liftCotangentEquiv P).toLinearMap))
      succZero i)

private theorem naiveCotangentChainComplex_eq_zero_of_succ_succ
    (P : Extension.{u} A B) (i : ℕ)
    (x : P.naiveCotangentChainComplex.X (i + 2)) :
    x = 0 := by
  let e := naiveCotangentChainComplexXIsoPUnit P i
  have h : e.hom.hom x = e.hom.hom 0 := by
    cases e.hom.hom x
    rfl
  apply_fun e.inv.hom at h
  simpa using h

private theorem naiveCotangentChainComplex_subsingleton_of_succ_succ
    (P : Extension.{u} A B) (i : ℕ) :
    Subsingleton (P.naiveCotangentChainComplex.X (i + 2)) := by
  refine ⟨fun x y ↦ ?_⟩
  rw [naiveCotangentChainComplex_eq_zero_of_succ_succ P i x,
    naiveCotangentChainComplex_eq_zero_of_succ_succ P i y]

private noncomputable def naiveCotangentChainHomotopyHom
    {P Q : Extension.{u} A B} (f g : P.Hom Q)
    (i j : ℕ) (_ : (ComplexShape.down ℕ).Rel j i) :
    P.naiveCotangentChainComplex.X i ⟶ Q.naiveCotangentChainComplex.X j := by
  rcases i with _ | i
  · rcases j with _ | j
    · exact 0
    · cases j with
      | zero =>
          exact ModuleCat.ofHom (liftCotangentHomotopyMap f g)
      | succ j =>
          exact 0
  · exact 0

private theorem naiveCotangentChainMap_sub_eq_nullHomotopicMap
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
    Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g =
      Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i with
  | zero =>
      change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 0 =
        (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 0
      rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left naiveCotangent_rel10
        naiveCotangent_not_rel0 (naiveCotangentChainHomotopyHom f g)]
      ext x
      simpa [Extension.naiveCotangentChainMap, naiveCotangentChainHomotopyHom,
        naiveCotangentChainComplex, liftCotangentHomotopyMap, LinearMap.comp_assoc] using
        LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map f g) x
  | succ i =>
      cases i with
      | zero =>
          change (Extension.naiveCotangentChainMap f - Extension.naiveCotangentChainMap g).f 1 =
            (Homotopy.nullHomotopicMap' (naiveCotangentChainHomotopyHom f g)).f 1
          rw [Homotopy.nullHomotopicMap'_f naiveCotangent_rel21 naiveCotangent_rel10
            (naiveCotangentChainHomotopyHom f g)]
          ext x
          rcases x with ⟨x⟩
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            (ModuleCat.Hom.hom
                (P.naiveCotangentChainComplex.d 1 0 ≫
                  naiveCotangentChainHomotopyHom f g 0 1 naiveCotangent_rel10 +
                naiveCotangentChainHomotopyHom f g 1 2 naiveCotangent_rel21 ≫
                  Q.naiveCotangentChainComplex.d 2 1))
              { down := x }
          rw [naiveCotangentChainComplex_d_succ_succ Q 0,
            naiveCotangentChainComplex_d_1_0 P]
          simp [naiveCotangentChainHomotopyHom, liftCotangentHomotopyMap]
          change ULift.up ((Cotangent.map f - Cotangent.map g) x) =
            ULift.up ((f.sub g) (P.cotangentComplex x))
          rw [LinearMap.congr_fun (Extension.Cotangent.map_sub_map f g) x]
          rfl
      | succ i =>
          haveI := naiveCotangentChainComplex_subsingleton_of_succ_succ Q i
          ext x
          exact Subsingleton.elim _ _

private noncomputable def naiveCotangentChainMapHomotopy
    {P Q : Extension.{u} A B} (f g : P.Hom Q) :
    Homotopy (Extension.naiveCotangentChainMap f) (Extension.naiveCotangentChainMap g) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (naiveCotangentChainMap_sub_eq_nullHomotopicMap f g)).trans
      (Homotopy.nullHomotopy' (naiveCotangentChainHomotopyHom f g)))

private noncomputable abbrev defaultExtensionHom
    {ι ι' : Type u} (P : Generators A B ι) (Q : Generators A B ι') :
    P.toExtension.Hom Q.toExtension :=
  (Generators.defaultHom P Q).toExtensionHom

namespace Algebra.Generators

/-- Presentation-independence bridge: the naive cotangent complexes attached to any two
presentations of the same `A`-algebra `B` are canonically homotopy equivalent. -/
noncomputable def naiveCotangentChainHomotopyEquiv
    {ι ι' : Type u}
    (P : Generators A B ι) (Q : Generators A B ι') :
    HomotopyEquiv P.toExtension.naiveCotangentChainComplex Q.toExtension.naiveCotangentChainComplex where
  hom := Extension.naiveCotangentChainMap (defaultExtensionHom P Q)
  inv := Extension.naiveCotangentChainMap (defaultExtensionHom Q P)
  homotopyHomInvId := by
    let f := defaultExtensionHom P Q
    let g := defaultExtensionHom Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp f g).symm).trans
        ((naiveCotangentChainMapHomotopy (g.comp f) (.id P.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id P.toExtension)))
  homotopyInvHomId := by
    let f := defaultExtensionHom P Q
    let g := defaultExtensionHom Q P
    exact
      (Homotopy.ofEq (Extension.naiveCotangentChainMap_comp g f).symm).trans
        ((naiveCotangentChainMapHomotopy (f.comp g) (.id Q.toExtension)).trans
          (Homotopy.ofEq (Extension.naiveCotangentChainMap_id Q.toExtension)))

end Algebra.Generators

private theorem cotangent_subsingleton_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    Subsingleton P.Cotangent := by
  letI : Subsingleton ↥P.ker := by
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    exact hP.1 <| by
      simpa [RingHom.mem_ker] using x.2.trans y.2.symm
  exact Cotangent.mk_surjective.subsingleton

private theorem cotangentComplex_eq_zero_of_subsingleton_cotangent
    (P : Extension.{u} A B) [Subsingleton P.Cotangent] :
    P.cotangentComplex = 0 := by
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  simp [hx]

private theorem toKaehler_bijective_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    Function.Bijective P.toKaehler := by
  letI : Subsingleton P.Cotangent := cotangent_subsingleton_of_bijective P hP
  refine ⟨?_, P.toKaehler_surjective⟩
  intro x y hxy
  have hxy' : P.toKaehler (x - y) = 0 := by
    simpa using sub_eq_zero.mpr hxy
  have hexact := (LinearMap.exact_iff).mp P.exact_cotangentComplex_toKaehler
  have hmem : x - y ∈ LinearMap.range P.cotangentComplex := by
    rw [← hexact]
    exact hxy'
  rcases hmem with ⟨z, hz⟩
  rw [cotangentComplex_eq_zero_of_subsingleton_cotangent P] at hz
  exact sub_eq_zero.mp <| by simpa using hz.symm

/-- Bridge/view comparison: if a presentation `P` has bijective algebra map `P.Ring ≃ B`, then
its naive cotangent complex is already concentrated in degree `0` and is isomorphic to the chain
complex `single₀ Ω[B⁄A]`. -/
noncomputable def extension_naiveCotangentChainComplex_iso_single₀_kaehler_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    P.naiveCotangentChainComplex ≅
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) := by
  letI : Subsingleton P.Cotangent := cotangent_subsingleton_of_bijective P hP
  let succZero :
      ∀ {X₀ X₁ : ModuleCat.{u} B} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat.{u} B) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of.{u} B PUnit, 0, zero_comp⟩
  let C := P.naiveCotangentChainComplex
  let D := (ChainComplex.single₀ (ModuleCat.{u} B)).obj
    (ModuleCat.of.{u} B Ω[B⁄A])
  let e₀ : P.CotangentSpace ≃ₗ[B] Ω[B⁄A] :=
    LinearEquiv.ofBijective P.toKaehler (toKaehler_bijective_of_bijective P hP)
  let e : ∀ n : ℕ, C.X n ≅ D.X n
    | 0 => by
        simpa [C, D, naiveCotangentChainComplex] using e₀.toModuleIso
    | 1 => by
        simpa [C, D, naiveCotangentChainComplex] using
          ((ModuleCat.isZero_of_subsingleton
              (ModuleCat.of B (ULift P.Cotangent))).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
              (ModuleCat.of B Ω[B⁄A]) 1 (by decide)).isoZero.symm)
    | n + 2 => by
        have hs : (succZero (C.d (n + 1) n)).1 = ModuleCat.of B PUnit := rfl
        have hX :
            C.X (n + 2) ≅ (succZero (C.d (n + 1) n)).1 := by
          simpa [C, naiveCotangentChainComplex] using
            (ChainComplex.mk'XIso
              (ModuleCat.of.{u} B P.CotangentSpace)
              (ModuleCat.of.{u} B (ULift P.Cotangent))
              (ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap))
              succZero n)
        simpa [D] using
          (hX ≪≫ eqToIso hs ≪≫
            (ModuleCat.isZero_of_subsingleton (ModuleCat.of B PUnit)).isoZero ≪≫
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
              (ModuleCat.of B Ω[B⁄A]) (n + 2) (by simp)).isoZero.symm)
  exact HomologicalComplex.Hom.isoOfComponents e <| by
    intro i j hij
    subst i
    cases j with
    | zero =>
        have hcot :
            ModuleCat.ofHom (P.cotangentComplex.comp ULift.moduleEquiv.toLinearMap) = 0 := by
          rw [cotangentComplex_eq_zero_of_subsingleton_cotangent P]
          rfl
        have hC : C.d 1 0 = 0 := by
          simpa [C] using (naiveCotangentChainComplex_d_1_0 P).trans hcot
        have hD : D.d 1 0 = 0 := by
          simp [D]
        change (e 1).hom ≫ D.d 1 0 = C.d 1 0 ≫ (e 0).hom
        rw [hC, hD]
        simp
    | succ j =>
        have hC : C.d (j + 2) (j + 1) = 0 := by
          simpa [C] using naiveCotangentChainComplex_d_succ_succ P j
        have hD : D.d (j + 2) (j + 1) = 0 := by
          simp [D]
        change (e (j + 2)).hom ≫ D.d (j + 2) (j + 1) =
          C.d (j + 2) (j + 1) ≫ (e (j + 1)).hom
        rw [hC, hD]
        simp

/-- Bridge/view comparison: if a presentation `P` has bijective algebra map `P.Ring ≃ B`, then
its naive cotangent complex is homotopy equivalent to the chain complex concentrated in degree `0`
with value `Ω[B⁄A]`. -/
noncomputable def extension_naiveCotangentChainComplex_homotopyEquiv_single₀_kaehler_of_bijective
    (P : Extension.{u} A B) (hP : Function.Bijective (algebraMap P.Ring B)) :
    HomotopyEquiv
      P.naiveCotangentChainComplex
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) :=
  HomotopyEquiv.ofIso
    (extension_naiveCotangentChainComplex_iso_single₀_kaehler_of_bijective P hP)

private noncomputable def polynomialPresentation
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    Generators A B ι where
  val := fun i ↦ e (.X i)
  σ' := e.symm
  aeval_val_σ' b := by
    let h :
        MvPolynomial.aeval (fun i ↦ e (.X i)) = e.toAlgHom :=
      (MvPolynomial.aeval_unique e.toAlgHom).symm
    simp [h]

private theorem polynomialPresentation_algebraMap_bijective
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    Function.Bijective (algebraMap (polynomialPresentation e).Ring B) := by
  change Function.Bijective (MvPolynomial.aeval (fun i ↦ e (.X i)))
  let h :
      MvPolynomial.aeval (fun i ↦ e (.X i)) = e.toAlgHom :=
    (MvPolynomial.aeval_unique e.toAlgHom).symm
  simpa [h] using e.bijective

-- Proof sketch: compare the canonical owner `NL_{B/A}` with the chosen polynomial presentation
-- attached to `e` by the default-presentation homotopy equivalence, then use the bijective-ring
-- bridge above to collapse the chosen presentation to `single₀ Ω[B⁄A]`.
/-- Lemma 10.134.3: if `B` is a polynomial algebra over `A`, witnessed by an `A`-algebra
equivalence `MvPolynomial ι A ≃ₐ[A] B`, then the canonical naive cotangent complex `NL_{B⁄A}` is
homotopy equivalent to the chain complex concentrated in degree `0` with value `Ω[B⁄A]`. -/
noncomputable def naiveCotangent_homotopyEquiv_single₀_kaehler_of_mvPolynomial
    {ι : Type u} (e : MvPolynomial ι A ≃ₐ[A] B) :
    HomotopyEquiv
      (NL_{B⁄A})
      ((ChainComplex.single₀ (ModuleCat.{u} B)).obj
        (ModuleCat.of.{u} B Ω[B⁄A])) := by
  let P := polynomialPresentation e
  exact
    (Generators.naiveCotangentChainHomotopyEquiv (Generators.self A B) P).trans
      (extension_naiveCotangentChainComplex_homotopyEquiv_single₀_kaehler_of_bijective
        P.toExtension (polynomialPresentation_algebraMap_bijective e))

end
