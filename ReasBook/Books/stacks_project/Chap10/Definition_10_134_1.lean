import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
