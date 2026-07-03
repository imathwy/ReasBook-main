import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_6_1 (from Chap12) -/
namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

/-
Domain-style sampling for Definition 12.6.1:
- primary domain: extensions in homological algebra, formalized as short exact sequences in a
  category with zero morphisms;
- sampled owner declarations:
  `ShortComplex`,
  `ShortComplex.ShortExact`,
  `ShortComplex.ShortExact.mk'`,
  `ShortComplex.ShortExact.extClass`;
- best owner abstraction: `ShortComplex C` with the owner predicate `S.ShortExact`;
- primitive source-facing data: the middle object `E` and the two structure maps
  `A ⟶ E ⟶ B` whose composite is zero;
- derived API: the associated short complex `toShortComplex`, the short exactness proof, and the
  induced `Mono`/`Epi` instances on the structure maps;
- source/core/bridge triage:
  `source-facing`: an extension of `B` by `A`, i.e. a short exact sequence
    `0 ⟶ A ⟶ E ⟶ B ⟶ 0` with fixed endpoints;
  `core/canonical`: `ShortComplex C` together with `ShortComplex.ShortExact`;
  `bridge/view`: `toShortComplex`.

The fixed-endpoint source-facing structure is kept here because replacing it by a raw subtype of
`ShortComplex C` would force endpoint transports into the public API. The refinement should
therefore reuse the `ShortComplex` owner through a thin bridge, not collapse the source-facing
notion into a transport-heavy wrapper.
-/
/-- Definition 12.6.1: an extension of `B` by `A` in an abelian category is a short exact
sequence `0 ⟶ A ⟶ E ⟶ B ⟶ 0`. The owner abstraction is `ShortComplex C`; a source-facing
extension is a short exact short complex whose endpoints are fixed to `A` and `B`. -/
structure Extension (A B : C) where
  E : C
  f : A ⟶ E
  g : E ⟶ B
  zero : f ≫ g = 0
  shortExact : (ShortComplex.mk f g zero).ShortExact

namespace Extension

abbrev toShortComplex (S : Extension A B) : ShortComplex C :=
  ShortComplex.mk S.f S.g S.zero

instance : CoeOut (Extension A B) (ShortComplex C) where
  coe := toShortComplex

instance (S : Extension A B) : Mono S.f :=
  S.shortExact.mono_f

instance (S : Extension A B) : Epi S.g :=
  S.shortExact.epi_g

end Extension

end

end CategoryTheory

/-! ### Definition_12_6_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Limits

universe w v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

/- Definition 12.6.2 has three layers:
- source-facing: extensions of `B` by `A` modulo isomorphisms that fix the endpoints;
- core/canonical: the owner object `Ext B A 1`;
- bridge/view: the canonical map sending a source-facing extension class to its degree-one
  `Ext` class. -/
namespace CategoryTheory
namespace Extension

variable {S T U : Extension A B}

/-- Two source-facing extensions are isomorphic when the induced morphisms on the fixed endpoints
`A` and `B` are the identities. Since the endpoints are fixed, the primitive source-facing data is
an isomorphism of middle terms compatible with the structure maps; the ambient short-complex
isomorphism is a derived bridge to the owner `Ext` API. -/
def Isomorphic (S T : Extension A B) : Prop :=
  ∃ e : S.E ≅ T.E, S.f ≫ e.hom = T.f ∧ e.hom ≫ T.g = S.g

theorem Isomorphic.refl (S : Extension A B) : Isomorphic S S := by
  refine ⟨Iso.refl S.E, ?_, ?_⟩ <;> simp

theorem Isomorphic.symm (h : Isomorphic S T) : Isomorphic T S := by
  rcases h with ⟨e, hf, hg⟩
  refine ⟨e.symm, ?_, ?_⟩
  · have hf' := congrArg (fun k ↦ k ≫ e.inv) hf
    simpa [Category.assoc] using hf'.symm
  · have hg' := congrArg (fun k ↦ e.inv ≫ k) hg
    simpa [Category.assoc] using hg'.symm

theorem Isomorphic.trans (hST : Isomorphic S T) (hTU : Isomorphic T U) : Isomorphic S U := by
  rcases hST with ⟨eST, hfST, hgST⟩
  rcases hTU with ⟨eTU, hfTU, hgTU⟩
  refine ⟨eST.trans eTU, ?_, ?_⟩
  · calc
      S.f ≫ (eST.trans eTU).hom = (S.f ≫ eST.hom) ≫ eTU.hom := by
        simp [Iso.trans_hom]
      _ = T.f ≫ eTU.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eTU.hom) hfST
      _ = U.f := hfTU
  · calc
      (eST.trans eTU).hom ≫ U.g = eST.hom ≫ (eTU.hom ≫ U.g) := by
        simp [Iso.trans_hom, Category.assoc]
      _ = eST.hom ≫ T.g := by rw [hgTU]
      _ = S.g := hgST

/-- The canonical equivalence relation on source-facing extensions used to form extension classes. -/
private def setoid : Setoid (Extension A B) where
  r := Isomorphic
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

end Extension

/-- Definition 12.6.2: source-facing extension classes are extensions modulo endpoint-fixing
isomorphism. -/
abbrev ExtensionClass (A B : C) :=
  _root_.Quotient (show Setoid (Extension A B) from Extension.setoid)

namespace ExtensionClass

/-- Endpoint-fixing isomorphic source-facing extensions determine the same extension class. -/
theorem mk_eq_mk_of_isomorphic {S T : Extension A B} (h : Extension.Isomorphic S T) :
    (⟦S⟧ : ExtensionClass A B) = ⟦T⟧ :=
  show _root_.Quotient.mk (show Setoid (Extension A B) from Extension.setoid) S =
      _root_.Quotient.mk (show Setoid (Extension A B) from Extension.setoid) T from
    _root_.Quotient.sound h

end ExtensionClass

end CategoryTheory

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace CategoryTheory
namespace Extension

section Operations

variable {S T : Extension A B}
variable {A' B' : C}

/-- Pulling back a source-facing extension along a morphism on the right endpoint gives a new
source-facing extension with the same left endpoint. -/
noncomputable def pullback (u : B' ⟶ B) (S : Extension A B) : Extension A B' :=
  Extension.mk
    (Limits.pullback u S.g)
    (Limits.pullback.lift 0 S.f (by
      sorry))
    (Limits.pullback.fst u S.g)
    (by
      sorry)
    (by
      sorry)

/-- Pushing out a source-facing extension along a morphism on the left endpoint gives a new
source-facing extension with the same right endpoint. -/
noncomputable def pushout (a : A ⟶ A') (S : Extension A B) : Extension A' B :=
  Extension.mk
    (Limits.pushout a S.f)
    (Limits.pushout.inl a S.f)
    (Limits.pushout.desc (0 : A' ⟶ B) S.g (by
      sorry))
    (by
      sorry)
    (by
      sorry)

/-- The split extension `0 ⟶ A ⟶ A ⊞ B ⟶ B ⟶ 0`. -/
noncomputable def split (A B : C) : Extension A B :=
  Extension.mk
    (A ⊞ B)
    (biprod.inl : A ⟶ A ⊞ B)
    (biprod.snd : A ⊞ B ⟶ B)
    (by
      sorry)
    (by
      sorry)

/-- Negating a source-facing extension is pushing out along `-𝟙_A`. -/
noncomputable def neg (S : Extension A B) : Extension A B :=
  pushout (-𝟙 A) S

private noncomputable def biprodExtension (S T : Extension A B) : Extension (A ⊞ A) (B ⊞ B) :=
  Extension.mk
    (S.E ⊞ T.E)
    (biprod.map S.f T.f)
    (biprod.map S.g T.g)
    (by
      sorry)
    (by
      sorry)

private noncomputable def diagonal (B : C) : B ⟶ B ⊞ B :=
  biprod.lift (𝟙 B) (𝟙 B)

private noncomputable def codiagonal (A : C) : A ⊞ A ⟶ A :=
  biprod.desc (𝟙 A) (𝟙 A)

/-- The Baer sum of two source-facing extensions is obtained by pulling back their biproduct along
the diagonal of `B` and then pushing out along the codiagonal of `A`. -/
noncomputable def baerSum (S T : Extension A B) : Extension A B :=
  pushout (codiagonal A) (pullback (diagonal B) (biprodExtension S T))

theorem Isomorphic.pullback (u : B' ⟶ B) (h : Isomorphic S T) :
    Isomorphic (pullback u S) (pullback u T) := by
  sorry

theorem Isomorphic.pushout (a : A ⟶ A') (h : Isomorphic S T) :
    Isomorphic (pushout a S) (pushout a T) := by
  sorry

theorem Isomorphic.neg (h : Isomorphic S T) : Isomorphic (neg S) (neg T) := by
  sorry

theorem Isomorphic.baerSum {S₁ S₂ T₁ T₂ : Extension A B}
    (hS : Isomorphic S₁ S₂) (hT : Isomorphic T₁ T₂) :
    Isomorphic (baerSum S₁ T₁) (baerSum S₂ T₂) := by
  sorry

end Operations

end Extension

namespace ExtensionClass

section Operations

variable {A' B' : C}

/-- Pullback on extension classes. -/
noncomputable def pullback (u : B' ⟶ B) : ExtensionClass A B → ExtensionClass A B' :=
  _root_.Quotient.map (Extension.pullback u) fun _ _ h ↦ Extension.Isomorphic.pullback u h

/-- Pushout on extension classes. -/
noncomputable def pushout (a : A ⟶ A') : ExtensionClass A B → ExtensionClass A' B :=
  _root_.Quotient.map (Extension.pushout a) fun _ _ h ↦ Extension.Isomorphic.pushout a h

/-- The split extension class. -/
noncomputable def zero (A B : C) : ExtensionClass A B :=
  ⟦Extension.split A B⟧

/-- Negation on extension classes. -/
noncomputable def neg : ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map Extension.neg fun _ _ h ↦ Extension.Isomorphic.neg h

/-- The Baer sum on extension classes. -/
noncomputable def baerSum : ExtensionClass A B → ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map₂ Extension.baerSum fun _ _ h₁ _ _ h₂ ↦ Extension.Isomorphic.baerSum h₁ h₂

noncomputable instance : Zero (ExtensionClass A B) := ⟨zero A B⟩

noncomputable instance : Neg (ExtensionClass A B) := ⟨neg⟩

noncomputable instance : Add (ExtensionClass A B) := ⟨baerSum⟩

end Operations

end ExtensionClass
end CategoryTheory

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A B : C}

namespace CategoryTheory
namespace Extension

variable {S T : Extension A B}

theorem shortExact_extClass_eq_of_isomorphic (h : Isomorphic S T) :
    S.shortExact.extClass = T.shortExact.extClass := by
  rcases h with ⟨e, hf, hg⟩
  let i : S.toShortComplex ≅ T.toShortComplex :=
    ShortComplex.isoMk (Iso.refl A) e (Iso.refl B) (by simpa using hf.symm) (by simpa using hg)
  simpa [i] using
    (ShortComplex.ShortExact.extClass_naturality S.shortExact T.shortExact i.hom)

end Extension

namespace ExtensionClass

section ExtBridge

variable {A' B' : C}

/-- The canonical bridge from source-facing extension classes to the owner object `Ext¹(B, A)`. -/
noncomputable def toExt : ExtensionClass A B → Ext B A 1 :=
  _root_.Quotient.lift (fun S ↦ S.shortExact.extClass) fun _ _ h ↦
    Extension.shortExact_extClass_eq_of_isomorphic h

theorem toExt_pullback (u : B' ⟶ B) (ξ : ExtensionClass A B) :
    toExt (pullback u ξ) = (Ext.mk₀ u).precomp A (zero_add 1) (toExt ξ) := by
  sorry

theorem toExt_pushout (a : A ⟶ A') (ξ : ExtensionClass A B) :
    toExt (pushout a ξ) = (Ext.mk₀ a).postcomp B (add_zero 1) (toExt ξ) := by
  sorry

theorem toExt_zero : toExt (0 : ExtensionClass A B) = 0 := by
  sorry

theorem toExt_neg (ξ : ExtensionClass A B) : toExt (-ξ) = -toExt ξ := by
  sorry

theorem toExt_baerSum (ξ η : ExtensionClass A B) :
    toExt (baerSum ξ η) = toExt ξ + toExt η := by
  sorry

theorem toExt_add (ξ η : ExtensionClass A B) : toExt (ξ + η) = toExt ξ + toExt η := by
  sorry

end ExtBridge

end ExtensionClass
end CategoryTheory

end

/-! ### Lemma_12_6_3 (from Chap12) -/
universe w v u

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

namespace CategoryTheory
namespace ExtensionClass

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' B B' : C}

/-
Domain triage: this item lies in the abelian-category `Ext¹` classification domain for short exact
sequences.

Sampled owner-style declarations:
* `inferInstance : AddCommGroup (Ext B A 1)`
* `(Ext.mk₀ u).precomp A (zero_add 1) : Ext B A 1 →+ Ext B' A 1`
* `(Ext.mk₀ a).postcomp B (add_zero 1) : Ext B A 1 →+ Ext B A' 1`
* `ExtensionClass.toExt_add`, `ExtensionClass.toExt_pullback`, and `ExtensionClass.toExt_pushout`

Layering for this item:
* source-facing: `ExtensionClass A B` with Baer sum, split extension, pullback, and pushout;
* core/canonical: `Ext B A 1` with its additive structure and first/second-variable maps;
* bridge/view: `ExtensionClass.toExt`.

This file targets the `source-facing` layer: it upgrades the source-facing operations to the
commutative-group and additive-functorial structure stated in Lemma 12.6.3, while reusing the
canonical owner `Ext¹` through `toExt`.
-/

noncomputable instance : Sub (ExtensionClass A B) where
  sub ξ η := ξ + -η

noncomputable instance : SMul ℕ (ExtensionClass A B) where
  smul n ξ := nsmulRec n ξ

noncomputable instance : SMul ℤ (ExtensionClass A B) where
  smul := zsmulRec nsmulRec

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A A' B B' : C}

@[simp] theorem toExt_sub (ξ η : ExtensionClass A B) : toExt (ξ - η) = toExt ξ - toExt η := by
  change toExt (ξ + -η) = toExt ξ - toExt η
  simp [sub_eq_add_neg, toExt_add, toExt_neg]

@[simp] theorem toExt_nsmul (ξ : ExtensionClass A B) (n : ℕ) : toExt (n • ξ) = n • toExt ξ := by
  induction n with
  | zero =>
      change toExt 0 = 0 • toExt ξ
      rw [zero_nsmul]
      exact toExt_zero
  | succ n ih =>
      change toExt (nsmulRec n ξ + ξ) = (n + 1) • toExt ξ
      rw [toExt_add, succ_nsmul]
      simpa [HSMul.hSMul] using congrArg (fun x ↦ x + toExt ξ) ih

@[simp] theorem toExt_zsmul (ξ : ExtensionClass A B) (n : ℤ) : toExt (n • ξ) = n • toExt ξ := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact toExt_nsmul ξ n
  | negSucc n =>
      change toExt (-(nsmulRec (n + 1) ξ)) = (Int.negSucc n) • toExt ξ
      rw [toExt_neg, negSucc_zsmul]
      simpa [HSMul.hSMul] using congrArg Neg.neg (toExt_nsmul ξ (n + 1))

/-- The canonical comparison map from source-facing extension classes to `Ext¹` is bijective. -/
theorem toExt_bijective :
    Function.Bijective (toExt : ExtensionClass A B → Ext B A 1) := by
  sorry

/-- The categorical extension group `ExtensionClass A B` is canonically identified with
`Ext¹(B, A)`. -/
noncomputable def toExtAddEquiv : ExtensionClass A B ≃+ Ext B A 1 :=
  { toEquiv := Equiv.ofBijective (toExt : ExtensionClass A B → Ext B A 1) toExt_bijective
    map_add' := toExt_add }

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' B B' : C}

/-- Lemma 12.6.3: Baer sum gives the source-facing extension classes a commutative group law. -/
noncomputable instance : AddCommGroup (ExtensionClass A B) :=
  letI : HasExt.{max u v} C := HasExt.standard C
  Function.Injective.addCommGroup toExt toExt_bijective.injective toExt_zero toExt_add toExt_neg
    toExt_sub toExt_nsmul toExt_zsmul

/-- Pullback of extension classes along a morphism in the right endpoint is additive. -/
noncomputable def pullbackAddHom (u : B' ⟶ B) : ExtensionClass A B →+ ExtensionClass A B' :=
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B ≃+ Ext B A 1 := toExtAddEquiv
  let e' : ExtensionClass A B' ≃+ Ext B' A 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B' A 1 := (Ext.mk₀ u).precomp A (zero_add 1)
  (e'.symm : Ext B' A 1 →+ ExtensionClass A B').comp (f.comp (e : ExtensionClass A B →+ Ext B A 1))

/-- Pushout of extension classes along a morphism in the left endpoint is additive. -/
noncomputable def pushoutAddHom (a : A ⟶ A') : ExtensionClass A B →+ ExtensionClass A' B :=
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B ≃+ Ext B A 1 := toExtAddEquiv
  let e' : ExtensionClass A' B ≃+ Ext B A' 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B A' 1 := (Ext.mk₀ a).postcomp B (add_zero 1)
  (e'.symm : Ext B A' 1 →+ ExtensionClass A' B).comp (f.comp (e : ExtensionClass A B →+ Ext B A 1))

@[simp] theorem pullbackAddHom_apply (u : B' ⟶ B) (ξ : ExtensionClass A B) :
    pullbackAddHom u ξ = pullback u ξ := by
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A B' ≃+ Ext B' A 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B' A 1 := (Ext.mk₀ u).precomp A (zero_add 1)
  apply toExt_bijective.injective
  rw [toExt_pullback]
  change e (e.symm (f (toExt ξ))) = f (toExt ξ)
  exact e.apply_symm_apply (f (toExt ξ))

@[simp] theorem pushoutAddHom_apply (a : A ⟶ A') (ξ : ExtensionClass A B) :
    pushoutAddHom a ξ = pushout a ξ := by
  letI : HasExt.{max u v} C := HasExt.standard C
  let e : ExtensionClass A' B ≃+ Ext B A' 1 := toExtAddEquiv
  let f : Ext B A 1 →+ Ext B A' 1 := (Ext.mk₀ a).postcomp B (add_zero 1)
  apply toExt_bijective.injective
  rw [toExt_pushout]
  change e (e.symm (f (toExt ξ))) = f (toExt ξ)
  exact e.apply_symm_apply (f (toExt ξ))

@[simp] theorem pullback_zero (u : B' ⟶ B) :
    pullback u (0 : ExtensionClass A B) = 0 := by
  rw [← pullbackAddHom_apply]
  exact (pullbackAddHom u).map_zero

@[simp] theorem pullback_add (u : B' ⟶ B) (ξ η : ExtensionClass A B) :
    pullback u (ξ + η) = pullback u ξ + pullback u η := by
  rw [← pullbackAddHom_apply, ← pullbackAddHom_apply, ← pullbackAddHom_apply]
  exact (pullbackAddHom u).map_add ξ η

@[simp] theorem pushout_zero (a : A ⟶ A') :
    pushout a (0 : ExtensionClass A B) = 0 := by
  rw [← pushoutAddHom_apply]
  exact (pushoutAddHom a).map_zero

@[simp] theorem pushout_add (a : A ⟶ A') (ξ η : ExtensionClass A B) :
    pushout a (ξ + η) = pushout a ξ + pushout a η := by
  rw [← pushoutAddHom_apply, ← pushoutAddHom_apply, ← pushoutAddHom_apply]
  exact (pushoutAddHom a).map_add ξ η

end

end ExtensionClass
end CategoryTheory

/-! ### Lemma_12_6_4 (from Chap12) -/
namespace CategoryTheory.Abelian.Ext

/- Domain triage: this item lies in the abelian-category `Ext` exact-sequence domain.
Sampled owner-style declarations: `contravariantSequence`, `contravariantSequence_exact`,
`covariantSequence`, `covariantSequence_exact`, `mono_precomp_mk₀_of_epi`,
`mono_postcomp_mk₀_of_mono`, and `addEquiv₀`.

Layering for this item:
* source-facing: the textbook degree-`0`/`1` six-term exact sequences attached to a short exact
  sequence in an abelian category and a fixed object in the remaining `Ext` variable;
* core/canonical owner: the mathlib exactness theorems `contravariantSequence_exact` and
  `covariantSequence_exact`, together with the packaged long exact sequences
  `contravariantSequence` and `covariantSequence`;
* bridge/view: the degree-`0` monomorphism lemmas `mono_precomp_mk₀_of_epi` and
  `mono_postcomp_mk₀_of_mono`, and the canonical identification `addEquiv₀ : Ext⁰ ≃ Hom`.

Primitive data: a short exact sequence in an abelian category and the fixed object in the
remaining `Ext` variable.
Derived API: the long exact `Ext` sequences, their exactness theorems, the leading degree-`0`
monomorphisms, and the identification `Ext⁰ ≃ Hom`.

No local wrapper API is needed: the textbook six-term displays are the initial segments of these
canonical long exact sequences, so the correct refinement is direct recall of the owner
declarations rather than a parallel local sequence package. -/

/- Lemma 12.6.4 (1): for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in an abelian category
and any object `N`, the contravariant `Ext` groups form the canonical long exact sequence. The
textbook six-term display is its degree-`0` and degree-`1` initial segment, with the leading
`0 ⟶ Hom(M₃, N)` supplied by monicity of the degree-`0` map and the identification
`Ext⁰(Mᵢ, N) ≅ Hom(Mᵢ, N)`. -/
recall contravariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`contravariantSequence`. -/
recall contravariantSequence

/- Companion recall: the first degree-`0` map in the contravariant sequence is monic, giving the
leading `0 ⟶ Hom(M₃, N)` in the textbook six-term sequence. -/
recall mono_precomp_mk₀_of_epi

/- Lemma 12.6.4 (2): for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` in an abelian category
and any object `N`, the covariant `Ext` groups form the canonical long exact sequence. The
textbook six-term display is its degree-`0` and degree-`1` initial segment, with the leading
`0 ⟶ Hom(N, M₁)` supplied by monicity of the degree-`0` map and the identification
`Ext⁰(N, Mᵢ) ≅ Hom(N, Mᵢ)`. -/
recall covariantSequence_exact

/- Companion recall: the long exact sequence itself is packaged by the owner declaration
`covariantSequence`. -/
recall covariantSequence

/- Companion recall: the first degree-`0` map in the covariant sequence is monic, giving the
leading `0 ⟶ Hom(N, M₁)` in the textbook six-term sequence. -/
recall mono_postcomp_mk₀_of_mono

/- Companion recall: degree `0` `Ext` is canonically identified with morphisms by `addEquiv₀`. -/
recall addEquiv₀

end CategoryTheory.Abelian.Ext
