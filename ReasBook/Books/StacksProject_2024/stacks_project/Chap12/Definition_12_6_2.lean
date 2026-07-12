import Mathlib
import StacksProject_2024.Chap12.Definition_12_6_1

-- Declarations for this item will be appended below by the statement pipeline.

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

noncomputable abbrev extClass (S : Extension A B) : Ext B A 1 :=
  S.shortExact.extClass

theorem shortExact_extClass_eq_of_isomorphic (h : Isomorphic S T) :
    S.extClass = T.extClass := by
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
  _root_.Quotient.lift (fun S ↦ S.extClass) fun _ _ h ↦
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
