import Mathlib
import StacksProject_2024.Chap12.Definition_12_6_2

-- Declarations for this item will be appended below by the statement pipeline.

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
