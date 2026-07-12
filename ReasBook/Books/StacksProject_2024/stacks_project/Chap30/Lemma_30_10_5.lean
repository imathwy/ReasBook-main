import Mathlib
import StacksProject_2024.Chap30.Lemma_30_10_3_Artin_Rees

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

-- Semantic recall: `lean_leansearch` found the canonical owners
-- `Scheme.Modules.restrict`, `Scheme.IdealSheafData.subscheme`, and
-- `Scheme.Modules.Hom`. Local Chapter 30 precedent models powers of an ideal sheaf acting on a
-- module by affine-open section submodules, so the global `I^n𝒢` terms below are explicit
-- descending subobjects characterized by that affine-open API.

/-- The open complement `X \ Z` of the closed subset cut out by an ideal sheaf datum. -/
abbrev idealSheafOpenComplement {X : Scheme.{u}} (I : X.IdealSheafData) : X.Opens where
  carrier := (I.support : Set X)ᶜ
  is_open' := I.support.2.isOpen_compl

/-- Membership in the open complement of the support of an ideal sheaf datum. -/
theorem mem_idealSheafOpenComplement {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    x ∈ idealSheafOpenComplement I ↔ x ∉ (I.support : Set X) := sorry

/-- Lemma 30.10.5 (1): for a Noetherian scheme `X`, a quasi-coherent module `ℱ`, a coherent
module `𝒢`, and a quasi-coherent ideal sheaf datum `I`, the filtered colimit of
`Hom_{\mathcal O_X}(I^n𝒢, ℱ)` is isomorphic to
`Hom_{\mathcal O_U}(𝒢|_U, ℱ|_U)` for `U = X \ support(I)`, where the powers `I^n𝒢` are
represented by the canonical subobject family `idealPowerProductSubobject I 𝒢 n`. -/
@[stacks 01YB]
theorem colimit_hom_idealPowerProductSubobjects_iso_restrict
    [IsNoetherian X]
    (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsCoherent]
    (I : X.IdealSheafData) :
    Nonempty
      (colimit
        (Functor.ofSequence
          (fun n (φ : (idealPowerProductSubobject I 𝒢 n : X.Modules) ⟶ ℱ) ↦
            Subobject.ofLE
                (idealPowerProductSubobject I 𝒢 (n + 1))
                (idealPowerProductSubobject I 𝒢 n)
                (idealPowerProductSubobject_antitone I 𝒢 n) ≫
              φ)) ≅
        (((Scheme.Modules.restrictFunctor (idealSheafOpenComplement I).ι).obj 𝒢) ⟶
          ((Scheme.Modules.restrictFunctor (idealSheafOpenComplement I).ι).obj ℱ))) := sorry

/-- Lemma 30.10.5 (2): in the same setup, the special case `𝒢 = \mathcal O_X` gives an
isomorphism from the filtered colimit of `Hom_{\mathcal O_X}(I^n, ℱ)` to the sections
`Γ(U, ℱ)`, where `U = X \ support(I)`. The powers `I^n \subset \mathcal O_X` are represented by
the canonical family `idealPowerSubobject I n`. -/
@[stacks 01YB]
theorem colimit_hom_idealPowerSubobjects_iso_sections
    [IsNoetherian X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData) :
    Nonempty
      (colimit
        ((Functor.ofSequence
          (fun n (φ : (Subobject.underlying.obj (idealPowerSubobject I n)) ⟶ ℱ) ↦
            Subobject.ofLE
                (idealPowerSubobject I (n + 1))
                (idealPowerSubobject I n)
                (idealPowerSubobject_antitone I n) ≫
              φ)) : ℕ ⥤ Type u) ≅
        Γ(ℱ, idealSheafOpenComplement I)) := sorry

end AlgebraicGeometry.Scheme.Modules
