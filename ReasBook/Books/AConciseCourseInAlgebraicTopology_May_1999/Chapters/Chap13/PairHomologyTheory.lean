import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra

universe u

open SpacePair

-- Semantic recall via `lean_leansearch` and local precedent from Chapters 14 and 19:
-- `SpacePair` and its weak-equivalence owner now live in `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.SpacePair`.
-- This file builds the Chapter 13 homology-theory owner on top of that canonical pair API.

/-- A graded homology theory on pairs of spaces with coefficients in `π`, formalized on the
Chapter 13 category `SpacePair` with its canonical weak-equivalence owner
`spacePairWeakEquivalences`. The underlying graded functors and connecting morphisms are explicit
data; the five Eilenberg-Steenrod-style axioms are recorded as fields of the structure. -/
structure PairHomologyTheory (π : Type u) [AddCommGroup π] where
  homology : ℤ → SpacePair.{u} ⥤ ModuleCat.{u} ℤ
  boundary (q : ℤ) : homology q ⟶ subspaceFunctor ⋙ homology (q - 1)
  dimensionZero :
    Nonempty ((homology 0).obj point ≅ ModuleCat.of ℤ π)
  dimensionHigher (q : ℤ) (hq : q ≠ 0) : IsZero ((homology q).obj point)
  exact₁_zero (q : ℤ) (P : SpacePair.{u}) :
    ((homology q).map (subspaceInclusion P)) ≫ ((homology q).map (absoluteToRelative P)) = 0
  exact₁ (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((homology q).map (subspaceInclusion P))
      ((homology q).map (absoluteToRelative P))
      (exact₁_zero q P)).Exact
  exact₂_zero (q : ℤ) (P : SpacePair.{u}) :
    ((homology q).map (absoluteToRelative P)) ≫ ((boundary q).app P) = 0
  exact₂ (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((homology q).map (absoluteToRelative P))
      ((boundary q).app P)
      (exact₂_zero q P)).Exact
  exact₃_zero (q : ℤ) (P : SpacePair.{u}) :
    ((boundary q).app P) ≫ ((homology (q - 1)).map (subspaceInclusion P)) = 0
  exact₃ (q : ℤ) (P : SpacePair.{u}) :
    (CategoryTheory.ShortComplex.mk
      ((boundary q).app P)
      ((homology (q - 1)).map (subspaceInclusion P))
      (exact₃_zero q P)).Exact
  excision (q : ℤ) (P : SpacePair.{u}) (U : Set P.space)
      (hU : closure U ⊆ interior P.subspace) :
      IsIso ((homology q).map (removeSubsetInclusion P U))
  additivity {ι : Type u} (q : ℤ) (P : ι → SpacePair.{u}) :
    Nonempty (((homology q).obj (sigmaPair P)) ≅ ∐ fun i : ι ↦ (homology q).obj (P i))
  weakEquivalenceInvariant (q : ℤ) {P Q : SpacePair.{u}} (f : P ⟶ Q) [WeakEquivalence f] :
    IsIso ((homology q).map f)

/-- A `PairHomologyTheory` can be used as its underlying graded covariant functor. -/
instance {π : Type u} [AddCommGroup π] :
    CoeFun (PairHomologyTheory π) (fun _ ↦ ℤ → SpacePair.{u} ⥤ ModuleCat.{u} ℤ) where
  coe H := H.homology

namespace PairHomologyTheory

variable {π : Type u} [AddCommGroup π]

/-- An isomorphism of homology theories is a graded natural isomorphism compatible with the
connecting morphisms. -/
structure Iso (H K : PairHomologyTheory π) where
  app (q : ℤ) : H.homology q ≅ K.homology q
  boundary_comm (q : ℤ) :
    H.boundary q ≫ Functor.whiskerLeft subspaceFunctor (app (q - 1)).hom =
      (app q).hom ≫ K.boundary q

namespace Iso

/-- Helper for Theorem 13.1.1: the identity comparison satisfies the boundary compatibility
condition degreewise. -/
theorem refl_boundary_comm (H : PairHomologyTheory π) (q : ℤ) :
    H.boundary q ≫
        Functor.whiskerLeft subspaceFunctor
          (CategoryTheory.Iso.refl (H.homology (q - 1))).hom =
      (CategoryTheory.Iso.refl (H.homology q)).hom ≫ H.boundary q := by
  -- The identity comparison leaves the boundary natural transformation unchanged.
  simp

/-- Helper for Theorem 13.1.1: every pair homology theory is canonically isomorphic to itself by
the degreewise identity isomorphisms, with boundary compatibility supplied by
`refl_boundary_comm`. -/
def refl (H : PairHomologyTheory π) : PairHomologyTheory.Iso H H :=
  { app := fun q ↦ CategoryTheory.Iso.refl (H.homology q)
    boundary_comm := refl_boundary_comm H }

/-- Helper for Theorem 13.1.1: inverting a comparison also inverts the boundary square after
postcomposing and precomposing with the inverse degreewise isomorphisms. -/
theorem symm_boundary_comm {H K : PairHomologyTheory π} (i : PairHomologyTheory.Iso H K)
    (q : ℤ) :
    K.boundary q ≫ Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)).symm).hom =
      ((i.app q).symm).hom ≫ H.boundary q := by
  ext P x
  -- First postcompose the original square with the inverse restricted comparison.
  have hPost :
      (H.boundary q).app P =
        (i.app q).hom.app P ≫ (K.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)).symm).hom).app P := by
    have h := congrArg
      (fun m ↦
        m ≫ (Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)).symm).hom).app P)
      (NatTrans.congr_app (i.boundary_comm q) P)
    simpa [Category.assoc] using h
  -- Then precompose with the inverse in degree `q` to isolate the reversed square.
  have hCancel :
      (i.app q).inv.app P ≫ (H.boundary q).app P =
        (K.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)).symm).hom).app P := by
    have h := congrArg (fun m ↦ (i.app q).inv.app P ≫ m) hPost
    simpa [Category.assoc] using h
  simpa using congrArg (fun f ↦ f x) hCancel.symm

/-- Helper for Theorem 13.1.1: an isomorphism of pair homology theories can be reversed by
inverting its degreewise natural isomorphisms, with boundary compatibility supplied by
`symm_boundary_comm`. -/
def symm {H K : PairHomologyTheory π} (i : PairHomologyTheory.Iso H K) :
    PairHomologyTheory.Iso K H :=
  { app := fun q ↦ (i.app q).symm
    boundary_comm := symm_boundary_comm i }

/-- Helper for Theorem 13.1.1: composing two comparison squares yields the boundary square for
the degreewise composite isomorphism. -/
theorem trans_boundary_comm {H K L : PairHomologyTheory π} (i : PairHomologyTheory.Iso H K)
    (j : PairHomologyTheory.Iso K L) (q : ℤ) :
    H.boundary q ≫
        Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)) ≪≫ (j.app (q - 1))).hom =
      ((i.app q ≪≫ j.app q).hom) ≫ L.boundary q := by
  ext P x
  -- Rewrite the first comparison square, then splice in the second one.
  have hi :
      (H.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor (i.app (q - 1)).hom).app P =
        (i.app q).hom.app P ≫ (K.boundary q).app P := by
    simpa using NatTrans.congr_app (i.boundary_comm q) P
  have hj :
      (K.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor (j.app (q - 1)).hom).app P =
        (j.app q).hom.app P ≫ (L.boundary q).app P := by
    simpa using NatTrans.congr_app (j.boundary_comm q) P
  have hComp :
      (H.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)) ≪≫ (j.app (q - 1))).hom).app P =
        ((i.app q ≪≫ j.app q).hom.app P) ≫ (L.boundary q).app P := by
    calc
      (H.boundary q).app P ≫
          (Functor.whiskerLeft subspaceFunctor ((i.app (q - 1)) ≪≫ (j.app (q - 1))).hom).app P
        =
          ((H.boundary q).app P ≫
              (Functor.whiskerLeft subspaceFunctor (i.app (q - 1)).hom).app P) ≫
            (Functor.whiskerLeft subspaceFunctor (j.app (q - 1)).hom).app P := by
              simp [Category.assoc]
      _ =
          ((i.app q).hom.app P ≫ (K.boundary q).app P) ≫
            (Functor.whiskerLeft subspaceFunctor (j.app (q - 1)).hom).app P := by
              rw [hi]
      _ =
          (i.app q).hom.app P ≫
            ((K.boundary q).app P ≫
              (Functor.whiskerLeft subspaceFunctor (j.app (q - 1)).hom).app P) := by
                simp [Category.assoc]
      _ = (i.app q).hom.app P ≫ ((j.app q).hom.app P ≫ (L.boundary q).app P) := by
            rw [hj]
      _ = ((i.app q ≪≫ j.app q).hom.app P) ≫ (L.boundary q).app P := by
            simp [Category.assoc]
  simpa using congrArg (fun f ↦ f x) hComp

/-- Helper for Theorem 13.1.1: pair-homology-theory isomorphisms compose degreewise, with
boundary compatibility supplied by `trans_boundary_comm`. -/
def trans {H K L : PairHomologyTheory π} (i : PairHomologyTheory.Iso H K)
    (j : PairHomologyTheory.Iso K L) : PairHomologyTheory.Iso H L :=
  { app := fun q ↦ i.app q ≪≫ j.app q
    boundary_comm := trans_boundary_comm i j }

/-- Helper for Theorem 13.1.1: the identity comparison supplies a witness that any pair
homology theory is isomorphic to itself. -/
theorem nonempty_refl (H : PairHomologyTheory π) : Nonempty (PairHomologyTheory.Iso H H) := by
  -- Package the canonical identity comparison as the required witness.
  exact ⟨refl H⟩

/-- Helper for Theorem 13.1.1: reversing a comparison turns any witness `H ≅ K` into a witness
`K ≅ H`. -/
theorem nonempty_symm {H K : PairHomologyTheory π} :
    Nonempty (PairHomologyTheory.Iso H K) → Nonempty (PairHomologyTheory.Iso K H) := by
  -- Extract the original comparison and invert it degreewise.
  rintro ⟨i⟩
  exact ⟨symm i⟩

/-- Helper for Theorem 13.1.1: pair-homology-theory comparisons compose, so an intermediate owner
can be used to transfer uniqueness from one theory to another. -/
theorem nonempty_trans {H K L : PairHomologyTheory π} :
    Nonempty (PairHomologyTheory.Iso H K) →
      Nonempty (PairHomologyTheory.Iso K L) →
      Nonempty (PairHomologyTheory.Iso H L) := by
  -- Extract both comparisons and compose their degreewise isomorphisms.
  rintro ⟨i⟩ ⟨j⟩
  exact ⟨trans i j⟩

end Iso

end PairHomologyTheory
