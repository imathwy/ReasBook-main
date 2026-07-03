import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Definition_12_14_2
import StacksProject_2024.Chap12.Lemma_12_14_4
import StacksProject_2024.Chap12.Lemma_12_14_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex ChainComplex

universe v u

noncomputable section

variable {V : Type u} [Category.{v} V] [Preadditive V]

/- Source/core/bridge triage:
- source-facing:
  `chainComplex_self_homotopy_equiv_hom_to_shift`.
- core/canonical owner declarations in this domain:
  `CategoryTheory.Functor.mapHomotopy`,
  `ChainComplex.chainToCochain V`,
  `cochainComplex_self_homotopy_equiv_hom_to_shift` from `Lemma_12_14_9`,
  and the ambient equivalence `cochainComplexEquivalence V`.
- target item here: a chain-complex bridge/view obtained by transporting those owner
  equivalences across `cochainComplexEquivalence V`.

Primitive data:
- the canonical bridge `ChainComplex.chainToCochain V`,
- the induced entrywise transport of homotopies across that equivalence,
- the induced equivalence on shifted morphisms from full faithfulness and the canonical
  commutation isomorphism `((ChainComplex.chainToCochain V).commShiftIso (1)).app B`.

Derived API:
- `homotopyEquivSelf`,
- `homotopy_isEmpty_or_nonempty_equiv`,
- `chainToCochainHomotopyEquiv`,
- `chainComplex_self_homotopy_equiv_hom_to_shift`,
- `chainComplex_homotopy_isEmpty_or_exists_hom_to_shift_bijection`.
-/

/- Bridge/view owner: `chainToCochain V` transports homotopies in both directions. -/
def chainToCochainHomotopyEquiv {A B : ChainComplex V ℤ} {a b : A ⟶ B} :
    Homotopy a b ≃
      Homotopy ((chainToCochain V).map a) ((chainToCochain V).map b) where
  toFun h := by
    refine
      { hom := fun p q ↦ h.hom (-p) (-q)
        zero := ?_
        comm := ?_ }
    · intro p q hpq
      rw [h.zero (-p) (-q)]
      · rfl
      · dsimp at hpq ⊢
        lia
    · intro n
      sorry
  invFun h := by
    refine
      { hom := fun i j ↦
          (A.XIsoOfEq (by simp)).hom ≫ h.hom (-i) (-j) ≫ (B.XIsoOfEq (by simp)).hom
        zero := ?_
        comm := ?_ }
    · intro i j hij
      rw [h.zero (-i) (-j)]
      · sorry
      · dsimp at hij ⊢
        lia
    · intro n
      sorry
  left_inv h := by
    sorry
  right_inv h := by
    sorry

variable {A B : ChainComplex V ℤ}

/- Bridge/view owner: under `chainToCochain V`, a morphism into the cochain `[-1]` shift is
exactly a morphism into the chain `[1]`-shift. -/
private noncomputable abbrev chainToCochainShiftHomEquiv (A B : ChainComplex V ℤ) :
    (((cochainComplexEquivalence V).functor.obj A) ⟶
      ((cochainComplexEquivalence V).functor.obj B)⟦(-1 : ℤ)⟧) ≃
        (A ⟶ B⟦(1 : ℤ)⟧) :=
  let F := chainToCochain V
  let e :
      (cochainComplexEquivalence V).functor.obj (B⟦(1 : ℤ)⟧) ≅
        ((cochainComplexEquivalence V).functor.obj B)⟦(-1 : ℤ)⟧ :=
    (show F.obj (B⟦(1 : ℤ)⟧) ≅
        ((shiftFunctor (PullbackShift (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ))
          (1 : ℤ)).obj (F.obj B)) from
        (F.commShiftIso (1 : ℤ)).app B) ≪≫
      (pullbackShiftIso (CochainComplex V ℤ) (negAddMonoidHom : ℤ →+ ℤ) (1 : ℤ) (-1 : ℤ)
        (by simp)).app (F.obj B)
  (((cochainComplexEquivalence V).fullyFaithfulFunctor.homEquiv).trans
    ((Iso.refl _).homCongr e)).symm

/-- Lemma 12.14.3: for a chain map `a : A_• ⟶ B_•`, there is a bijection between the
self-homotopies of `a` and the morphisms `A_• ⟶ B[1]_•`. -/
noncomputable def chainComplex_self_homotopy_equiv_hom_to_shift (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(1 : ℤ)⟧) :=
  chainToCochainHomotopyEquiv.trans
    ((cochainComplex_self_homotopy_equiv_hom_to_shift
        ((chainToCochain V).map a)).trans
      (chainToCochainShiftHomEquiv A B))

-- Proof sketch: if `Homotopy a b` is empty we are done. Otherwise choose a homotopy
-- `h : Homotopy a b`; translating by `h` with `homotopyEquivSelf h` and then applying
-- `chainComplex_self_homotopy_equiv_hom_to_shift a` gives the required bijection with
-- `A_• ⟶ B[1]_•`.
/-- Lemma 12.14.3: for chain maps `a, b : A_• ⟶ B_•`, the homotopies from `a` to `b` are either
empty or nonempty together with an induced equivalence to the morphisms `A_• ⟶ B[1]_•`. -/
theorem chainComplex_homotopy_isEmpty_or_exists_hom_to_shift_bijection (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (Homotopy a b ≃ (A ⟶ B⟦(1 : ℤ)⟧)) := by
  simpa using homotopy_isEmpty_or_nonempty_equiv a b
    (chainComplex_self_homotopy_equiv_hom_to_shift a)
