import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cochain
open CochainComplex.HomComplex.Cocycle

universe v u

noncomputable section

variable {ι : Type*} {c : ComplexShape ι}
variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {K L : HomologicalComplex D c} {f g : K ⟶ L}

/-- Translating by a fixed homotopy `h : Homotopy f g` identifies the homotopies from `f` to `g`
with the self-homotopies of `f`. -/
private def homotopyEquivSelf (h : Homotopy f g) : Homotopy f g ≃ Homotopy f f where
  toFun k := k.trans h.symm
  invFun k := k.trans h
  left_inv k := by
    ext i j
    simp [Homotopy.trans, Homotopy.symm, add_assoc]
  right_inv k := by
    ext i j
    simp [Homotopy.trans, Homotopy.symm, add_assoc]

/-- If self-homotopies of `a` are identified with a type `α`, then the homotopies from `a` to `b`
are either empty or identified with `α` after choosing one homotopy `a ⟶ b`. -/
theorem homotopy_isEmpty_or_nonempty_equiv {A B : HomologicalComplex D c} (a b : A ⟶ B)
    {α : Type*} (e : Homotopy a a ≃ α) :
    IsEmpty (Homotopy a b) ∨ Nonempty (Homotopy a b ≃ α) := by
  by_cases h : Nonempty (Homotopy a b)
  · right
    rcases h with ⟨h⟩
    exact ⟨(homotopyEquivSelf h).trans e⟩
  · left
    exact ⟨fun k ↦ h ⟨k⟩⟩

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : CochainComplex C ℤ}

/- Source/core/bridge triage:
- primary domain: homotopies of cochain-complex maps and the associated hom-complex.
- core/canonical owner declarations:
  `homotopyEquivSelf`,
  `homotopy_isEmpty_or_nonempty_equiv`,
  `Homotopy.equivSubZero`,
  `Cochain.equivHomotopy`,
  `Cocycle.equivHomShift`.
- target items here: bridge/view declarations packaging that owner chain into the source-facing
  bijection between homotopies and morphisms into the `(-1)`-shift.

Primitive data:
- a homotopy `h : Homotopy a b`,
- the owner hom-complex cochain and cocycle descriptions.

Derived API:
- `cochainComplex_self_homotopy_equiv_hom_to_shift`,
- `cochainComplex_homotopyTranslateToShiftNegOne`,
- `homotopy_isEmpty_or_exists_shiftNegOne_bijection`.
-/
private noncomputable def zeroHomotopyEquivCocycle :
    Homotopy (0 : A ⟶ B) 0 ≃ Cocycle A B (-1) :=
  (Cochain.equivHomotopy (0 : A ⟶ B) 0).trans <|
    Equiv.subtypeEquivRight fun z ↦ by
      rw [Cocycle.mem_iff (-1) 0 (neg_add_cancel 1) z]
      simp
      simpa using (eq_comm : 0 = δ (-1) 0 z ↔ δ (-1) 0 z = 0)

/-- Lemma 12.14.9: for a cochain map `a : A^• ⟶ B^•`, self-homotopies of `a` are in bijection
with morphisms `A^• ⟶ B^•[-1]`. -/
@[stacks 011I]
noncomputable def cochainComplex_self_homotopy_equiv_hom_to_shift (a : A ⟶ B) :
    Homotopy a a ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  Homotopy.equivSubZero.trans <|
    by simpa using zeroHomotopyEquivCocycle.trans equivHomShift.symm.toEquiv

-- Proof sketch: use `cochainComplex_self_homotopy_equiv_hom_to_shift` to transport the additive
-- group structure on `A ⟶ B⟦(-1 : ℤ)⟧` to self-homotopies of `a`, and let these act on
-- `Homotopy a b` by composition with a chosen homotopy.
/-- Translating by a chosen homotopy `h : Homotopy a b` sends any other homotopy from `a` to `b`
to the corresponding morphism `A^• ⟶ B^•[-1]`. -/
private noncomputable def cochainComplex_homotopyTranslateToShiftNegOne {a b : A ⟶ B}
    (h : Homotopy a b) :
    Homotopy a b ≃ (A ⟶ B⟦(-1 : ℤ)⟧) :=
  (homotopyEquivSelf h).trans (cochainComplex_self_homotopy_equiv_hom_to_shift a)

-- Proof sketch: if `Homotopy a b` is empty we are done. Otherwise choose a homotopy `h : Homotopy
-- a b`; translation by `h` gives the required bijection with `A ⟶ B⟦-1⟧`, which is the
-- principal-homogeneous-space description of the nonempty case without packaging it as
-- existential torsor data.
/-- Companion statement: for cochain maps `a, b : A^• ⟶ B^•`, the homotopies from `a` to `b` are
either empty or nonempty together with an induced equivalence to the morphisms
`A^• ⟶ B^•[-1]`. -/
theorem homotopy_isEmpty_or_exists_shiftNegOne_bijection (a b : A ⟶ B) :
    IsEmpty (Homotopy a b) ∨
      Nonempty (Homotopy a b ≃ (A ⟶ B⟦(-1 : ℤ)⟧)) := by
  simpa [cochainComplex_homotopyTranslateToShiftNegOne] using
    homotopy_isEmpty_or_nonempty_equiv a b
      (cochainComplex_self_homotopy_equiv_hom_to_shift a)
