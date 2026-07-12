import Mathlib
import Mathlib.CategoryTheory.Monoidal.End

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling:
- primary domain: simplicial endofunctor constructions from an endofunctor equipped with maps to
  the identity and to its self-composite;
- sampled owner declarations:
  `Nat.iterate`,
  `Functor.isoWhiskerRight`,
  `Functor.associator`,
  `Functor.leftUnitor`,
  `Functor.rightUnitor`;
- best owner abstraction: the source-facing recursive family `iteratedEndofunctor Y`; its bridge
  to the canonical iteration owner is `iteratedEndofunctor_eq_iterate`, while its comparison,
  face, and degeneracy maps use the canonical functor-coherence API for composition of
  endofunctors of `C`;
- layer triage:
  - `source-facing`: the family `iteratedEndofunctor Y` and the explicit face/degeneracy maps;
  - `core/canonical`: the functor coherence maps `Functor.associator`, `Functor.leftUnitor`,
    `Functor.rightUnitor`, together with whiskering and `Nat.iterate`;
  - `bridge/view`: `iteratedEndofunctor_eq_iterate` and the comparison isomorphism
    `iteratedEndofunctorCompIso`;
- primitive data: the endofunctor `Y` together with `d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`;
- derived API: the comparison isomorphism and the face/degeneracy maps obtained by inserting `d`
  or `s` in the chosen factor.
-/

/-- Example 14.33.1: given an endofunctor `Y : C ⥤ C` with natural transformations
`d : Y ⟶ 𝟭 C` and `s : Y ⟶ Y ⋙ Y`, define `X n` to be the `(n + 1)`-fold composite of `Y`.
The companion declarations below provide the canonical comparison isomorphisms
`X (n + m + 1) ≅ X n ⋙ X m` and the face and degeneracy maps obtained by inserting `d` or `s`
in the chosen factor, counted from the left. -/
@[stacks 0G5M]
def iteratedEndofunctor (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => Y
  | n + 1 => iteratedEndofunctor Y n ⋙ Y

scoped[IteratedEndofunctor] notation:80 Y:max "⦅" n:max "⦆" =>
  iteratedEndofunctor Y n

open scoped IteratedEndofunctor

/-- Postcomposition by `Y` commutes with the canonical iterate of postcomposition by `Y`. -/
private theorem iterate_postcompose_eq (Y F : C ⥤ C) (n : ℕ) :
    Nat.iterate (fun G : C ⥤ C ↦ G ⋙ Y) n (F ⋙ Y) =
      Nat.iterate (fun G : C ⥤ C ↦ G ⋙ Y) n F ⋙ Y := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih => simp [Nat.iterate, ih]

/-- The source-facing recursive `(n + 1)`-fold composite agrees with the canonical `n`-fold
iteration of postcomposition by `Y`. -/
theorem iteratedEndofunctor_eq_iterate (Y : C ⥤ C) (n : ℕ) :
    Y⦅n⦆ = Nat.iterate (fun F : C ⥤ C ↦ F ⋙ Y) n Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedEndofunctor, ih]
      symm
      simpa [Nat.iterate] using iterate_postcompose_eq Y Y n

/-- The canonical associator identifies the `(n + m + 1)`-fold iterate with the composite of the
`n`-th and `m`-th iterates, i.e. `Y⦅(n + m + 1)⦆ ≅ Y⦅n⦆ ⋙ Y⦅m⦆`. -/
def iteratedEndofunctorCompIso (Y : C ⥤ C) (n m : ℕ) :
    Y⦅(n + m + 1)⦆ ≅ (Y⦅n⦆) ⋙ Y⦅m⦆ :=
  match m with
  | 0 => Iso.refl _
  | m + 1 =>
      Functor.isoWhiskerRight (iteratedEndofunctorCompIso Y n m) Y ≪≫
        Functor.associator (Y⦅n⦆) (Y⦅m⦆) Y

/-- The face maps obtained by applying `d` in the chosen factor. Here
`d[Y, d]⦅n, j⦆` is the map `Y⦅(n + 1)⦆ ⟶ Y⦅n⦆` obtained by using `d` on the `j`-th copy of
`Y`, counted from the left. -/
def iteratedFaceMap (Y : C ⥤ C) (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 2)) :
    Y⦅(n + 1)⦆ ⟶ Y⦅n⦆ :=
  match n with
  | 0 =>
      Fin.lastCases
        (Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
        (fun _ ↦ Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
        j
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y⦅(n + 1)⦆) d ≫ (Functor.rightUnitor (Y⦅(n + 1)⦆)).hom)
        (fun i ↦ Functor.whiskerRight (iteratedFaceMap Y d n i) Y)
        j

/-- The degeneracy maps obtained by applying `s` in the chosen factor. Here
`s[Y, s]⦅n, j⦆` is the map `Y⦅n⦆ ⟶ Y⦅(n + 1)⦆` obtained by using `s` on the `j`-th copy of
`Y`, counted from the left. -/
def iteratedDegeneracyMap (Y : C ⥤ C) (s : Y ⟶ Y ⋙ Y) (n : ℕ) (j : Fin (n + 1)) :
    Y⦅n⦆ ⟶ Y⦅(n + 1)⦆ :=
  match n with
  | 0 =>
      s
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y⦅n⦆) s ≫ (Functor.associator (Y⦅n⦆) Y Y).inv)
        (fun i ↦ Functor.whiskerRight (iteratedDegeneracyMap Y s n i) Y)
        j

scoped[IteratedEndofunctor] notation:80 "d[" Y ", " d "]⦅" n ", " j "⦆" =>
  iteratedFaceMap Y d n j
scoped[IteratedEndofunctor] notation:80 "s[" Y ", " s "]⦅" n ", " j "⦆" =>
  iteratedDegeneracyMap Y s n j

end CategoryTheory
