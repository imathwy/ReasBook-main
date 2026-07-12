import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory HomologicalComplex

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
variable (A : CochainComplex 𝒜 ℤ) (k : ℤ)

/- Domain-style sampling:
- primary domain: shifts of cochain complexes in a preadditive category;
- sampled owner declarations:
  `CochainComplex.shiftFunctor`,
  `CochainComplex.shiftFunctor_obj_X'`,
  `CochainComplex.shiftFunctor_obj_d'`,
  `CochainComplex.shiftFunctor_map_f'`.

Source/core/bridge triage:
- `core/canonical`: `CochainComplex.shiftFunctor`;
- `source-facing`: the shifted cochain complex `A⟦k⟧`;
- `bridge/view`: the degreewise object, differential, and morphism formulas supplied by the
  sampled companion lemmas.

Primitive data are only the owner functor. The formulas
`(A⟦k⟧).X n = A.X (n + k)`, `d = (-1)^k • A.d (n + k) (n + k + 1)`, and
`((shiftFunctor _ k).map f).f n = f.f (n + k)` are derived API, so this file should remain a
canonical recall item rather than reintroducing a parallel local shift definition.
 -/

/- Companion recall: the underlying shifted cochain complex is the canonical shift object
`A⟦k⟧`. -/
#check A⟦k⟧

/-- Definition 12.14.7: for a cochain complex `A`, the `k`-shift `A[k]` is the canonical owner
object `A⟦k⟧`. -/
abbrev cochainShift (A : CochainComplex 𝒜 ℤ) (k : ℤ) : CochainComplex 𝒜 ℤ :=
  A⟦k⟧

/-- Helper for Definition 12.14.7: the shifted morphism is the image of a cochain-map under the
canonical shift functor. -/
abbrev cochainShiftMap {A B : CochainComplex 𝒜 ℤ} (f : A ⟶ B) (k : ℤ) :
    cochainShift A k ⟶ cochainShift B k :=
  (shiftFunctor (CochainComplex 𝒜 ℤ) k).map f

/-- Helper for Definition 12.14.7: the source-facing shift construction on cochain complexes is
the canonical owner functor `CochainComplex.shiftFunctor`. -/
recall CochainComplex.shiftFunctor

/-- Helper for Definition 12.14.7: the degree-`n` term of the shifted cochain complex is the
degree-`n + k` term of the original complex. -/
lemma cochain_shift_obj (A : CochainComplex 𝒜 ℤ) (k n : ℤ) :
    (A⟦k⟧).X n = A.X (n + k) := by
  -- Read the shifted degree directly from the canonical cochain-shift owner.
  simpa using (CochainComplex.shiftFunctor_obj_X' (K := A) k n)

/-- Helper for Definition 12.14.7: after transporting along the canonical degree equalities, the
shifted differential is `(-1)^k` times the translated differential of the original complex. -/
lemma cochain_shift_d (A : CochainComplex 𝒜 ℤ) (k i j : ℤ) :
    (A⟦k⟧).d i j =
      eqToHom (cochain_shift_obj (A := A) k i) ≫
        (k.negOnePow • A.d (i + k) (j + k)) ≫
        eqToHom (cochain_shift_obj (A := A) k j).symm := by
  -- Read the shifted differential formula from the canonical owner and rewrite its degree terms.
  simpa [cochain_shift_obj, Category.assoc] using
    (CochainComplex.shiftFunctor_obj_d' (K := A) k i j)

/-- Helper for Definition 12.14.7: the degree-`n` component of the shifted morphism is the
degree-`n + k` component of the original morphism, up to the canonical degree transports. -/
lemma cochain_shift_map_f {A B : CochainComplex 𝒜 ℤ} (f : A ⟶ B) (k n : ℤ) :
    ((shiftFunctor (CochainComplex 𝒜 ℤ) k).map f).f n =
      eqToHom (cochain_shift_obj (A := A) k n) ≫
        f.f (n + k) ≫
        eqToHom (cochain_shift_obj (A := B) k n).symm := by
  -- Read the shifted component formula from functoriality of the canonical shift owner.
  simpa [cochain_shift_obj, Category.assoc] using
    (CochainComplex.shiftFunctor_map_f' (φ := f) k n)
