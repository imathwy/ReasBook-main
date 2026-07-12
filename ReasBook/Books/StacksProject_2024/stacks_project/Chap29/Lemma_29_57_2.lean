import Mathlib
import StacksProject_2024.Chap29.Definition_29_57_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-side owners `Scheme.Hom.fiber`,
  `Scheme.Hom.fiberToSpecResidueField`, and `IsFinite`;
- local precedent in `Definition_29_57_1.lean` already models "degrees of the fibres" by the
  global sections algebra of the scheme-theoretic fiber over a residue field;
- the field-valued-point formulation should therefore expose the pullback global-sections algebra
  and its degree as named bridge API, rather than relying on hidden local instances in theorem
  headers.
This file therefore keeps `degreesOfFibresBoundedBy` as the owner and records the field-valued
point formulation through the canonical pullback-to-`Spec k` bridge lemmas used elsewhere in
Section 29.57.
-/

/-- The global sections of the pullback of `f` along a field-valued point `g : Spec(k) ⟶ Y`. -/
abbrev fieldValuedPointPullbackGlobalSections (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) :=
  Scheme.Γ.obj (Opposite.op (pullback f g : Scheme))

/-- The canonical `k`-algebra structure on the global sections of the field-valued pullback of
`f` along `g : Spec(k) ⟶ Y`. -/
@[reducible] instance fieldValuedPointPullbackGlobalSectionsAlgebra (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) :
    Algebra k (fieldValuedPointPullbackGlobalSections f g) :=
  (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ appTop (pullback.snd f g))).toAlgebra

/-- The degree of the field-valued pullback `Spec(k) ×[Y] X` over `k`. -/
abbrev fieldValuedPointPullbackDegree (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) : ℕ :=
  Module.finrank k (fieldValuedPointPullbackGlobalSections f g)

/-- Lemma 29.57.2 (1): a natural number `n` bounds the degrees of the fibres of `f` if and only
if for every field-valued point `Spec(k) ⟶ Y`, the base change `Spec(k) ×[Y] X` is finite over
`k` of degree at most `n`. -/
@[stacks 03J5]
theorem degreesOfFibresBoundedBy_iff_forall_fieldValuedPoints (f : X ⟶ Y) (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
        IsFinite (pullback.snd f g) ∧
          fieldValuedPointPullbackDegree f g ≤ n := sorry

/-- Lemma 29.57.2 (2): if every field-valued base change of `f` is finite over the base field of
degree at most `n`, then the fibres of `f` are universally bounded. -/
theorem universallyBoundedFibres_of_forall_fieldValuedPoints
    {f : X ⟶ Y} {n : ℕ}
    (h : ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
      IsFinite (pullback.snd f g) ∧
        fieldValuedPointPullbackDegree f g ≤ n) :
    universallyBoundedFibres f := by
  exact ⟨n, (degreesOfFibresBoundedBy_iff_forall_fieldValuedPoints f n).2 h⟩

/-- Lemma 29.57.2 (3): if the degrees of the fibres of `f` are bounded by `n`, then every
field-valued base change `Spec(k) ×[Y] X` is finite and has at most `n` points. -/
theorem finite_card_pullback_le_of_degreesOfFibresBoundedBy
    {f : X ⟶ Y} {n : ℕ} (h : degreesOfFibresBoundedBy f n)
    {k : Type u} [Field k]
    (g : Spec (CommRingCat.of k) ⟶ Y) :
    Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n := sorry

end Scheme.Hom
end AlgebraicGeometry
