import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

namespace SetRel

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.8.4 introduces eigensets by the image equation `AC = λ C`.
- `core/canonical`: the process/image owner already present in the chapter is `SetRel.image`, and
  the textbook dilate `λ C` is the canonical pointwise scalar action on sets.
- `bridge/view`: the textbook notation `AC` is rendered directly as `A.image C`, so no extra
  action notation or wrapper owner is introduced here.

Primary mathematical domain:
- convex processes acting on sets through relation image.

Domain-style sampling used here:
- `SetRel.image` from `Mathlib.Data.Rel` for the image of a set under a relation;
- the canonical pointwise set scalar action `lam • C`.

Primitive data vs derived API:
- primitive owner data: a self-relation `A : SetRel U U`, a scalar `lam : R`, and a set `C`;
- primitive source-facing owner introduced here: `A.IsEigenset lam C`;
- derived API: the direct rewriting lemma exposing the defining image equation.

Layer target: `source-facing`, stated directly on the canonical relation-image owner.
-/

section

variable {R : Type u} {U : Type v} [SMul R U]

/-- Definition 39.8.4: a set `C` is an eigenset of a self-relation `A` with eigenvalue `lam`
when its image under `A`, written in the text as `AC`, is exactly the dilate `lam • C`. -/
def IsEigenset (A : SetRel U U) (lam : R) (C : Set U) : Prop :=
  A.image C = lam • C

-- Proof sketch: unfold `SetRel.IsEigenset`; this is the definitional equation of the owner,
-- restated in a rewrite-friendly `..._def` form.
/-- An eigenset is exactly a set whose image under `A` equals its `lam`-dilate. -/
@[simp] theorem isEigenset_def
    (A : SetRel U U) (lam : R) (C : Set U) :
    A.IsEigenset lam C ↔ A.image C = lam • C := sorry

-- Proof sketch: this is the same defining equivalence as `isEigenset_def`, recorded under the
-- standard `..._iff` companion name for rewriting and search.
/-- An eigenset is exactly a set whose image under `A` equals its `lam`-dilate. -/
@[simp] theorem isEigenset_iff
    (A : SetRel U U) (lam : R) (C : Set U) :
    A.IsEigenset lam C ↔ A.image C = lam • C := sorry

-- Proof sketch: unfold `SetRel.IsEigenset`; an eigenset hypothesis is exactly the defining image
-- equation `A.image C = lam • C`.
/-- An eigenset hypothesis directly yields the defining image equation `A.image C = lam • C`. -/
@[simp] theorem isEigenset_image_eq
    {A : SetRel U U} {lam : R} {C : Set U} (hC : A.IsEigenset lam C) :
    A.image C = lam • C := sorry

namespace IsEigenset

-- Proof sketch: unfold `SetRel.IsEigenset`; the hypothesis already is the defining image
-- equation `A.image C = lam • C`.
/-- An eigenset hypothesis directly yields the defining image equation. -/
theorem image_eq {A : SetRel U U} {lam : R} {C : Set U} (hC : A.IsEigenset lam C) :
    A.image C = lam • C := sorry

end IsEigenset

end

end SetRel
