import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Function

section

variable {ι : Type*} {E : Type*} [Zero E]

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.3.12 introduces the notion of an elementary vector of a linear
  subspace of `ℝ^N`.
- `core/canonical`: the primitive owner is set-based `Set.IsElementary S z`, with support
  minimality expressed by the order-theoretic owner `MinimalFor` applied to
  `Function.support`.
- `bridge/view`: the textbook phrasing "there does not exist a nonzero vector with strictly
  smaller support" is exposed through a single owner-side specification theorem; the
  submodule surface is a thin bridge to the primitive set owner.

Domain-style sampling used here:
- `Set.IsElementary` as the primitive owner layer for support-minimality;
- `Submodule 𝕜 (ι → E)` as the canonical linear bridge owner for chapter-facing use;
- `Function.support` for coordinate support;
- `MinimalFor` and `minimalFor_iff_forall_lt` for inclusion-minimal support.

Primitive data vs derived API:
- primitive owner data: the canonical owner predicate
  `MinimalFor (fun y ↦ y ∈ S ∧ y ≠ 0) support z`;
- derived API: membership/nonzero projection lemmas, support-minimality, the textbook
  strict-subset specification theorem, and the submodule bridge.

Layer target: `source-facing`, with a primitive set owner and a submodule bridge.
-/

namespace Set

/-- Primitive owner for Text 22.3.12: a vector `z` in a carrier set of vectors is elementary when
it is nonzero and its support is minimal, under inclusion, among supports of nonzero vectors from
that carrier. -/
def IsElementary (S : Set (ι → E)) (z : ι → E) : Prop :=
  MinimalFor (fun y : ι → E ↦ y ∈ S ∧ y ≠ 0) support z

/-- The set of elementary vectors of a carrier set. -/
def elementary (S : Set (ι → E)) : Set (ι → E) :=
  S.IsElementary

@[simp] theorem mem_elementary (S : Set (ι → E)) (z : ι → E) :
    z ∈ S.elementary ↔ S.IsElementary z :=
  Iff.rfl

namespace IsElementary

variable {S : Set (ι → E)} {z y w : ι → E}

/-- An elementary vector lies in its carrier set. -/
theorem mem (hz : S.IsElementary z) : z ∈ S :=
  hz.prop.1

/-- An elementary vector is nonzero. -/
theorem ne_zero (hz : S.IsElementary z) : z ≠ 0 :=
  hz.prop.2

/-- An elementary vector has support minimal among supports of nonzero vectors in its carrier
set. -/
theorem support_minimal (hz : S.IsElementary z) (hyS : y ∈ S) (hy0 : y ≠ 0)
    (hsubset : support y ⊆ support z) :
    support z ⊆ support y :=
  hz.le_of_le ⟨hyS, hy0⟩ hsubset

/-- Primitive support-minimal specification equivalent to the owner predicate. -/
theorem iff_mem_ne_zero_and_support_minimal :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  constructor
  · intro hz
    refine ⟨hz.mem, hz.ne_zero, ?_⟩
    intro y hyS hy0 hy_subset
    exact hz.support_minimal hyS hy0 hy_subset
  · rintro ⟨hzS, hz0, hminimal⟩
    rw [Set.IsElementary, minimalFor_iff_forall_lt]
    refine ⟨⟨hzS, hz0⟩, ?_⟩
    intro y hyss hy
    exact hyss.2 (hminimal hy.1 hy.2 hyss.1)

/-- The textbook strict-subset formulation is equivalent to the primitive owner predicate. -/
theorem iff_mem_ne_zero_and_support_ssubset_eq_zero :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → support y ⊂ support z → y = 0 := by
  constructor
  · intro hz
    refine ⟨hz.mem, hz.ne_zero, ?_⟩
    intro y hyS hyss
    by_contra hy0
    exact hz.not_prop_of_lt hyss ⟨hyS, hy0⟩
  · rintro ⟨hzS, hz0, hssubset_zero⟩
    refine (iff_mem_ne_zero_and_support_minimal (S := S) (z := z)).2 ⟨hzS, hz0, ?_⟩
    intro y hyS hy0 hy_subset
    by_contra hz_not_subset
    have hy_ne : support y ≠ support z := by
      intro hy_eq
      exact hz_not_subset hy_eq.symm.subset
    have hyss : support y ⊂ support z :=
      Set.ssubset_iff_subset_ne.2 ⟨hy_subset, hy_ne⟩
    exact hy0 (hssubset_zero hyS hyss)

/-- The textbook strict-subset exclusion form is a direct bridge from the canonical owner-side
strict-subset-zero criterion. -/
theorem iff_mem_ne_zero_and_not_exists_support_ssubset :
    S.IsElementary z ↔
      z ∈ S ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ S ∧ y ≠ 0 ∧ support y ⊂ support z := by
  constructor
  · rintro hz
    rcases (iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z)).1 hz with
      ⟨hzS, hz0, hssubset_zero⟩
    refine ⟨hzS, hz0, ?_⟩
    rintro ⟨y, hyS, hy0, hyss⟩
    exact hy0 (hssubset_zero hyS hyss)
  · rintro ⟨hzS, hz0, hno_strict_subset⟩
    refine (iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z)).2 ⟨hzS, hz0, ?_⟩
    intro y hyS hyss
    by_contra hy0
    exact hno_strict_subset ⟨y, hyS, hy0, hyss⟩

/-- Any vector in the same carrier set whose support is strictly smaller than that of an
elementary vector must itself be zero. -/
theorem eq_zero_of_support_ssubset (hz : S.IsElementary z) (hwS : w ∈ S)
    (hw : support w ⊂ support z) :
    w = 0 := by
  by_contra hw0
  exact hz.not_prop_of_lt hw ⟨hwS, hw0⟩

end IsElementary

variable {S : Set (ι → E)} {z : ι → E}

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to membership/nonzero plus support minimality among nonzero vectors of `S`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_minimal :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_minimal (S := S) (z := z))

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to membership/nonzero plus strict-subset vanishing in `S`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ S → support y ⊂ support z → y = 0 := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero (S := S) (z := z))

/-- Owner-side notation surface for elementary vectors: membership in `S.elementary` is equivalent
to the textbook strict-subset exclusion criterion. -/
theorem mem_elementary_iff_mem_ne_zero_and_not_exists_support_ssubset :
    z ∈ S.elementary ↔
      z ∈ S ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ S ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Set.mem_elementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset (S := S) (z := z))

end Set

end

section

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
  [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace Submodule

/-- Text 22.3.12 on the canonical linear owner: a vector `z` in a submodule is elementary when it
is elementary in the carrier set of that submodule. -/
def IsElementary (L : Submodule 𝕜 (ι → E)) (z : ι → E) : Prop :=
  (L : Set (ι → E)).IsElementary z

/-- The owner-side set of elementary vectors of `L`. -/
def elementary (L : Submodule 𝕜 (ι → E)) : Set (ι → E) :=
  (L : Set (ι → E)).elementary

@[simp] theorem mem_elementary (L : Submodule 𝕜 (ι → E)) (z : ι → E) :
    z ∈ L.elementary ↔ L.IsElementary z :=
  Iff.rfl

namespace IsElementary

variable {L : Submodule 𝕜 (ι → E)} {z y w : ι → E}

/-- An elementary vector lies in its subspace. -/
theorem mem (hz : L.IsElementary z) : z ∈ L := by
  exact Set.IsElementary.mem hz

/-- An elementary vector is nonzero. -/
theorem ne_zero (hz : L.IsElementary z) : z ≠ 0 :=
  Set.IsElementary.ne_zero hz

/-- An elementary vector has support minimal among the supports of nonzero vectors in its
subspace. -/
theorem support_minimal (hz : L.IsElementary z) (hyL : y ∈ L) (hy0 : y ≠ 0)
    (hsubset : support y ⊆ support z) :
    support z ⊆ support y :=
  Set.IsElementary.support_minimal hz hyL hy0 hsubset

/-- Primitive support-minimal specification equivalent to the canonical owner predicate. -/
theorem iff_mem_ne_zero_and_support_minimal :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_minimal
      (S := (L : Set (ι → E))) (z := z))

/-- The textbook strict-subset formulation is equivalent to the canonical owner predicate for
elementary vectors. -/
theorem iff_mem_ne_zero_and_support_ssubset_eq_zero :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → support y ⊂ support z → y = 0 := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero
      (S := (L : Set (ι → E))) (z := z))

/-- The textbook strict-subset exclusion criterion is a bridge theorem from the canonical
strict-subset-zero owner form. -/
theorem iff_mem_ne_zero_and_not_exists_support_ssubset :
    L.IsElementary z ↔
      z ∈ L ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ L ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Submodule.IsElementary] using
    (Set.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset
      (S := (L : Set (ι → E))) (z := z))

/-- Any vector in the same subspace whose support is strictly smaller than that of an elementary
vector must itself be zero. -/
theorem eq_zero_of_support_ssubset (hz : L.IsElementary z) (hwL : w ∈ L)
    (hw : support w ⊂ support z) :
    w = 0 :=
  Set.IsElementary.eq_zero_of_support_ssubset hz hwL hw

end IsElementary

variable {L : Submodule 𝕜 (ι → E)} {z : ι → E}

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to membership/nonzero plus support minimality among nonzero vectors
of `L`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_minimal :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → y ≠ 0 → support y ⊆ support z → support z ⊆ support y := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_support_minimal (L := L) (z := z))

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to membership/nonzero plus strict-subset vanishing in `L`. -/
theorem mem_elementary_iff_mem_ne_zero_and_support_ssubset_eq_zero :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧
        ∀ ⦃y : ι → E⦄, y ∈ L → support y ⊂ support z → y = 0 := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_support_ssubset_eq_zero (L := L) (z := z))

/-- Owner-side notation surface for elementary vectors of a submodule: membership in
`L.elementary` is equivalent to the textbook strict-subset exclusion criterion. -/
theorem mem_elementary_iff_mem_ne_zero_and_not_exists_support_ssubset :
    z ∈ L.elementary ↔
      z ∈ L ∧ z ≠ 0 ∧ ¬ ∃ y : ι → E, y ∈ L ∧ y ≠ 0 ∧ support y ⊂ support z := by
  simpa [Submodule.mem_elementary] using
    (Submodule.IsElementary.iff_mem_ne_zero_and_not_exists_support_ssubset
      (L := L) (z := z))

end Submodule

end
