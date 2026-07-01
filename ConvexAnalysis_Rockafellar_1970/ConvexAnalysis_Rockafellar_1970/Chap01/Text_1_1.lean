import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Affine

variable {k : Type*} {V : Type*} {P : Type*}
  [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

open AffineMap AffineSubspace

/-
Source/core/bridge triage:
- `source-facing`: Text 1.1 gives the textbook set-language criterion for affine subsets,
  namely closure under all binary affine combinations; stated coordinate-free, the same criterion
  characterizes affine subsets of an affine space over any scalar ring where `2` is invertible.
- `core/canonical`: the owner abstractions are bundled affine subspaces `AffineSubspace k P` and
  the intrinsic set-level closure owner `Set.IsAffine k M`.
- `bridge/view`: the theorem below identifies this owner-level carrier view with the fixed-point
  equation `affineSpan k M = M`, and then with the textbook `lineMap` closure criterion.
- Domain-style sampling used here:
  `AffineSubspace k P`,
  `AffineMap.lineMap_mem`,
  `affineSpan_le`,
  `AffineSubspace.smul_vsub_vadd_mem`.
- Primitive data vs derived API: the primitive owner data are closure under
  `smul_vsub_vadd`; affine-subspace carrier witnesses, affine-span fixed-point, and `lineMap`
  closure forms are derived bridge views.
- Layer target: `source-facing`; the theorem keeps the textbook set-level criterion while reusing
  the canonical owner directly.
-/
recall AffineMap.lineMap_mem
recall affineSpan_le
recall AffineSubspace.smul_vsub_vadd_mem

/- Canonicalization decision record (this pass):
- Codomain/ambient check: not an extended-codomain file; the ambient owner is `AffineSubspace k P`.
- Scalar check: keep `[Ring k]` from the canonical affine API; the lineMap-to-owner bridge needs
  invertibility of `2` only in the reverse direction.
- Owner check: keep the canonical owner `AffineSubspace k P` and set-level intrinsic owner
  `Set.IsAffine`.
- Topology check: no topology-facing statement appears here.
- Surface-noise check: remove public coercion clutter by stating carrier equalities as
  `M = S` and `affineSpan k M = M` instead of explicit `(S : Set P)`/`(affineSpan ... : Set P)`.
-/

private theorem smul_vsub_vadd_eq_lineMap_lineMap [Invertible (2 : k)] (c : k) (p₁ p₂ p₃ : P) :
    c • (p₁ -ᵥ p₂) +ᵥ p₃ =
      lineMap p₂ (lineMap (lineMap p₂ p₁ c) p₃ (⅟ (2 : k))) (2 : k) := by
  refine (vsub_left_injective p₂) ?_
  change
    (c • (p₁ -ᵥ p₂) +ᵥ p₃) -ᵥ p₂ =
      lineMap p₂ (lineMap (lineMap p₂ p₁ c) p₃ (⅟ (2 : k))) (2 : k) -ᵥ p₂
  rw [vadd_vsub_assoc, lineMap_vsub_left]
  let q : P := lineMap p₂ p₁ c
  change c • (p₁ -ᵥ p₂) + (p₃ -ᵥ p₂) = (2 : k) • (lineMap q p₃ (⅟ (2 : k)) -ᵥ p₂)
  have hsplit :
      lineMap q p₃ (⅟ (2 : k)) -ᵥ p₂ =
        (lineMap q p₃ (⅟ (2 : k)) -ᵥ q) + (q -ᵥ p₂) := by
    rw [vsub_add_vsub_cancel]
  rw [hsplit, lineMap_vsub_left]
  have hq : q -ᵥ p₂ = c • (p₁ -ᵥ p₂) := by
    simp [q, lineMap_vsub_left]
  rw [hq, smul_add, smul_smul]
  have htwo : (2 : k) * ⅟ (2 : k) = 1 := by
    simp
  rw [htwo, one_smul]
  have hp3q : p₃ -ᵥ q = (p₃ -ᵥ p₂) - c • (p₁ -ᵥ p₂) := by
    simp [q, lineMap_apply, vsub_vadd_eq_vsub_sub]
  rw [hp3q, two_smul, sub_eq_add_neg]
  abel_nf

section

variable [Invertible (2 : k)] {M : Set P}

private theorem smul_vsub_vadd_mem_of_lineMap_mem
    (hline : ∀ x ∈ M, ∀ y ∈ M, ∀ t : k, lineMap x y t ∈ M)
    (c : k) {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ M) (hp₂ : p₂ ∈ M) (hp₃ : p₃ ∈ M) :
    c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M := by
  rw [smul_vsub_vadd_eq_lineMap_lineMap]
  have hp₁₂ : lineMap p₂ p₁ c ∈ M := hline p₂ hp₂ p₁ hp₁ c
  have hp₁₂₃ : lineMap (lineMap p₂ p₁ c) p₃ (⅟ (2 : k)) ∈ M :=
    hline (lineMap p₂ p₁ c) hp₁₂ p₃ hp₃ (⅟ (2 : k))
  exact hline p₂ hp₂ (lineMap (lineMap p₂ p₁ c) p₃ (⅟ (2 : k))) hp₁₂₃ (2 : k)

end

namespace Set

variable (k)

/-- Canonical set-level owner for affineness: a set is affine when it is the carrier of some
affine subspace, equivalently when it is closed under `smul_vsub_vadd`. We use the intrinsic
closure rule as primitive owner data. -/
def IsAffine (M : Set P) : Prop :=
  ∀ c : k, ∀ p₁ ∈ M, ∀ p₂ ∈ M, ∀ p₃ ∈ M, c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M

variable {k}

/-- Textbook surface notation for set-level affineness over scalar ring `k`. -/
scoped[Affine] notation:50 "affine[" k "] " M => Set.IsAffine k M

/-- A set is affine exactly when it agrees with its affine span. -/
theorem isAffine_iff_affineSpan_eq_self (M : Set P) :
    (affine[k] M) ↔ affineSpan k M = M := by
  constructor
  · intro hM
    have hle : affineSpan k M ≤
        ({ carrier := M
         , smul_vsub_vadd_mem := fun c {p₁} {p₂} {p₃} hp₁ hp₂ hp₃ ↦
            hM c p₁ hp₁ p₂ hp₂ p₃ hp₃ } : AffineSubspace k P) :=
      (affineSpan_le (k := k)).2 (fun _ hx ↦ hx)
    ext x
    constructor
    · intro hx
      exact hle hx
    · intro hx
      exact subset_affineSpan k M hx
  · intro hM c p₁ hp₁ p₂ hp₂ p₃ hp₃
    have hp₁' : p₁ ∈ affineSpan k M := subset_affineSpan k M hp₁
    have hp₂' : p₂ ∈ affineSpan k M := subset_affineSpan k M hp₂
    have hp₃' : p₃ ∈ affineSpan k M := subset_affineSpan k M hp₃
    have hmem : c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ affineSpan k M :=
      (affineSpan k M).smul_vsub_vadd_mem c hp₁' hp₂' hp₃'
    exact hM ▸ hmem

/-- Primitive owner unpacking: an affine set is exactly the carrier of some affine subspace. -/
theorem isAffine_iff_exists_affineSubspace_eq (M : Set P) :
    (affine[k] M) ↔ ∃ S : AffineSubspace k P, M = S := by
  constructor
  · intro hM
    refine ⟨{ carrier := M
            , smul_vsub_vadd_mem := fun c {p₁} {p₂} {p₃} hp₁ hp₂ hp₃ ↦
                hM c p₁ hp₁ p₂ hp₂ p₃ hp₃ }, rfl⟩
  · rintro ⟨S, hS⟩ c p₁ hp₁ p₂ hp₂ p₃ hp₃
    subst hS
    exact S.smul_vsub_vadd_mem c hp₁ hp₂ hp₃

/-- Owner-primitive bridge: set-level affineness is equivalent to closure under
`smul_vsub_vadd`. -/
theorem isAffine_iff_smul_vsub_vadd_mem (M : Set P) :
    (affine[k] M) ↔
      ∀ c : k, ∀ p₁ ∈ M, ∀ p₂ ∈ M, ∀ p₃ ∈ M, c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M := by
  rfl

namespace IsAffine

variable {M : Set P}

/-- Re-oriented owner equation: an affine set is fixed by affine span. -/
theorem affineSpan_eq (hM : affine[k] M) : affineSpan k M = M :=
  (isAffine_iff_affineSpan_eq_self (k := k) M).1 hM

/-- Owner bridge from set-level affineness to bundled affine subspaces. -/
theorem exists_affineSubspace_eq (hM : affine[k] M) :
    ∃ S : AffineSubspace k P, M = S :=
  (isAffine_iff_exists_affineSubspace_eq (k := k) M).1 hM

/-- Primitive closure rule for affine sets. -/
theorem smul_vsub_vadd_mem (hM : affine[k] M)
    (c : k) {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ M) (hp₂ : p₂ ∈ M) (hp₃ : p₃ ∈ M) :
    c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M :=
  hM c p₁ hp₁ p₂ hp₂ p₃ hp₃

/-- Constructor from affine-span fixed-point form. -/
theorem of_affineSpan_eq (hM : affineSpan k M = M) : affine[k] M :=
  (isAffine_iff_affineSpan_eq_self (k := k) M).2 hM

/-- Constructor from primitive affine-subspace closure. -/
theorem of_smul_vsub_vadd_mem
    (hsmul : ∀ c : k, ∀ p₁ ∈ M, ∀ p₂ ∈ M, ∀ p₃ ∈ M, c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M) :
    affine[k] M :=
  hsmul

/-- Constructor from bundled-affine-subspace carrier form. -/
theorem of_exists_affineSubspace_eq (hM : ∃ S : AffineSubspace k P, M = S) :
    affine[k] M :=
  (isAffine_iff_exists_affineSubspace_eq (k := k) M).2 hM

end IsAffine

/-- A set is the carrier of its affine span exactly when it is closed under the primitive
affine-subspace operation `smul_vsub_vadd`. -/
theorem affineSpan_eq_self_iff_smul_vsub_vadd_mem (M : Set P) :
    affineSpan k M = M ↔
      ∀ c : k, ∀ p₁ ∈ M, ∀ p₂ ∈ M, ∀ p₃ ∈ M, c • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ M := by
  rw [← isAffine_iff_affineSpan_eq_self (k := k) (M := M)]
  exact isAffine_iff_smul_vsub_vadd_mem (k := k) M

/-- If a set already agrees with its affine span, then it is closed under every binary affine
combination. -/
theorem lineMap_mem_of_affineSpan_eq_self {M : Set P} (hM : affineSpan k M = M)
    {x y : P} (hx : x ∈ M) (hy : y ∈ M) (t : k) :
    lineMap x y t ∈ M := by
  have hAffine : affine[k] M := IsAffine.of_affineSpan_eq (k := k) hM
  simpa [lineMap_apply] using hAffine.smul_vsub_vadd_mem t hy hx hx

/-- A set closed under every binary affine combination is already the carrier of its affine
span. -/
theorem affineSpan_eq_self_of_lineMap_mem [Invertible (2 : k)] {M : Set P}
    (hline : ∀ x ∈ M, ∀ y ∈ M, ∀ t : k, lineMap x y t ∈ M) :
    affineSpan k M = M := by
  exact (affineSpan_eq_self_iff_smul_vsub_vadd_mem (k := k) (M := M)).2
    (fun c p₁ hp₁ p₂ hp₂ p₃ hp₃ ↦ smul_vsub_vadd_mem_of_lineMap_mem hline c hp₁ hp₂ hp₃)

/-- Text 1.1 in owner form: a set is affine exactly when it is closed under `lineMap`. -/
theorem isAffine_iff_lineMap_mem [Invertible (2 : k)] (M : Set P) :
    (affine[k] M) ↔ ∀ x ∈ M, ∀ y ∈ M, ∀ t : k, lineMap x y t ∈ M := by
  constructor
  · intro hAffine x hx y hy t
    exact lineMap_mem_of_affineSpan_eq_self (k := k)
      (IsAffine.affineSpan_eq (k := k) hAffine) hx hy t
  · intro hline
    exact IsAffine.of_affineSpan_eq (k := k)
      (affineSpan_eq_self_of_lineMap_mem (k := k) hline)

namespace IsAffine

variable {M : Set P}

/-- Binary affine-combination closure for affine sets. -/
theorem lineMap_mem (hM : affine[k] M)
    {x y : P} (hx : x ∈ M) (hy : y ∈ M) (t : k) :
    lineMap x y t ∈ M :=
  lineMap_mem_of_affineSpan_eq_self (k := k)
    (IsAffine.affineSpan_eq (k := k) hM) hx hy t

/-- Constructor from binary affine-combination closure. -/
theorem of_lineMap_mem [Invertible (2 : k)]
    (hline : ∀ x ∈ M, ∀ y ∈ M, ∀ t : k, lineMap x y t ∈ M) :
    affine[k] M :=
  (isAffine_iff_lineMap_mem (k := k) M).2 hline

end IsAffine

/-- Text 1.1 in set-language: a subset of an affine space over a scalar ring with invertible `2`
is the carrier of its affine span exactly when it is closed under `lineMap`. The owner object
remains `AffineSubspace k P`. -/
theorem affineSpan_eq_self_iff_lineMap_mem [Invertible (2 : k)] (M : Set P) :
    affineSpan k M = M ↔ ∀ x ∈ M, ∀ y ∈ M, ∀ t : k, lineMap x y t ∈ M := by
  rw [← isAffine_iff_affineSpan_eq_self (k := k) (M := M)]
  exact isAffine_iff_lineMap_mem (k := k) M

end Set
