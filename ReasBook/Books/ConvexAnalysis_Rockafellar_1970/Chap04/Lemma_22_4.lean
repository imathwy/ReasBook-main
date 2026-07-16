import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_22_3_12

-- Declarations for this item will be appended below by the statement pipeline.

open Function

section

variable {ι : Type*} {𝕜 : Type*} [DivisionRing 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 22.4 says that two elementary vectors of the same subspace with the same
  support differ by a nonzero scalar factor.
- `core/canonical`: the owner abstraction is the chapter predicate `L.IsElementary z` from
  `Text_22_3_12`, stated for an arbitrary submodule `L : Submodule 𝕜 (ι → 𝕜)` over a division
  ring.
- `bridge/view`: the theorem is derived at the owner path `Submodule.IsElementary`, with an
  additional notation-surface bridge on `z ∈ L.elementary` for chapter-facing use.

Domain-style sampling used here:
- `Submodule.IsElementary` from `Text_22_3_12` as the owner predicate for elementary
  vectors in `Submodule 𝕜 (ι → 𝕜)`;
- `Submodule.IsElementary.support_minimal` as the canonical minimal-support API;
- `Submodule.IsElementary.eq_zero_of_support_ssubset` as the canonical strict-subset
  vanishing consequence;
- `Function.support` for coordinate support;
- scalar multiplication `a • z` in the ambient function-space module structure.

Primitive data vs derived API:
- primitive owner data already upstream: the submodule `L`, vectors `z z' : ι → 𝕜`, and the
  predicate `L.IsElementary _`;
- canonical derived API here: support-inclusion uniqueness-up-to-nonzero-scalar for nonzero
  vectors in `L` (`exists_ne_zero_smul_eq_of_support_subset_of_mem`);
- bridge wrappers: equal-support, "both vectors elementary", and unit-scalar forms.

Layer target: `source-facing`.
-/

namespace Submodule.IsElementary

variable {L : Submodule 𝕜 (ι → 𝕜)} {z z' : ι → 𝕜}

-- Proof sketch for the core scalar-alignment step: choose an index in the common support and
-- scale one vector so that the chosen coordinates agree. The difference still lies in the
-- subspace, its support is contained in the common support, and the chosen coordinate vanishes,
-- so its support is strictly smaller; the elementary-vector minimal-support property forces the
-- difference to be zero.
private theorem exists_ne_zero_smul_eq_of_support_eq_aux
    (hz : L.IsElementary z) (hz'L : z' ∈ L)
    (hsupp : support z = support z') :
    ∃ a : 𝕜, a ≠ 0 ∧ z' = a • z := by
  have hsupport_nonempty : (support z).Nonempty := support_nonempty_iff.2 hz.ne_zero
  rcases hsupport_nonempty with ⟨i, hi⟩
  have hzi : z i ≠ 0 := mem_support.mp hi
  have hi' : i ∈ support z' := by
    simpa [hsupp] using hi
  have hz'i : z' i ≠ 0 := mem_support.mp hi'
  have hsupp' : support z' ⊆ support z := hsupp.symm.subset
  let a : 𝕜 := z' i / z i
  let w : ι → 𝕜 := z' - a • z
  have hwL : w ∈ L := by
    dsimp [w]
    exact L.sub_mem hz'L (L.smul_mem a hz.mem)
  have hw_subset : support w ⊆ support z := by
    dsimp [w]
    refine (support_sub z' (a • z)).trans ?_
    exact Set.union_subset hsupp' (support_const_smul_subset a z)
  have hwi : w i = 0 := by
    dsimp [w, a]
    change z' i - (z' i / z i) * z i = 0
    rw [div_mul_cancel₀ _ hzi, sub_self]
  have hwi_not_mem : i ∉ support w := by
    simp [mem_support, hwi]
  have hw_ssubset : support w ⊂ support z := by
    refine Set.ssubset_iff_subset_ne.2 ⟨hw_subset, ?_⟩
    intro hEq
    exact hwi_not_mem (hEq.symm ▸ hi)
  have hw_zero : w = 0 := hz.eq_zero_of_support_ssubset hwL hw_ssubset
  have ha : a ≠ 0 := div_ne_zero hz'i hzi
  refine ⟨a, ha, ?_⟩
  dsimp [w] at hw_zero
  exact sub_eq_zero.mp hw_zero

/-- Canonical owner-side primitive form of Lemma 22.4: if `z` is elementary in `L`, and `z'` is a
nonzero vector of `L` with support contained in `support z`, then `z'` is a nonzero scalar
multiple of `z`. -/
theorem exists_ne_zero_smul_eq_of_support_subset_of_mem
    (hz : L.IsElementary z) (hz'L : z' ∈ L) (hz'0 : z' ≠ 0)
    (hsupp : support z' ⊆ support z) :
    ∃ a : 𝕜, a ≠ 0 ∧ z' = a • z := by
  have hsupp' : support z ⊆ support z' :=
    hz.support_minimal hz'L hz'0 hsupp
  have hsuppEq : support z = support z' := Set.Subset.antisymm hsupp' hsupp
  exact exists_ne_zero_smul_eq_of_support_eq_aux hz hz'L hsuppEq

/-- Unit-scalar bridge form of Lemma 22.4 with primitive assumptions. -/
theorem eq_smul_of_support_subset_of_mem
    (hz : L.IsElementary z) (hz'L : z' ∈ L) (hz'0 : z' ≠ 0)
    (hsupp : support z' ⊆ support z) :
    ∃ a : 𝕜ˣ, z' = a • z := by
  rcases hz.exists_ne_zero_smul_eq_of_support_subset_of_mem hz'L hz'0 hsupp with ⟨a, ha, haz⟩
  refine ⟨Units.mk0 a ha, ?_⟩
  simpa [Units.smul_def] using haz

/-- Owner-side strengthening of Lemma 22.4 in "both vectors elementary" form: if `z` and `z'` are
 elementary vectors and `support z ⊆ support z'`, then minimality forces equal support and `z'` is
 a unit scalar multiple of `z`. The canonical primitive form is
 `exists_ne_zero_smul_eq_of_support_subset_of_mem`. -/
theorem eq_smul_of_support_subset
    (hz : L.IsElementary z) (hz' : L.IsElementary z')
    (hsupp : support z ⊆ support z') :
    ∃ a : 𝕜ˣ, z' = a • z := by
  have hsupp' : support z' ⊆ support z :=
    hz'.support_minimal hz.mem hz.ne_zero hsupp
  exact hz.eq_smul_of_support_subset_of_mem hz'.mem hz'.ne_zero hsupp'

/-- Lemma 22.4, unit-scalar form: if two elementary vectors of a subspace of `𝕜^ι` have the same
support, then one is a unit scalar multiple of the other. -/
theorem eq_smul_of_support_eq
    (hz : L.IsElementary z) (hz' : L.IsElementary z')
    (hsupp : support z = support z') :
    ∃ a : 𝕜ˣ, z' = a • z := by
  exact hz.eq_smul_of_support_subset_of_mem hz'.mem hz'.ne_zero hsupp.symm.subset

/-- Lemma 22.4, textbook scalar form: if two elementary vectors of a subspace of `𝕜^ι` have the
same support, then one is a nonzero scalar multiple of the other. The canonical owner-side
primitive form is `exists_ne_zero_smul_eq_of_support_subset_of_mem`; this theorem is a direct
wrapper in the "both vectors elementary" surface. -/
theorem exists_ne_zero_smul_eq_of_support_subset
    (hz : L.IsElementary z) (hz' : L.IsElementary z')
    (hsupp : support z ⊆ support z') :
    ∃ a : 𝕜, a ≠ 0 ∧ z' = a • z := by
  have hsupp' : support z' ⊆ support z :=
    hz'.support_minimal hz.mem hz.ne_zero hsupp
  exact hz.exists_ne_zero_smul_eq_of_support_subset_of_mem hz'.mem hz'.ne_zero hsupp'

/-- Lemma 22.4, textbook scalar form specialized to equal support. -/
theorem exists_ne_zero_smul_eq_of_support_eq
    (hz : L.IsElementary z) (hz' : L.IsElementary z')
    (hsupp : support z = support z') :
    ∃ a : 𝕜, a ≠ 0 ∧ z' = a • z := by
  exact hz.exists_ne_zero_smul_eq_of_support_subset_of_mem hz'.mem hz'.ne_zero hsupp.symm.subset

end Submodule.IsElementary

namespace Submodule

variable {L : Submodule 𝕜 (ι → 𝕜)} {z z' : ι → 𝕜}

/-- Lemma 22.4 on the notation surface: if two vectors are elementary in `L` and have equal
support, then one is a unit scalar multiple of the other. -/
theorem eq_smul_of_support_eq
    (hz : z ∈ L.elementary) (hz' : z' ∈ L.elementary)
    (hsupp : support z = support z') :
    ∃ a : 𝕜ˣ, z' = a • z := by
  have hzE : L.IsElementary z := by
    simpa [Submodule.mem_elementary] using hz
  have hzE' : L.IsElementary z' := by
    simpa [Submodule.mem_elementary] using hz'
  exact hzE.eq_smul_of_support_eq hzE' hsupp

/-- Lemma 22.4 on the notation surface, nonzero-scalar form. -/
theorem exists_ne_zero_smul_eq_of_support_eq
    (hz : z ∈ L.elementary) (hz' : z' ∈ L.elementary)
    (hsupp : support z = support z') :
    ∃ a : 𝕜, a ≠ 0 ∧ z' = a • z := by
  have hzE : L.IsElementary z := by
    simpa [Submodule.mem_elementary] using hz
  have hzE' : L.IsElementary z' := by
    simpa [Submodule.mem_elementary] using hz'
  exact hzE.exists_ne_zero_smul_eq_of_support_eq hzE' hsupp

end Submodule

end
