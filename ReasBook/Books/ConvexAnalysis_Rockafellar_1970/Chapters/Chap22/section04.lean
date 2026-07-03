import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_22_4_1 (from Chap04) -/
open Function

section

universe u

variable {ι : Type*} [Finite ι]
variable {E : Type*} [Zero E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 22.4.1 says that a subspace of `𝕜^ι` (with finite coordinate type)
  has only finitely many elementary vectors up to nonzero scalar multiples.
- `core/canonical`: finite support-class representatives are first organized at the intrinsic
  carrier-set owner `Set.IsElementary`.
- `bridge/view`: the chapter-facing `Submodule` theorems are thin bridges from that intrinsic
  owner.

Domain-style sampling used here:
- `Set.IsElementary` from `Text_22_3_12` as the primitive owner predicate;
- `Set.elementary` from `Text_22_3_12` as the primitive owner-side set surface;
- `Submodule.IsElementary` from `Text_22_3_12` as the owner predicate;
- `Submodule.elementary` from `Text_22_3_12` as the canonical owner-side set surface;
- `Submodule.IsElementary.support_minimal` from `Text_22_3_12`;
- `Submodule.IsElementary.eq_smul_of_support_eq` from `Lemma_22_4`;
- `Submodule.eq_span_elementary` from `Lemma_22_5`.

Primitive data vs derived API:
- primitive owner data already upstream: the carrier set `S : Set (ι → E)` and the predicate
  `S.IsElementary`;
- derived API here: finiteness of support classes and support-class representatives at the
  primitive owner level, then the stronger nonzero-scalar representative theorem in the
  `DivisionRing`/`Submodule` specialization.

Layer target: intrinsic owner first (`Set`), with `Submodule` bridge theorems.
-/

-- Proof sketch: there are only finitely many subsets of `ι`, hence only finitely many support
-- classes of elementary vectors in `S`. For each support that occurs, choose one elementary
-- representative; Lemma 22.4 shows that any other elementary vector with the same support is a
-- nonzero scalar multiple of that representative.
namespace Set

/-- The support classes of the elementary vectors of `S` form a finite set. -/
theorem finite_supports_of_elementary (S : Set (ι → E)) :
    (support '' S.elementary).Finite := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  exact Set.toFinite _

/-- Primitive finite-class form: the elementary vectors of `S` admit finitely many representatives
for their support classes. -/
theorem exists_finset_elementary_support_representatives
    (S : Set (ι → E)) :
    ∃ T : Finset (ι → E),
      (↑T : Set (ι → E)) ⊆ S.elementary ∧
        ∀ z, z ∈ S.elementary →
          ∃ y, y ∈ T ∧ support z = support y := by
  classical
  have hsupports_finite : (support '' S.elementary).Finite := S.finite_supports_of_elementary
  let supports : Finset (Set ι) := hsupports_finite.toFinset
  have hsupports :
      ∀ s : {s // s ∈ supports}, ∃ z : ι → E, z ∈ S.elementary ∧ support z = s.1 := by
    intro s
    exact hsupports_finite.mem_toFinset.mp s.2
  choose rep hrep_elem hrep_support using hsupports
  let T : Finset (ι → E) := supports.attach.image rep
  refine ⟨T, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨s, -, rfl⟩
    exact hrep_elem s
  · intro z hz
    have hz_support : support z ∈ supports := by
      exact hsupports_finite.mem_toFinset.mpr ⟨z, hz, rfl⟩
    let s : {s // s ∈ supports} := ⟨support z, hz_support⟩
    have hy_mem : rep s ∈ T := by
      refine Finset.mem_image.mpr ?_
      exact ⟨s, by simp, rfl⟩
    exact ⟨rep s, hy_mem, by simpa [s] using (hrep_support s).symm⟩

/-- Set-level bridge for the primitive finite support-class representatives. -/
theorem exists_finite_elementary_support_representatives
    (S : Set (ι → E)) :
    ∃ T : Set (ι → E), T.Finite ∧
      T ⊆ S.elementary ∧
        ∀ z, z ∈ S.elementary →
          ∃ y ∈ T, support z = support y := by
  classical
  rcases S.exists_finset_elementary_support_representatives with ⟨T, hT_elem, hTrep⟩
  refine ⟨(↑T : Set (ι → E)), T.finite_toSet, hT_elem, ?_⟩
  intro z hz
  rcases hTrep z hz with ⟨y, hyT, hsupport⟩
  exact ⟨y, by simpa using hyT, hsupport⟩

end Set

end

section

variable {ι : Type*} [Finite ι]
variable {𝕜 : Type u} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]

namespace Submodule

/-- Submodule bridge: finiteness of support classes follows from the intrinsic set-level owner. -/
theorem finite_supports_of_elementary (L : Submodule 𝕜 (ι → E)) :
    (support '' L.elementary).Finite := by
  simpa [Submodule.elementary] using
    (Set.finite_supports_of_elementary (S := (L : Set (ι → E))))

/-- Submodule bridge for finite support-class representatives. -/
theorem exists_finset_elementary_support_representatives
    (L : Submodule 𝕜 (ι → E)) :
    ∃ S : Finset (ι → E),
      (↑S : Set (ι → E)) ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y, y ∈ S ∧ support z = support y := by
  simpa [Submodule.elementary] using
    (Set.exists_finset_elementary_support_representatives (S := (L : Set (ι → E))))

/-- Submodule bridge for finite support-class representatives in set form. -/
theorem exists_finite_elementary_support_representatives
    (L : Submodule 𝕜 (ι → E)) :
    ∃ S : Set (ι → E), S.Finite ∧
      S ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y ∈ S, support z = support y := by
  simpa [Submodule.elementary] using
    (Set.exists_finite_elementary_support_representatives (S := (L : Set (ι → E))))

end Submodule

end

section

variable {ι : Type*} [Finite ι]

namespace Set

variable {G : Type*}
variable {E : Type*} [Zero E] [SMul G E]

/-- Intrinsic set-level owner: if elementary vectors of `S` with equal support are scalar
multiples under a chosen action, then `S` has finitely many elementary vectors up to that scalar
multiple relation. -/
theorem exists_finite_elementary_representatives_of_eq_smul_of_support_eq
    (S : Set (ι → E))
    (hsmul :
      ∀ {z y : ι → E},
        z ∈ S.elementary → y ∈ S.elementary → support z = support y →
          ∃ a : G, z = a • y) :
    ∃ T : Set (ι → E), T.Finite ∧
      T ⊆ S.elementary ∧
        ∀ z, z ∈ S.elementary →
          ∃ y ∈ T, ∃ a : G, z = a • y := by
  rcases S.exists_finite_elementary_support_representatives with ⟨T, hT_finite, hT_elem, hTrep⟩
  refine ⟨T, hT_finite, hT_elem, ?_⟩
  intro z hz
  rcases hTrep z hz with ⟨y, hyT, hsupport⟩
  rcases hsmul hz (hT_elem hyT) hsupport with ⟨a, ha⟩
  exact ⟨y, hyT, a, ha⟩

end Set

namespace Submodule

section

variable {𝕜 : Type u} [Semiring 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {G : Type*} [SMul G E]

/-- Intrinsic submodule owner: if elementary vectors in `L` with equal support are scalar
multiples under a chosen action, then `L` has finitely many elementary vectors up to that scalar
multiple relation. -/
theorem exists_finite_elementary_representatives_of_eq_smul_of_support_eq
    (L : Submodule 𝕜 (ι → E))
    (hsmul :
      ∀ {z y : ι → E},
        z ∈ L.elementary → y ∈ L.elementary → support z = support y →
          ∃ a : G, z = a • y) :
    ∃ S : Set (ι → E), S.Finite ∧
      S ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y ∈ S, ∃ a : G, z = a • y := by
  simpa [Submodule.elementary] using
    (Set.exists_finite_elementary_representatives_of_eq_smul_of_support_eq
      (S := (L : Set (ι → E))) (hsmul := hsmul))

/-- Intrinsic submodule owner, operational bridge: the finite representative set can be encoded by
a `Finset`. -/
theorem exists_finset_elementary_representatives_of_eq_smul_of_support_eq
    (L : Submodule 𝕜 (ι → E))
    (hsmul :
      ∀ {z y : ι → E},
        z ∈ L.elementary → y ∈ L.elementary → support z = support y →
          ∃ a : G, z = a • y) :
    ∃ S : Finset (ι → E),
      (↑S : Set (ι → E)) ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y, y ∈ S ∧ ∃ a : G, z = a • y := by
  classical
  rcases L.exists_finite_elementary_representatives_of_eq_smul_of_support_eq hsmul with
    ⟨S, hS_finite, hS_elem, hSrep⟩
  refine ⟨hS_finite.toFinset, ?_, ?_⟩
  · simpa [hS_finite.coe_toFinset] using hS_elem
  · intro z hz
    rcases hSrep z hz with ⟨y, hyS, a, rfl⟩
    exact ⟨y, hS_finite.mem_toFinset.mpr hyS, a, rfl⟩

end

section

variable {𝕜 : Type u} [DivisionRing 𝕜]

/-- Corollary 22.4.1, invariant finite-set form: a subspace `L` of `𝕜^ι` has only finitely many
elementary vectors up to nonzero scalar multiples. Equivalently, there is a finite set of
elementary representatives such that every elementary vector in `L` is a nonzero scalar multiple
of one of them. -/
theorem exists_finite_elementary_representatives
    (L : Submodule 𝕜 (ι → 𝕜)) :
    ∃ S : Set (ι → 𝕜), S.Finite ∧
      S ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y ∈ S, ∃ a : 𝕜ˣ, z = a • y := by
  refine L.exists_finite_elementary_representatives_of_eq_smul_of_support_eq ?_
  intro z y hz hy hsupport
  exact L.eq_smul_of_support_eq hy hz hsupport.symm

/-- Corollary 22.4.1, operational bridge: the invariant finite representative set can be encoded by
a `Finset`. -/
theorem exists_finset_elementary_representatives
    (L : Submodule 𝕜 (ι → 𝕜)) :
    ∃ S : Finset (ι → 𝕜),
      (↑S : Set (ι → 𝕜)) ⊆ L.elementary ∧
        ∀ z, z ∈ L.elementary →
          ∃ y, y ∈ S ∧ ∃ a : 𝕜ˣ, z = a • y := by
  refine L.exists_finset_elementary_representatives_of_eq_smul_of_support_eq ?_
  intro z y hz hy hsupport
  exact L.eq_smul_of_support_eq hy hz hsupport.symm

end

end Submodule

end

/-! ### Lemma_22_4 (from Chap04) -/
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
