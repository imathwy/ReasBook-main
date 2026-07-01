import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Lemma_22_4

-- Declarations for this item will be appended below by the statement pipeline.

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
