import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*} {V : Type*} {P : Type*}
variable [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
open scoped Rockafellar

/- Text 1.9: affine independence is the canonical predicate `AffineIndependent 𝕜`; the chapter
owner for set-level affine-hull dimension is `Set.affineDim`.
For a family `b : Fin (m + 1) → P`, the textbook criterion is that
`dim[𝕜](Set.range b) = m`.
-/
recall AffineIndependent

/- 
Source/core/bridge triage:
- `source-facing`: Text 1.9 identifies affine independence of `m + 1` points with affine-hull
  dimension `m`.
- `core/canonical`: mathlib owns `AffineIndependent`; the chapter set-level owner for affine-hull
  dimension is `Set.affineDim`, backed by `AffineSubspace.affineDim`.
- `bridge/view`: the theorem below is the thin bridge from the owner vector-span criterion to the
  source-facing affine-dimension wording on the point-range set.
- Layer target: `bridge/view`.
- Primitive data vs derived API: this file introduces no new primitive data; it derives the
  textbook criterion from `AffineIndependent`, `Set.affineDim`, and the existing
  owner-side lemmas identifying affine independence with the dimension of the vector span and the
  direction of an affine span with that vector span.
- Domain-style sampling used here:
  `AffineIndependent`,
  `affineIndependent_iff_finrank_vectorSpan_eq`,
  `Set.affineDim`,
  `direction_affineSpan`,
  `finiteDimensional_direction_affineSpan_range`.
-/
namespace AffineIndependent

/-- Intrinsic cardinality form of Text 1.9: a finite family is affinely independent exactly when
the affine dimension of its range is `card - 1`. This is the canonical owner-layer statement;
the `m + 1` textbook form is a thin corollary. -/
theorem iff_range_affineDim_eq_card_sub_one
    {ι : Type*} [Finite ι] (b : ι → P) :
    AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let m' : ℕ := Nat.card ι - 1
    have hcard_pos : 0 < Nat.card ι := Nat.card_pos
    have hcard' : Nat.card ι = m' + 1 := by
      dsimp [m']
      simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hcard_pos).symm
    have hcard_fintype : Fintype.card ι = m' + 1 := by
      simpa [Nat.card_eq_fintype_card] using hcard'
    have hspan : affineSpan 𝕜 (Set.range b) ≠ ⊥ := by
      simp [affineSpan_eq_bot]
    have hmain : AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = m' := by
      change AffineIndependent 𝕜 b ↔ AffineSubspace.affineDim (affineSpan 𝕜 (Set.range b)) = m'
      rw [AffineSubspace.affineDim, if_neg hspan]
      rw [direction_affineSpan]
      simpa using affineIndependent_iff_finrank_vectorSpan_eq 𝕜 b hcard_fintype
    have hcard_int : (Fintype.card ι : ℤ) - 1 = m' := by
      calc
        (Fintype.card ι : ℤ) - 1 = (((m' + 1 : ℕ) : ℤ) - 1) := by simp [hcard_fintype]
        _ = m' := by simp
    simpa [Nat.card_eq_fintype_card, hcard_int] using hmain
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hAI : AffineIndependent 𝕜 b := affineIndependent_of_subsingleton 𝕜 b
    have hdim : dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 := by
      have hrange : Set.range b = (∅ : Set P) := by
        ext x
        simp
      simp [hrange, Set.affineDim, AffineSubspace.affineDim, Nat.card_eq_fintype_card]
    exact ⟨fun _ => hdim, fun _ => hAI⟩

/-- A family of `m + 1` points is affinely independent exactly when the affine dimension of its
range equals `m`. -/
theorem iff_range_affineDim_eq_of_card_eq
    {ι : Type*} {m : ℕ} [Finite ι] (b : ι → P) (hcard : Nat.card ι = m + 1) :
    AffineIndependent 𝕜 b ↔ dim[𝕜](Set.range b) = m := by
  have hmain := iff_range_affineDim_eq_card_sub_one (𝕜 := 𝕜) (b := b)
  have hcard_int : (Nat.card ι : ℤ) - 1 = m := by
    rw [hcard]
    simp
  simpa [hcard_int] using hmain

/-- Owner-level consequence of Text 1.9: an affinely independent finite family has affine-hull
dimension equal to `card - 1`. -/
theorem range_affineDim_eq_card_sub_one
    {ι : Type*} [Finite ι] {b : ι → P} (hb : AffineIndependent 𝕜 b) :
    dim[𝕜](Set.range b) = (Nat.card ι : ℤ) - 1 :=
  (iff_range_affineDim_eq_card_sub_one (𝕜 := 𝕜) (b := b)).1 hb

/-- Owner-level textbook cardinality form: for a finite family of cardinality `m + 1`,
affine independence forces affine dimension `m`. -/
theorem range_affineDim_eq_of_card_eq
    {ι : Type*} {m : ℕ} [Finite ι] {b : ι → P}
    (hb : AffineIndependent 𝕜 b) (hcard : Nat.card ι = m + 1) :
    dim[𝕜](Set.range b) = m :=
  (iff_range_affineDim_eq_of_card_eq (𝕜 := 𝕜) (b := b) (m := m) hcard).1 hb

end AffineIndependent

namespace Affine.Simplex

/-- Owner-level Text 1.9 corollary: the affine dimension of the vertex range of a simplex equals
its index parameter. -/
@[simp] theorem affineDim_range_points_eq {m : ℕ} (s : Affine.Simplex 𝕜 P m) :
    dim[𝕜](Set.range s.points) = m := by
  exact s.independent.range_affineDim_eq_of_card_eq (hcard := Nat.card_fin (m + 1))

end Affine.Simplex
