import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_5_1 (from Items/Chap04) -/
universe u

noncomputable section

section

variable {X : Type u} (r : FreeGroup X)

local instance : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X
local notation "G" => PresentedGroup (Set.singleton r)
local notation "gen" => (PresentedGroup.of : X → G)

/-!
Primary domain: one-relator groups and Magnus's Freiheitssatz.

Layer triage:
- `source-facing`: a one-relator quotient `G = ⟨X ; r⟩`, a subset `L ⊆ X` omitting a generator
  `x` that occurs in the cyclically reduced relator `r`, and the conclusion that the images of `L`
  form a free basis of the subgroup they generate.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `PresentedGroup.of` for the generator map, and
  `freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis` from Theorem `2-6-1` as the owner
  theorem for this one-relator Freiheitssatz statement.
- `bridge/view`: `basisLetterOccurs basis x r` is the project's canonical occurrence predicate for
  the source phrase “the generator `x` occurs in `r`”.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the owner abstraction for the one-relator group
   `⟨X ; r⟩`.
2. `PresentedGroup.of` is the canonical map sending each generator of `X` to its class in that
   quotient.
3. `basisLetterOccurs basis x r` is the established project API for occurrence of a generator in a
   relator.
4. `freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis` from Theorem `2-6-1` is the
   upstream owner theorem already expressing this chapter item at the canonical owner level.

Primitive vs. derived:
the primitive source data are the relator `r`, the subset `L`, and the omitted generator `x`
occurring in `r`; the subgroup `Subgroup.closure (gen '' L)` and the basis assertion on its
generator-image subset are derived owner-side objects. This item therefore recalls the Chapter
`2-6-1` owner theorem directly instead of keeping parallel local wrapper theorems.
-/

/- Theorem 4-5-1 adds no new owner-level construction beyond Theorem `2-6-1`. The recalled theorem
already contains the source-facing free-basis conclusion together with the stronger injectivity
statement for the generator images. -/
#check (freiheitssatz_injOn_presentedGroup_of_and_isFreeGroupBasis r :
  ∀ (L : Set X) {x : X},
    FreeGroup.IsCyclicallyReduced r.toWord →
      basisLetterOccurs basis x r →
        x ∉ L →
          Set.InjOn gen L ∧
            IsFreeGroupBasis {g : Subgroup.closure (gen '' L) | (g : G) ∈ gen '' L})

end

/-! ### Theorem_4_5_2 (from Items/Chap04) -/
universe u

section

/-!
Primary domain: one-relator groups and torsion in one-relator quotients.

Layer triage:
- `source-facing`: a one-relator group on generators `X` with defining relator `r`, together
  with the two torsion alternatives from the textbook: the quotient is torsion free when `r` is
  not a proper power, and when `r = u ^ n` with `u` root-free, the image of `u` has exact order
  `n` and controls all finite-order elements up to conjugacy.
- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` is the owner for the one-relator
  quotient, `PresentedGroup.mk` is the canonical image map, `IsMulTorsionFree`, `orderOf`,
  `IsOfFinOrder`, and `IsConj` are the owner predicates for torsion, exact order, finite order,
  and conjugacy, and `IsProperPower` is the project predicate for proper powers.
- `bridge/view`: the textbook generator list `⟨t, b, c, … ; r⟩` carries no extra owner-level data
  beyond the ambient free group on a type `X`, and the cyclically reduced hypothesis on `r` is
  redundant for the final torsion statements, so it is omitted from the public Lean API.

Domain sampling:
1. `PresentedGroup ({r} : Set (FreeGroup X))` is the established owner abstraction for a
   one-relator group in this project.
2. `isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower` already records the
   torsion-free clause at exactly that owner level.
3. `orderOf_root_image_eq_maximal_exponent` and
   `exists_isConj_zpow_root_image_of_isOfFinOrder` already give the exact-order and torsion
   conjugacy conclusions for a chosen maximal root of the relator.
4. The remaining bridge needed here is only the maximal-root consequence of the hypothesis that
   the chosen root `u` is itself not a proper power.

Primitive vs. derived:
the primitive public data are the relator `r` and, in the torsion case, a chosen root `u` with
`r = u ^ n` and `u` not a proper power. Torsion-freeness, exact order, and conjugacy of
finite-order elements are derived owner-level conclusions on the quotient.
-/

variable {X : Type u}

/- Theorem 4-5-2 (1): if the relator `r` of a one-relator group is not a proper power in the
ambient free group, then the quotient `PresentedGroup ({r} : Set (FreeGroup X))` is torsion free.
This is exactly Proposition `2-5-17`, so the file reuses that canonical theorem directly rather
than keeping a duplicate local wrapper. -/
#check isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower

section

variable (r u : FreeGroup X) (n : ℕ+)

local notation "rels" => (Set.singleton r : Set (FreeGroup X))
local notation "G" => PresentedGroup rels
local notation "q" => PresentedGroup.mk rels

/-- If `r = u ^ n` and `u` is root-free, then `n` is maximal among all positive root exponents
of `r`. This is the only local bridge needed to reuse Proposition `2-5-16`. -/
private theorem relator_root_exponent_le_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u) {t : FreeGroup X} {m : ℕ+}
    (ht : r = t ^ (m : ℕ)) :
    m ≤ n := by
  have hpow : u ^ (n : ℕ) = t ^ (m : ℕ) := by
    calc
      u ^ (n : ℕ) = r := hroot.symm
      _ = t ^ (m : ℕ) := ht
  have hu_ne_one : u ≠ 1 := by
    intro hu1
    apply hu
    refine ⟨1, 2, by decide, by simp [hu1]⟩
  have hcomm : Commute (u ^ ((n : ℕ) : ℤ)) (t ^ ((m : ℕ) : ℤ)) := by
    simp [zpow_natCast, hpow]
  rcases exists_common_zpowers_generator_of_commute_zpow u t ((n : ℕ) : ℤ) ((m : ℕ) : ℤ)
      (by exact_mod_cast n.ne_zero) (by exact_mod_cast m.ne_zero) hcomm with
    ⟨c, hu_mem, ht_mem⟩
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hu_mem
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp ht_mem
  have hc_ne_one : c ≠ 1 := by
    intro hc
    apply hu_ne_one
    rw [← ha, hc]
    simp
  have ha_abs_le_one : Int.natAbs a ≤ 1 := by
    by_contra hle
    have hgt : 1 < Int.natAbs a := lt_of_not_ge hle
    apply hu
    cases a with
    | ofNat k =>
        refine ⟨c, k, hgt, ?_⟩
        simpa [zpow_natCast] using ha
    | negSucc k =>
        refine ⟨c⁻¹, k.succ, hgt, ?_⟩
        simpa using ha
  have ha_ne_zero : a ≠ 0 := by
    intro ha0
    apply hu_ne_one
    rw [← ha, ha0]
    simp
  have ha_abs_pos : 0 < Int.natAbs a := Int.natAbs_pos.mpr ha_ne_zero
  have ha_abs_eq_one : Int.natAbs a = 1 := by omega
  have hc_not_fin : ¬ IsOfFinOrder c := not_isOfFinOrder_of_isMulTorsionFree hc_ne_one
  have hexp : a * ((n : ℕ) : ℤ) = b * ((m : ℕ) : ℤ) := by
    apply (injective_zpow_iff_not_isOfFinOrder.mpr hc_not_fin)
    calc
      c ^ (a * ((n : ℕ) : ℤ)) = (c ^ a) ^ (((n : ℕ) : ℤ)) := by rw [zpow_mul]
      _ = u ^ (((n : ℕ) : ℤ)) := by rw [ha]
      _ = t ^ (((m : ℕ) : ℤ)) := by rw [zpow_natCast, zpow_natCast, hpow]
      _ = (c ^ b) ^ (((m : ℕ) : ℤ)) := by rw [hb]
      _ = c ^ (b * ((m : ℕ) : ℤ)) := by rw [zpow_mul]
  have hnatAbs : Int.natAbs a * (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa [Int.natAbs_mul] using congrArg Int.natAbs hexp
  have hn_eq' : 1 * (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa [ha_abs_eq_one] using hnatAbs
  have hn_eq : (n : ℕ) = Int.natAbs b * (m : ℕ) := by
    simpa using hn_eq'
  have hb_abs_ne_zero : Int.natAbs b ≠ 0 := by
    intro hb0
    have hn_zero : (n : ℕ) = 0 := by
      simp [hn_eq, hb0]
    exact n.ne_zero hn_zero
  have hb_abs_pos : 1 ≤ Int.natAbs b := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hb_abs_ne_zero)
  calc
    (m : ℕ) ≤ Int.natAbs b * (m : ℕ) := by
      simpa using Nat.mul_le_mul_right (m : ℕ) hb_abs_pos
    _ = n := hn_eq.symm

/-- Theorem 4-5-2 (2): if `r = u ^ n` and `u` is not a proper power, then the image of `u` in the
one-relator quotient has exact order `n`. -/
-- Proof sketch: the private helper identifies `n` as the maximal positive root exponent of `r`.
-- Apply the existing maximal-root one-relator torsion theorem from Proposition `2-5-16`.
theorem orderOf_relator_root_image_eq_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u) :
    orderOf (q u) = n := by
  simpa using
    orderOf_root_image_eq_maximal_exponent r u n hroot
      (fun {_} {_} ht ↦ relator_root_exponent_le_of_not_properPower r u n hroot hu ht)

/-- Theorem 4-5-2 (3): if `r = u ^ n` and `u` is not a proper power, then every finite-order
element of the one-relator quotient is conjugate to an integral power of the image of `u`. -/
-- Proof sketch: reuse the same maximal-root bridge and then apply Proposition `2-5-16 (2)`.
theorem exists_isConj_zpow_relator_root_image_of_isOfFinOrder_of_not_properPower
    (hroot : r = u ^ (n : ℕ)) (hu : ¬ IsProperPower u)
    (g : G) (hg : IsOfFinOrder g) :
    ∃ k : ℤ, IsConj g ((q u) ^ k) := by
  simpa using
    exists_isConj_zpow_root_image_of_isOfFinOrder r u n hroot
      (fun {_} {_} ht ↦ relator_root_exponent_le_of_not_properPower r u n hroot hu ht) g hg

end

end

/-! ### Theorem_4_5_3 (from Items/Chap04) -/
universe u

namespace GroupPresentation

section

variable {X : Type u} [Primcodable X]

/-!
Primary domain: algorithmic one-relator group theory and the generalized word problem for
subgroups generated by recursive subsets of the distinguished generators.

Layer triage:
- `source-facing`: a one-relator group `G = ⟨X ; r⟩`, a recursive subset `L ⊆ X`, the subgroup
  generated by the image of `L`, and the decision problem of whether a signed word on `X`
  represents an element of that subgroup.
- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))` for the one-relator quotient,
  `PresentedGroup.mk` for evaluation of signed words in the quotient, `PresentedGroup.of` for the
  distinguished generators, `Subgroup.closure` for the generated subgroup, and `ComputablePred`
  for the algorithmic statement.
- `bridge/view`: Proposition `2-5-5` already states exactly this subgroup-membership problem on
  the canonical owner objects, so this file should recall that theorem directly rather than keep a
  second wrapper theorem.

Domain sampling:
1. `PresentedGroup ({r} : Set (FreeGroup X))` is the project owner for one-relator groups.
2. `PresentedGroup.mk` is the canonical evaluation map from signed words to the quotient.
3. `Subgroup.closure (PresentedGroup.of '' L)` is the canonical subgroup generated by a subset of
   the distinguished generators.
4. `computable_represents_element_of_generatorImageSubgroup` from Proposition `2-5-5` already
   provides the exact owner-level computability statement needed here.

Primitive vs. derived:
the primitive source data are the relator `r`, the recursive subset `L`, and the signed input
word. The subgroup generated by `L` inside the one-relator quotient is a derived owner-side
object, so no parallel local wrapper theorem should remain in this file.
-/

/- Theorem 4-5-3 adds no new owner-level construction beyond Proposition `2-5-5`. The upstream
theorem already has the exact source-faithful interface for deciding whether a signed word
represents an element of the subgroup generated by a recursive subset of the distinguished
generators in a one-relator quotient. -/
#check computable_represents_element_of_generatorImageSubgroup

end

end GroupPresentation

/-! ### Definition_4_5_4 (from Items/Chap04) -/
universe u

set_option autoImplicit false

section

variable {X : Type u} (r : FreeGroup X)

local notation "G" => PresentedGroup (Set.singleton r)

/-!
Primary domain: one-relator groups and Magnus subgroups.

Layer triage:
- `source-facing`: a one-relator group `G = ⟨X ; r⟩` together with a subgroup generated by a subset
  `L ⊆ X` omitting some generator that occurs in the relator `r`.
- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
  `PresentedGroup.of` for the generator images, and `Subgroup.closure` for the subgroup generated
  by those images.
- `bridge/view`: `basisLetterOccurs (FreeGroupBasis.ofFreeGroup X) x r` is the chapter's canonical
  occurrence predicate expressing that the generator `x` occurs in the relator `r`.

Domain sampling:
1. `PresentedGroup (Set.singleton r)` is the canonical owner for the one-relator quotient
   `⟨X ; r⟩`.
2. `PresentedGroup.of` is the canonical map sending each generator of `X` to its class in that
   quotient.
3. `Subgroup.closure (PresentedGroup.of '' L)` is the owner-side rendering of the subgroup
   generated by the image of a subset `L ⊆ X`.
4. `basisLetterOccurs (FreeGroupBasis.ofFreeGroup X) x r` is the existing project API for the
   source phrase “the generator `x` occurs in `r`”.

Primitive vs. derived:
the primitive source data are the relator `r`, the subgroup `M`, a generating subset `L ⊆ X`, and
an omitted generator `x` occurring in `r`. The subgroup generated by `L` inside `G` is the derived
owner-side object `Subgroup.closure (PresentedGroup.of '' L)`, so no parallel wrapper or
duplicate unpacking API is introduced.
-/

/-- Definition 4-5-4: a subgroup `M` of the one-relator group `G = ⟨X ; r⟩` is a Magnus subgroup
when `M` is generated by the image of a subset `L ⊆ X` omitting some generator that occurs in the
relator `r`. -/
def IsMagnusSubgroup (M : Subgroup G) : Prop :=
  ∃ L : Set X, ∃ x : X,
    basisLetterOccurs (FreeGroupBasis.ofFreeGroup X) x r ∧
      x ∉ L ∧
      M = Subgroup.closure (PresentedGroup.of '' L)

end

/-! ### Theorem_4_5_5 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open scoped Pointwise

noncomputable section

-- Layer triage:
-- `source-facing`: a one-relator group `PresentedGroup (Set.singleton r)`, a Magnus subgroup in
-- the sense of Definition `4-5-4`, and the intersection of that subgroup with a nontrivial
-- conjugate.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for the one-relator quotient,
-- `IsMagnusSubgroup` from Definition `4-5-4` for the source-facing Magnus subgroup predicate, and
-- subgroup conjugation via the action of `MulAut.conj`.
-- `bridge/view`: this theorem is stated directly with the chapter owner predicate, so no parallel
-- local Magnus-subgroup wrapper is kept here.
--
-- Domain sampling:
-- 1. `PresentedGroup (Set.singleton r)` is the chapter's canonical owner for the one-relator
--    group with defining relator `r`.
-- 2. `IsMagnusSubgroup` from Definition `4-5-4` is the existing source-facing predicate for
--    Magnus subgroups.
-- 3. `MulAut.conj g • M` is mathlib's canonical API for the conjugate subgroup `gMg⁻¹`.
--
-- Primitive vs. derived:
-- the primitive source-facing data are the relator `r`, the subgroup `M`, and the owner-level
-- hypothesis `IsMagnusSubgroup r M`, and the theorem's cyclicity conclusion is stated directly for the
-- canonical conjugate-intersection subgroup.

variable {X : Type u}
variable (r : FreeGroup X)

local instance : DecidableEq X := Classical.decEq X

local notation "G" => PresentedGroup (Set.singleton r)

/-- Theorem 4-5-5: if `r` is cyclically reduced, `M` is a Magnus subgroup of the one-relator
group `PresentedGroup (Set.singleton r)`, and `g` does not lie in `M`, then the
intersection `gMg⁻¹ ∩ M` is cyclic. -/
-- Proof sketch: argue by induction on the length of the cyclically reduced relator. The
-- two-generator case is handled by viewing the group as a free product with amalgamation and using
-- normal-form uniqueness to force the intersection into the amalgamated cyclic subgroup. In the
-- general case, rewrite the one-relator group as an HNN extension after arranging a generator of
-- exponent sum zero; Britton's lemma then reduces a noncyclic conjugate intersection to the
-- induction hypothesis on a shorter relator, and the standard zero-exponent-sum trick covers the
-- remaining case.
theorem conjugate_intersection_isCyclic_of_isMagnusSubgroup
    (hred : FreeGroup.IsCyclicallyReduced r.toWord)
    (M : Subgroup G) (hM : IsMagnusSubgroup r M) (g : G)
    (hg : g ∉ M) :
    IsCyclic ↥((MulAut.conj g • M) ⊓ M) :=
  sorry

end

/-! ### Theorem_4_5_6 (from Items/Chap04) -/
universe u

set_option autoImplicit false

open List

noncomputable section

section

variable {X : Type u}

local instance : DecidableEq X := Classical.decEq X

local notation "basis" => FreeGroupBasis.ofFreeGroup X

private theorem not_basisLetterOccurs_mk_of_not_mem_map_fst
    {word : List (X × Bool)} {x : X} (hx : x ∉ word.map Prod.fst) :
    ¬ basisLetterOccurs basis x (FreeGroup.mk word) := by
  rw [basisLetterOccurs, reducedWordSupport, List.mem_toFinset]
  intro hx'
  have hxred : x ∈ (FreeGroup.reduce word).map Prod.fst := by
    simpa [FreeGroupBasis.ofFreeGroup, FreeGroup.toWord_mk] using hx'
  have hred : FreeGroup.Red word (FreeGroup.reduce word) := FreeGroup.reduce.red
  have hsub : (FreeGroup.reduce word).map Prod.fst <+ word.map Prod.fst := by
    simpa using (FreeGroup.Red.sublist hred).map Prod.fst
  exact hx <| hsub.subset hxred

-- Layer triage:
-- `source-facing`: a cyclically reduced relator word `relator`, a freely reduced word `w`, a
-- second word `v` omitting some generator occurring in `w`, and equality of the two words in the
-- one-relator torsion quotient with defining relator `(FreeGroup.mk relator) ^ n`.
-- `core/canonical`: Proposition `2-5-27` is the existing owner theorem for long overlaps in the
-- quotient `PresentedGroup ({s ^ n} : Set (FreeGroup X))`, using `List.IsInfix`,
-- `basisLetterOccurs basis`, `FreeGroup.IsCyclicallyReduced`, and `PresentedGroup.mk`.
-- `bridge/view`: this file keeps the stronger source-facing omission hypothesis on the displayed
-- list word `v` and specializes the owner theorem to the displayed reduced words.
--
-- Domain sampling:
-- 1. `exists_long_common_part_with_relator_of_eq_in_power_relator_quotient` from Proposition
--    `2-5-27` is the chapter's owner theorem for the long-overlap conclusion in a torsion
--    one-relator quotient.
-- 2. `basisLetterOccurs basis` from Proposition `1-7-4` is the existing occurrence predicate for
--    generators in the canonical reduced word of a free-group element.
-- 3. `List.IsInfix` from mathlib is the owner predicate for consecutive subwords of reduced
--    words.
-- 4. Mathlib's `FreeGroup.pow_mk`, `FreeGroup.toWord_mk`, and
--    `FreeGroup.IsCyclicallyReduced.flatten_replicate` are the canonical length API turning the
--    owner theorem's bound into the source-facing bound on `((FreeGroup.mk relator) ^ n).toWord`.
--
-- Primitive vs. derived:
-- the primitive public data are the displayed words `relator`, `w`, `v`, the exponent `n`, and
-- the quotient equality between `w` and `v`; the canonical occurrence and long-overlap predicates
-- are derived bridge API used only internally to express the proof through the upstream owner
-- theorem.

/-- Theorem 4-5-6: if `G = ⟨X ; r^n = 1⟩` with `r` cyclically reduced and `n > 1`, and a freely
reduced word `w` is equal in `G` to a word `v` omitting some generator that occurs in `w`, then
`w` contains a contiguous subword that is also a subword of the reduced word of `r^n` or `r⁻ⁿ`,
and whose length is greater than `(n - 1) / n` times the length of `r^n`. The fractional bound is
rendered as the equivalent natural-number inequality
`n * segment.length > (n - 1) * (((FreeGroup.mk relator : FreeGroup X) ^ n).toWord.length)`. -/
-- Proof sketch: this is the long-overlap theorem for one-relator torsion groups. One applies the
-- Magnus breakdown of the equality `w = v` in the quotient by `r^n`, reducing first to the case
-- where the omitted generator occurs in the defining relator. Induct on the length of the
-- cyclically reduced relator and use the HNN-extension/free-product normal-form analysis to force
-- a long overlap between `w` and one of the cyclic conjugates of `r^n` or `r⁻ⁿ`.
theorem exists_long_relatorPower_subword_of_eq_in_oneRelatorTorsion
    (relator w v : List (X × Bool)) (n : ℕ)
    (hr_cyclic : FreeGroup.IsCyclicallyReduced relator)
    (hw_reduced : FreeGroup.IsReduced w)
    (hn : 1 < n)
    (heq :
      PresentedGroup.mk (Set.singleton ((FreeGroup.mk relator : FreeGroup X) ^ n))
          (FreeGroup.mk w) =
        PresentedGroup.mk (Set.singleton ((FreeGroup.mk relator : FreeGroup X) ^ n))
          (FreeGroup.mk v))
    (homit : ∃ x : X, x ∈ w.map Prod.fst ∧ x ∉ v.map Prod.fst) :
    ∃ segment : List (X × Bool),
      segment <:+: w ∧
        (segment <:+: (FreeGroup.mk relator ^ n).toWord ∨
          segment <:+: ((FreeGroup.mk relator ^ n)⁻¹).toWord) ∧
        n * segment.length >
          (n - 1) * ((FreeGroup.mk relator ^ n).toWord.length) := by
  classical
  let s : FreeGroup X := FreeGroup.mk relator
  rcases homit with ⟨x, hxw, hxv⟩
  have hs_cyclic : FreeGroup.IsCyclicallyReduced s.toWord := by
    simpa [s, FreeGroup.toWord_mk, hr_cyclic.isReduced.reduce_eq] using hr_cyclic
  have hoccurs_w : basisLetterOccurs basis x (FreeGroup.mk w) := by
    have hoccurs_w_iff : basisLetterOccurs basis x (FreeGroup.mk w) ↔ x ∈ w.map Prod.fst := by
      rw [basisLetterOccurs, reducedWordSupport, List.mem_toFinset]
      simp [FreeGroupBasis.ofFreeGroup, FreeGroup.toWord_mk, hw_reduced.reduce_eq]
    exact hoccurs_w_iff.2 hxw
  have hnot_occurs_v : ¬ basisLetterOccurs basis x (FreeGroup.mk v) := by
    exact not_basisLetterOccurs_mk_of_not_mem_map_fst hxv
  obtain ⟨segment, hwpart, hrelpart, hlen⟩ :=
    exists_long_common_part_with_relator_of_eq_in_power_relator_quotient
      s n (FreeGroup.mk w) (FreeGroup.mk v)
      hn hs_cyclic (by simpa [s] using heq) hoccurs_w hnot_occurs_v
  have hs_norm : s.norm = relator.length := by
    simp [s, FreeGroup.norm, FreeGroup.toWord_mk, hr_cyclic.isReduced.reduce_eq]
  have hpow_len : (s ^ n).toWord.length = n * s.norm := by
    simp [s, hs_norm, FreeGroup.pow_mk, FreeGroup.toWord_mk,
      (hr_cyclic.flatten_replicate n).isReduced.reduce_eq]
  refine ⟨segment, ?_, ?_, ?_⟩
  · simpa [FreeGroup.toWord_mk, hw_reduced.reduce_eq] using hwpart
  · simpa [s] using hrelpart
  · have hn_pos : 0 < n := lt_trans Nat.zero_lt_one hn
    have hlen' : n * segment.length > n * ((n - 1) * s.norm) :=
      Nat.mul_lt_mul_of_pos_left hlen hn_pos
    have hpow_len' : ((FreeGroup.mk relator : FreeGroup X) ^ n).toWord.length = n * s.norm := by
      simpa [s] using hpow_len
    rw [gt_iff_lt, hpow_len']
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlen'

end
