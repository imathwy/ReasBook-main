import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_2 (from Chap07) -/
universe u

open scoped InnerProductSpace Pointwise

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

local notation "σ[" C "]" => fun u ↦ sSup ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)

/-- Helper for Exercise 7.2: the inner-product image of a Minkowski sum is the pairwise-sum image
of the two inner-product images. -/
private lemma inner_image_add_eq_image2_add (C D : Set 𝓗) (u : 𝓗) :
    ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' (C + D)) =
      Set.image2 (· + ·) ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' C)
        ((fun x : 𝓗 ↦ (⟪x, u⟫_ℝ : EReal)) '' D) := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨x, hx, rfl⟩
    rcases Set.mem_add.mp hx with ⟨c, hc, d, hd, rfl⟩
    -- Unpack membership in the Minkowski sum into a pair `(c,d)` and rewrite the inner product.
    refine Set.mem_image2.mpr ?_
    refine ⟨(⟪c, u⟫_ℝ : EReal), ⟨c, hc, rfl⟩, (⟪d, u⟫_ℝ : EReal), ⟨d, hd, rfl⟩, ?_⟩
    simp [inner_add_left]
  · intro hr
    rcases Set.mem_image2.mp hr with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨c, hc, rfl⟩
    rcases hb with ⟨d, hd, rfl⟩
    -- Reassemble the scalar witnesses into a point of `C + D`.
    refine ⟨c + d, Set.mem_add.mpr ⟨c, hc, d, hd, rfl⟩, ?_⟩
    simpa [inner_add_left] using hab

/-- Helper for Exercise 7.2: the supremum of all pairwise sums in `EReal` is the sum of the two
individual suprema. -/
private lemma sSup_image2_add_eq (A B : Set EReal) :
    sSup (Set.image2 (· + ·) A B) = sSup A + sSup B := by
  apply le_antisymm
  · -- Every pairwise sum is bounded above by the sum of the two suprema.
    refine sSup_le ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact add_le_add (le_sSup ha) (le_sSup hb)
  · -- Approximate each supremum from below and combine the two approximants.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_sSup_iff.mp ha with ⟨a', ha', haa'⟩
    rcases lt_sSup_iff.mp hb with ⟨b', hb', hbb'⟩
    have hab' : a + b < a' + b' := EReal.add_lt_add haa' hbb'
    exact hab'.le.trans <| le_sSup <| Set.mem_image2.mpr ⟨a', ha', b', hb', rfl⟩

-- Proof sketch: evaluate both sides at `u`, expand `σ[C + D] u` and the pointwise sum
-- `σ[C] u + σ[D] u` as suprema of inner-product images, and use
-- `⟪c + d, u⟫ = ⟪c, u⟫ + ⟪d, u⟫` together with the elementary identity
-- `sup {a + b | a ∈ A, b ∈ B} = sup A + sup B` in `EReal`.
/-- Exercise 7.2: the support function of the Minkowski sum of two subsets of a real Hilbert
space is the pointwise sum of their support functions. -/
theorem supportFunction_minkowski_sum_eq_add (C D : Set 𝓗) :
    σ[C + D] = σ[C] + σ[D] := by
  -- Evaluate the function identity at an arbitrary direction `u`.
  ext u
  -- Rewrite the scalar image of `C + D` as pairwise sums of scalar images from `C` and `D`.
  rw [Pi.add_apply, inner_image_add_eq_image2_add]
  -- The supremum of these pairwise sums is the sum of the two scalar suprema.
  exact sSup_image2_add_eq _ _

/-! ### Proposition_7_2 (from Chap07) -/
open Set
open scoped InnerProductSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: enlarging the set can only increase the support value. -/
private lemma innerSupremumOn_mono {A B : Set E} (hAB : A ⊆ B) (u : E) :
    innerSupremumOn A u ≤ innerSupremumOn B u := by
  -- Compare the two support values through inclusion of the defining images.
  rw [innerSupremumOn_eq_sSup_image, innerSupremumOn_eq_sSup_image]
  exact sSup_le_sSup <| by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hAB hx, rfl⟩

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: a pointwise upper bound on `⟪x, u⟫` over `S` bounds the support
value of `S` at `u`. -/
private lemma innerSupremumOn_le_of_forall_inner_le {S : Set E} {u : E} {b : EReal}
    (hbound : ∀ x ∈ S, (⟪x, u⟫_ℝ : EReal) ≤ b) :
    innerSupremumOn S u ≤ b := by
  -- Show that `b` is an upper bound for every value in the image defining the support function.
  rw [innerSupremumOn_eq_sSup_image]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hbound x hx

omit [CompleteSpace E] in
/-- Helper for Proposition 7.2: taking the closure of a set does not change its support value. -/
private lemma innerSupremumOn_closure_eq (S : Set E) (u : E) :
    innerSupremumOn (closure S) u = innerSupremumOn S u := by
  apply le_antisymm
  · -- Every point of `closure S` still lies in the closed halfspace determined by `σ[S] u`.
    refine innerSupremumOn_le_of_forall_inner_le ?_
    intro x hx
    have hclosed :
        IsClosed {z : E | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      simpa [Set.preimage, Set.setOf_mem_eq] using
        (isClosed_Iic.preimage
          (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const)))
    have hsubset :
        S ⊆ {z : E | (⟪z, u⟫_ℝ : EReal) ≤ innerSupremumOn S u} := by
      intro z hz
      rw [innerSupremumOn_eq_sSup_image]
      have hz_mem :
          (⟪z, u⟫_ℝ : EReal) ∈ ((fun y : E ↦ (⟪y, u⟫_ℝ : EReal)) '' S) :=
        ⟨z, hz, rfl⟩
      exact (isLUB_sSup _).1 hz_mem
    exact closure_minimal hsubset hclosed hx
  · -- The reverse inequality is immediate from `S ⊆ closure S`.
    exact innerSupremumOn_mono subset_closure u

/-- Proposition 7.2 (1): if `C ⊆ D`, then every support point of `D` that lies in `C` is a
support point of `C`, expressed using the textbook `spts` notation. -/
theorem inter_exposedPoints_subset_of_subset
    (C D : Set E) (hCD : C ⊆ D) :
    C ∩ spts D ⊆ spts C := by
  intro x hx
  rcases hx with ⟨hxC, hxD⟩
  rw [Set.mem_supportPoints_iff] at hxD ⊢
  rcases hxD with ⟨_, u, hu0, hu_support⟩
  -- Reuse the exposing vector for `D` and restrict the support inequality along `C ⊆ D`.
  refine ⟨hxC, u, hu0, ?_⟩
  exact le_trans (innerSupremumOn_mono hCD u) hu_support

-- Proof sketch: one inclusion follows from the first clause applied to `C ⊆ closure C`.
-- For the reverse inclusion, an exposing functional for `C` extends to `closure C` by continuity,
-- and the point remains in `C` by definition.
/-- Proposition 7.2 (2): the support points of `C` are exactly the points of `C` that are support
points of `closure C`. -/
theorem exposedPoints_eq_inter_exposedPoints_closure
    (C : Set E) :
    spts C = C ∩ spts (closure C) := by
  -- Route correction: work directly with the textbook `spts` witness and closure invariance of
  -- `innerSupremumOn`, rather than with the earlier off-spec exposed-point formulation.
  ext x
  constructor
  · intro hx
    rw [Set.mem_supportPoints_iff] at hx
    rcases hx with ⟨hxC, u, hu0, hu_support⟩
    -- Keep the same exposing vector and move the support inequality from `C` to `closure C`.
    refine ⟨hxC, ?_⟩
    rw [Set.mem_supportPoints_iff]
    refine ⟨subset_closure hxC, u, hu0, ?_⟩
    simpa [innerSupremumOn_closure_eq (S := C) (u := u)] using hu_support
  · intro hx
    -- Apply the inclusion statement to `C ⊆ closure C`.
    exact inter_exposedPoints_subset_of_subset C (closure C) subset_closure hx

end
