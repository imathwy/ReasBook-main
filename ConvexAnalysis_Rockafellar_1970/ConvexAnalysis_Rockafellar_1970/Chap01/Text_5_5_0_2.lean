import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {ι : Type u} {𝕜 : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [Finite ι]

open scoped Pointwise Function

namespace Text_5_5_0_2

/-- Helper for Text 5.5.0.2: the owner used here sends a finite-coordinate point to the supremum
of its coordinate range. This is the local source-faithful replacement for the missing imported
owner artifact. -/
def greatestCoordinate {ι : Type u} {α : Type w} [SupSet α] [Finite ι] [Nonempty ι] :
    (ι → α) → α :=
  fun x ↦ sSup (Set.range x)

/-- Helper for Text 5.5.0.2: unfolding the local greatest-coordinate owner exposes the supremum
of the coordinate range. -/
@[simp] theorem greatestCoordinate_apply {ι : Type u} {α : Type w} [SupSet α] [Finite ι]
    [Nonempty ι] (x : ι → α) :
    greatestCoordinate x = sSup (Set.range x) :=
  rfl

end Text_5_5_0_2

open Text_5_5_0_2

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item states that the finite-coordinate function sending `x` to the
  greatest of its coordinates is positively homogeneous.
- `core/canonical`: the owner abstraction is the chapter predicate
  `Function.PositivelyHomogeneous : ((ι → α) → α) → Prop`, applied to the owner
  `greatestCoordinate`
  from
  Text 5.5.0.1.
- `bridge/view`: the phrase "greatest of the components" is rendered canonically by the
  imported owner `greatestCoordinate`, whose defining formula is the finite supremum
  `sSup (Set.range x)` of the coordinate range.
- Primitive data vs derived API: `greatestCoordinate` is the primitive source-facing
  object; the pointwise positive-scalar scaling law
  `greatestCoordinate_map_smul_pos` is the primitive theorem-level bridge, and the owner theorem
  `greatestCoordinate_positivelyHomogeneous` is derived from it.
- Layer target: `source-facing`, stated via the canonical owner predicate.

Domain-style sampling used here:
- `Function.PositivelyHomogeneous` from `Definition_4_8`;
- `Set.range_smul` for the canonical scaling of a coordinate range;
- `OrderIso.smulRight` + `OrderIso.map_csSup'` for transport of finite suprema through positive
  scalar multiplication;
- the standard supremum expression `sSup (Set.range x)` for the largest coordinate value.
-/

/-- Helper for Text 5.5.0.2: pointwise scalar multiplication of a coordinate function scales its
coordinate range set. -/
lemma range_smul_coordinate_eq [SMul 𝕜 α] (c : 𝕜) (x : ι → α) :
    Set.range (c • x) = c • Set.range x := by
  -- The range-level statement is the canonical set-theoretic form of pointwise scaling.
  simpa using (Set.range_smul c x)

/-- Helper for Text 5.5.0.2: a positive scalar commutes with the finite supremum of a coordinate
range. -/
lemma csSup_range_smul [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] (c : 𝕜⁺) (x : ι → α) :
    sSup ((c : 𝕜) • Set.range x) = c • sSup (Set.range x) := by
  -- Positive scaling acts by an order isomorphism, so it transports this finite supremum.
  simpa using
    ((OrderIso.smulRight (β := α) c.2).map_csSup' (s := Set.range x) (Set.range_nonempty x)
      (Finite.bddAbove_range x)).symm

/-- Primitive positive-scalar scaling law behind Text 5.5.0.2 for the
finite-coordinate greatest-coordinate owner. -/
theorem greatestCoordinate_map_smul_pos [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] (c : 𝕜⁺) (x : ι → α) :
    greatestCoordinate (c • x) = c • greatestCoordinate x := by
  change greatestCoordinate ((c : 𝕜) • x) = (c : 𝕜) • greatestCoordinate x
  -- Rewrite both sides into the finite-supremum owner from the source proof.
  rw [greatestCoordinate_apply (x := ((c : 𝕜) • x))]
  rw [range_smul_coordinate_eq]
  rw [greatestCoordinate_apply (x := x)]
  -- The order-isomorphism lemma is exactly the statement that maximum commutes with positive scaling.
  exact csSup_range_smul (ι := ι) (𝕜 := 𝕜) (α := α) c x

/-- Textbook scalar-plus-positivity bridge for `greatestCoordinate_map_smul_pos`. -/
theorem greatestCoordinate_map_smul [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] {c : 𝕜} (hc : 0 < c) (x : ι → α) :
    greatestCoordinate (c • x) = c • greatestCoordinate x := by
  -- Package the positive scalar into `𝕜⁺` to reuse the primitive owner-level scaling law.
  exact greatestCoordinate_map_smul_pos ⟨c, hc⟩ x

/-- Text 5.5.0.2: the function sending `x` to the greatest of its coordinates is positively
homogeneous on finite-coordinate spaces over conditionally complete lattices with
positive-scalar order monotonicity/reflectivity. -/
theorem greatestCoordinate_positivelyHomogeneous [Preorder 𝕜] [GroupWithZero 𝕜]
    [MulAction 𝕜 α] [PosSMulMono 𝕜 α] [PosSMulReflectLE 𝕜 α]
    [Nonempty ι] :
    (greatestCoordinate : (ι → α) → α).PositivelyHomogeneous 𝕜 := by
  -- The owner predicate asks for the pointwise positive-scalar identity proved above.
  intro c x
  exact greatestCoordinate_map_smul_pos c x

end
