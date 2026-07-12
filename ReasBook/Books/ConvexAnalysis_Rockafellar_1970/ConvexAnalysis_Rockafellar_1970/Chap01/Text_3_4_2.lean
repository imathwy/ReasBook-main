import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_4_0
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 3.4.2 identifies inverse-image/image formulas for a translated positive cone
  and for the positive cone itself.
- `core/canonical`: the owner layer is the general positive-cone API
  `orthant[R](E)` with `ge_iff_sub_mem_orthant`, together with canonical
  `Set.preimage`/`Set.image` and pointwise translation on sets.
- `bridge/view`: concrete matrix/coordinate orthant readings are downstream specializations of the
  abstract owners in this file.
- Primitive data vs derived API: positive-cone membership and set image/preimage are primitive; any
  coordinate-model rendering is derived.
- Layer target: `core/canonical` first, then `bridge/view`.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no special extended-codomain layer is needed here; the canonical target
  is the ordered additive module positive-cone API.
- Scalar/ambient check: remove concrete coordinate-model bridge surfaces from this source item;
  keep only the abstraction layer needed by the mathematics.
- Owner check: keep `orthant[R](E)` and `Set.image`/`Set.preimage` as the primary owners.
- Topology check: this item is not topology-facing, so no intrinsic/relative topology owner is
  applicable.
- Notation check: no new notation owner is needed; theorem surfaces stay in canonical set/order
  notation.
-/

section Owner

section Preimage

/-- Text 3.4.2 (1), owner-level form: the preimage of a translated orthant is exactly a
pointwise order-inequality set. -/
theorem preimage_vadd_orthant_eq_setOf_ge
    {R X F : Type*}
    [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
    [Semiring R] [PartialOrder R] [Module R F] [PosSMulMono R F]
    (f : X → F) (a : F) :
    f ⁻¹' (a +ᵥ orthant[R](F)) = {x : X | f x ≥ a} := by
  -- Reduce the set equality to the source proof's pointwise membership equivalence.
  ext x
  -- Translate membership in the shifted orthant into a difference-in-orthant condition.
  rw [mem_preimage, mem_setOf_eq, mem_vadd_set_iff_neg_vadd_mem]
  rw [vadd_eq_add, add_comm, ← sub_eq_add_neg]
  exact sub_mem_orthant_iff (R := R) (x := f x) (x' := a)

end Preimage

section Image

variable {R E F : Type*}

/-- Text 3.4.2 (2), owner-level form: the image of the orthant is exactly the existential
nonnegativity witness view `∃ x ≥ 0, f x = y`. -/
theorem image_orthant_eq_setOf_exists_nonneg
    [Semiring R] [PartialOrder R]
    [AddCommMonoid E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    (f : E → F) :
    f '' orthant[R](E) =
      {y : F | ∃ x : E, x ≥ 0 ∧ f x = y} := by
  -- Compare both sets by unpacking and repackaging the image witness.
  ext y
  constructor
  · intro hy
    -- A point in the image comes with a preimage witness already lying in the orthant.
    rcases (Set.mem_image (f := f) (s := orthant[R](E)) (y := y)).1 hy with
      ⟨x, hx, hxy⟩
    exact ⟨x, (mem_orthant_iff (𝕜 := R) (M := E) (x := x)).1 hx, hxy⟩
  · rintro ⟨x, hx0, hxy⟩
    -- Conversely, a nonnegative witness packages directly into image membership.
    exact (Set.mem_image (f := f) (s := orthant[R](E)) (y := y)).2
      ⟨x, (mem_orthant_iff (𝕜 := R) (M := E) (x := x)).2 hx0, hxy⟩

end Image

end Owner
