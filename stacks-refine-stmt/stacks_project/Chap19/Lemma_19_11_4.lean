import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U M : C}

/- Domain-style sampling for Lemma 19.11.4:
- primary domain: generators/separators and smallness of object properties in Grothendieck abelian
  categories;
- sampled owner declarations:
  `isSeparator_iff_exists_not_factors_subobject`,
  `Cardinal.mk (Subobject M)`,
  `ObjectProperty.EssentiallySmall`,
  the derived instance `EssentiallySmall P.FullSubcategory`;
- best owner abstractions: `IsSeparator U` for the generator hypothesis in part (1), and
  `ObjectProperty.EssentiallySmall` for the bounded-size class of objects in part (2);
- primitive data: the separator hypothesis `IsSeparator U`, the object `M`, and the bound
  `Cardinal.mk (Subobject M) ≤ κ`;
- derived API: the existential bounded-coproduct presentation in part (1), and the full-subcategory
  essential-smallness statement in part (2).

Source/core/bridge triage:
- `source-facing`: the existential quotient statement by a coproduct of at most `κ` copies of `U`;
- `core/canonical`: the owner notions `IsSeparator`, `Cardinal.mk (Subobject M)`, and
  `ObjectProperty.EssentiallySmall`;
- `bridge/view`: the formulation of part (2) as essential smallness of the full subcategory, which
  is derived from the owner-level object-property smallness instance.
-/

-- Proof sketch: for each proper subobject `N ⊊ M`, use
-- `isSeparator_iff_exists_not_factors_subobject` to choose a morphism `f_N : U ⟶ M` which does
-- not factor through `N`. Assemble these maps into a single morphism
-- `∐ fun _ : Shrink.{w} (Subobject M) ↦ U ⟶ M`. If its image were a proper subobject, the chosen
-- map attached to that image would factor through it via the coproduct inclusion, a contradiction.
-- Hence this map is epi, and the resulting index set has cardinal at most `κ` after the necessary
-- universe lift from `Type w` to the ambient subobject-cardinality universe.
/-- Lemma 19.11.4 (1): if `U` is a generator of a Grothendieck abelian category and
`|M| = #(Subobject M) ≤ κ`, then `M` is a quotient of a coproduct of at most `κ` copies of `U`. -/
lemma exists_epi_from_coproduct_of_generator_of_subobject_cardinal_le
    (hU : IsSeparator U) (κ : Cardinal) (hM : Cardinal.mk (Subobject M) ≤ κ) :
    ∃ (ι : Type w)
      (_ : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift.{w} κ)
      (f : (∐ fun _ : ι ↦ U) ⟶ M), Epi f := sorry

-- Proof sketch: by part (1), every bounded object is a quotient of a coproduct of at most `κ`
-- copies of the chosen generator, using an index type in `Type w`. Quotients of all such
-- `w`-small coproducts are classified by a set via the corresponding subobject lattices, so the
-- resulting object property is essentially small; the source-facing full-subcategory statement is
-- then the canonical derived instance.
/-- The object property `M ↦ Cardinal.mk (Subobject M) ≤ κ` is essentially small. -/
instance subobjectCardinalLE_essentiallySmall (κ : Cardinal) :
    ObjectProperty.EssentiallySmall.{w}
      (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ) := by
  sorry

variable (κ : Cardinal)

/- Lemma 19.11.4 (2): for every cardinal `κ`, the full subcategory of objects `M` with
`|M| = #(Subobject M) ≤ κ` is essentially small. This is the canonical full-subcategory instance
attached to `subobjectCardinalLE_essentiallySmall κ`. -/
#check
  (inferInstance :
    EssentiallySmall.{w}
      (ObjectProperty.FullSubcategory (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ)))

end CategoryTheory
