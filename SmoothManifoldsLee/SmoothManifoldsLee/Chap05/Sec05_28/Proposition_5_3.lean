import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this environment, so this item is kept self-contained
-- instead of importing the syntactically broken helper file `Proposition_5_2`.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ∞ N]

/-- The canonical parametrization of the slice `M × {p}` in the product manifold `M × N`. -/
def productSliceMap (p : N) : M → M × N :=
  fun x ↦ (x, p)

/-- The image of `productSliceMap p` is exactly the slice `M × {p}`. -/
-- Proof sketch: unwind the definitions of `productSliceMap`, `Set.range`, and the product of sets;
-- a point lies in the range exactly when its second coordinate is `p`.
theorem range_productSliceMap_eq_univ_prod_singleton (p : N) :
    Set.range (productSliceMap p : M → M × N) = (Set.univ : Set M) ×ˢ ({p} : Set N) := sorry

/-- The canonical parametrization of a product slice is a smooth embedding. -/
-- Proof sketch: the map `x ↦ (x, p)` is smooth as the product of the identity on `M` and the
-- constant map at `p`; it is a topological embedding because the first projection is a continuous
-- left inverse, and it is an immersion by the standard slice-immersion normal form.
theorem productSliceMap_isSmoothEmbedding (p : N) :
    Manifold.IsSmoothEmbedding I (I.prod J) ∞ (productSliceMap p : M → M × N) := sorry

/-- Proposition 5.3: for each `p : N`, the slice `M × {p}`, realized as the range of
`productSliceMap p`, inherits an induced smooth manifold structure making it an embedded
submanifold of `M × N` diffeomorphic to `M`. -/
-- Proof sketch: apply Proposition 5.2 to the smooth embedding `productSliceMap_isSmoothEmbedding
-- p`. The resulting induced image manifold structure on the range identifies the slice with `M`
-- via `productSliceMap p`, and `range_productSliceMap_eq_univ_prod_singleton` matches the range
-- with the textbook subset `M × {p}`.
theorem product_slice_has_induced_manifold_structure (p : N) :
    ∃ (_ : ChartedSpace H (Set.range (productSliceMap p : M → M × N)))
      (_ : IsManifold I ∞ (Set.range (productSliceMap p : M → M × N))),
        Manifold.IsSmoothEmbedding I (I.prod J) ∞
          (Subtype.val : Set.range (productSliceMap p : M → M × N) → M × N) ∧
        ∃ Φ : M ≃ₘ⟮I, I⟯ Set.range (productSliceMap p : M → M × N),
          ∀ x,
            ((Φ x : Set.range (productSliceMap p : M → M × N)) : M × N) =
              productSliceMap p x := sorry

end
