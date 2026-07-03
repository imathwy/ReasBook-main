import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_11_1 (from Chap14) -/
open CategoryTheory
open scoped Simplicial

universe u

section

variable (U : SSet.{u}) (n : ℕ)

/- Domain-style sampling for Definition 14.11.1:
- primary domain: simplicial sets and their canonical face/degeneracy API
- sampled owner API:
  `SSet`,
  `SimplicialObject.δ`,
  `SimplicialObject.σ`,
  `SSet.degenerate`,
  `SSet.mem_degenerate_iff`,
  `SSet.degenerate_eq_iUnion_range_σ`
- source/core/bridge triage:
  `source-facing`: textbook terminology for simplices, faces, degeneracies, and degenerate
    simplices of a simplicial set;
  `core/canonical`: the ambient owner `SSet`, whose primitive data already provide simplex types
    `U _⦋n⦌`, face maps `U.δ`, degeneracy maps `U.σ`, and the degenerate locus `U.degenerate n`;
  `bridge/view`: the explicit existential reformulation of `z ∈ U.degenerate (n + 1)` in terms of
    a chosen degeneracy map `U.σ j`.
- primitive data: none are introduced locally; all primitive simplicial-set data already live on
  the owner `SSet`
- derived API: the textbook relations “is the `j`-th face of”, “is the `j`-th degeneracy of”, and
  “is degenerate” are direct restatements of the canonical owner data, so the file should recall
  those declarations rather than repackage them as local wrapper predicates or theorems
- layer target: `core/canonical` recall for simplices, faces, degeneracies, and degenerate
  simplices, together with recall of the canonical owner theorems describing degenerate simplices.
-/

/- Definition 14.11.1: an `n`-simplex of a simplicial set `U` is simply an element of the
degree-`n` term `U _⦋n⦌`. -/
#check (U _⦋n⦌)

/- The textbook `j`-th face of a simplex is obtained by the canonical face map `U.δ j`. -/
recall SimplicialObject.δ

/- The textbook `j`-th degeneracy of a simplex is obtained by the canonical degeneracy map
`U.σ j`. -/
recall SimplicialObject.σ

/- Degenerate simplices are recorded by the canonical set `U.degenerate n`. -/
recall SSet.degenerate

/- The canonical pointwise criterion for degeneracy is `SSet.mem_degenerate_iff`. -/
recall SSet.mem_degenerate_iff

/- The textbook description “degenerate iff in the image of some degeneracy map” is the canonical
set equality `SSet.degenerate_eq_iUnion_range_σ`. -/
recall SSet.degenerate_eq_iUnion_range_σ

end

/-! ### Example_14_11_2 (from Chap14) -/
open CategoryTheory
open SSet.stdSimplex
open scoped Simplicial

/- Domain-style sampling for Example 14.11.2:
- primary domain: simplicial sets and the standard simplex `Δ[n]`, especially the degenerate and
  nondegenerate simplices of `Δ[n]`;
- sampled owner API:
  `SSet.HasDimensionLE`,
  `SSet.degenerate_eq_top_of_hasDimensionLT`,
  `stdSimplex.nonDegenerateEquiv`,
  `stdSimplex.mem_nonDegenerate_iff_mono`,
  `SimplexCategory.eq_id_of_mono`;
- best owner abstraction: the mathlib standard-simplex owner API already organizes both dimension
  bounds and nondegeneracy for `Δ[n]`; the first source-facing sentence is the exact owner
  specialization `Δ[n].degenerate_eq_top_of_hasDimensionLT ...`, while the second is a thin
  consequence of the canonical nondegenerate-simplex owner API;
- primitive data: the canonical simplicial set `Δ[n]`, the degrees `n` and `m`, and an
  `m`-simplex `x : Δ[n] _⦋m⦌`;
- derived API: degeneracy in degrees `m > n` is the canonical owner theorem
  `Δ[n].degenerate_eq_top_of_hasDimensionLT ...`, while uniqueness of the top nondegenerate
  simplex comes from `stdSimplex.mem_nonDegenerate_iff_mono` together with
  `SimplexCategory.eq_id_of_mono`.

Source/core/bridge triage:
- `source-facing`: the Stacks example says that every simplex of `Δ[n]` in degree `> n` is
  degenerate, and that the unique nondegenerate `n`-simplex is the identity simplex;
- `core/canonical`: the owner declarations sampled above;
- `bridge/view`: none. The file should remain a thin source-facing consequence of the owner API.
-/

variable (n m : ℕ) (h : n < m)

/- Example 14.11.2 (first sentence): every `m`-simplex of `Δ[n]` with `n < m` is degenerate.
Mathlib already exposes this exactly as the owner specialization
`Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) m h`. -/
#check (Δ[n].degenerate_eq_top_of_hasDimensionLT (n + 1) m h : Δ[n].degenerate m = ⊤)

-- Proof sketch: a nondegenerate `n`-simplex of `Δ[n]` corresponds to a mono endomorphism of
-- `⦋n⦌`, and `SimplexCategory.eq_id_of_mono` identifies every such endomorphism with the identity.
/-- Example 14.11.2: the set of nondegenerate `n`-simplices of `Δ[n]` is the singleton consisting
of the simplex corresponding to the identity morphism of `[n]`. -/
theorem stdSimplex_nonDegenerate_eq_singleton_identity (n : ℕ) :
    Δ[n].nonDegenerate n =
      {objEquiv.symm (𝟙 ⦋n⦌)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simpa using
      (objEquiv_symm_mem_nonDegenerate_iff_mono (𝟙 ⦋n⦌)).2
        (by infer_instance : Mono (𝟙 ⦋n⦌))
  · intro x hx
    rw [mem_nonDegenerate_iff_mono] at hx
    exact objEquiv.injective <| SimplexCategory.eq_id_of_mono (objEquiv x)

/-! ### Lemma_14_11_3 (from Chap14) -/
open CategoryTheory Opposite
open SSet.stdSimplex
open scoped Simplicial

universe u

/- Domain-style sampling for Lemma 14.11.3:
- primary domain: standard simplices and the simplicial Yoneda equivalence in `SSet`;
- sampled owner API:
  `SSet.stdSimplex`,
  `stdSimplex.objEquiv`,
  `SSet.yonedaEquiv`,
  `CategoryTheory.yonedaEquiv_apply`;
- best owner abstraction: the source-facing bijection is already the simplicial specialization
  `SSet.yonedaEquiv`, and its evaluation formula is the corresponding specialization of
  `CategoryTheory.yonedaEquiv_apply`;
- source/core/bridge triage:
  `source-facing`: the canonical bijection `(Δ[n] ⟶ U) ≃ U _⦋n⦌`;
  `core/canonical`: `SSet.yonedaEquiv`;
  `bridge/view`: the explicit evaluation formula at the identity simplex of `Δ[n]`.

Primitive data are only the simplicial set `U` and the standard simplex degree `n`. The identity
simplex of `Δ[n]` is derived from the owner presentation `stdSimplex.objEquiv`, and the
source’s evaluation description is derived API of `SSet.yonedaEquiv`. The file should therefore
keep `SSet.yonedaEquiv` as the main entry and expose only the thin evaluation bridge. -/

section

variable (U : SSet.{u}) (n : ℕ)

/- Lemma 14.11.3: for a simplicial set `U` and an integer `n ≥ 0`, there is a canonical bijection
`(Δ[n] ⟶ U) ≃ U _⦋n⦌`; this is exactly the simplicial Yoneda owner `SSet.yonedaEquiv`. -/
recall SSet.yonedaEquiv

variable (f : Δ[n] ⟶ U)

/- Companion check: the source’s evaluation description is not a second owner theorem; it is the
definitional simplicial specialization of `CategoryTheory.yonedaEquiv_apply`, evaluating `f` on
the identity simplex `objEquiv.symm (𝟙 ⦋n⦌)` of `Δ[n]`. -/
#check
  (show SSet.yonedaEquiv f =
      f.app (op ⦋n⦌) (objEquiv.symm (𝟙 ⦋n⦌)) from
    rfl)

end

/-! ### Example_14_11_4 (from Chap14) -/
open CategoryTheory
open scoped RepresentablePresheaf Simplicial

universe u

section

variable (U : SSet.{u}) (n : ℕ)

/- Domain-style sampling for Example 14.11.4:
- primary domain: representable simplicial presheaves, their categories of elements, and the
  slice/fibred-in-sets presentation of standard simplices;
- sampled owner API:
  `representableElementsOpToOverEquivalence`,
  `representableElementsOpToOver_isEquivalenceOverBase`,
  `CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence`,
  `SSet.yonedaEquiv`;
- best owner abstraction: the source-facing owner for the example is the representable-to-slice
  bridge for `⦋n⦌ : SimplexCategory`, namely
  `representableElementsOpToOverEquivalence ⦋n⦌`; the simplicial Yoneda
  equivalence is then the canonical derived Hom formula for that representable;
- primitive data: the simplex degree `n`, and then the target simplicial set `U` for the final
  Hom computation;
- derived API: the over-base equivalence with `Over.forget ⦋n⦌`, and the Hom-to-`n`-simplex
  equivalence `SSet.yonedaEquiv`.

Source/core/bridge triage:
- `source-facing`: the identification of `Δ/[n] → Δ` with the category of elements of the
  representable presheaf `h[⦋n⦌]`, hence with the standard simplex `Δ[n]`;
- `core/canonical`: `representableElementsOpToOverEquivalence`, together with the final owner
  `SSet.yonedaEquiv`;
- `bridge/view`: the over-base equivalence
  `representableElementsOpToOver_isEquivalenceOverBase ⦋n⦌`. -/

/- Example 14.11.4: the category `Δ/[n] → Δ`, viewed as a category fibred in sets over `Δ`, is
the opposite category of elements of the representable presheaf `h[⦋n⦌]`; the project’s
representable-to-slice bridge specializes this to a canonical equivalence
`h[⦋n⦌].Elementsᵒᵖ ≌ Δ/[n]`. -/
#check
  (representableElementsOpToOverEquivalence ⦋n⦌ :
    h[⦋n⦌].Elementsᵒᵖ ≌ Over ⦋n⦌)

/- Companion bridge: in the fibred-over-the-base formulation, the same comparison is an
equivalence over `SimplexCategory` from the representable category of elements to the slice
projection `Over.forget ⦋n⦌`. -/
#check (representableElementsOpToOver_isEquivalenceOverBase ⦋n⦌)

/- Since the standard simplex `Δ[n]` is the simplicial representable at `⦋n⦌`, the resulting
presheaf formula for maps into `U` is the canonical simplicial Yoneda equivalence. -/
#check (SSet.yonedaEquiv : (Δ[n] ⟶ U) ≃ U _⦋n⦌)

end

/-! ### Lemma_14_11_5 (from Chap14) -/
open CategoryTheory.MonoidalCategory

universe u

section

variable (U V : SSet.{u}) (a b : ℕ) [U.HasDimensionLE a] [V.HasDimensionLE b]

/- Domain-style sampling for Lemma 14.11.5:
- primary domain: simplicial sets, their dimension bounds, and behavior under the cartesian
  product `⊗`;
- sampled owner declarations:
  `SSet.HasDimensionLT`,
  `SSet.HasDimensionLE`,
  `SSet.hasDimensionLE_prod`,
  the canonical instance giving `(U ⊗ V).HasDimensionLE (a + b)`;
- best owner abstraction: the mathlib owner theorem `SSet.hasDimensionLE_prod`, whose
  specialization at `n := a + b` is the exact textbook statement;
- primitive data: simplicial sets `U`, `V` together with the bounds `U.HasDimensionLE a` and
  `V.HasDimensionLE b`;
- derived API: the target statement is exactly the specialization `(U ⊗ V).HasDimensionLE (a + b)`,
  so the deleted local theorem was only a duplicate shell around the owner theorem rather than new
  source-facing data.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma says that the product of simplicial sets of dimensions at most
  `a` and `b` has dimension at most `a + b`;
- `core/canonical`: `SSet.hasDimensionLE_prod`;
- `bridge/view`: none; the main entry below is already the exact source-facing specialization of
  the canonical owner theorem.

The correct refinement is therefore to expose the exact specialized instance rather than keep a
parallel local theorem or only recall the broader owner theorem. -/

/- Lemma 14.11.5: if simplicial sets `U` and `V` have dimension at most `a` and `b`, then their
cartesian product has dimension at most `a + b`. In mathlib this is exactly the specialization of
`SSet.hasDimensionLE_prod` at `n := a + b`. -/
#check (SSet.hasDimensionLE_prod U V a b (a + b) : (U ⊗ V).HasDimensionLE (a + b))

end
