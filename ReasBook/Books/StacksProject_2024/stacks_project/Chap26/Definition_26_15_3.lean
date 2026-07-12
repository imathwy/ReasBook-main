import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.Topology.Sets.OpenCover

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe v w

namespace CategoryTheory

/-
Domain-style sampling for Definition 26.15.3:
- primary domain: set-valued contravariant functors on `Scheme` and source-faithful predicates on
  their subfunctors;
- sampled owner declarations:
  `Presheaf.IsSheaf`,
  `Scheme.zariskiTopology`,
  `CategoryTheory.Subfunctor`,
  `AlgebraicGeometry.IsOpenImmersion`,
  `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`;
- best owner abstraction: the sheaf clause is the canonical big-Zariski sheaf condition
  `Presheaf.IsSheaf Scheme.zariskiTopology F`, and the subfunctor clause is the canonical
  `CategoryTheory.Subfunctor F`; the open-immersion and cover clauses are source-faithful
  predicates on a subfunctor or indexed family of subfunctors;
- derived API: explicit factorization predicates through the canonical open subscheme
  `U.toScheme ⟶ T` for later local representability arguments.

Source/core/bridge triage:
- `source-facing`: sheaf property for the Zariski topology, subfunctors, subfunctors representable
  by open immersions, and covering families of subfunctors;
- `core/canonical`: `Presheaf.IsSheaf Scheme.zariskiTopology F` and `CategoryTheory.Subfunctor F`;
- `bridge/view`: the source-faithful predicates `Subfunctor.isRepresentableByOpenImmersions` and
  `Subfunctor.covers`.

Semantic recall: `lean_leansearch` returned the big-Zariski owners
`AlgebraicGeometry.Scheme.zariskiPretopology`,
`AlgebraicGeometry.Scheme.subcanonical_zariskiTopology`, and
`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`; together with local Chapter 6/7
precedent for `Presheaf.IsSheaf` and `CategoryTheory.Subfunctor`, this identifies the first two
clauses as canonical recalls and the remaining two as source-faithful predicates.
-/

/- Definition 26.15.3 (1): for a contravariant functor on schemes with values in sets, the sheaf
property for the Zariski topology is exactly the canonical big-Zariski sheaf condition
`Presheaf.IsSheaf Scheme.zariskiTopology F`. -/
section

variable (F : Schemeᵒᵖ ⥤ Type v)

#check (Presheaf.IsSheaf Scheme.zariskiTopology F : Prop)

/- Definition 26.15.3 (2): a subfunctor of a set-valued contravariant functor on schemes is the
canonical mathlib structure `CategoryTheory.Subfunctor`. -/
#check (Subfunctor F : Type _)

end

namespace Subfunctor

/-- Definition 26.15.3 (3): a subfunctor `H ⊂ F` is representable by open immersions if, for each
scheme `T` and section `ξ ∈ F(T)`, there is an open subscheme of `T` through which exactly the
morphisms whose pullback of `ξ` lies in `H` factor. The open subscheme is expressed through the
canonical owner `U.toScheme` with inclusion `U.ι`. -/
@[stacks 01JI]
def isRepresentableByOpenImmersions {F : Schemeᵒᵖ ⥤ Type v} (H : Subfunctor F) : Prop :=
  ∀ ⦃T : Scheme⦄ (ξ : F.obj (op T)),
    ∃ U : T.Opens,
      ∀ ⦃T' : Scheme⦄ (f : T' ⟶ T),
        (∃ lift : T' ⟶ U.toScheme, lift ≫ U.ι = f) ↔
        F.map f.op ξ ∈ H.obj (op T')

/-- Definition 26.15.3 (4): an indexed family of subfunctors `Hᵢ ⊂ F` covers `F` if every
section `ξ ∈ F(T)` is locally contained in the corresponding `Hᵢ` on some open cover of `T`
indexed by `I`, with each open piece represented by its canonical open subscheme. -/
@[stacks 01JI]
def covers {F : Schemeᵒᵖ ⥤ Type v} {I : Type w} (H : I → Subfunctor F) : Prop :=
  ∀ ⦃T : Scheme⦄ (ξ : F.obj (op T)),
    ∃ U : I → T.Opens, TopologicalSpace.IsOpenCover U ∧
      ∀ i : I,
        F.map (U i).ι.op ξ ∈
          (H i).obj (op (U i).toScheme)

/-- The constant family of maximal subfunctors, indexed by a nonempty type, covers `F`. -/
theorem covers_top {F : Schemeᵒᵖ ⥤ Type v} {I : Type w} [Nonempty I] :
    Subfunctor.covers (fun _ : I ↦ (⊤ : Subfunctor F)) := by
  intro T ξ
  refine ⟨fun _ ↦ ⊤, ?_, ?_⟩
  · simpa [TopologicalSpace.IsOpenCover]
  · intro i
    simp

end Subfunctor

end CategoryTheory
