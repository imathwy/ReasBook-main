import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4

universe u v w z

namespace Function

section

open scoped Rockafellar

variable {U : Type u} {X : Type v}

/-- Canonical curry/uncurry bridge for subtype owners on function spaces:
any owner `P` on product-space functions transports along `Function.uncurry` to the corresponding
owner on bifunctions. -/
def uncurrySubtypeEquiv {Y : Type*} (P : (U × X → Y) → Prop) :
    {F : U → X → Y // P (Function.uncurry F)} ≃ {f : U × X → Y // P f} :=
  (Equiv.curry U X Y).symm.subtypeEquiv fun _ ↦ Iff.rfl

variable {𝕜 : Type z} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid (U × X)] [SMul 𝕜 (U × X)]
variable [AddCommMonoid α] [SMul 𝕜 α] [PartialOrder α]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma33.0.21 identifies convex bifunctions with convex graph functions on the
  product space.
- `core/canonical`: the primitive owner layer is the intrinsic function-space bridge
  `Function.uncurrySubtypeEquiv`; `Function.isConvexUncurryEquiv` is the convex-owner
  specialization at the bifunction owner notation `convᵇ[𝕜](F)` (definitionally
  `(Function.uncurry F).IsConvex 𝕜`).
- `bridge/view`: this item is the subtype-level curry/uncurry equivalence at the existing
  canonical owner layer, with no bifunction-only wrapper owner.
- primitive ambient structure for this bridge is only the product-space scalar/additive layer on
  `U × X`; no separate `U`/`X` module assumptions are required here.

Domain-style sampling used here:
- the graph-function owner `Function.IsConvex`;
- the direct convex-bifunction owner notation `convᵇ[𝕜](F)`, recalled later in
  `Definition33_0_28`;
- the canonical curry/uncurry operators on function spaces.

Layer target: `bridge/view`.
-/

/-- Lemma33.0.21: currying and uncurrying identify convex bifunctions with convex graph functions
on the product space. -/
def isConvexUncurryEquiv :
    {F : U → X → WithTopBot α // convᵇ[𝕜](F)} ≃
      {f : U × X → WithTopBot α // f.IsConvex 𝕜} :=
  uncurrySubtypeEquiv fun f : U × X → WithTopBot α ↦ f.IsConvex 𝕜

/-- The forward map of `isConvexUncurryEquiv` is the underlying uncurrying operation on
convex bifunctions. -/
-- Proof sketch: `isConvexUncurryEquiv` is the restriction of the standard curry/uncurry
-- equivalence on function spaces to the convex-function subtypes, so its forward map is the
-- uncurried representative.
theorem isConvexUncurryEquiv_apply
    (F : {F : U → X → WithTopBot α // convᵇ[𝕜](F)}) :
    (isConvexUncurryEquiv F).1 = uncurry F.1 := rfl

end

end Function
