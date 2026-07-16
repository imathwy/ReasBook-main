import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ObjectProperty Pretriangulated TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived

local notation "DModX" => ModuleDerived X
local notation "MPseudoCoherentObj" m =>
  (fun K : DModX ↦ ModuleDerived.IsMPseudoCoherent K m : ObjectProperty DModX)

variable [CategoryWithHomology (Modules X)]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]
variable [Abelian (Modules X)]
variable [∀ n : ℤ, (shiftFunctor (ModuleDerived X) n).Additive]

/- Domain-style sampling for Lemma 20.47.4:
- primary domain: `m`-pseudo-coherent objects of `D(𝒪_X)` and their behavior in
  distinguished triangles;
- sampled owner declarations:
  `IsMPseudoCoherent`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `Triangle.rotate`,
  `Triangle.invRotate`;
- best owner abstraction: the source-facing owner remains the ringed-space predicate
  `K.IsMPseudoCoherent m`, while for fixed `m` the canonical exact two-out-of-three owner is the
  object property `(fun K : DModX ↦ K.IsMPseudoCoherent m)`;
- primitive vs. derived:
  primitive data are the owner predicate `IsMPseudoCoherent`, its shift behavior, and the
  distinguished triangle;
  derived API is clause `(1)` together with the fixed-`m` canonical
  `ObjectProperty.IsTriangulatedClosed₂` instance below, from which clauses `(2)` and `(3)` are
  recovered;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements of Lemma `20.47.4`;
  `core/canonical`: `IsMPseudoCoherent` and the fixed-`m` object property
    `(fun K : DModX ↦ K.IsMPseudoCoherent m)`;
  `bridge/view`: `isMPseudoCoherent_shift_iff` together with `Triangle.rotate` and
    `Triangle.invRotate`.
-/

/-- Proof-internal transport of `m`-pseudo-coherence across an isomorphism in `D(𝒪_X)`. -/
private theorem isMPseudoCoherent_of_iso {K L : DModX} (e : K ≅ L) (m : ℤ)
    (hK : K.IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := by
  sorry

instance isMPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    IsClosedUnderIsomorphisms (MPseudoCoherentObj m) := by
  sorry

/-- Shifting a derived `𝒪_X`-module by `n` translates the `m`-pseudo-coherence bound by
the same amount. -/
private theorem isMPseudoCoherent_shift_iff (K : DModX) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := by
  sorry

-- Proof sketch: choose local strictly perfect approximations of `T.obj₁` in degree `m + 1` and
-- of `T.obj₂` in degree `m`, realize the first morphism of the distinguished triangle by an
-- actual map between those local models, and compare the cone triangle with `T` locally. The cone
-- stays strictly perfect, and the long exact cohomology sequence gives the required
-- cohomological bounds for `T.obj₃`, so Lemma `20.47.2` yields `m`-pseudo-coherence.
/-- Lemma 20.47.4 (1): in a distinguished triangle in `D(𝒪_X)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
@[stacks 08CD]
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(𝒪_X)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂ (MPseudoCoherentObj m) := by
  sorry

-- Proof sketch: this is the `obj₁`-`obj₃` to `obj₂` consequence of the canonical fixed-`m`
-- `ObjectProperty.IsTriangulatedClosed₂` owner above.
omit [CategoryWithHomology (Modules X)]
  [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]
  [Abelian (Modules X)] in
/-- Lemma 20.47.4 (2): in a distinguished triangle in `D(𝒪_X)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
@[stacks 08CD]
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : T.obj₁.IsMPseudoCoherent m)
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ (MPseudoCoherentObj m) T hT h₁ h₃

-- Proof sketch: rotate the distinguished triangle once so that `T.obj₁⟦1⟧` becomes the third
-- vertex, apply part `(1)`, and shift back.
/-- Lemma 20.47.4 (3): in a distinguished triangle in `D(𝒪_X)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
@[stacks 08CD]
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
