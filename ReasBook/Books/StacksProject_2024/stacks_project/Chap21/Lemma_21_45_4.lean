import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open RingedSite.Hom (ModuleCat ModuleDerived localizedRestriction)

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

open _root_.RingedSite.Hom.ModuleDerived

section

/- Domain-style sampling for Lemma 21.45.4:
- primary domain: `m`-pseudo-coherent objects of `D(𝒪_X)` on a ringed site and their
  behavior in distinguished triangles;
- sampled owner declarations:
  `IsMPseudoCoherent`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `Triangle.rotate`,
  `Triangle.invRotate`;
- best owner abstraction: the Chapter 21 owner predicate
  `K.IsMPseudoCoherent m`, with the fixed-`m` canonical exact two-out-of-three owner
  `(fun K : DMod ↦ K.IsMPseudoCoherent m : ObjectProperty DMod)`;
- primitive vs. derived:
  primitive data are the owner predicate `K.IsMPseudoCoherent m` and the distinguished triangle;
  proof-internal transport uses the existing owner-level pseudo-coherence behavior under
  isomorphisms and shifts;
  derived API is clause `(1)` together with the fixed-`m`
  `ObjectProperty.IsTriangulatedClosed₂` instance, from which clauses `(2)` and `(3)` are
  recovered.

Source/core/bridge triage:
- `source-facing`: the three numbered closure statements of Lemma `21.45.4`;
- `core/canonical`: `DerivedCategory.IsMPseudoCoherent` and the fixed-`m` object property
  `(fun K : DMod ↦ K.IsMPseudoCoherent m)`;
- `bridge/view`: the shift equivalence below and the use of `Triangle.rotate` / `Triangle.invRotate`
  to move between clause `(1)` and the source-facing clauses `(2)` and `(3)`.
-/

variable {X : RingedSite.{u, v}}

local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]

variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]
variable [Abelian (ModuleCat X)]
variable [∀ n : ℤ, (shiftFunctor (ModuleDerived X) n).Additive]

/-- Proof-internal transport of `m`-pseudo-coherence across an isomorphism in `D(𝒪_X)`. -/
private theorem isMPseudoCoherent_of_iso {K L : DMod} (e : K ≅ L) (m : ℤ)
    (hK : K.IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := by
  sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(𝒪_X)` are closed under isomorphisms. -/
instance isMPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_iso e hK := by
    exact isMPseudoCoherent_of_iso e m hK

/-- Proof-internal shift transport for `m`-pseudo-coherence in `D(𝒪_X)`. -/
private theorem isMPseudoCoherent_shift_iff (K : DMod) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := by
  sorry

-- Proof sketch: choose strictly perfect local models for `T.obj₁` in degree `m + 1` and for
-- `T.obj₂` in degree `m`, lift the morphism `T.mor₁ : T.obj₁ ⟶ T.obj₂` locally to a morphism of
-- complexes, and compare the cone triangle with `T`. The cone stays strictly perfect, and the
-- long exact homology sequence shows the third vertex is `m`-pseudo-coherent.
/-- Lemma 21.45.4 (1): in a distinguished triangle in `D(𝒪_X)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
@[stacks 08FV]
theorem isMPseudoCoherent_obj₃_of_distinguished_triangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := by
  sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(𝒪_X)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂ (fun K : DMod ↦ K.IsMPseudoCoherent m) :=
  .mk' fun T hT h₁ h₃ ↦ by
    have h₃' : (T.obj₃⟦-1⟧).IsMPseudoCoherent (m + 1) := by
      simpa using (isMPseudoCoherent_shift_iff T.obj₃ (-1) m).2 h₃
    exact isMPseudoCoherent_obj₃_of_distinguished_triangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: this is the `obj₁`-`obj₃` to `obj₂` consequence of the canonical fixed-`m`
-- `ObjectProperty.IsTriangulatedClosed₂` owner above.
/-- Lemma 21.45.4 (2): in a distinguished triangle in `D(𝒪_X)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
@[stacks 08FV]
theorem isMPseudoCoherent_obj₂_of_distinguished_triangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent m)
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := by
  exact ObjectProperty.ext_of_isTriangulatedClosed₂
    (fun K : DMod ↦ K.IsMPseudoCoherent m) T hT h₁ h₃

-- Proof sketch: rotate the distinguished triangle once, apply part `(1)` to obtain
-- `m`-pseudo-coherence of `T.obj₁⟦1⟧`, and then shift back using
-- `isMPseudoCoherent_shift_iff`.
/-- Lemma 21.45.4 (3): in a distinguished triangle in `D(𝒪_X)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
@[stacks 08FV]
theorem isMPseudoCoherent_obj₁_of_distinguished_triangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := by
  have hshift : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₃_of_distinguished_triangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  have hshift' : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent ((m + 1) - 1) := by
    simpa using hshift
  exact (isMPseudoCoherent_shift_iff T.obj₁ 1 (m + 1)).1 hshift'

end

end SheafOfModules.RingedSite
