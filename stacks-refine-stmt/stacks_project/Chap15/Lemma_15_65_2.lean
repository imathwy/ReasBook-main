import stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.2:
- primary domain: `m`-pseudo-coherent objects of `D(R)` and their behavior in distinguished
  triangles;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `rot_of_distTriang`,
  `inv_rot_of_distTriang`;
- best owner abstraction: the source-facing owner is the canonical predicate
  `DerivedCategory.IsMPseudoCoherent` on objects of `D(R)`; for a fixed `m`, the exact
  two-out-of-three owner already present in mathlib is the object property
  `(fun K : DMod ↦ K.IsMPseudoCoherent m)`;
- primitive vs. derived:
  primitive data are the owner predicate `IsMPseudoCoherent`, the shift behavior of that owner,
  and the distinguished triangle;
  derived API is clause `(1)` together with the fixed-`m` canonical
  `ObjectProperty.IsTriangulatedClosed₂` instance below; the source-facing clauses `(2)` and `(3)`
  are then recovered from that owner property and the canonical triangle rotations;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements of Lemma `15.65.2`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent` and the fixed-`m`
    object property `(fun K : DMod ↦ K.IsMPseudoCoherent m)` on `D(R)`;
  `bridge/view`: the shift equivalence below and the use of `Triangle.rotate` / `Triangle.invRotate`
    to move between clause `(1)` and the source-facing clauses `(2)` and `(3)`.
-/

-- Proof sketch: shift a bounded finite-free approximation of `K` termwise; the cohomology
-- comparison conditions in degrees `> m` and `= m` translate by the standard homology shift
-- isomorphisms.
/-- Shifting an object of `D(R)` by `n` translates the `m`-pseudo-coherence bound by the same
amount. -/
theorem isMPseudoCoherent_shift_iff (K : DMod) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := sorry

instance isMPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_iso e hK := by
    rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
    refine ⟨E, hbounds, hfree, α ≫ e.hom, ?_, ?_⟩
    · intro i hi
      simpa using hαgt i hi
    · simpa [Functor.map_comp] using
        (show Epi ((H m).map α ≫ (H m).map e.hom) by infer_instance)

-- Proof sketch: compare finite-free approximations of `T.obj₁` and `T.obj₂` by a morphism of
-- complexes and use the cone triangle together with the long exact cohomology sequence to produce
-- the required approximation of `T.obj₃`.
/-- Lemma 15.65.2 (1): in a distinguished triangle in `D(R)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1)) (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(R)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂ (fun K : DMod ↦ K.IsMPseudoCoherent m) :=
  .mk' fun T hT h₁ h₃ ↦ by
    have h₃' : (T.obj₃⟦-1⟧).IsMPseudoCoherent (m + 1) := by
      simpa using (isMPseudoCoherent_shift_iff T.obj₃ (-1) m).2 h₃
    exact isMPseudoCoherent_obj₃_of_distinguishedTriangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: rotate the distinguished triangle once and reduce to part `(1)`.
/-- Lemma 15.65.2 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
`m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent m) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := by
  let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: rotate the distinguished triangle once so that `T.obj₁⟦1⟧` becomes the third
-- vertex, apply part `(1)`, and shift back.
/-- Lemma 15.65.2 (3): in a distinguished triangle in `D(R)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1)) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := by
  have hshift : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  have hshift' : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent ((m + 1) - 1) := by
    simpa using hshift
  exact (isMPseudoCoherent_shift_iff T.obj₁ 1 (m + 1)).1 hshift'

end

end CategoryTheory
