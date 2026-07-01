import Mathlib
import cartan.VI.section26.«0008_Problem_VI_5_extra_8»

open scoped Manifold

universe u

/- Domain sampling: the primary domain here is maximal holomorphic extension over connected
Hausdorff unramified surfaces above `ℂ`. The relevant owner declarations inspected before this
refinement were:
* `ConnectedHausdorffUnramifiedSurfaceOver.Hom` in `0008_Problem_VI_5_extra_8.lean`, which is the
  comparison-map owner for the chapter's source-facing unramified-surface notion;
* `PlaneHolomorphicExtension.Compatible` in `0008`, which is the derived compatibility predicate
  for continuation maps between two extensions of the same germ;
* `MaximalPlaneHolomorphicExtension` in `0008`, whose universal property is the source-facing
  owner of maximal analytic continuation.
Primitive data is therefore only the maximal-extension datum and its universal property. The
canonical comparison morphism and its inverse laws are derived API, not new primitive wrapper data.

Source/core/bridge triage:
* source-facing: `MaximalPlaneHolomorphicExtension`;
* core/canonical: `ConnectedHausdorffUnramifiedSurfaceOver.Hom`;
* bridge/view: the canonical comparison morphism `MaximalPlaneHolomorphicExtension.hom`. -/

namespace ConnectedHausdorffUnramifiedSurfaceOver.Hom

variable {X Y Z : ConnectedHausdorffUnramifiedSurfaceOver ℂ}

/-- Helper for Theorem VI.5-extra-9: the identity map on an unramified surface is holomorphic. -/
theorem mdifferentiable_id_map (X : ConnectedHausdorffUnramifiedSurfaceOver ℂ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X ↦ x) := by
  simpa using (mdifferentiable_id : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X ↦ x))

/-- Helper for Theorem VI.5-extra-9: the identity map commutes with the projection to `ℂ`. -/
theorem id_commutes_projection (X : ConnectedHausdorffUnramifiedSurfaceOver ℂ) :
    ∀ x : X, X.projection ((fun y : X ↦ y) x) = X.projection x :=
  fun _ ↦ rfl

/-- Helper for Theorem VI.5-extra-9: the identity morphism of an unramified surface over `ℂ`. -/
def id (X : ConnectedHausdorffUnramifiedSurfaceOver ℂ) : Hom X X where
  toFun := fun x ↦ x
  holomorphic_toFun := mdifferentiable_id_map X
  commutes := id_commutes_projection X

/-- Helper for Theorem VI.5-extra-9: the composite of two holomorphic surface morphisms is
holomorphic. -/
theorem mdifferentiable_comp_map (g : Hom Y Z) (f : Hom X Y) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x ↦ g (f x)) :=
  g.holomorphic_toFun.comp f.holomorphic_toFun

/-- Helper for Theorem VI.5-extra-9: a composite of surface morphisms still commutes with the
projections to `ℂ`. -/
theorem comp_commutes_projection (g : Hom Y Z) (f : Hom X Y) :
    ∀ x : X, Z.projection (g (f x)) = X.projection x := by
  intro x
  rw [g.commutes (f x), f.commutes x]

/-- Helper for Theorem VI.5-extra-9: the composition of morphisms of unramified surfaces over
`ℂ`. -/
def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  toFun := fun x ↦ g (f x)
  holomorphic_toFun := mdifferentiable_comp_map g f
  commutes := comp_commutes_projection g f

end ConnectedHausdorffUnramifiedSurfaceOver.Hom

/-- Helper for Theorem VI.5-extra-9: a maximal plane holomorphic extension is an extension
equipped with the universal property from Problem VI.5-extra-8. -/
structure MaximalPlaneHolomorphicExtension (U : Set ℂ) (f : ℂ → ℂ) where
  base : PlaneHolomorphicExtension U f
  isMaximal : base.IsMaximal

namespace MaximalPlaneHolomorphicExtension

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- Helper for Theorem VI.5-extra-9: the canonical comparison morphism between maximal plane
holomorphic extensions of the same germ. -/
noncomputable def hom (S T : MaximalPlaneHolomorphicExtension U f) :
    ConnectedHausdorffUnramifiedSurfaceOver.Hom S.base.surface T.base.surface :=
  Classical.choose (ExistsUnique.exists (T.isMaximal S.base))

/-- Helper for Theorem VI.5-extra-9: the canonical comparison morphism preserves the distinguished
embedding and the extended holomorphic function. -/
theorem hom_compatible (S T : MaximalPlaneHolomorphicExtension U f) :
    PlaneHolomorphicExtension.Compatible S.base T.base (hom S T) := by
  -- The chosen witness comes directly from the existence half of the maximality property.
  simpa [hom] using (Classical.choose_spec (ExistsUnique.exists (T.isMaximal S.base)))

/-- Helper for Theorem VI.5-extra-9: the canonical comparison morphism agrees with the
distinguished embeddings of `U`. -/
theorem hom_comp_embedding (S T : MaximalPlaneHolomorphicExtension U f) (z : U) :
    hom S T (S.base.embedding z) = T.base.embedding z :=
  (hom_compatible S T).1 z

/-- Helper for Theorem VI.5-extra-9: the canonical comparison morphism preserves the extended
holomorphic value. -/
theorem hom_commutes_extension (S T : MaximalPlaneHolomorphicExtension U f) (x : S.base.surface) :
    T.base.extension (hom S T x) = S.base.extension x :=
  (hom_compatible S T).2 x

/-- Helper for Theorem VI.5-extra-9: any compatible comparison morphism into a maximal extension is
the canonical one. -/
theorem hom_eq (S T : MaximalPlaneHolomorphicExtension U f)
    (h : ConnectedHausdorffUnramifiedSurfaceOver.Hom S.base.surface T.base.surface)
    (hh : PlaneHolomorphicExtension.Compatible S.base T.base h) :
    h = hom S T := by
  -- Maximality gives uniqueness of every compatible lift into `T`.
  rcases T.isMaximal S.base with ⟨k, hk, huniq⟩
  have hhk : h = k := huniq h hh
  have hhom : hom S T = k := huniq (hom S T) (hom_compatible S T)
  exact hhk.trans hhom.symm

/-- Helper for Theorem VI.5-extra-9: the canonical self-comparison morphism is the identity. -/
theorem hom_self (S : MaximalPlaneHolomorphicExtension U f) :
    hom S S = ConnectedHausdorffUnramifiedSurfaceOver.Hom.id S.base.surface := by
  -- The identity map is itself compatible, so uniqueness forces it to equal `hom S S`.
  exact (hom_eq S S (ConnectedHausdorffUnramifiedSurfaceOver.Hom.id S.base.surface) (by
    constructor
    · intro z
      rfl
    · intro x
      rfl)).symm

/-- Helper for Theorem VI.5-extra-9: the comparison in the opposite direction is a left inverse of
the canonical comparison. -/
theorem hom_inv_hom (S T : MaximalPlaneHolomorphicExtension U f) :
    Function.LeftInverse (hom T S) (hom S T) := by
  intro x
  have hcomp :
      ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp (hom T S) (hom S T) = hom S S := by
    -- Both the composite and the identity satisfy the same compatibility equations with `S`.
    exact hom_eq S S
      (ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp (hom T S) (hom S T)) (by
        constructor
        · intro z
          simp [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp, hom_comp_embedding]
        · intro x'
          simp [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp, hom_commutes_extension])
  have hvalue := congrArg (fun g ↦ g x) (hcomp.trans (hom_self S))
  simpa [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp,
    ConnectedHausdorffUnramifiedSurfaceOver.Hom.id] using hvalue

/-- Helper for Theorem VI.5-extra-9: the comparison in the opposite direction is a right inverse
of the canonical comparison. -/
theorem hom_hom_inv (S T : MaximalPlaneHolomorphicExtension U f) :
    Function.RightInverse (hom T S) (hom S T) := by
  intro y
  have hcomp :
      ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp (hom S T) (hom T S) = hom T T := by
    -- Repeating the same uniqueness argument on `T` identifies the opposite composite with `id`.
    exact hom_eq T T
      (ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp (hom S T) (hom T S)) (by
        constructor
        · intro z
          simp [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp, hom_comp_embedding]
        · intro x'
          simp [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp, hom_commutes_extension])
  have hvalue := congrArg (fun g ↦ g y) (hcomp.trans (hom_self T))
  simpa [ConnectedHausdorffUnramifiedSurfaceOver.Hom.comp,
    ConnectedHausdorffUnramifiedSurfaceOver.Hom.id] using hvalue

end MaximalPlaneHolomorphicExtension

/-- Theorem VI.5-extra-9: any two maximal plane holomorphic extensions of the same germ are
canonically isomorphic over `ℂ`. More precisely, there is a unique compatible comparison morphism
between them, and its inverse is the canonical comparison morphism in the opposite direction. -/
theorem analyticContinuation_existsUniqueIso {U : Set ℂ} {f : ℂ → ℂ}
    (S T : MaximalPlaneHolomorphicExtension U f) :
    ∃! h : ConnectedHausdorffUnramifiedSurfaceOver.Hom S.base.surface T.base.surface,
      PlaneHolomorphicExtension.Compatible S.base T.base h ∧
        Function.LeftInverse (MaximalPlaneHolomorphicExtension.hom T S) h ∧
        Function.RightInverse (MaximalPlaneHolomorphicExtension.hom T S) h := by
  -- The universal-property comparison map is the unique candidate from the source proof.
  refine ⟨MaximalPlaneHolomorphicExtension.hom S T, ?_, ?_⟩
  · exact ⟨
      MaximalPlaneHolomorphicExtension.hom_compatible S T,
      MaximalPlaneHolomorphicExtension.hom_inv_hom S T,
      MaximalPlaneHolomorphicExtension.hom_hom_inv S T⟩
  · intro h hh
    -- Any other compatible map agrees with the canonical one by maximality.
    exact MaximalPlaneHolomorphicExtension.hom_eq S T h hh.1
