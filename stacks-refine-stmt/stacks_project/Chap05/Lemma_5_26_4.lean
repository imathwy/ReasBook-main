import Mathlib.Topology.ExtremallyDisconnected

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set Homeomorph

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [ExtremallyDisconnected Y] {f : X → Y}

/- Domain-style sampling for Gleason's extremally disconnected compact-Hausdorff criterion:
- primary domain: compact Hausdorff topology and extremally disconnected targets
- sampled declarations:
  `isHomeomorph_iff_continuous_bijective`,
  `exists_compact_surjective_zorn_subset`,
  `image_subset_closure_compl_image_compl_of_isOpen`,
  `ExtremallyDisconnected.homeoCompactToT2`
- best owner abstraction: `ExtremallyDisconnected.homeoCompactToT2`

Layer triage:
- `source-facing`: the Stacks lemma phrased as an `IsHomeomorph` criterion for a continuous
  surjection whose proper closed subsets have proper image
- `core/canonical`: mathlib's homeomorphism owner
  `ExtremallyDisconnected.homeoCompactToT2`
- `bridge/view`: this file's `IsHomeomorph` consequence obtained by taking
  `.isHomeomorph` of the owner homeomorphism; because this file keeps the natural two-universe
  surface, the proof uses the standard `ULift` homeomorphism bridge to reach the same-universe
  owner theorem

Primitive data is exactly the continuous surjection together with the proper-closed-image
condition. The injectivity proof is derived API already internalized by the owner theorem, so
keeping a second local injectivity theorem here would be duplicate wheel API. The codomain
compactness assumption is also derived from compactness of `X` and surjectivity, so it should not
remain in the public surface.
-/

/-- Lemma 5.26.4: a surjective continuous map from a Hausdorff quasi-compact space to an
extremally disconnected Hausdorff space is a homeomorphism if the image of every proper closed
subset of the source is a proper subset of the target. The target's quasi-compactness is automatic
from surjectivity and compactness of the source, so it is omitted from the Lean hypotheses. -/
theorem isHomeomorph_of_extremallyDisconnected_of_surjective_of_image_proper_closed
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hproper :
      ∀ Z : Set X, Z ≠ (univ : Set X) → IsClosed Z → f '' Z ≠ (univ : Set Y)) :
    IsHomeomorph f := by
  let f' : ULift.{max u v} X → ULift.{max u v} Y := fun x ↦ ULift.up (f x.down)
  let eX : ULift.{max u v} X ≃ₜ X := ulift
  let eY : ULift.{max u v} Y ≃ₜ Y := ulift
  have hf' : Continuous f' := by
    have heY : Continuous eY.symm := eY.symm.continuous
    simpa only [f'] using heY.comp (hf.comp eX.continuous)
  have hsurj' : Function.Surjective f' := by
    intro y
    rcases hsurj y.down with ⟨x, hx⟩
    refine ⟨ULift.up x, ?_⟩
    cases y
    simpa only [f'] using congrArg ULift.up hx
  haveI : ExtremallyDisconnected (ULift.{max u v} Y) :=
    extremallyDisconnected_of_homeo eY.symm
  have hproper' :
      ∀ Z : Set (ULift.{max u v} X), Z ≠ univ → IsClosed Z → f' '' Z ≠ (univ : Set (ULift.{max u v} Y)) := by
    intro Z hZ hZclosed himage
    have hdown_ne : eX '' Z ≠ (univ : Set X) := by
      intro hZU
      apply hZ
      ext x
      constructor
      · intro _
        trivial
      · intro _
        have hx : x.down ∈ eX '' Z := by
          simpa only [hZU] using (show x.down ∈ (univ : Set X) from trivial)
        rcases hx with ⟨z, hz, hzdown⟩
        cases z
        cases x
        simp at hzdown ⊢
        cases hzdown
        simpa using hz
    have hclosed' : IsClosed (eX '' Z) := eX.isClosed_image.mpr hZclosed
    have hproperX : f '' (eX '' Z) ≠ (univ : Set Y) :=
      hproper _ hdown_ne hclosed'
    have himage' : eY '' (f' '' Z) = f '' (eX '' Z) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨y', hy', hy_eq⟩
        rcases hy' with ⟨x, hx, hx_eq⟩
        refine ⟨x.down, ⟨x, hx, rfl⟩, ?_⟩
        have : f x.down = y'.down := by
          simpa only [f'] using congrArg ULift.down hx_eq
        exact this.trans <| by simpa using hy_eq
      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨x', hx', rfl⟩
        exact ⟨ULift.up (f x'.down), ⟨x', hx', rfl⟩, rfl⟩
    apply hproperX
    rw [← himage', himage]
    rw [image_univ_of_surjective eY.surjective]
  let e' : ULift.{max u v} X ≃ₜ ULift.{max u v} Y :=
    ExtremallyDisconnected.homeoCompactToT2 hf' hsurj' hproper'
  have hhomeo' : IsHomeomorph f' := by
    simpa only [e', f'] using e'.isHomeomorph
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨hf, ?_, hsurj⟩
  intro x₁ x₂ hfx
  have hfx' : f' (ULift.up x₁) = f' (ULift.up x₂) := by
    simp [f', hfx]
  exact congrArg ULift.down (hhomeo'.bijective.1 hfx')

end
