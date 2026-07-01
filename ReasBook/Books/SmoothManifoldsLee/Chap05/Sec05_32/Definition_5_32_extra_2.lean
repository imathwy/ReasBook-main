import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding

open scoped ContDiff Manifold
open TopologicalSpace

universe u𝕜 uE uH uM uE' uH' uN uE'' uH''

section WeaklyEmbeddedSubmanifolds

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/-- The subset-level owner for an immersed submanifold structure on `S ⊆ M`: the subtype
inclusion `S ↪ M` is an immersion for the chosen smooth structure on `S`. -/
abbrev IsImmersedSubmanifold : Prop :=
  Manifold.IsImmersion J I ⊤ (Subtype.val : S → M)

/-- Definition 5.32-extra-2: A boundaryless immersed submanifold `S ⊆ M` is weakly embedded if
the inclusion `S ↪ M` is an immersion and every smooth map to `M` whose image lies in `S` is
smooth as a map to `S`. Some authors call weakly embedded submanifolds initial submanifolds. -/
class IsWeaklyEmbeddedSubmanifold : Prop extends BoundarylessManifold J S where
  isImmersion_subtype_val : IsImmersedSubmanifold I J S
  contMDiff_toSubtype {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
      {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
      [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
      {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
      ContMDiff K J ⊤ (Set.codRestrict F S hFS)

/-- Helper for Definition 5.32-extra-2: structure elimination turns the stored weakly embedded
restriction axiom into an ordinary standalone theorem. -/
lemma weakly_embedded_restriction_axiom
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    [hS : IsWeaklyEmbeddedSubmanifold.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''} I J S]
    {F : N → M}
    (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  -- Route correction: fix all universes and manifold instances in the lemma header before using
  -- the stored weakly embedded restriction field.
  exact
    @IsWeaklyEmbeddedSubmanifold.contMDiff_toSubtype.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''}
      𝕜 _ E _ _ H _ M _ _ I E' _ _ H' _ J S _ hS
      E'' _ _ H'' _ N _ _ K _ F hF hFS

/-- Helper for Definition 5.32-extra-2: unpacking an explicit weakly embedded structure yields the
stored codomain-restriction smoothness statement with all binders fixed. -/
lemma contMDiff_toSubtype_of_weakly_embedded
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    (hS : IsWeaklyEmbeddedSubmanifold.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''} I J S)
    {F : N → M}
    (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  -- Route correction: use the extracted standalone restriction theorem instead of projecting the
  -- class field directly at this use site.
  letI : IsWeaklyEmbeddedSubmanifold I J S := hS
  exact weakly_embedded_restriction_axiom (I := I) (J := J) (S := S) (N := N) (K := K) hF hFS

/-- Helper for Definition 5.32-extra-2: the weakly embedded codomain-restriction field applied to
the ambient-valued map underlying a subtype-valued map. -/
lemma contMDiff_codRestrict_subtype_val
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    (hS : IsWeaklyEmbeddedSubmanifold.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''} I J S)
    {f : N → S}
    (hf : ContMDiff K I ⊤ (fun x ↦ (f x : M))) :
    ContMDiff K J ⊤ (Set.codRestrict (fun x ↦ (f x : M)) S (fun x : N ↦ (f x).2)) := by
  -- Specialize the explicit weakly embedded restriction theorem to the ambient map underlying `f`.
  exact contMDiff_toSubtype_of_weakly_embedded
    (I := I) (J := J) (S := S) (K := K) hS hf (fun x : N ↦ (f x).2)

/-- Helper for Definition 5.32-extra-2: the codomain-restricted ambient map agrees pointwise with
the original subtype-valued map. -/
lemma codRestrict_coe_eq_apply
    {N : Type uN} {f : N → S} (x : N) :
    Set.codRestrict (fun y ↦ (f y : M)) S (fun y : N ↦ (f y).2) x = f x := by
  -- Both sides are the same subtype element at the chosen point.
  rfl

/-- Helper for Definition 5.32-extra-2: codomain restriction of the ambient-valued map underlying
a subtype-valued map recovers the original map. -/
lemma codRestrict_coe_eq
    {N : Type uN} {f : N → S} :
    Set.codRestrict (fun x ↦ (f x : M)) S (fun x : N ↦ (f x).2) = f := by
  -- Both functions have the same value in the subtype at each point.
  funext x
  exact codRestrict_coe_eq_apply (S := S) (f := f) x

/-- Helper for Definition 5.32-extra-2: composing with the inclusion of an open subtype preserves
`C^n` regularity for arbitrary differentiability order. -/
lemma contMDiff_subtype_val_comp_iff
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    {n : ℕ∞ω} (U : Opens M) (f : N → U) :
    ContMDiff K I n (Subtype.val ∘ f) ↔ ContMDiff K I n f := by
  -- Unfold `ContMDiff` pointwise and invoke the local invariant-property equivalence for
  -- composition with `Subtype.val`.
  simp_rw [ContMDiff, ContMDiffAt, ContMDiffWithinAt,
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff]

-- Proof sketch: apply the defining codomain-restriction property to the ambient map
-- `Subtype.val ∘ f`; its values lie in `S` tautologically, and the resulting codomain-restricted
-- map is definitionally `f`.
/-- A map into a weakly embedded submanifold is smooth once its composition with the subtype
inclusion into the ambient manifold is smooth. -/
theorem contMDiff_of_comp_subtype_val
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    [IsWeaklyEmbeddedSubmanifold.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''} I J S] {f : N → S}
    (hf : ContMDiff K I ⊤ (fun x ↦ (f x : M))) :
    ContMDiff K J ⊤ f := by
  -- Apply the weakly embedded codomain-restriction field to the ambient-valued map underlying `f`.
  have hS :
      IsWeaklyEmbeddedSubmanifold.{u𝕜, uE, uH, uM, uE', uH', uN, uE'', uH''} I J S := by
    infer_instance
  have hcod :
      ContMDiff K J ⊤ (Set.codRestrict (fun x ↦ (f x : M)) S (fun x : N ↦ (f x).2)) :=
    contMDiff_codRestrict_subtype_val (I := I) (J := J) (S := S) K hS hf
  -- Rewrite the codomain-restricted ambient map back to the original subtype-valued map.
  simpa [codRestrict_coe_eq (S := S) (f := f)] using hcod

/-- Helper for Definition 5.32-extra-2: a smooth map whose image lies in an open subset is smooth
as a map into the corresponding open subtype. -/
lemma contMDiff_codRestrict_opens
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type uH''} [TopologicalSpace H''] {N : Type uN} [TopologicalSpace N]
    [ChartedSpace H'' N] (K : ModelWithCorners 𝕜 E'' H'') [IsManifold K ⊤ N]
    (U : Opens M) {F : N → M} (hF : ContMDiff K I ⊤ F) (hFU : ∀ x, F x ∈ (U : Set M)) :
    ContMDiff K I ⊤ (fun x ↦ (⟨F x, hFU x⟩ : U)) := by
  -- Reduce smoothness into the open subtype to smoothness after composing with its inclusion.
  refine (contMDiff_subtype_val_comp_iff (I := I) (K := K) U (fun x ↦ (⟨F x, hFU x⟩ : U))).mp ?_
  simpa [Function.comp] using hF

noncomputable section

local instance : ChartedSpace H (Set.univ : Set M) := by
  let U : Opens M := ⊤
  change ChartedSpace H U
  infer_instance

local instance : IsManifold I ⊤ (Set.univ : Set M) := by
  let U : Opens M := ⊤
  change IsManifold I ⊤ U
  infer_instance

/-- The ambient manifold is weakly embedded in itself, with the canonical inherited smooth
structure on the open subtype `Set.univ`. -/
instance isWeaklyEmbeddedSubmanifold_univ [BoundarylessManifold I M]
    : IsWeaklyEmbeddedSubmanifold I I (Set.univ : Set M) where
  toBoundarylessManifold := by
    let U : Opens M := ⊤
    change BoundarylessManifold I U
    infer_instance
  isImmersion_subtype_val := by
    let U : Opens M := ⊤
    change Manifold.IsImmersion I I ⊤ (Subtype.val : U → M)
    simpa using Manifold.IsImmersion.of_opens U
  contMDiff_toSubtype := by
    intro E'' _ _ H'' _ N _ _ K _ F hF hFS
    -- Route correction: replace the removed imported corollary with the local open-subtype
    -- restriction lemma specialized to the open set `⊤`.
    let U : Opens M := ⊤
    simpa [U, Set.codRestrict] using contMDiff_codRestrict_opens (I := I) (K := K) U hF hFS

end

end WeaklyEmbeddedSubmanifolds
