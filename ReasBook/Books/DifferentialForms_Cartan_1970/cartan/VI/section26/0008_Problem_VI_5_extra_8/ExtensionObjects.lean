import Mathlib
import DifferentialForms_Cartan_1970.VI.section25.«0008_Proposition_4_I»
import DifferentialForms_Cartan_1970.VI.section26.«0002_Definition_VI_5_extra_2»

open scoped Manifold
open Set

universe u u₁ u₂

-- Domain sampling: the primary domain here is analytic continuation on one-dimensional complex
-- manifolds over `ℂ`. The relevant owner declarations inspected before this refinement were:
-- * the chapter-local source-facing owner `ConnectedHausdorffUnramifiedSurfaceOver ℂ` from
--   `0002_Definition_VI_5_extra_2.lean`;
-- * its inherited manifold API `ConnectedHausdorffUnramifiedSurfaceOver.mdifferentiable_projection`
--   in `0002`, which places projection maps directly in the canonical holomorphic interface;
-- * the section-26 use of `MDifferentiable`, which is the owner for holomorphic maps between the
--   resulting Riemann-surface charts.
-- The best owner abstraction for this item is the source-facing extension object
-- `PlaneHolomorphicExtension U f`. Primitive data in the extension problem is the connected
-- Hausdorff unramified surface over `ℂ`, the embedding of `U`, and the extended holomorphic
-- function. Compatibility of continuation maps and maximality are derived API: they are
-- properties of an existing extension object, not additional primitive data that should be packed
-- into a second wrapper owner.

namespace ConnectedHausdorffUnramifiedSurfaceOver

/-- A morphism of connected Hausdorff unramified surfaces over `ℂ` is a holomorphic map commuting
with the projections to `ℂ`. -/
structure Hom (X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ) where
  toFun : X → Y
  holomorphic_toFun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  commutes (x : X) : Y.projection (toFun x) = X.projection x

instance {X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ} :
    CoeFun (Hom X Y) (fun _ ↦ X → Y) where
  coe h := h.toFun

end ConnectedHausdorffUnramifiedSurfaceOver

/-- A holomorphic extension of `f` from the open set `U ⊆ ℂ` to a connected Hausdorff unramified
surface over `ℂ`. -/
structure PlaneHolomorphicExtension (U : Set ℂ) (f : ℂ → ℂ) where
  surface : ConnectedHausdorffUnramifiedSurfaceOver.{0,u} ℂ
  embedding : U → surface
  isOpenEmbedding_embedding : Topology.IsOpenEmbedding embedding
  projection_comp_embedding (z : U) : surface.projection (embedding z) = z
  extension : surface → ℂ
  holomorphic_extension : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) extension
  extension_comp_embedding (z : U) : extension (embedding z) = f z

namespace PlaneHolomorphicExtension

open ConnectedHausdorffUnramifiedSurfaceOver

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- A comparison morphism between two holomorphic extensions of the same germ is a surface map
that preserves both the distinguished embedding of `U` and the extended holomorphic value. -/
def Compatible
    (E₁ : PlaneHolomorphicExtension.{u₁} U f)
    (E₂ : PlaneHolomorphicExtension.{u₂} U f)
    (h : Hom E₁.surface E₂.surface) : Prop :=
  (∀ z : U, h (E₁.embedding z) = E₂.embedding z) ∧
    ∀ x : E₁.surface, E₂.extension (h x) = E₁.extension x

/-- A holomorphic extension is maximal when every other extension of the same germ admits a unique
comparison morphism into it. -/
def IsMaximal
    (E : PlaneHolomorphicExtension.{u} U f) : Prop :=
  -- Route correction: the universal comparison family stays in the original small carrier
  -- universe, while the maximal witness itself may live one universe higher after gluing.
  ∀ E' : PlaneHolomorphicExtension.{0} U f,
    ∃! h : Hom E'.surface E.surface, Compatible E' E h

end PlaneHolomorphicExtension

/-- Helper for Problem VI.5-extra-8: the original open set `U` is itself an unramified surface
over `ℂ` via the inclusion map. -/
noncomputable def tautological_surface
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U] :
    ConnectedHausdorffUnramifiedSurfaceOver ℂ :=
  ConnectedHausdorffUnramifiedSurfaceOver.ofIsLocalHomeomorph
    (Subtype.val : U → ℂ) hU_open.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- Helper for Problem VI.5-extra-8: every point of the tautological surface projects back into
the original open set `U`. -/
lemma tautological_surface_projection_eq
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : tautological_surface hU_open) :
    (tautological_surface hU_open).projection z = z.1 := by
  rfl

/-- Helper for Problem VI.5-extra-8: every point of the tautological surface projects back into
the original open set `U`. -/
lemma tautological_surface_projection_mem
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : tautological_surface hU_open) :
    (tautological_surface hU_open).projection z ∈ U := by
  -- The tautological projection is just the subtype value map.
  rw [tautological_surface_projection_eq hU_open z]
  exact z.2

/-- Helper for Problem VI.5-extra-8: the pullback of `f` along the tautological projection is
holomorphic on the tautological surface. -/
lemma subtype_extension_mdifferentiable
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : tautological_surface hU_open ↦ f ((tautological_surface hU_open).projection z)) := by
  let X := tautological_surface hU_open
  -- First record the ambient holomorphicity of `f` on the open set `U`.
  have hf_on : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U := hf.mdifferentiableOn
  have hproj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X.projection :=
    ConnectedHausdorffUnramifiedSurfaceOver.mdifferentiable_projection X
  -- Then compose with the tautological projection, whose image is contained in `U`.
  have hcomp : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ X.projection) Set.univ :=
    hf_on.comp hproj.mdifferentiableOn (by
      intro z _hz
      simpa [X] using tautological_surface_projection_mem hU_open z)
  simpa [X, Function.comp] using (mdifferentiableOn_univ.mp hcomp)

/-- Helper for Problem VI.5-extra-8: the tautological embedding into the tautological surface
commutes with the projection to `ℂ`. -/
lemma tautological_surface_projection_comp_embedding
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : U) :
    (tautological_surface hU_open).projection z = z := by
  simpa using tautological_surface_projection_eq hU_open z

/-- Helper for Problem VI.5-extra-8: the tautological extension agrees with `f` on the embedded
copy of `U`. -/
lemma tautological_extension_comp_embedding
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (z : U) :
    (fun x : tautological_surface hU_open ↦ f ((tautological_surface hU_open).projection x)) z = f z := by
  -- On the tautological surface the projection is the subtype inclusion.
  simpa using congrArg f (tautological_surface_projection_comp_embedding hU_open z)

/-- Helper for Problem VI.5-extra-8: the given germ on `U` already determines a base
holomorphic extension object. -/
noncomputable def tautological_extension
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : PlaneHolomorphicExtension.{0} U f where
  surface := tautological_surface hU_open
  embedding := fun z ↦ z
  isOpenEmbedding_embedding := Topology.IsOpenEmbedding.id
  projection_comp_embedding := tautological_surface_projection_comp_embedding hU_open
  extension := fun z ↦ f ((tautological_surface hU_open).projection z)
  holomorphic_extension := subtype_extension_mdifferentiable hU_open hf
  extension_comp_embedding := tautological_extension_comp_embedding hU_open

/-- Helper for Problem VI.5-extra-8: the hypotheses already give a nonempty family of
holomorphic extensions, namely the tautological one on `U` itself. -/
theorem plane_holomorphic_extension_nonempty
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    Nonempty (PlaneHolomorphicExtension.{0} U f) := by
  letI : ConnectedSpace U := Subtype.connectedSpace ⟨hU_nonempty, hU_connected⟩
  -- The open subtype carries the initial extension object before any maximal quotient is formed.
  exact ⟨tautological_extension hU_open hf⟩
