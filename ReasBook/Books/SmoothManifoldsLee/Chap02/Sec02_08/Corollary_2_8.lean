import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Topology.Sets.OpenCover

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uA

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type uH'} [TopologicalSpace H']
  {N : Type uM} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'}

/-- Corollary 2.8 (Gluing Lemma for Smooth Maps): if smooth local maps on an open cover of `M`
agree on pairwise overlaps, then there is a unique global smooth map whose restrictions are the
given local maps. The owner abstraction is the sheaf `smoothSheaf I I' M N`; this theorem is the
source-facing gluing bridge specialized to global sections. -/
theorem gluing_lemma_for_smooth_maps
    {A : Type uA} {U : A → Opens M} {f : ∀ a, U a → N}
    (hU : IsOpenCover U)
    (hf : ∀ a, ContMDiff I I' ∞ (f a))
    (hcompat : ∀ a b (x : ↥((U a) ⊓ (U b))), f a ⟨x, x.2.1⟩ = f b ⟨x, x.2.2⟩) :
    ∃! F : C^∞⟮I, M; I', N⟯, ∀ a (x : U a), F x = f a x := by
  let 𝒮 := smoothSheaf I I' M N
  let sf : ∀ a, 𝒮.presheaf.obj (Opposite.op (U a)) := fun a ↦ ⟨f a, hf a⟩
  have hsf : TopCat.Presheaf.IsCompatible 𝒮.1 U sf := by
    intro a b
    apply ContMDiffMap.ext
    intro x
    exact hcompat a b x
  have hcover : (⊤ : Opens M) ≤ iSup U := by
    simp [hU.iSup_eq_top]
  obtain ⟨gl, hgl, -⟩ :=
    𝒮.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover sf hsf
  let toTop : M → (⊤ : Opens M) := fun x ↦ ⟨x, by trivial⟩
  have htoTop : ContMDiff I I ∞ toTop := by
    have h_id : ContMDiff I I ∞ (Subtype.val ∘ toTop) := by
      change ContMDiff I I ∞ (fun x : M ↦ x)
      simpa using (contMDiff_id : ContMDiff I I ∞ (fun x : M ↦ x))
    exact (ContMDiff.subtypeVal_comp_iff (⊤ : Opens M) toTop).1 h_id
  let F : C^∞⟮I, M; I', N⟯ := ⟨fun x ↦ gl (toTop x), (smoothSheaf.contMDiff_section gl).comp htoTop⟩
  have hF : ∀ a (x : U a), F x = f a x := by
    intro a x
    simpa [F, sf, toTop] using
      congrArg (fun s : 𝒮.presheaf.obj (Opposite.op (U a)) ↦ s x) (hgl a)
  refine ⟨F, hF, ?_⟩
  intro G hG
  ext x
  rcases hU.exists_mem x with ⟨a, ha⟩
  exact (hG a ⟨x, ha⟩).trans (hF a ⟨x, ha⟩).symm
