import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject

noncomputable section

section

namespace CategoryTheory.ShortComplex.ShortExact

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasPullbacks C] [HasKernels C]
  [HasBinaryBiproducts C] [HasZeroObject C] [Balanced C] [IsNormalEpiCategory C]
variable {S₁ S₂ : ShortComplex C}
variable [Projective S₁.X₂] [Projective S₂.X₂]

/- Domain-style sampling:
- primary domain: short exact complexes in a preadditive balanced category, pullbacks, kernels,
  projective splittings, binary biproducts, and the normal-epi API needed to recognize kernel
  sequences as exact;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.ShortExact.splittingOfProjective`,
  `CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct`,
  `CategoryTheory.Limits.isIso_kernel_map_of_isPullback`,
  `CategoryTheory.Limits.kernelCompMono`,
  `CategoryTheory.normalEpiOfEpi`,
  and the biproduct owner notation `⊞`;
- best owner abstraction: the intrinsic owner statement lives at the categorical short-exact /
  projective / pullback / biproduct layer, with the normal-epi comparison only supplying the
  derived exactness of kernel sequences; the module-product / linear-equivalence statement is only
  a bridge/view;
- source/core/bridge triage:
  `source-facing`: Schanuel's lemma for two short exact complexes with projective middle terms and
    a chosen identification of the right terms;
  `core/canonical`: the short exact owner namespace together with projective splittings and binary
    biproducts;
  `bridge/view`: the later `ModuleCat` linear-equivalence reformulation via `biprodIsoProd`;
- primitive data: the two short exact complexes, projectivity of their middle terms, and the
  right-term isomorphism `e₃`;
- derived API: the two split short exact sequences on the pullback object and the induced
  biproduct identifications. -/

private noncomputable def cokernelOfKernelι {X Y : C} (q : X ⟶ Y) [Epi q] :
    IsColimit (CokernelCofork.ofπ q (kernel.condition q)) := by
  let nq : NormalEpi q := normalEpiOfEpi q
  let l : nq.W ⟶ kernel q := kernel.lift q nq.g nq.w
  refine CokernelCofork.IsColimit.ofπ' q (kernel.condition q) (fun {Z'} s hs ↦ ?_)
  refine ⟨nq.isColimit.desc <| CokernelCofork.ofπ s <| by
      rw [show nq.g = l ≫ kernel.ι q by simp [l], Category.assoc, hs]
      simp, ?_⟩
  simpa using nq.isColimit.fac
    (CokernelCofork.ofπ s <| by
      rw [show nq.g = l ≫ kernel.ι q by simp [l], Category.assoc, hs]
      simp)
    WalkingParallelPair.one

omit [HasPullbacks C] [HasBinaryBiproducts C] [Balanced C] in
private theorem shortExact_kernelSequence {X Y : C} (q : X ⟶ Y) [Epi q] :
    (ShortComplex.mk (kernel.ι q) q (by simp)).ShortExact := by
  let S : ShortComplex C := ShortComplex.mk (kernel.ι q) q (by simp)
  have hi : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using (kernelIsKernel q)
  have hp : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using (cokernelOfKernelι q)
  let f' : kernel q ⟶ kernel q := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by
    have hlift : f' ≫ kernel.ι q = kernel.ι q := by
      have := hi.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero
      simpa only [S, f'] using this
    apply (cancel_mono (kernel.ι q)).1
    simpa using hlift
  let g' : Y ⟶ Y := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by
    have hdesc : q ≫ g' = q := by
      have := hp.fac (CokernelCofork.ofπ S.g S.zero) WalkingParallelPair.one
      simpa only [S, g'] using this
    apply (cancel_epi q).1
    simpa using hdesc
  let wπ : f' ≫ (0 : kernel q ⟶ (0 : C)) = 0 := by simp
  have hfEpi : Epi f' := by
    rw [hf']
    infer_instance
  have hπ :
      IsColimit (CokernelCofork.ofπ (0 : kernel q ⟶ (0 : C)) wπ) := by
    exact CokernelCofork.IsColimit.ofEpiOfIsZero _ hfEpi (isZero_zero _)
  let wι : (0 : (0 : C) ⟶ Y) ≫ hp.desc (CokernelCofork.ofπ S.g S.zero) = 0 := by
    simp only [Limits.zero_comp]
  have hgMono : Mono (hp.desc (CokernelCofork.ofπ S.g S.zero)) := by
    simpa [g'] using (show Mono g' by rw [hg']; infer_instance)
  have hι :
      IsLimit (KernelFork.ofι (0 : (0 : C) ⟶ Y) wι) := by
    exact KernelFork.IsLimit.ofMonoOfIsZero _ hgMono (isZero_zero _)
  have hExact : S.Exact := by
    let hData : S.HomologyData :=
      { left :=
          { K := kernel q
            H := (0 : C)
            i := kernel.ι q
            π := 0
            wi := by simp [S]
            hi := hi
            wπ := wπ
            hπ := hπ }
        right :=
          { Q := Y
            H := (0 : C)
            p := q
            ι := 0
            wp := by simp [S]
            hp := hp
            wι := wι
            hι := hι }
        iso := Iso.refl _ }
    refine ⟨?_⟩
    exact ⟨hData, isZero_zero _⟩
  have hShortExact : S.ShortExact := ShortComplex.ShortExact.mk' hExact inferInstance inferInstance
  simpa [S] using hShortExact

private noncomputable abbrev schanuelPullback (e₃ : S₁.X₃ ≅ S₂.X₃) : C :=
  pullback (S₁.g ≫ e₃.hom) S₂.g

private noncomputable abbrev schanuelLeftSequence (e₃ : S₁.X₃ ≅ S₂.X₃) : ShortComplex C :=
  ShortComplex.mk
    (kernel.ι (pullback.snd (S₁.g ≫ e₃.hom) S₂.g))
    (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
    (by simp)

private noncomputable abbrev schanuelRightSequence (e₃ : S₁.X₃ ≅ S₂.X₃) : ShortComplex C :=
  ShortComplex.mk
    (kernel.ι (pullback.fst (S₁.g ≫ e₃.hom) S₂.g))
    (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
    (by simp)

omit [HasBinaryBiproducts C] [Balanced C] [Projective S₁.X₂] [Projective S₂.X₂] in
private theorem schanuelLeftSequence_shortExact
    (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Epi (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)] :
    (schanuelLeftSequence e₃).ShortExact := by
  simpa [schanuelLeftSequence] using
    (shortExact_kernelSequence (pullback.snd (S₁.g ≫ e₃.hom) S₂.g) :
      (ShortComplex.mk
        (kernel.ι (pullback.snd (S₁.g ≫ e₃.hom) S₂.g))
        (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
        (by simp)).ShortExact)

omit [HasBinaryBiproducts C] [Balanced C] [Projective S₁.X₂] [Projective S₂.X₂] in
private theorem schanuelRightSequence_shortExact
    (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Epi (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)] :
    (schanuelRightSequence e₃).ShortExact := by
  simpa [schanuelRightSequence] using
    (shortExact_kernelSequence (pullback.fst (S₁.g ≫ e₃.hom) S₂.g) :
      (ShortComplex.mk
        (kernel.ι (pullback.fst (S₁.g ≫ e₃.hom) S₂.g))
        (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
        (by simp)).ShortExact)

private noncomputable def kernelIsoOfShortExact {S : ShortComplex C} (hS : S.ShortExact) :
    kernel S.g ≅ S.X₁ :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel

private noncomputable def schanuelLeftKernelIso
    (hS₁ : S₁.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃) :
    kernel (pullback.snd (S₁.g ≫ e₃.hom) S₂.g) ≅ S₁.X₁ :=
  let sq := (IsPullback.of_hasPullback (S₁.g ≫ e₃.hom) S₂.g).flip
  letI :
      IsIso
        (kernel.map
          (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
          (S₁.g ≫ e₃.hom)
          (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
          S₂.g
          sq.w) :=
    CategoryTheory.Limits.isIso_kernel_map_of_isPullback sq
  asIso
      (kernel.map
        (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
        (S₁.g ≫ e₃.hom)
        (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
        S₂.g
        sq.w) ≪≫
    kernelCompMono S₁.g e₃.hom ≪≫
    kernelIsoOfShortExact hS₁

private noncomputable def schanuelRightKernelIso
    (hS₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃) :
    kernel (pullback.fst (S₁.g ≫ e₃.hom) S₂.g) ≅ S₂.X₁ :=
  let sq := IsPullback.of_hasPullback (S₁.g ≫ e₃.hom) S₂.g
  letI :
      IsIso
        (kernel.map
          (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
          S₂.g
          (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
          (S₁.g ≫ e₃.hom)
          sq.w) :=
    CategoryTheory.Limits.isIso_kernel_map_of_isPullback sq
  asIso
      (kernel.map
        (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)
        S₂.g
        (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)
        (S₁.g ≫ e₃.hom)
        sq.w) ≪≫
    kernelIsoOfShortExact hS₂

private noncomputable def schanuelLeftIso
    (hS₁ : S₁.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Epi (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)] :
    schanuelPullback e₃ ≅ S₁.X₁ ⊞ S₂.X₂ :=
  (splittingOfProjective (schanuelLeftSequence_shortExact e₃)).isoBinaryBiproduct ≪≫
    biprod.mapIso (schanuelLeftKernelIso hS₁ e₃) (Iso.refl _)

private noncomputable def schanuelRightIso
    (hS₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Epi (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)] :
    schanuelPullback e₃ ≅ S₁.X₂ ⊞ S₂.X₁ :=
  (splittingOfProjective (schanuelRightSequence_shortExact e₃)).isoBinaryBiproduct ≪≫
    biprod.mapIso (schanuelRightKernelIso hS₂ e₃) (Iso.refl _) ≪≫
    biprod.braiding _ _

-- Proof sketch: pull back the two right maps over the identified right term. The two projection
-- maps from the pullback are epimorphisms, so each kernel-projection short complex is short
-- exact. Because the corresponding right terms are projective, each short exact complex splits,
-- giving two canonical biproduct descriptions of the same pullback object. Composing those
-- identifications yields Schanuel's stable isomorphism.
/-- Lemma 10.109.1 (Schanuel's lemma), owner form: for two short exact complexes in the ambient
short-complex/projective/pullback layer, with projective middle terms, identified right term, and
epimorphic pullback projections, the corresponding stable biproducts are canonically isomorphic. -/
noncomputable def schanuel_lemma
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Epi (pullback.snd (S₁.g ≫ e₃.hom) S₂.g)]
    [Epi (pullback.fst (S₁.g ≫ e₃.hom) S₂.g)] :
    S₁.X₁ ⊞ S₂.X₂ ≅ S₁.X₂ ⊞ S₂.X₁ :=
  (schanuelLeftIso hS₁ e₃).symm ≪≫ schanuelRightIso hS₂ e₃

end

end CategoryTheory.ShortComplex.ShortExact

section

variable {R : Type u} [Ring R]
variable {K L M P₁ P₂ : Type v}
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup L] [Module R L]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable [Module.Projective R P₁] [Module.Projective R P₂]

open CategoryTheory.ShortComplex.ShortExact

-- Proof sketch: package the two exact module sequences as short exact complexes in `ModuleCat R`,
-- apply the categorical owner theorem `schanuel_lemma`, and transport the resulting biproduct
-- isomorphism to products of modules via `ModuleCat.biprodIsoProd`.
/-- Thin `ModuleCat` bridge from the categorical owner form of Schanuel's lemma to linear
equivalences of product modules. -/
noncomputable def schanuel_lemma_of_linearMaps
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁) (hp₁ : Function.Surjective p₁)
    (hc₂ : Function.Injective c₂) (h₂ : Function.Exact c₂ p₂) (hp₂ : Function.Surjective p₂) :
    (K × P₂) ≃ₗ[R] (P₁ × L) :=
  let S₁ : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.moduleCatMk c₁ p₁ h₁.linearMap_comp_eq_zero
  let S₂ : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.moduleCatMk c₂ p₂ h₂.linearMap_comp_eq_zero
  letI : Projective S₁.X₂ := by
    simpa [S₁] using (inferInstance : Projective (ModuleCat.of R P₁))
  letI : Projective S₂.X₂ := by
    simpa [S₂] using (inferInstance : Projective (ModuleCat.of R P₂))
  let hS₁ : S₁.ShortExact := ModuleCat.shortComplex_shortExact S₁ h₁ hc₁ hp₁
  let hS₂ : S₂.ShortExact := ModuleCat.shortComplex_shortExact S₂ h₂ hc₂ hp₂
  letI := hS₁.epi_g
  letI := hS₂.epi_g
  let e : ModuleCat.of R K ⊞ ModuleCat.of R P₂ ≅ ModuleCat.of R P₁ ⊞ ModuleCat.of R L :=
    schanuel_lemma hS₁ hS₂ (Iso.refl _)
  ((ModuleCat.biprodIsoProd _ _).symm ≪≫ e ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

end

end
