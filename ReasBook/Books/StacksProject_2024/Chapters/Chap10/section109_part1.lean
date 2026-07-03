import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_109_1_Schanuel_s_lemma (from Chap10) -/
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

/-! ### Definition_10_109_2 (from Chap10) -/
universe u v

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R]

/- 
Domain-style sampling:
- primary domain: projective dimension in the abelian category `ModuleCat R`.
- inspected owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `CategoryTheory.projectiveDimension_le_iff`,
  `CategoryTheory.HasProjectiveDimensionLE`.
- best owner abstraction: `projectiveDimension`.
- source/core/bridge triage:
  `source-facing`: finite projective dimension for an `R`-module;
  `core/canonical`: `projectiveDimension`;
  `bridge/view`: `projectiveDimension_ne_top_iff` together with `projectiveDimension_le_iff`.
- primitive data vs derived API: there is no extra source-defined data here; the invariant
  `projectiveDimension` is primitive, while the existence of a natural-number bound is derived API.
-/

/- Definition 10.109.2: finite projective dimension for an `R`-module is expressed by the
canonical invariant `CategoryTheory.projectiveDimension`. -/
#check (projectiveDimension : ModuleCat.{v} R → WithBot ℕ∞)

/- Companion recall: `projectiveDimension M ≠ ⊤` is the canonical finite-projective-dimension
criterion, and with `projectiveDimension_le_iff` it is equivalent to the existence of a natural
number bound on `projectiveDimension M`. -/
recall projectiveDimension_ne_top_iff
recall projectiveDimension_le_iff

end ModuleCat

/-! ### Lemma_10_109_3 (from Chap10) -/
universe v

open CategoryTheory

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat`, short exact complexes, and projective
  syzygies.
* inspected owner declarations:
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `LinearMap.shortComplexKer`, and `LinearMap.shortExact_shortComplexKer`.
* best owner abstraction: a short exact complex `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with projective middle
  term; a kernel `LinearMap.ker π` is a bridge/view via `LinearMap.shortComplexKer π`.
* layer triage:
  the short-exact corollary below is `core/canonical`,
  `projective_ker_of_surjective_of_hasProjectiveDimensionLE_one` is `bridge/view`,
  and the finite exact-sequence statement remains `source-facing`.
* primitive data: the short exact owner object and the projective-dimension bound on its cokernel.
* derived API: projectivity of the kernel / top syzygy.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type v} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules with `X₂` projective, if
`X₃` has projective dimension at most `1`, then `X₁` is projective. This is the `n = 0`
specialization of the canonical owner theorem
`ShortExact.hasProjectiveDimensionLT_X₃_iff`. -/
theorem projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one
    (hS : S.ShortExact) [Projective S.X₂] (hpd : HasProjectiveDimensionLE S.X₃ 1) :
    Projective S.X₁ := by
  -- We rewrite projectivity of `X₁` as projective dimension `≤ 0`.
  rw [projective_iff_hasProjectiveDimensionLE_zero]
  -- The short-exact owner theorem shifts the projective-dimension bound from `X₃` to `X₁`.
  simpa [HasProjectiveDimensionLE] using
    (hS.hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp (by
      simpa [HasProjectiveDimensionLE] using hpd)

end

end ShortExact
end ShortComplex
end CategoryTheory

section

variable {R : Type v} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.109.3: categorical projectivity of `ModuleCat.of R P` gives the usual
module-theoretic projectivity of `P`. -/
lemma module_projective_of_categorical_projective
    {P : Type v} [AddCommGroup P] [Module R P]
    (hP : Projective (ModuleCat.of R P)) :
    Module.Projective R P := by
  -- We convert categorical factorisations through epis into lifts through surjective linear maps.
  let _ : Small.{v} R := small_self R
  refine Module.Projective.of_lifting_property ?_
  intro A B _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of R P) := hP
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.109.3: the first syzygy of a surjection from a projective module lowers
the projective-dimension bound by one. -/
lemma hasProjectiveDimensionLE_first_syzygy_of_surjective
    {F₀ : Type v} [AddCommGroup F₀] [Module R F₀]
    (π : F₀ →ₗ[R] M) (hπ : Function.Surjective π)
    [Module.Projective R F₀] {n : ℕ}
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) n := by
  let S : ShortComplex (ModuleCat.{v} R) := LinearMap.shortComplexKer π
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
  -- The owner theorem equates the shifted bounds on the cokernel and the kernel.
  simpa [S, HasProjectiveDimensionLE] using
    (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp (by
      simpa [HasProjectiveDimensionLE] using hpd)

/-- Lemma 10.109.3 (1): if `F₀ ⟶ M ⟶ 0` is exact with `F₀` projective and `M` has projective
dimension at most `1`, then `ker(F₀ ⟶ M)` is projective. This is the `e = 0` case of the
textbook lemma, phrased in terms of the equivalent upper-bound condition on projective
dimension. The raw-kernel formulation is the bridge obtained from the owner theorem
`CategoryTheory.ShortComplex.ShortExact.projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one`
by applying it to `LinearMap.shortComplexKer π`. -/
-- Proof sketch: package `π` as the short exact complex
-- `0 ⟶ ker π ⟶ F₀ ⟶ M ⟶ 0`, apply the owner theorem in
-- `CategoryTheory.ShortComplex.ShortExact`, and then identify the left term with the module
-- `LinearMap.ker π`.
theorem projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
    {F₀ : Type v}
    [AddCommGroup F₀] [Module R F₀]
    (π : F₀ →ₗ[R] M) (hπ : Function.Surjective π)
    [Module.Projective R F₀]
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) 1) :
    Module.Projective R (LinearMap.ker π) := by
  have hproj_cat : Projective (ModuleCat.of R (LinearMap.ker π)) := by
    -- We package `π` into the canonical short exact sequence
    -- `0 ⟶ ker π ⟶ F₀ ⟶ M ⟶ 0`.
    simpa [LinearMap.shortComplexKer] using
      CategoryTheory.ShortComplex.ShortExact.projective_X₁_of_projective_X₂_of_hasProjectiveDimensionLE_one
        (R := R) (S := LinearMap.shortComplexKer π)
        (LinearMap.shortExact_shortComplexKer hπ) hpd
  -- Finally we translate categorical projectivity back to the module-theoretic statement.
  exact module_projective_of_categorical_projective (R := R) hproj_cat

/-- Lemma 10.109.3 (2): if
`F_{e+1} ⟶ F_e ⟶ ⋯ ⟶ F₀ ⟶ M ⟶ 0`
is exact, every `Fᵢ` is projective, and `M` has projective dimension at most `e + 1`, then the
kernel of the top differential `F_{e+1} ⟶ F_e` is projective. This is the canonical upper-bound
reformulation of the textbook hypothesis `e ≥ d - 1` when `M` has projective dimension `d`. -/
-- Proof sketch: prove the statement by induction on `e`. The case `e = 0` is part (1). For the
-- inductive step, replace `M` by the first syzygy `ker(F₀ ⟶ M)`, use the canonical short-exact
-- projective-dimension shift to see that this syzygy has projective dimension at most `e`, and
-- then apply the induction hypothesis to the truncated exact projective sequence.
theorem projective_top_kernel_of_exact_of_hasProjectiveDimensionLE
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module.Projective R (F i)]
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[R] F i.castSucc)
    (π : F 0 →ₗ[R] M)
    (hπ : Function.Surjective π)
    (h_exact₀ : Function.Exact (d 0) π)
    (h_exact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hpd : HasProjectiveDimensionLE (ModuleCat.of R M) (e + 1)) :
    Module.Projective R (LinearMap.ker (d (Fin.last e))) := by
  induction e generalizing M with
  | zero =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- Exactness at `F₀` gives `π ∘ d₀ = 0`, so `d₀` lands in `ker π`.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[R] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- Exactness identifies `ker π` with the image of `d₀`.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hkerπ_proj : Module.Projective R (LinearMap.ker π) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := M) π hπ hpd
      have hpd_kerπ : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 0 := by
        let _ : Module.Projective R (LinearMap.ker π) := hkerπ_proj
        -- A projective first syzygy has projective dimension `≤ 0`.
        rw [← CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero]
        infer_instance
      let _ : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 0 := hpd_kerπ
      -- We apply the `e = 0` kernel criterion once more to the surjection onto `ker π`.
      have hprojκ : Module.Projective R (LinearMap.ker κ) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := LinearMap.ker π) κ hκ_surj
          (inferInstance : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) 1)
      exact hκ_ker ▸ hprojκ
  | succ e ih =>
      have hκ_mem : ∀ x, d 0 x ∈ LinearMap.ker π := by
        intro x
        -- Exactness at `F₀` again produces the codomain restriction to the first syzygy.
        simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
          LinearMap.congr_fun h_exact₀.linearMap_comp_eq_zero x
      let κ : F 1 →ₗ[R] LinearMap.ker π :=
        LinearMap.codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_ker : LinearMap.ker κ = LinearMap.ker (d 0) := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π) (d 0) hκ_mem
      have hκ_surj : Function.Surjective κ := by
        intro x
        -- The first syzygy is the image of `d₀`.
        rcases (h_exact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_exact : Function.Exact (d 1) κ := by
        -- The codomain restriction preserves the kernel, so the exactness equality is unchanged.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (h_exact 0).linearMap_ker_eq
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π)) (e + 1) :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M) (π := π) hπ hpd
      let F' : Fin (e + 2) → Type v := fun i => F i.succ
      let d' : (i : Fin (e + 1)) → F' i.succ →ₗ[R] F' i.castSucc := fun i => d i.succ
      have h_exact' : ∀ i : Fin e, Function.Exact (d' i.succ) (d' i.castSucc) := by
        intro i
        -- The truncated complex inherits exactness from the original sequence.
        simpa [d'] using h_exact i.succ
      -- Induction on the truncated exact projective resolution finishes the higher-syzygy case.
      simpa [F', d'] using
        ih (M := LinearMap.ker π) (F := F') (d := d') (π := κ) hκ_surj hκ_exact h_exact' hpd'

end

/-! ### Lemma_10_109_4 (from Chap10) -/
universe u v

open CategoryTheory

section

variable {R : Type v} [Ring R]

/-
Domain-style sampling:
* primary domain: projective dimension in `ModuleCat R`, together with projective resolutions and
  source-facing bounded exact sequences.
* inspected owner declarations:
  `CategoryTheory.ProjectiveResolution`,
  `CategoryTheory.projectiveResolution`,
  `CategoryTheory.HasProjectiveDimensionLE`,
  `CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero`,
  `CategoryTheory.ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`.
* best owner abstraction: `P : ProjectiveResolution M` for `M : ModuleCat R`.
* layer triage:
  `ProjectiveResolution.SyzygyProjective` is `core/canonical`,
  `HasFiniteProjectiveResolutionLengthLE` is `source-facing`,
  the TFAE below is a `bridge/view` between them and `HasProjectiveDimensionLE`.
* primitive data: the owner object `P : ProjectiveResolution M`.
* derived API: projectivity of the `d`th syzygy and the bounded finite-sequence reformulation of
  `HasProjectiveDimensionLE`.
-/

namespace CategoryTheory.ProjectiveResolution

variable {M : ModuleCat.{v} R}

/-- The textbook syzygy condition attached to a projective resolution in degree `d`. For `d = 0`
this says that `M` is projective, for `d = 1` it says that `ker(P₀ ⟶ M)` is projective, and for
`d ≥ 2` it says that `ker(P_{d-1} ⟶ P_{d-2})` is projective. -/
def SyzygyProjective (P : ProjectiveResolution M) (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | 1 => Projective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom))
  | n + 2 => Projective (ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom))

-- Proof sketch: unfold `SyzygyProjective` and read off the `d = 0` branch.
/-- In degree `0`, the syzygy-projective condition is exactly projectivity of `M`. -/
theorem syzygyProjective_zero_iff (P : ProjectiveResolution M) :
    P.SyzygyProjective 0 ↔ Projective M :=
  Iff.rfl

end CategoryTheory.ProjectiveResolution

variable (M : ModuleCat.{v} R)

/-- `M` admits a finite projective resolution of length at most `d`. For `d = 0` this means that
`M` itself is projective; for `d = n + 1` it is an exact sequence
`0 ⟶ P_{n+1} ⟶ P_n ⟶ ⋯ ⟶ P₀ ⟶ M ⟶ 0`
with every `Pᵢ` projective. -/
def HasFiniteProjectiveResolutionLengthLE (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → ModuleCat.{v} R),
        (∀ i, Projective (P i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
            (π : P 0 ⟶ M),
            Function.Surjective π ∧
              Function.Exact (δ 0) π ∧
              (∀ i : Fin n, Function.Exact (δ i.succ) (δ i.castSucc)) ∧
              Function.Injective (δ (Fin.last n))

-- Proof sketch: unfold `HasFiniteProjectiveResolutionLengthLE`; the `d = 0` branch is defined to
-- be projectivity of `M`.
/-- A finite projective resolution of length at most `0` is exactly projectivity of `M`. -/
theorem hasFiniteProjectiveResolutionLengthLE_zero_iff :
    HasFiniteProjectiveResolutionLengthLE M 0 ↔ Projective M :=
  Iff.rfl

/-- Helper for Lemma 10.109.4: a finite projective resolution of positive length starts with a
projective presentation whose kernel still has a finite projective resolution of one shorter
length. -/
theorem exists_projective_presentation_with_finite_kernel_resolution {n : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLE M (n + 1)) :
    ∃ (P₀ : ModuleCat.{v} R) (π : P₀ ⟶ M),
      Projective P₀ ∧
        Function.Surjective π ∧
          HasFiniteProjectiveResolutionLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n := by
  cases n with
  | zero =>
      rcases hM with ⟨P, hP, δ, π, hπ, hExact, _, hInj⟩
      refine ⟨P 0, π, hP 0, hπ, ?_⟩
      let κ : P 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          -- Exactness at `P₀` identifies the image of `δ₀` with `ker π`.
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact.linearMap_comp_eq_zero x))
      have hκ_surj : Function.Surjective κ := by
        intro x
        rcases (hExact x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_inj : Function.Injective κ := by
        intro x y hxy
        exact hInj (by simpa [κ] using congrArg Subtype.val hxy)
      let e : P 1 ≅ ModuleCat.of R (LinearMap.ker π.hom) :=
        (LinearEquiv.ofBijective κ.hom ⟨hκ_inj, hκ_surj⟩).toModuleIso
      -- The leftmost projective module is isomorphic to the kernel, so the kernel is projective.
      simpa [HasFiniteProjectiveResolutionLengthLE] using Projective.of_iso e (hP (Fin.last 1))
  | succ n =>
      rcases hM with ⟨P, hP, δ, π, hπ, hExact₀, hExact, hInj⟩
      refine ⟨P 0, π, hP 0, hπ, ?_⟩
      let κ : P 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          -- Exactness at `P₀` shows that `δ₀` factors through `ker π`.
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x))
      have hκ_surj : Function.Surjective κ := by
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom (fun x ↦ by
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
            LinearMap.congr_fun hExact₀.linearMap_comp_eq_zero x)
      let P' : Fin (n + 2) → ModuleCat.{v} R := fun i ↦ P i.succ
      let δ' : (i : Fin (n + 1)) → P' i.succ ⟶ P' i.castSucc := fun i ↦ δ i.succ
      refine ⟨P', ?_, δ', κ, hκ_surj, ?_, ?_, ?_⟩
      · intro i
        -- The truncated family inherits projectivity degreewise.
        exact hP i.succ
      · -- Exactness of `δ₁` against the restricted presentation map is the shifted first exactness.
        exact LinearMap.exact_iff.mpr <| hκ_ker.trans (hExact 0).linearMap_ker_eq
      · intro i
        -- Every later exactness statement is inherited verbatim from the original sequence.
        simpa [δ', Fin.castSucc_succ] using hExact i.succ
      · -- The top differential of the truncated finite resolution is the original top differential.
        simpa [δ'] using hInj

/-- Helper for Lemma 10.109.4: a finite projective resolution of length at most `d` gives the
owner-level projective-dimension bound `HasProjectiveDimensionLE M d`. -/
theorem hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE {d : ℕ}
    (hM : HasFiniteProjectiveResolutionLengthLE M d) :
    HasProjectiveDimensionLE M d := by
  induction d generalizing M with
  | zero =>
      -- The base case is exactly the characterization of projectivity.
      rw [hasFiniteProjectiveResolutionLengthLE_zero_iff] at hM
      exact (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).1 hM
  | succ d ih =>
      rcases exists_projective_presentation_with_finite_kernel_resolution (M := M) hM with
        ⟨P₀, π, hP₀, hπ, hker⟩
      have hker_pd :
          HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) d :=
        ih (M := ModuleCat.of R (LinearMap.ker π.hom)) hker
      let S : ShortComplex (ModuleCat.{v} R) := LinearMap.shortComplexKer π.hom
      have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hπ
      -- The short exact sequence `0 → ker π → P₀ → M → 0` raises the bound by one.
      simpa [S, HasProjectiveDimensionLE] using
        (hS.hasProjectiveDimensionLT_X₃_iff d hP₀).mpr (by
          simpa [HasProjectiveDimensionLE] using hker_pd)

/-- Helper for Lemma 10.109.4: an exact pair of linear maps factors through the kernel of the
second map. -/
theorem linearMap_mem_ker_of_exact {A B C : Type v}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (hExact : Function.Exact f g) :
    ∀ x, f x ∈ LinearMap.ker g := by
  -- Exactness says `g ∘ f = 0`, so every value of `f` lands in `ker g`.
  intro x
  simpa [LinearMap.mem_ker, LinearMap.comp_apply] using
    LinearMap.congr_fun hExact.linearMap_comp_eq_zero x

/-- Helper for Lemma 10.109.4: the first differential of a projective resolution is exact against
the augmentation map as a pair of linear maps. -/
theorem projectiveResolution_exact_zero_linearMap
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) :
    Function.Exact (P.complex.d 1 0).hom (P.π.f 0).hom := by
  -- We translate the categorical exactness statement into the linear-map exactness used below.
  simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀

/-- Helper for Lemma 10.109.4: consecutive differentials in a projective resolution are exact as
linear maps. -/
theorem projectiveResolution_exact_succ_linearMap
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) (n : ℕ) :
    Function.Exact (P.complex.d (n + 2) (n + 1)).hom (P.complex.d (n + 1) n).hom := by
  -- Again we pass from the categorical exactness owner theorem to the linear-map formulation.
  simpa using (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ n)

/-- Helper for Lemma 10.109.4: if a projective presentation has kernel with a finite projective
resolution of length at most `n`, then the target has one of length at most `n + 1`. -/
theorem hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
    {P₀ : ModuleCat.{v} R} (π : P₀ ⟶ M) (hP₀ : Projective P₀)
    (hπ : Function.Surjective π.hom) {n : ℕ}
    (hker : HasFiniteProjectiveResolutionLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n) :
    HasFiniteProjectiveResolutionLengthLE M (n + 1) := by
  cases n with
  | zero =>
      rw [hasFiniteProjectiveResolutionLengthLE_zero_iff] at hker
      let κ : ModuleCat.of R (LinearMap.ker π.hom) ⟶ P₀ :=
        ModuleCat.ofHom (LinearMap.ker π.hom).subtype
      -- The length-one case is the defining short exact sequence `0 → ker π → P₀ → M → 0`.
      refine ⟨Fin.cons P₀ (fun _ : Fin 1 ↦ ModuleCat.of R (LinearMap.ker π.hom)), ?_,
        Fin.cases κ (fun i : Fin 0 ↦ Fin.elim0 i), π,
        hπ, ?_, ?_, ?_⟩
      · intro i
        fin_cases i
        · simpa using hP₀
        · simpa using hker
      · simpa [κ] using LinearMap.exact_subtype_ker_map π.hom
      · intro i
        exact Fin.elim0 i
      · exact Submodule.injective_subtype (LinearMap.ker π.hom)
  | succ n =>
      rcases hker with ⟨P, hP, δ, πK, hπK, hExact₀, hExact, hInj⟩
      let κ : P 0 ⟶ P₀ := πK ≫ ModuleCat.ofHom (LinearMap.ker π.hom).subtype
      let P' : Fin (n + 3) → ModuleCat.{v} R := Fin.cons P₀ P
      let δ' : (i : Fin (n + 2)) → P' i.succ ⟶ P' i.castSucc :=
        Fin.cases κ fun i ↦ δ i
      -- We prepend `P₀ ⟶ M` to the finite resolution of `ker π`.
      refine ⟨P', ?_, δ', π, hπ, ?_, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
            simpa [P'] using hP₀
        | succ i =>
            simpa [P'] using hP i
      · -- Surjectivity of `πK` identifies the image of `κ` with `ker π`.
        have hκ_exact :
            Function.Exact ((LinearMap.ker π.hom).subtype.comp πK.hom) π.hom :=
          (Function.Surjective.comp_exact_iff_exact
            (f := (LinearMap.ker π.hom).subtype) (g := π.hom) hπK).2
            (LinearMap.exact_subtype_ker_map π.hom)
        simpa [κ] using hκ_exact
      · intro i
        cases i using Fin.cases with
        | zero =>
            -- The next exactness statement is unchanged because the subtype map is injective.
            have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
              Submodule.injective_subtype (LinearMap.ker π.hom)
            have hExact₀' :
                Function.Exact (δ 0).hom ((LinearMap.ker π.hom).subtype.comp πK.hom) :=
              (Function.Injective.comp_exact_iff_exact
                (f := (δ 0).hom) (g := πK.hom) hsub_inj).2 hExact₀
            simpa [δ', κ] using hExact₀'
        | succ i =>
            -- Farther to the left, the exactness statements are inherited verbatim.
            simpa [δ'] using hExact i
      · -- The top differential is unchanged when we prepend a new degree-zero term.
        simpa [δ'] using hInj

/-- Helper for Lemma 10.109.4: in an exact sequence
`F_{e+1} → ⋯ → F₀ → M → 0` of projective modules, a bound
`HasProjectiveDimensionLE M (e + 2)` forces the kernel of the top differential to be projective. -/
theorem projective_top_kernel_of_shifted_exact_of_hasProjectiveDimensionLE
    {e : ℕ} {M' : ModuleCat.{v} R}
    {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M')
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (hpd : HasProjectiveDimensionLE M' (e + 2)) :
    Projective (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom)) := by
  induction e generalizing M' with
  | zero =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      let _ : Module.Projective R (F 0) :=
        module_projective_of_categorical_projective (R := R) (P := F 0) (hF 0)
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) 1 :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M') (π := π.hom) hπ hpd
      let _ : Module.Projective R (F 1) :=
        module_projective_of_categorical_projective (R := R) (P := F 1) (hF 1)
      have hprojκ : Module.Projective R (LinearMap.ker κ.hom) :=
        projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
          (R := R) (M := LinearMap.ker π.hom) κ.hom hκ_surj hpd'
      let _ : Module.Projective R (LinearMap.ker (δ 0).hom) := hκ_ker ▸ hprojκ
      -- The kernel of `κ` is the same top kernel as the original two-step exact sequence.
      simpa using
        (show Projective (ModuleCat.of R (LinearMap.ker (δ 0).hom)) from inferInstance)
  | succ e ih =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies the first syzygy with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_exact : Function.Exact (δ 1).hom κ.hom := by
        -- Restricting the codomain to `ker π` preserves exactness because the subtype map
        -- is injective.
        have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
          Submodule.injective_subtype (LinearMap.ker π.hom)
        have hExact₁ :
            Function.Exact (δ 1).hom ((LinearMap.ker π.hom).subtype.comp κ.hom) := by
          simpa [κ] using hExact 0
        exact (Function.Injective.comp_exact_iff_exact
          (f := (δ 1).hom) (g := κ.hom) hsub_inj).1 hExact₁
      let _ : Module.Projective R (F 0) :=
        module_projective_of_categorical_projective (R := R) (P := F 0) (hF 0)
      have hpd' : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker π.hom)) (e + 2) :=
        hasProjectiveDimensionLE_first_syzygy_of_surjective
          (R := R) (M := M') (π := π.hom) hπ hpd
      let F' : Fin (e + 2) → ModuleCat.{v} R := fun i ↦ F i.succ
      let δ' : (i : Fin (e + 1)) → F' i.succ ⟶ F' i.castSucc := fun i ↦ δ i.succ
      have hExact' : ∀ i : Fin e, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        simpa [δ'] using hExact i.succ
      -- Route correction: instead of calling Lemma `10.109.3` at the original indexing, we
      -- shift once to `ker π` and recurse on the truncated exact sequence.
      simpa [δ', Fin.succ_last] using
        ih (M' := ModuleCat.of R (LinearMap.ker π.hom))
          (F := F') (hF := fun i ↦ hF i.succ) (δ := δ') (π := κ)
          hκ_surj hκ_exact hExact' hpd'

/-- Helper for Lemma 10.109.4: if the top kernel in an exact sequence of projectives is
projective, then truncating there gives a finite projective resolution. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_shifted_exact_of_projective_top_kernel
    {e : ℕ} {M' : ModuleCat.{v} R}
    {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M')
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (htop : Projective (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom))) :
    HasFiniteProjectiveResolutionLengthLE M' (e + 2) := by
  induction e generalizing M' with
  | zero =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` identifies `ker π` with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hker : HasFiniteProjectiveResolutionLengthLE
          (ModuleCat.of R (LinearMap.ker π.hom)) 1 := by
        have htop' : Projective (ModuleCat.of R (LinearMap.ker κ.hom)) := by
          exact hκ_ker.symm ▸ htop
        have hker₀ : HasFiniteProjectiveResolutionLengthLE
            (ModuleCat.of R (LinearMap.ker κ.hom)) 0 := by
          simpa [hasFiniteProjectiveResolutionLengthLE_zero_iff] using htop'
        -- The first syzygy has a projective presentation with projective kernel `ker δ₀`.
        exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
          (M := ModuleCat.of R (LinearMap.ker π.hom)) κ (hF 1) hκ_surj hker₀
      -- Prepending `F₀ ⟶ M` gives a finite resolution of `M`.
      exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
        (M := M') π (hF 0) hπ hker
  | succ e ih =>
      let κ : F 1 ⟶ ModuleCat.of R (LinearMap.ker π.hom) :=
        ModuleCat.ofHom <|
          LinearMap.codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_surj : Function.Surjective κ.hom := by
        -- Exactness at `F₀` again identifies the first syzygy with the image of `δ₀`.
        intro x
        rcases (hExact₀ x.1).mp x.2 with ⟨y, hy⟩
        refine ⟨y, Subtype.ext ?_⟩
        simpa [κ] using hy
      have hκ_ker : LinearMap.ker κ.hom = LinearMap.ker (δ 0).hom := by
        simpa [κ] using
          LinearMap.ker_codRestrict (LinearMap.ker π.hom) (δ 0).hom
            (linearMap_mem_ker_of_exact (R := R) hExact₀)
      have hκ_exact : Function.Exact (δ 1).hom κ.hom := by
        -- Restricting the codomain to `ker π` preserves exactness because the subtype map
        -- is injective.
        have hsub_inj : Function.Injective (LinearMap.ker π.hom).subtype :=
          Submodule.injective_subtype (LinearMap.ker π.hom)
        have hExact₁ :
            Function.Exact (δ 1).hom ((LinearMap.ker π.hom).subtype.comp κ.hom) := by
          simpa [κ] using hExact 0
        exact (Function.Injective.comp_exact_iff_exact
          (f := (δ 1).hom) (g := κ.hom) hsub_inj).1 hExact₁
      let F' : Fin (e + 2) → ModuleCat.{v} R := fun i ↦ F i.succ
      let δ' : (i : Fin (e + 1)) → F' i.succ ⟶ F' i.castSucc := fun i ↦ δ i.succ
      have hExact' : ∀ i : Fin e, Function.Exact (δ' i.succ).hom (δ' i.castSucc).hom := by
        intro i
        simpa [δ'] using hExact i.succ
      have hker : HasFiniteProjectiveResolutionLengthLE
          (ModuleCat.of R (LinearMap.ker π.hom)) (e + 2) := by
        -- After shifting to the first syzygy, the top kernel is unchanged.
        simpa [δ', Fin.succ_last] using
          ih (M' := ModuleCat.of R (LinearMap.ker π.hom))
            (F := F') (hF := fun i ↦ hF i.succ) (δ := δ') (π := κ)
            hκ_surj hκ_exact hExact' htop
      -- One more projective presentation step recovers a finite resolution of `M`.
      exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
        (M := M') π (hF 0) hπ hker

namespace CategoryTheory.ProjectiveResolution

/-- Helper for Lemma 10.109.4: once `M` has projective dimension at most `d`, every projective
resolution of `M` has projective `d`th syzygy. -/
theorem syzygyProjective_of_hasProjectiveDimensionLE (P : ProjectiveResolution M) {d : ℕ}
    (hpd : HasProjectiveDimensionLE M d) :
    P.SyzygyProjective d := by
  cases d with
  | zero =>
      -- In degree `0`, the syzygy condition is exactly projectivity of `M`.
      simpa [SyzygyProjective] using
        (CategoryTheory.projective_iff_hasProjectiveDimensionLE_zero M).2 hpd
  | succ d =>
      cases d with
      | zero =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          let _ : Module.Projective R (P.complex.X 0) :=
            module_projective_of_categorical_projective
              (R := R) (P := P.complex.X 0) (P.projective 0)
          -- The degree-one clause is the first-syzygy case of Lemma `10.109.3`.
          let _ : Module.Projective R (LinearMap.ker (P.π.f 0).hom) :=
            projective_ker_of_surjective_of_hasProjectiveDimensionLE_one
              (R := R) (M := M) (P.π.f 0).hom hπ hpd
          simpa [SyzygyProjective] using
            (show Projective (ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)) from inferInstance)
      | succ n =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- Route correction: the higher-degree clause is proved on the shifted exact prefix,
          -- not by applying Lemma `10.109.3` directly at the original indexing.
          simpa [SyzygyProjective] using
            projective_top_kernel_of_shifted_exact_of_hasProjectiveDimensionLE
              (R := R) (M' := M) (F := fun i ↦ P.complex.X i)
              (hF := fun i ↦ P.projective i)
              (δ := fun i ↦ P.complex.d i.succ i.castSucc)
              (π := P.π.f 0) hπ
              (projectiveResolution_exact_zero_linearMap (R := R) P)
              (fun i ↦ by
                simpa using projectiveResolution_exact_succ_linearMap (R := R) P (i : ℕ))
              hpd

/-- Helper for Lemma 10.109.4: if a projective resolution has projective `d`th syzygy, then its
first `d + 1` terms already form a finite projective resolution of length at most `d`. -/
theorem hasFiniteProjectiveResolutionLengthLE_of_syzygyProjective (P : ProjectiveResolution M)
    {d : ℕ} (hP : P.SyzygyProjective d) :
    HasFiniteProjectiveResolutionLengthLE M d := by
  cases d with
  | zero =>
      -- In degree `0`, both predicates are the same projectivity condition.
      simpa [SyzygyProjective, HasFiniteProjectiveResolutionLengthLE] using hP
  | succ d =>
      cases d with
      | zero =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- The degree-one clause is the defining short exact sequence `0 → ker π → P₀ → M → 0`.
          exact hasFiniteProjectiveResolutionLengthLE_succ_of_projective_presentation
            (M := M) (P.π.f 0) (P.projective 0) hπ hP
      | succ n =>
          have hπ : Function.Surjective (P.π.f 0).hom :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          -- Truncating at the projective top kernel gives the required finite resolution.
          exact hasFiniteProjectiveResolutionLengthLE_of_shifted_exact_of_projective_top_kernel
            (R := R) (M' := M) (F := fun i ↦ P.complex.X i)
            (hF := fun i ↦ P.projective i)
            (δ := fun i ↦ P.complex.d i.succ i.castSucc)
            (π := P.π.f 0) hπ
            (projectiveResolution_exact_zero_linearMap (R := R) P)
            (fun i ↦ by
              simpa using projectiveResolution_exact_succ_linearMap (R := R) P (i : ℕ))
            (by simpa [SyzygyProjective] using hP)

end CategoryTheory.ProjectiveResolution

/-- Lemma 10.109.4: the condition that `M` has projective dimension at most `d` is equivalent to
the existence of a finite projective resolution of length at most `d`, to the existence of some
projective resolution whose `d`th syzygy is projective, and to the assertion that every projective
resolution has projective `d`th syzygy. -/
-- Proof sketch: `(1) ↔ (2)` is the textbook definition of projective dimension. `(2) → (4)` is
-- the syzygy-projectivity criterion of Lemma `10.109.3`, `(4) → (3)` is immediate, and `(3) → (2)`
-- follows by truncating a projective resolution once the `d`th syzygy is projective.
theorem projectiveDimensionLE_tfae_resolution_conditions (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE M d,
        HasFiniteProjectiveResolutionLengthLE M d,
        ∃ P : ProjectiveResolution M, P.SyzygyProjective d,
        ∀ P : ProjectiveResolution M, P.SyzygyProjective d ] := by
  -- The textbook cycle is `(1) → (4) → (3) → (2) → (1)`.
  tfae_have 1 → 4 := by
    intro hpd
    change ∀ Q : ProjectiveResolution M, Q.SyzygyProjective d
    intro Q
    exact CategoryTheory.ProjectiveResolution.syzygyProjective_of_hasProjectiveDimensionLE
      (R := R) (M := M) (P := Q) hpd
  tfae_have 4 → 3 := by
    intro h
    refine ⟨CategoryTheory.projectiveResolution M, h _⟩
  tfae_have 3 → 2 := by
    rintro ⟨Q, hQ⟩
    exact CategoryTheory.ProjectiveResolution.hasFiniteProjectiveResolutionLengthLE_of_syzygyProjective
      (R := R) (M := M) (P := Q) hQ
  tfae_have 2 → 1 := by
    intro h
    exact hasProjectiveDimensionLE_of_hasFiniteProjectiveResolutionLengthLE (M := M) h
  tfae_finish

end
