import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Limits

universe w v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {A B : C}

/- Definition 12.6.2 has three layers:
- source-facing: extensions of `B` by `A` modulo isomorphisms that fix the endpoints;
- core/canonical: the owner object `Ext B A 1`;
- bridge/view: the canonical map sending a source-facing extension class to its degree-one
  `Ext` class. -/
namespace CategoryTheory
namespace Extension

variable {S T U : Extension A B}

/-- Two source-facing extensions are isomorphic when the induced morphisms on the fixed endpoints
`A` and `B` are the identities. Since the endpoints are fixed, the primitive source-facing data is
an isomorphism of middle terms compatible with the structure maps; the ambient short-complex
isomorphism is a derived bridge to the owner `Ext` API. -/
def Isomorphic (S T : Extension A B) : Prop :=
  ∃ e : S.E ≅ T.E, S.f ≫ e.hom = T.f ∧ e.hom ≫ T.g = S.g

theorem Isomorphic.refl (S : Extension A B) : Isomorphic S S := by
  refine ⟨Iso.refl S.E, ?_, ?_⟩ <;> simp

theorem Isomorphic.symm (h : Isomorphic S T) : Isomorphic T S := by
  rcases h with ⟨e, hf, hg⟩
  refine ⟨e.symm, ?_, ?_⟩
  · have hf' := congrArg (fun k ↦ k ≫ e.inv) hf
    simpa [Category.assoc] using hf'.symm
  · have hg' := congrArg (fun k ↦ e.inv ≫ k) hg
    simpa [Category.assoc] using hg'.symm

theorem Isomorphic.trans (hST : Isomorphic S T) (hTU : Isomorphic T U) : Isomorphic S U := by
  rcases hST with ⟨eST, hfST, hgST⟩
  rcases hTU with ⟨eTU, hfTU, hgTU⟩
  refine ⟨eST.trans eTU, ?_, ?_⟩
  · calc
      S.f ≫ (eST.trans eTU).hom = (S.f ≫ eST.hom) ≫ eTU.hom := by
        simp [Iso.trans_hom]
      _ = T.f ≫ eTU.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eTU.hom) hfST
      _ = U.f := hfTU
  · calc
      (eST.trans eTU).hom ≫ U.g = eST.hom ≫ (eTU.hom ≫ U.g) := by
        simp [Iso.trans_hom, Category.assoc]
      _ = eST.hom ≫ T.g := by rw [hgTU]
      _ = S.g := hgST

/-- The canonical equivalence relation on source-facing extensions used to form extension classes. -/
private def setoid : Setoid (Extension A B) where
  r := Isomorphic
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

end Extension

/-- Source-facing extension classes for Definition 12.6.2 are extensions modulo endpoint-fixing
isomorphism. -/
@[stacks 010K]
abbrev ExtensionClass (A B : C) :=
  _root_.Quotient (show Setoid (Extension A B) from Extension.setoid)

namespace ExtensionClass

/-- Endpoint-fixing isomorphic source-facing extensions determine the same extension class. -/
theorem mk_eq_mk_of_isomorphic {S T : Extension A B} (h : Extension.Isomorphic S T) :
    (⟦S⟧ : ExtensionClass A B) = ⟦T⟧ :=
  show _root_.Quotient.mk (show Setoid (Extension A B) from Extension.setoid) S =
      _root_.Quotient.mk (show Setoid (Extension A B) from Extension.setoid) T from
    _root_.Quotient.sound h

end ExtensionClass

end CategoryTheory

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace CategoryTheory
namespace Extension

section Operations

variable {S T : Extension A B}
variable {A' B' : C}

/-- Helper for Definition 12.6.2: the canonical map `A ⟶ pullback u S.g` is defined because the
left square commutes. -/
private lemma pullbackInclusion_condition (u : B' ⟶ B) (S : Extension A B) :
    (0 : A ⟶ B') ≫ u = S.f ≫ S.g := by
  simp [S.zero]

/-- Helper for Definition 12.6.2: the canonical map `A ⟶ pullback u S.g` used in the pullback
extension. -/
noncomputable def pullbackInclusion (u : B' ⟶ B) (S : Extension A B) :
    A ⟶ Limits.pullback u S.g :=
  Limits.pullback.lift 0 S.f (pullbackInclusion_condition u S)

/-- Helper for Definition 12.6.2: the canonical pullback inclusion composes trivially with the
pullback projection to `B'`. -/
private lemma pullbackInclusion_comp_fst (u : B' ⟶ B) (S : Extension A B) :
    pullbackInclusion u S ≫ Limits.pullback.fst u S.g = 0 := by
  simpa [pullbackInclusion] using
    (Limits.pullback.lift_fst (0 : A ⟶ B') S.f (pullbackInclusion_condition u S))

/-- Helper for Definition 12.6.2: the pullback inclusion remembers the original left map through
the second pullback projection. -/
private lemma pullbackInclusion_comp_snd (u : B' ⟶ B) (S : Extension A B) :
    pullbackInclusion u S ≫ Limits.pullback.snd u S.g = S.f := by
  simpa [pullbackInclusion] using
    (Limits.pullback.lift_snd (0 : A ⟶ B') S.f (pullbackInclusion_condition u S))

/-- Helper for Definition 12.6.2: the pullback inclusion presents `A` as the kernel of the pulled
back quotient map. -/
private noncomputable def pullbackLegIsKernel (u : B' ⟶ B) (S : Extension A B) :
    IsLimit (KernelFork.ofι (pullbackInclusion u S) (pullbackInclusion_comp_fst u S)) :=
  -- The pullback point lies over `S.E`, so exactness of `S` lifts any kernel candidate through
  -- `S.f`, and the pullback universal property then reconstructs the original map.
  by
  haveI : Mono (pullbackInclusion u S) := mono_of_mono_fac (pullbackInclusion_comp_snd u S)
  refine KernelFork.IsLimit.ofι' _ _ ?_
  intro X k hk
  have hk' : (k ≫ Limits.pullback.snd u S.g) ≫ S.g = 0 := by
    calc
      (k ≫ Limits.pullback.snd u S.g) ≫ S.g = (k ≫ Limits.pullback.fst u S.g) ≫ u := by
        simpa [Category.assoc] using
          (congrArg (fun m : Limits.pullback u S.g ⟶ B ↦ k ≫ m)
            (Limits.pullback.condition (f := u) (g := S.g))).symm
      _ = 0 := by simp [hk]
  refine ⟨S.shortExact.exact.lift (k ≫ Limits.pullback.snd u S.g) hk', ?_⟩
  apply Limits.pullback.hom_ext
  · simp [Category.assoc, pullbackInclusion_comp_fst, hk]
  · simpa [Category.assoc, pullbackInclusion_comp_snd] using
      S.shortExact.exact.lift_f (k ≫ Limits.pullback.snd u S.g) hk'

/-- Helper for Definition 12.6.2: the pullback short complex is short exact. -/
private theorem pullbackShortExact (u : B' ⟶ B) (S : Extension A B) :
    (ShortComplex.mk (pullbackInclusion u S) (Limits.pullback.fst u S.g)
      (pullbackInclusion_comp_fst u S)).ShortExact := by
  -- The left map is a kernel, hence exact and mono; the right map is epi in an abelian category.
  have hExactMono :
      (ShortComplex.mk (pullbackInclusion u S) (Limits.pullback.fst u S.g)
        (pullbackInclusion_comp_fst u S)).Exact ∧ Mono (pullbackInclusion u S) :=
    (ShortComplex.exact_and_mono_f_iff_f_is_kernel
      (S := ShortComplex.mk (pullbackInclusion u S) (Limits.pullback.fst u S.g)
        (pullbackInclusion_comp_fst u S))).2 ⟨pullbackLegIsKernel u S⟩
  exact ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 inferInstance

/-- Helper for Definition 12.6.2: the canonical map `pushout a S.f ⟶ B` is defined because the
pushout square commutes with the zero map on `A'`. -/
private lemma pushoutProjection_condition (a : A ⟶ A') (S : Extension A B) :
    a ≫ (0 : A' ⟶ B) = S.f ≫ S.g := by
  simp [S.zero]

/-- Helper for Definition 12.6.2: the canonical projection `pushout a S.f ⟶ B` used in the
pushout extension. -/
noncomputable def pushoutProjection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout a S.f ⟶ B :=
  Limits.pushout.desc (0 : A' ⟶ B) S.g (pushoutProjection_condition a S)

/-- Helper for Definition 12.6.2: the left pushout map composes trivially with the canonical
projection to `B`. -/
private lemma pushoutInl_comp_projection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout.inl a S.f ≫ pushoutProjection a S = 0 := by
  simpa [pushoutProjection] using
    (Limits.pushout.inl_desc (0 : A' ⟶ B) S.g (pushoutProjection_condition a S))

/-- Helper for Definition 12.6.2: the right pushout map remembers the original quotient map. -/
private lemma pushoutInr_comp_projection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout.inr a S.f ≫ pushoutProjection a S = S.g := by
  simpa [pushoutProjection] using
    (Limits.pushout.inr_desc (0 : A' ⟶ B) S.g (pushoutProjection_condition a S))

/-- Helper for Definition 12.6.2: the pushout projection presents `B` as the cokernel of the
left pushout map. -/
private noncomputable def pushoutLegIsCokernel (a : A ⟶ A') (S : Extension A B) :
    IsColimit (CokernelCofork.ofπ (pushoutProjection a S) (pushoutInl_comp_projection a S)) :=
  -- Dually, exactness of `S` descends any cokernel candidate along `S.g`, and the pushout
  -- universal property verifies that the descended map is the unique factorization.
  by
  haveI : Epi (pushoutProjection a S) := epi_of_epi_fac (pushoutInr_comp_projection a S)
  refine CokernelCofork.IsColimit.ofπ' _ _ ?_
  intro X k hk
  have hk' : S.f ≫ (Limits.pushout.inr a S.f ≫ k) = 0 := by
    calc
      S.f ≫ (Limits.pushout.inr a S.f ≫ k) = a ≫ (Limits.pushout.inl a S.f ≫ k) := by
        simpa [Category.assoc] using
          (congrArg (fun m : A ⟶ Limits.pushout a S.f ↦ m ≫ k)
            (Limits.pushout.condition (f := a) (g := S.f))).symm
      _ = 0 := by simp [hk]
  refine ⟨S.shortExact.exact.desc (Limits.pushout.inr a S.f ≫ k) hk', ?_⟩
  apply Limits.pushout.hom_ext
  · rw [← Category.assoc, pushoutInl_comp_projection, Limits.zero_comp, hk]
  · rw [← Category.assoc, pushoutInr_comp_projection]
    simpa [Category.assoc] using
      S.shortExact.exact.g_desc (Limits.pushout.inr a S.f ≫ k) hk'

/-- Helper for Definition 12.6.2: the pushout short complex is short exact. -/
private theorem pushoutShortExact (a : A ⟶ A') (S : Extension A B) :
    (ShortComplex.mk (Limits.pushout.inl a S.f) (pushoutProjection a S)
      (pushoutInl_comp_projection a S)).ShortExact := by
  -- The right map is a cokernel, hence exact and epi; the left map is mono in an abelian category.
  have hExactEpi :
      (ShortComplex.mk (Limits.pushout.inl a S.f) (pushoutProjection a S)
        (pushoutInl_comp_projection a S)).Exact ∧ Epi (pushoutProjection a S) :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (S := ShortComplex.mk (Limits.pushout.inl a S.f) (pushoutProjection a S)
        (pushoutInl_comp_projection a S))).2 ⟨pushoutLegIsCokernel a S⟩
  exact ShortComplex.ShortExact.mk' hExactEpi.1 inferInstance hExactEpi.2

/-- Helper for Definition 12.6.2: the standard split extension has zero composite. -/
private lemma split_zero (A B : C) :
    (biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B) = 0 := by
  simp

/-- Helper for Definition 12.6.2: the standard biproduct extension is short exact. -/
private noncomputable def splitShortExact (A B : C) :
    (ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B)
      (split_zero A B)).ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact

/-- Helper for Definition 12.6.2: the biproduct extension has zero composite. -/
private lemma biprodExtension_zero (S T : Extension A B) :
    biprod.map S.f T.f ≫ biprod.map S.g T.g = 0 := by
  ext <;> simp [Category.assoc, S.zero, T.zero]

/-- Helper for Definition 12.6.2: the biproduct of two extensions is again short exact. -/
private noncomputable def biprodExtensionLegIsKernel (S T : Extension A B) :
    IsLimit (KernelFork.ofι (biprod.map S.f T.f) (biprodExtension_zero S T)) :=
  -- Each component of a kernel candidate lands in the corresponding exact row, so the two lifts
  -- combine into the desired universal morphism into the biproduct of kernels.
  by
  refine KernelFork.IsLimit.ofι' _ _ ?_
  intro X k hk
  have hkS : (k ≫ biprod.fst) ≫ S.g = 0 := by
    have hk' := congrArg (fun m : X ⟶ B ⊞ B ↦ m ≫ biprod.fst) hk
    simpa [Category.assoc] using hk'
  have hkT : (k ≫ biprod.snd) ≫ T.g = 0 := by
    have hk' := congrArg (fun m : X ⟶ B ⊞ B ↦ m ≫ biprod.snd) hk
    simpa [Category.assoc] using hk'
  refine ⟨biprod.lift
      (S.shortExact.exact.lift (k ≫ biprod.fst) hkS)
      (T.shortExact.exact.lift (k ≫ biprod.snd) hkT), ?_⟩
  apply biprod.hom_ext
  · simpa [Category.assoc] using S.shortExact.exact.lift_f (k ≫ biprod.fst) hkS
  · simpa [Category.assoc] using T.shortExact.exact.lift_f (k ≫ biprod.snd) hkT

/-- Helper for Definition 12.6.2: the biproduct of two extensions is again short exact. -/
private theorem biprodExtensionShortExact (S T : Extension A B) :
    (ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
      (biprodExtension_zero S T)).ShortExact := by
  -- Once the left leg is identified as a kernel, exactness and monicity are owner-side facts.
  have hExactMono :
      (ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
        (biprodExtension_zero S T)).Exact ∧ Mono (biprod.map S.f T.f) :=
    (ShortComplex.exact_and_mono_f_iff_f_is_kernel
      (S := ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
        (biprodExtension_zero S T))).2 ⟨biprodExtensionLegIsKernel S T⟩
  exact ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 inferInstance

/-- Pulling back a source-facing extension along a morphism on the right endpoint gives a new
source-facing extension with the same left endpoint. -/
noncomputable def pullback (u : B' ⟶ B) (S : Extension A B) : Extension A B' :=
  Extension.mk
    (Limits.pullback u S.g)
    (pullbackInclusion u S)
    (Limits.pullback.fst u S.g)
    (pullbackInclusion_comp_fst u S)
    (pullbackShortExact u S)

/-- Pushing out a source-facing extension along a morphism on the left endpoint gives a new
source-facing extension with the same right endpoint. -/
noncomputable def pushout (a : A ⟶ A') (S : Extension A B) : Extension A' B :=
  Extension.mk
    (Limits.pushout a S.f)
    (Limits.pushout.inl a S.f)
    (pushoutProjection a S)
    (pushoutInl_comp_projection a S)
    (pushoutShortExact a S)

/-- The split extension `0 ⟶ A ⟶ A ⊞ B ⟶ B ⟶ 0`. -/
noncomputable def split (A B : C) : Extension A B :=
  Extension.mk
    (A ⊞ B)
    (biprod.inl : A ⟶ A ⊞ B)
    (biprod.snd : A ⊞ B ⟶ B)
    (split_zero A B)
    (splitShortExact A B)

/-- Negating a source-facing extension is pushing out along `-𝟙_A`. -/
noncomputable def neg (S : Extension A B) : Extension A B :=
  pushout (-𝟙 A) S

private noncomputable def biprodExtension (S T : Extension A B) : Extension (A ⊞ A) (B ⊞ B) :=
  Extension.mk
    (S.E ⊞ T.E)
    (biprod.map S.f T.f)
    (biprod.map S.g T.g)
    (biprodExtension_zero S T)
    (biprodExtensionShortExact S T)

private noncomputable def diagonal (B : C) : B ⟶ B ⊞ B :=
  biprod.lift (𝟙 B) (𝟙 B)

private noncomputable def codiagonal (A : C) : A ⊞ A ⟶ A :=
  biprod.desc (𝟙 A) (𝟙 A)

/-- The Baer sum of two source-facing extensions is obtained by pulling back their biproduct along
the diagonal of `B` and then pushing out along the codiagonal of `A`. -/
noncomputable def baerSum (S T : Extension A B) : Extension A B :=
  pushout (codiagonal A) (pullback (diagonal B) (biprodExtension S T))

/-- Helper for Definition 12.6.2: the canonical comparison map between pullbacks fixes the first
projection. -/
private lemma pullbackMap_comp_fst (u : B' ⟶ B) {S T : Extension A B} (e : S.E ≅ T.E)
    (hg : e.hom ≫ T.g = S.g) :
    Limits.pullback.map u S.g u T.g (𝟙 B') e.hom (𝟙 B) (by simp) (by simpa using hg.symm) ≫
      Limits.pullback.fst u T.g =
        Limits.pullback.fst u S.g := by
  -- Unfold only the comparison map and read off its defining first projection.
  simpa [Limits.pullback.map, Category.assoc] using
    (Limits.pullback.lift_fst
      (Limits.pullback.fst u S.g ≫ 𝟙 B')
      (Limits.pullback.snd u S.g ≫ e.hom)
      (by
        rw [Category.comp_id]
        rw [Limits.pullback.condition]
        simpa [Category.assoc] using
          (congrArg (fun k ↦ Limits.pullback.snd u S.g ≫ k) hg).symm))

/-- Helper for Definition 12.6.2: the canonical comparison map between pullbacks sends the second
projection through the middle isomorphism. -/
private lemma pullbackMap_comp_snd (u : B' ⟶ B) {S T : Extension A B} (e : S.E ≅ T.E)
    (hg : e.hom ≫ T.g = S.g) :
    Limits.pullback.map u S.g u T.g (𝟙 B') e.hom (𝟙 B) (by simp) (by simpa using hg.symm) ≫
      Limits.pullback.snd u T.g =
        Limits.pullback.snd u S.g ≫ e.hom := by
  -- The second projection is the chosen middle morphism in the pullback lift.
  simpa [Limits.pullback.map, Category.assoc] using
    (Limits.pullback.lift_snd
      (Limits.pullback.fst u S.g ≫ 𝟙 B')
      (Limits.pullback.snd u S.g ≫ e.hom)
      (by
        rw [Category.comp_id]
        rw [Limits.pullback.condition]
        simpa [Category.assoc] using
          (congrArg (fun k ↦ Limits.pullback.snd u S.g ≫ k) hg).symm))

theorem Isomorphic.pullback (u : B' ⟶ B) (h : Isomorphic S T) :
    Isomorphic (pullback u S) (pullback u T) := by
  rcases h with ⟨e, hf, hg⟩
  let comparison :
      Limits.pullback u S.g ⟶ Limits.pullback u T.g :=
    Limits.pullback.map u S.g u T.g (𝟙 B') e.hom (𝟙 B) (by simp) (by simpa using hg.symm)
  haveI : IsIso comparison := by
    dsimp [comparison]
    infer_instance
  let comparisonIso : Limits.pullback u S.g ≅ Limits.pullback u T.g := asIso comparison
  refine ⟨comparisonIso, ?_, ?_⟩
  · -- Compare the two maps into the target pullback on its defining projections.
    apply Limits.pullback.hom_ext
    · calc
        ((Extension.pullback u S).f ≫ comparisonIso.hom) ≫ Limits.pullback.fst u T.g =
            (Extension.pullback u S).f ≫ Limits.pullback.fst u S.g := by
              simpa [comparisonIso, Category.assoc] using
                congrArg (fun k ↦ (Extension.pullback u S).f ≫ k)
                  (pullbackMap_comp_fst (u := u) (e := e) (hg := hg))
        _ = 0 := by simp [Extension.pullback, pullbackInclusion_comp_fst]
        _ = (Extension.pullback u T).f ≫ Limits.pullback.fst u T.g := by
              simp [Extension.pullback, pullbackInclusion_comp_fst]
    · calc
        ((Extension.pullback u S).f ≫ comparisonIso.hom) ≫ Limits.pullback.snd u T.g =
            ((Extension.pullback u S).f ≫ Limits.pullback.snd u S.g) ≫ e.hom := by
              simpa [comparisonIso, Category.assoc] using
                congrArg (fun k ↦ (Extension.pullback u S).f ≫ k)
                  (pullbackMap_comp_snd (u := u) (e := e) (hg := hg))
        _ = S.f ≫ e.hom := by simp [Extension.pullback, pullbackInclusion_comp_snd]
        _ = T.f := hf
        _ = (Extension.pullback u T).f ≫ Limits.pullback.snd u T.g := by
              simp [Extension.pullback, pullbackInclusion_comp_snd]
  · -- The pullback comparison map preserves the pulled-back quotient morphism.
    rw [show comparisonIso.hom = comparison by rfl]
    exact pullbackMap_comp_fst (u := u) (e := e) (hg := hg)

/-- Helper for Definition 12.6.2: the canonical comparison map between pushouts fixes the left
inclusion. -/
private lemma pushoutInl_comp_map (a : A ⟶ A') {S T : Extension A B} (e : S.E ≅ T.E)
    (hf : S.f ≫ e.hom = T.f) :
    Limits.pushout.inl a S.f ≫
        Limits.pushout.map a S.f a T.f (𝟙 A') e.hom (𝟙 A) (by simp) (by simpa using hf) =
      Limits.pushout.inl a T.f := by
  -- Unfold only the comparison map and read off its defining left leg.
  simpa [Limits.pushout.map, Category.assoc] using
    (Limits.pushout.inl_desc
      ((𝟙 A') ≫ Limits.pushout.inl a T.f)
      (e.hom ≫ Limits.pushout.inr a T.f)
      (by
        calc
          a ≫ ((𝟙 A') ≫ Limits.pushout.inl a T.f) = a ≫ Limits.pushout.inl a T.f := by simp
          _ = T.f ≫ Limits.pushout.inr a T.f := by
            simpa [Category.assoc] using (Limits.pushout.condition (f := a) (g := T.f))
          _ = S.f ≫ (e.hom ≫ Limits.pushout.inr a T.f) := by
            rw [← hf]
            simp [Category.assoc]))

/-- Helper for Definition 12.6.2: the canonical comparison map between pushouts sends the right
inclusion through the middle isomorphism. -/
private lemma pushoutInr_comp_map (a : A ⟶ A') {S T : Extension A B} (e : S.E ≅ T.E)
    (hf : S.f ≫ e.hom = T.f) :
    Limits.pushout.inr a S.f ≫
        Limits.pushout.map a S.f a T.f (𝟙 A') e.hom (𝟙 A) (by simp) (by simpa using hf) =
      e.hom ≫ Limits.pushout.inr a T.f := by
  -- The right inclusion is the chosen middle morphism in the pushout descent map.
  simpa [Limits.pushout.map, Category.assoc] using
    (Limits.pushout.inr_desc
      ((𝟙 A') ≫ Limits.pushout.inl a T.f)
      (e.hom ≫ Limits.pushout.inr a T.f)
      (by
        calc
          a ≫ ((𝟙 A') ≫ Limits.pushout.inl a T.f) = a ≫ Limits.pushout.inl a T.f := by simp
          _ = T.f ≫ Limits.pushout.inr a T.f := by
            simpa [Category.assoc] using (Limits.pushout.condition (f := a) (g := T.f))
          _ = S.f ≫ (e.hom ≫ Limits.pushout.inr a T.f) := by
            rw [← hf]
            simp [Category.assoc]))

theorem Isomorphic.pushout (a : A ⟶ A') (h : Isomorphic S T) :
    Isomorphic (pushout a S) (pushout a T) := by
  rcases h with ⟨e, hf, hg⟩
  let comparison :
      Limits.pushout a S.f ⟶ Limits.pushout a T.f :=
    Limits.pushout.map a S.f a T.f (𝟙 A') e.hom (𝟙 A) (by simp) (by simpa using hf)
  haveI : IsIso comparison := by
    dsimp [comparison]
    infer_instance
  let comparisonIso : Limits.pushout a S.f ≅ Limits.pushout a T.f := asIso comparison
  refine ⟨comparisonIso, ?_, ?_⟩
  · -- The left structure map is literally the left pushout inclusion.
    rw [show comparisonIso.hom = comparison by rfl]
    exact pushoutInl_comp_map (a := a) (e := e) (hf := hf)
  · -- Compare the two maps out of the source pushout on its defining generators.
    apply Limits.pushout.hom_ext
    · have hInlRaw :
          (Limits.pushout.inl a S.f ≫ comparison) ≫ (Extension.pushout a T).g =
            Limits.pushout.inl a T.f ≫ (Extension.pushout a T).g := by
        exact congrArg (fun k ↦ k ≫ (Extension.pushout a T).g)
          (pushoutInl_comp_map (a := a) (e := e) (hf := hf))
      have hInlAssoc :
          Limits.pushout.inl a S.f ≫ comparison ≫ (Extension.pushout a T).g =
            Limits.pushout.inl a T.f ≫ (Extension.pushout a T).g := by
        calc
          Limits.pushout.inl a S.f ≫ comparison ≫ (Extension.pushout a T).g =
              (Limits.pushout.inl a S.f ≫ comparison) ≫ (Extension.pushout a T).g := by
                symm
                exact Category.assoc _ _ _
          _ = Limits.pushout.inl a T.f ≫ (Extension.pushout a T).g := hInlRaw
      calc
        Limits.pushout.inl a S.f ≫ comparisonIso.hom ≫ (Extension.pushout a T).g =
            Limits.pushout.inl a T.f ≫ (Extension.pushout a T).g := by
              simpa [comparisonIso] using hInlAssoc
        _ = 0 := by simp [Extension.pushout, pushoutInl_comp_projection]
        _ = Limits.pushout.inl a S.f ≫ (Extension.pushout a S).g := by
              simp [Extension.pushout, pushoutInl_comp_projection]
    · have hInrRaw :
          (Limits.pushout.inr a S.f ≫ comparison) ≫ (Extension.pushout a T).g =
            (e.hom ≫ Limits.pushout.inr a T.f) ≫ (Extension.pushout a T).g := by
        exact congrArg (fun k ↦ k ≫ (Extension.pushout a T).g)
          (pushoutInr_comp_map (a := a) (e := e) (hf := hf))
      have hInrAssoc :
          Limits.pushout.inr a S.f ≫ comparison ≫ (Extension.pushout a T).g =
            (e.hom ≫ Limits.pushout.inr a T.f) ≫ (Extension.pushout a T).g := by
        calc
          Limits.pushout.inr a S.f ≫ comparison ≫ (Extension.pushout a T).g =
              (Limits.pushout.inr a S.f ≫ comparison) ≫ (Extension.pushout a T).g := by
                symm
                exact Category.assoc _ _ _
          _ = (e.hom ≫ Limits.pushout.inr a T.f) ≫ (Extension.pushout a T).g := hInrRaw
      calc
        Limits.pushout.inr a S.f ≫ comparisonIso.hom ≫ (Extension.pushout a T).g =
            (e.hom ≫ Limits.pushout.inr a T.f) ≫ (Extension.pushout a T).g := by
              simpa [comparisonIso] using hInrAssoc
        _ = e.hom ≫ T.g := by simp [Extension.pushout, pushoutInr_comp_projection, Category.assoc]
        _ = S.g := hg
        _ = Limits.pushout.inr a S.f ≫ (Extension.pushout a S).g := by
              simp [Extension.pushout, pushoutInr_comp_projection]

/-- Helper for Definition 12.6.2: endpoint-fixing isomorphisms are preserved by taking biproducts
of extensions. -/
private theorem Isomorphic.biprodExtension {S₁ S₂ T₁ T₂ : Extension A B}
    (hS : Isomorphic S₁ S₂) (hT : Isomorphic T₁ T₂) :
    Isomorphic (biprodExtension S₁ T₁) (biprodExtension S₂ T₂) := by
  -- Taking biproducts preserves the endpoint-fixing compatibility componentwise.
  rcases hS with ⟨eS, hfS, hgS⟩
  rcases hT with ⟨eT, hfT, hgT⟩
  have hfBiprod :
      biprod.map S₁.f T₁.f ≫ biprod.map eS.hom eT.hom = biprod.map S₂.f T₂.f := by
    ext <;> simp [Category.assoc, hfS, hfT]
  have hgBiprod :
      biprod.map eS.hom eT.hom ≫ biprod.map S₂.g T₂.g = biprod.map S₁.g T₁.g := by
    ext <;> simp [Category.assoc, hgS, hgT]
  exact ⟨biprod.mapIso eS eT, hfBiprod, hgBiprod⟩

theorem Isomorphic.neg (h : Isomorphic S T) : Isomorphic (neg S) (neg T) := by
  simpa [neg] using Isomorphic.pushout (-𝟙 A) h

theorem Isomorphic.baerSum {S₁ S₂ T₁ T₂ : Extension A B}
    (hS : Isomorphic S₁ S₂) (hT : Isomorphic T₁ T₂) :
    Isomorphic (baerSum S₁ T₁) (baerSum S₂ T₂) := by
  -- The Baer sum is functorial because it is built from biproduct, pullback, and pushout.
  simpa [baerSum] using
    Isomorphic.pushout (codiagonal A)
      (Isomorphic.pullback (diagonal B) (Isomorphic.biprodExtension hS hT))

end Operations

end Extension

namespace ExtensionClass

section Operations

variable {A' B' : C}

/-- Pullback on extension classes. -/
noncomputable def pullback (u : B' ⟶ B) : ExtensionClass A B → ExtensionClass A B' :=
  _root_.Quotient.map (Extension.pullback u) fun _ _ h ↦ Extension.Isomorphic.pullback u h

/-- Pushout on extension classes. -/
noncomputable def pushout (a : A ⟶ A') : ExtensionClass A B → ExtensionClass A' B :=
  _root_.Quotient.map (Extension.pushout a) fun _ _ h ↦ Extension.Isomorphic.pushout a h

/-- The split extension class. -/
noncomputable def zero (A B : C) : ExtensionClass A B :=
  ⟦Extension.split A B⟧

/-- Negation on extension classes. -/
noncomputable def neg : ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map Extension.neg fun _ _ h ↦ Extension.Isomorphic.neg h

/-- The Baer sum on extension classes. -/
noncomputable def baerSum : ExtensionClass A B → ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map₂ Extension.baerSum fun _ _ h₁ _ _ h₂ ↦ Extension.Isomorphic.baerSum h₁ h₂

noncomputable instance : Zero (ExtensionClass A B) := ⟨zero A B⟩

noncomputable instance : Neg (ExtensionClass A B) := ⟨neg⟩

noncomputable instance : Add (ExtensionClass A B) := ⟨baerSum⟩

end Operations

end ExtensionClass
end CategoryTheory

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A B : C}

namespace CategoryTheory
namespace Extension

variable {S T : Extension A B}

noncomputable abbrev extClass (S : Extension A B) : Ext B A 1 :=
  S.shortExact.extClass

theorem shortExact_extClass_eq_of_isomorphic (h : Isomorphic S T) :
    S.extClass = T.extClass := by
  rcases h with ⟨e, hf, hg⟩
  let i : S.toShortComplex ≅ T.toShortComplex :=
    ShortComplex.isoMk (Iso.refl A) e (Iso.refl B) (by simpa using hf.symm) (by simpa using hg)
  simpa [i] using
    (ShortComplex.ShortExact.extClass_naturality S.shortExact T.shortExact i.hom)

/-- Helper for Definition 12.6.2: an extension whose quotient map admits a section has trivial
class in `Ext¹`. -/
theorem extClass_eq_zero_of_section (S : Extension A B) (s : B ⟶ S.E) (hs : s ≫ S.g = 𝟙 B) :
    S.extClass = 0 := by
  -- A section of `S.g` turns `mk₀ (𝟙 B)` into `mk₀ s ≫ mk₀ S.g`, so the owner relation
  -- `comp_extClass` forces the extension class to vanish.
  calc
    S.extClass = (Ext.mk₀ (𝟙 B)).comp S.extClass (zero_add 1) := by
      simpa using (Ext.mk₀_id_comp S.extClass).symm
    _ = (Ext.mk₀ (s ≫ S.g)).comp S.extClass (zero_add 1) := by rw [hs]
    _ = (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp S.extClass (zero_add 1)) (zero_add 1) := by
      rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]
    _ = 0 := by rw [S.shortExact.comp_extClass, Ext.comp_zero]

end Extension

namespace ExtensionClass

section ExtBridge

variable {A' B' : C}

/-- The canonical bridge from source-facing extension classes to the owner object `Ext¹(B, A)`. -/
noncomputable def toExt : ExtensionClass A B → Ext B A 1 :=
  _root_.Quotient.lift (fun S ↦ S.extClass) fun _ _ h ↦
    Extension.shortExact_extClass_eq_of_isomorphic h

theorem toExt_pullback (u : B' ⟶ B) (ξ : ExtensionClass A B) :
    toExt (pullback u ξ) = (Ext.mk₀ u).precomp A (zero_add 1) (toExt ξ) := by
  refine _root_.Quotient.inductionOn ξ fun S ↦ ?_
  let φ : (Extension.pullback u S).toShortComplex ⟶ S.toShortComplex :=
    { τ₁ := 𝟙 A
      τ₂ := Limits.pullback.snd u S.g
      τ₃ := u
      comm₁₂ := by simpa using (Extension.pullbackInclusion_comp_snd u S).symm
      comm₂₃ := by simpa using (Limits.pullback.condition (f := u) (g := S.g)).symm }
  -- The canonical map from the pullback row to `S` is exactly the owner-side precomposition map.
  simpa [toExt, ExtensionClass.pullback, Ext.precomp, φ] using
    (ShortComplex.ShortExact.extClass_naturality
      (h₁ := (Extension.pullback u S).shortExact) (h₂ := S.shortExact) φ)

theorem toExt_pushout (a : A ⟶ A') (ξ : ExtensionClass A B) :
    toExt (pushout a ξ) = (Ext.mk₀ a).postcomp B (add_zero 1) (toExt ξ) := by
  refine _root_.Quotient.inductionOn ξ fun S ↦ ?_
  let φ : S.toShortComplex ⟶ (Extension.pushout a S).toShortComplex :=
    { τ₁ := a
      τ₂ := Limits.pushout.inr a S.f
      τ₃ := 𝟙 B
      comm₁₂ := by simpa using (Limits.pushout.condition (f := a) (g := S.f))
      comm₂₃ := by simpa using Extension.pushoutInr_comp_projection a S }
  -- The canonical map from `S` to the pushout row is exactly the owner-side postcomposition map.
  simpa [toExt, ExtensionClass.pushout, Ext.postcomp, φ] using
    (ShortComplex.ShortExact.extClass_naturality
      (h₁ := S.shortExact) (h₂ := (Extension.pushout a S).shortExact) φ).symm

theorem toExt_zero : toExt (0 : ExtensionClass A B) = 0 := by
  -- The split extension has the obvious section `biprod.inr`.
  change (Extension.split A B).extClass = 0
  refine Extension.extClass_eq_zero_of_section (Extension.split A B) biprod.inr ?_
  change (biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B) = 𝟙 B
  simp

theorem toExt_neg (ξ : ExtensionClass A B) : toExt (-ξ) = -toExt ξ := by
  -- Negation is pushout along `-𝟙 A`, and owner-side scalar multiplication by `-1`
  -- is postcomposition with `mk₀ (-𝟙 A)`.
  calc
    toExt (-ξ) = ((Ext.mk₀ (-𝟙 A)).postcomp B (add_zero 1)) (toExt ξ) := by
      simpa [ExtensionClass.neg, CategoryTheory.Extension.neg] using toExt_pushout (-𝟙 A) ξ
    _ = -toExt ξ := by
      simpa [Ext.postcomp] using (Ext.smul_eq_comp_mk₀ (toExt ξ) (-1 : ℤ)).symm

/-- Definition 12.6.2: via the canonical bridge `toExt`, the source-facing Baer sum agrees with
addition in `Ext¹(B, A)`. -/
theorem toExt_baerSum (ξ η : ExtensionClass A B) :
    toExt (baerSum ξ η) = toExt ξ + toExt η := by
  refine _root_.Quotient.inductionOn₂ ξ η fun S T ↦ ?_
  let e : Ext (B ⊞ B) (A ⊞ A) 1 := (Extension.biprodExtension S T).extClass
  let leftToBiprod : S.toShortComplex ⟶ (Extension.biprodExtension S T).toShortComplex :=
    { τ₁ := biprod.inl
      τ₂ := biprod.inl
      τ₃ := biprod.inl
      comm₁₂ := by simp [Extension.biprodExtension]
      comm₂₃ := by simp [Extension.biprodExtension] }
  let rightToBiprod : T.toShortComplex ⟶ (Extension.biprodExtension S T).toShortComplex :=
    { τ₁ := biprod.inr
      τ₂ := biprod.inr
      τ₃ := biprod.inr
      comm₁₂ := by simp [Extension.biprodExtension]
      comm₂₃ := by simp [Extension.biprodExtension] }
  have hLeft :
      (Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1) =
        S.extClass.comp (Ext.mk₀ (biprod.inl : A ⟶ A ⊞ A)) (add_zero 1) := by
    -- The left summand of the biproduct extension is exactly `S`.
    simpa [e, leftToBiprod] using
      (ShortComplex.ShortExact.extClass_naturality
        (h₁ := S.shortExact)
        (h₂ := (Extension.biprodExtension S T).shortExact)
        leftToBiprod).symm
  have hRight :
      (Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1) =
        T.extClass.comp (Ext.mk₀ (biprod.inr : A ⟶ A ⊞ A)) (add_zero 1) := by
    -- The right summand of the biproduct extension is exactly `T`.
    simpa [e, rightToBiprod] using
      (ShortComplex.ShortExact.extClass_naturality
        (h₁ := T.shortExact)
        (h₂ := (Extension.biprodExtension S T).shortExact)
        rightToBiprod).symm
  have hDiagonal :
      Extension.diagonal B = (biprod.inl : B ⟶ B ⊞ B) + biprod.inr := by
    -- The diagonal into a biproduct is the sum of the two inclusions.
    apply biprod.hom_ext
    · simp [Extension.diagonal]
    · simp [Extension.diagonal]
  have hCodiagonal :
      Extension.codiagonal A = (biprod.fst : A ⊞ A ⟶ A) + biprod.snd := by
    -- The codiagonal out of a biproduct is the sum of the two projections.
    apply biprod.hom_ext'
    · simp [Extension.codiagonal]
    · simp [Extension.codiagonal]
  have hLeftFst :
      ((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
          (Ext.mk₀ (biprod.fst : A ⊞ A ⟶ A)) (add_zero 1) =
        S.extClass := by
    -- Route correction: compute the diagonal corner from biproduct naturality instead of
    -- rebuilding it through separate pullback/pushout corner extensions.
    rw [hLeft, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp
  have hLeftSnd :
      ((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
          (Ext.mk₀ (biprod.snd : A ⊞ A ⟶ A)) (add_zero 1) =
        0 := by
    -- The mixed corner vanishes because the left inclusion followed by the right projection is `0`.
    rw [hLeft, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp
  have hRightFst :
      ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
          (Ext.mk₀ (biprod.fst : A ⊞ A ⟶ A)) (add_zero 1) =
        0 := by
    -- The symmetric mixed corner also vanishes.
    rw [hRight, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp
  have hRightSnd :
      ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
          (Ext.mk₀ (biprod.snd : A ⊞ A ⟶ A)) (add_zero 1) =
        T.extClass := by
    -- The second diagonal corner recovers `T`.
    rw [hRight, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp
  -- First rewrite the Baer sum through pullback and pushout, then expand the diagonal and
  -- codiagonal into biproduct sums and collapse the four resulting corners.
  calc
    toExt (baerSum (⟦S⟧ : ExtensionClass A B) ⟦T⟧) =
        (((Ext.mk₀ (Extension.diagonal B)).comp e (zero_add 1)).comp
          (Ext.mk₀ (Extension.codiagonal A)) (add_zero 1)) := by
      change
        toExt
            (ExtensionClass.pushout (Extension.codiagonal A)
              (ExtensionClass.pullback (Extension.diagonal B)
                (⟦Extension.biprodExtension S T⟧ : ExtensionClass (A ⊞ A) (B ⊞ B)))) =
          (((Ext.mk₀ (Extension.diagonal B)).comp e (zero_add 1)).comp
            (Ext.mk₀ (Extension.codiagonal A)) (add_zero 1))
      rw [toExt_pushout, toExt_pullback]
      simp [toExt, Ext.precomp, Ext.postcomp, e]
    _ =
        ((((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)) +
            ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1))).comp
          (Ext.mk₀ (Extension.codiagonal A)) (add_zero 1)) := by
      rw [hDiagonal, Ext.mk₀_add, Ext.add_comp]
    _ =
        ((((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)) +
            ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1))).comp
          (Ext.mk₀ (biprod.fst : A ⊞ A ⟶ A) + Ext.mk₀ biprod.snd) (add_zero 1)) := by
      rw [hCodiagonal, Ext.mk₀_add]
    _ =
        (((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
            (Ext.mk₀ (biprod.fst : A ⊞ A ⟶ A)) (add_zero 1) +
          ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
            (Ext.mk₀ (biprod.fst : A ⊞ A ⟶ A)) (add_zero 1)) +
          (((Ext.mk₀ (biprod.inl : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
              (Ext.mk₀ (biprod.snd : A ⊞ A ⟶ A)) (add_zero 1) +
            ((Ext.mk₀ (biprod.inr : B ⟶ B ⊞ B)).comp e (zero_add 1)).comp
              (Ext.mk₀ (biprod.snd : A ⊞ A ⟶ A)) (add_zero 1)) := by
      rw [Ext.comp_add, Ext.add_comp, Ext.add_comp]
    _ = S.extClass + T.extClass := by
      rw [hLeftFst, hLeftSnd, hRightFst, hRightSnd]
      simp
    _ = toExt (⟦S⟧ : ExtensionClass A B) + toExt (⟦T⟧ : ExtensionClass A B) := by
      rfl

theorem toExt_add (ξ η : ExtensionClass A B) : toExt (ξ + η) = toExt ξ + toExt η := by
  simpa using toExt_baerSum ξ η

end ExtBridge

end ExtensionClass
end CategoryTheory

end
