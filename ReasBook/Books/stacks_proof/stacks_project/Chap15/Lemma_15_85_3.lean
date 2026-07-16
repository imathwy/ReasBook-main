import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_proof.stacks_project.Chap10.Lemma_10_71_1
import stacks_proof.stacks_project.Chap13.Lemma_13_15_4
import stacks_proof.stacks_project.Chap13.Lemma_13_15_5
import stacks_proof.stacks_project.Chap13.Lemma_13_28_2
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_65_5
import stacks_proof.stacks_project.Chap15.Lemma_15_65_10
import stacks_proof.stacks_project.Chap15.Lemma_15_70_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

private abbrev ModCat := ModuleCat.{u} R
local notation "DMod" => DerivedCategory (ModCat (R := R))
local notation "Cpx" => CochainComplex (ModCat (R := R)) ℤ
local notation "H" => DerivedCategory.homologyFunctor (ModCat (R := R))
local notation "BoundedAbove" => (t.minus : ObjectProperty DMod)
local notation "FiniteFreeClass" => (fun M : ModCat (R := R) ↦ Module.Free R M ∧ Module.Finite R M)

/- Domain-style sampling for Lemma 15.85.3:
- primary domain: derived `R`-modules concentrated in `[-1, 0]`, represented by two-term
  cochain complexes;
- sampled owner declarations:
  `IsTwoTermRepresentative`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`,
  `Module.Free`,
  `Module.Finite`,
  `IsNoetherianRing`;
- best owner abstraction: the source-facing owner is `IsTwoTermRepresentative K P`, whose
  primitive data are that `P` represents `K` and is supported in degrees `-1` and `0`;
- primitive data: the representative complex together with the two-term owner predicate, while the
  module-theoretic conditions on the degree `0` and degree `-1` terms remain additional inputs;
- derived API: the existence theorems below and downstream predicates built from this owner.

Source/core/bridge triage:
- `source-facing`: the existence of a two-term representative with the stated free / finite
  properties;
- `core/canonical`: `IsTwoTermRepresentative`, together with `K.IsGE (-1)` and `K.IsLE 0`;
- `bridge/view`: the explicit isomorphism witness produced from the t-structure truncation API.

Accordingly, this file exposes direct existential statements over a cochain complex witness rather
than a parallel public wrapper structure carrying the same data. -/

/-- A cochain complex `P` is a two-term representative of `K` if it represents `K` and is
supported in degrees `-1` and `0`. -/
def IsTwoTermRepresentative
    (K : DMod)
    (P : Cpx) : Prop :=
  IsIsomorphic (DerivedCategory.Q.obj P) K ∧ P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0

/-- Helper for Lemma 15.85.3: the object property of free `R`-modules. -/
private abbrev FreeObj : CategoryTheory.ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Free R M

/-- Helper for Lemma 15.85.3: free `R`-modules contain a zero object. -/
local instance freeObj_containsZero :
    CategoryTheory.ObjectProperty.ContainsZero (FreeObj (R := R)) where
  exists_zero := ⟨ModuleCat.of R PUnit,
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance,
    Module.Free.of_subsingleton (R := R) (N := PUnit)⟩

/-- Helper for Lemma 15.85.3: every `R`-module is the quotient of a free `R`-module. -/
local instance freeObj_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover (FreeObj (R := R)) where
  exists_epi (M : ModuleCat.{u} R) := by
    refine ⟨ModuleCat.of R ((M : Type u) →₀ R), ?_, ModuleCat.freeDesc (fun x : (M : Type u) ↦ x), ?_⟩
    · change Module.Free R ((M : Type u) →₀ R)
      exact Module.Free.of_basis
        (Finsupp.basisSingleOne : Module.Basis (M : Type u) R ((M : Type u) →₀ R))
    · -- Proof comment: the free-forgetful counit hits each element by the corresponding basis
      -- vector.
      refine (ModuleCat.epi_iff_surjective _).2 ?_
      intro m
      refine ⟨ModuleCat.freeMk m, ?_⟩
      exact ModuleCat.freeDesc_apply (R := R) (f := fun x : (M : Type u) ↦ x) m

/-- Helper for Lemma 15.85.3: a zero `R`-module is finite. -/
private theorem moduleCat_finite_of_isZero
    {M : ModuleCat R} (hM : IsZero M) :
    Module.Finite R M := by
  -- Proof comment: any zero module is isomorphic to the one-point free module.
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  let e : ModuleCat.of R PUnit ≅ M :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hM.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.85.3: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : CochainComplex (ModCat (R := R)) ℤ := HomologicalComplex.zero

/-- Helper for Lemma 15.85.3: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree :
    (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    -- Proof comment: every term of the zero complex is a zero module, so the zero-module bridge
    -- supplies the required finite free structure.
    let hzero : IsZero ((zeroCpx (R := R)).X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModCat (R := R)) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero : IsZero (zeroCpx (R := R)))
    let _ : Subsingleton ((zeroCpx (R := R)).X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    refine ⟨Module.Free.of_subsingleton (R := R) (N := (zeroCpx (R := R)).X i), ?_⟩
    let e : ModuleCat.of R PUnit ≅ (zeroCpx (R := R)).X i :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
    exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.85.3: lower cohomological vanishing of `K` transfers to its chosen
`Q.objPreimage` representative. -/
private theorem objPreimage_homology_isZero_below_of_isGE
    (K : DMod) (hGE : K.IsGE (-1)) :
    ∀ i : ℤ, i < -1 → IsZero ((DerivedCategory.Q.objPreimage K).homology i) := by
  -- Proof comment: compute homology of the chosen preimage through the canonical comparison
  -- isomorphism.
  rw [DerivedCategory.isGE_iff] at hGE
  intro i hi
  exact (objPreimage_homology_iso (R := R) K i).isZero_iff.1 (hGE i hi)

/-- Helper for Lemma 15.85.3: upper cohomological vanishing of `K` transfers to its chosen
`Q.objPreimage` representative. -/
private theorem objPreimage_homology_isZero_above_of_isLE
    (K : DMod) (hLE : K.IsLE 0) :
    ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.Q.objPreimage K).homology i) := by
  -- Proof comment: the derived upper bound is again read on the chosen cochain representative
  -- using `objPreimage_homology_iso`.
  rw [DerivedCategory.isLE_iff] at hLE
  intro i hi
  exact (objPreimage_homology_iso (R := R) K i).isZero_iff.1 (hLE i hi)

/-- Helper for Lemma 15.85.3: on the retained range, the lower-truncation embedding
`n ↦ a + n` lands in the original degree. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (a n : ℤ) (han : a ≤ n) :
    (ComplexShape.embeddingUpIntGE a).f (Int.toNat (n - a)) = n := by
  -- Proof comment: the standard embedding for smart lower truncation is affine on the surviving
  -- indices.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.85.3: above the cutoff, smart lower truncation keeps the original term. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : Cpx) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n := by
  let i : ℕ := Int.toNat (n - a)
  let hi' : (ComplexShape.embeddingUpIntGE a).f i = n :=
    embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  let hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: the standard truncation API returns the retained term isomorphism once the
  -- surviving index is identified.
  exact K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.85.3: smart lower truncation preserves a strict upper support bound. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE_local
    (K : Cpx) {a b : ℤ} (hab : a ≤ b) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := by
  -- Proof comment: above `b`, either the degree is still retained and so vanishes in `K`, or it
  -- already lies below the truncation cutoff and vanishes by construction.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hai : a < i
  · exact IsZero.of_iso (K.isZero_of_isStrictlyLE b i hi) (truncGE_term_iso_of_gt K a i hai)
  · have hia : i < a := by
      omega
    exact (K.truncGE a).isZero_of_isStrictlyGE a i hia

/-- Helper for Lemma 15.85.3: a quasi-isomorphic bounded-above preimage model yields the desired
two-term representative after smart lower truncation at `-1`. -/
private theorem isTwoTermRepresentative_truncGE_negOne_of_quasiIso_preimage
    {K : DMod}
    {F : Cpx}
    (alpha : F ⟶ DerivedCategory.Q.objPreimage K)
    (hα : QuasiIso alpha)
    (hFLE : F.IsStrictlyLE 0)
    (hFbelow : ∀ i : ℤ, i < -1 → IsZero (F.homology i)) :
    IsTwoTermRepresentative (R := R) K (F.truncGE (-1)) := by
  -- Proof comment: the lower truncation remains quasi-isomorphic because `F` has no homology
  -- below `-1`; compose that comparison with the chosen quasi-isomorphism to `Q.objPreimage K`.
  have hπ : QuasiIso (F.πTruncGE (-1)) :=
    quasiIso_piTruncGE_of_isZero_homology_below (-1) F hFbelow
  have hQπ : IsIso (DerivedCategory.Q.map (F.πTruncGE (-1))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModCat (R := R)) (F.πTruncGE (-1))).2 hπ
  have hQα : IsIso (DerivedCategory.Q.map alpha) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModCat (R := R)) alpha).2 hα
  let eRep :
      DerivedCategory.Q.obj (F.truncGE (-1)) ≅ K :=
    (asIso (DerivedCategory.Q.map (F.πTruncGE (-1)))).symm ≪≫
      asIso (DerivedCategory.Q.map alpha) ≪≫
        DerivedCategory.Q.objObjPreimageIso K
  refine ⟨⟨eRep⟩, inferInstance, ?_⟩
  -- Proof comment: smart lower truncation preserves the strict upper support bound `≤ 0`.
  exact truncGE_isStrictlyLE_of_isStrictlyLE_local (K := F) (a := -1) (b := 0) (by omega) hFLE

/-- Helper for Lemma 15.85.3: the cutoff term of smart lower truncation at `-1` is the cokernel
of the previous differential. -/
private noncomputable def truncGE_negOne_term_iso_cokernel
    (F : Cpx) :
    (F.truncGE (-1)).X (-1) ≅ cokernel ((F.sc (-1)).f) := by
  let eCut :
      (F.truncGE (-1)).X (-1) ≅ F.opcycles (-1) :=
    F.truncGEXIsoOpcycles (e := ComplexShape.embeddingUpIntGE (-1)) rfl <| by
      simpa using (ComplexShape.boundaryGE_embeddingUpIntGE_iff (-1) 0).2 rfl
  let eOpc :
      F.opcycles (-1) ≅ cokernel ((F.sc (-1)).f) := by
    -- Proof comment: degree `-1` opcycles are the cokernel of the incoming differential in the
    -- degree-`-1` short complex.
    simpa [HomologicalComplex.opcycles] using
      (ShortComplex.opcyclesIsoCokernel (S := F.sc (-1)))
  exact eCut ≪≫ eOpc

/-- Helper for Lemma 15.85.3: the new degree-`-1` term created by smart lower truncation is
finite when the original degree-`-1` term is finite. -/
private theorem finite_truncGE_negOne_term_of_finite_term
    (F : Cpx) (hfinite : Module.Finite R (F.X (-1))) :
    Module.Finite R ((F.truncGE (-1)).X (-1)) := by
  let _ : Module.Finite R (F.X (-1)) := hfinite
  have hX2 : Module.Finite R ((F.sc (-1)).X₂ : ModuleCat R) := by
    simpa [HomologicalComplex.sc] using hfinite
  let hquot :
      Module.Finite R (((F.sc (-1)).X₂ : ModuleCat R) ⧸
        LinearMap.range ((F.sc (-1)).f).hom) := by
    let _ : Module.Finite R ((F.sc (-1)).X₂ : ModuleCat R) := hX2
    simpa using
      (Module.Finite.quotient R (LinearMap.range ((F.sc (-1)).f).hom))
  let hcoker :
      Module.Finite R (cokernel ((F.sc (-1)).f) : ModuleCat R) := by
    let _ :
        Module.Finite R (((F.sc (-1)).X₂ : ModuleCat R) ⧸
          LinearMap.range ((F.sc (-1)).f).hom) := hquot
    exact Module.Finite.equiv
      (ModuleCat.cokernelIsoRangeQuotient ((F.sc (-1)).f)).symm.toLinearEquiv
  let eCut :
      ((F.truncGE (-1)).X (-1)) ≅ cokernel ((F.sc (-1)).f) := by
    let eCut0 :
        (F.truncGE (-1)).X (-1) ≅ F.opcycles (-1) :=
      F.truncGEXIsoOpcycles (e := ComplexShape.embeddingUpIntGE (-1)) rfl <| by
        simpa using (ComplexShape.boundaryGE_embeddingUpIntGE_iff (-1) 0).2 rfl
    let eOpc :
        F.opcycles (-1) ≅ cokernel ((F.sc (-1)).f) := by
      simpa [HomologicalComplex.opcycles] using
        (ShortComplex.opcyclesIsoCokernel (S := F.sc (-1)))
    exact eCut0 ≪≫ eOpc
  let _ : Module.Finite R (cokernel ((F.sc (-1)).f) : ModuleCat R) := hcoker
  exact Module.Finite.equiv eCut.symm.toLinearEquiv

/-- Helper for Lemma 15.85.3: pseudo-coherence is preserved by isomorphisms in `D(R)`. -/
private theorem isPseudoCoherent_of_iso_local
    {K L : DMod} (e : K ≅ L) (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  -- Proof comment: reuse the same bounded-above finite-free witness and postcompose its
  -- comparison map with the isomorphism `e`.
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.85.3: a derived complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
private theorem isPseudoCoherent_iff_forall_isMPseudoCoherent_local
    (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  let E : Cpx := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) E
  have hiffE : E.IsPseudoCoherent ↔ ∀ m : ℤ, E.IsMPseudoCoherent m :=
    hTFAE.out 0 1
  constructor
  · intro hK m
    -- Proof comment: move to the fixed cochain representative where the cochain-level TFAE
    -- applies, then transport the degree-`m` conclusion back to `K`.
    have hE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      isPseudoCoherent_of_iso_local e.symm hK
    have hEm : (DerivedCategory.Q.obj E).IsMPseudoCoherent m :=
      (hiffE.mp hE) m
    exact isMPseudoCoherent_of_iso e m hEm
  · intro hK
    -- Proof comment: pull the degreewise hypotheses back to the chosen representative, apply the
    -- cochain-level criterion, and push the witness forward along the comparison isomorphism.
    have hEall : ∀ m : ℤ, (DerivedCategory.Q.obj E).IsMPseudoCoherent m := fun m ↦
      isMPseudoCoherent_of_iso e.symm m (hK m)
    have hE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      hiffE.mpr hEall
    exact isPseudoCoherent_of_iso_local e hE

/-- Helper for Lemma 15.85.3: if all homology in degrees `≥ m` vanishes, then the derived object
is `m`-pseudo-coherent. -/
private theorem isMPseudoCoherent_of_homology_vanishes_ge_local
    {K : DMod} {m : ℤ}
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let α : DerivedCategory.Q.obj (zeroCpx (R := R)) ⟶ K := 0
  refine ⟨zeroCpx (R := R), ?_, inferInstance, α, ?_, ?_⟩
  · -- Proof comment: the zero complex is bounded on both sides by any cutoff.
    refine ⟨m, m, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModCat (R := R)) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero : IsZero (zeroCpx (R := R)))
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModCat (R := R)) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero : IsZero (zeroCpx (R := R)))
  · intro i hi
    -- Proof comment: both source and target homology vanish in degree `i`, so the zero map is an
    -- isomorphism there.
    let hsrc : IsZero ((H i).obj (DerivedCategory.Q.obj (zeroCpx (R := R)))) := by
      simpa [zeroCpx] using
        (H i).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (zeroCpx (R := R))))
    let htgt : IsZero ((H i).obj K) := hK i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the same zero-object comparison makes the cutoff-degree map an epimorphism.
    let hsrc : IsZero ((H m).obj (DerivedCategory.Q.obj (zeroCpx (R := R)))) := by
      simpa [zeroCpx] using
        (H m).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero : IsZero (zeroCpx (R := R))))
    let htgt : IsZero ((H m).obj K) := hK m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.85.3: a zero `R`-module is finite free. -/
private lemma moduleCat_finite_free_of_isZero
    (M : ModuleCat R) (hM : IsZero M) :
    Module.Free R M ∧ Module.Finite R M := by
  -- Proof comment: zero modules are free by subsingleton and finite by comparison with `PUnit`.
  let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  refine ⟨Module.Free.of_subsingleton (R := R) (N := M), ?_⟩
  let e : ModuleCat.of R PUnit ≅ M :=
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hM.isoZero.symm
  exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.85.3: the cochain complex attached to a projective resolution of `N`
represents the degree-zero single object `N[0]`. -/
private noncomputable def projectiveResolution_cochain_single0_iso
    {N : ModuleCat R} (P : ProjectiveResolution N) :
    DerivedCategory.Q.obj P.cochainComplex ≅ (ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj N :=
  let _ : IsIso (DerivedCategory.Q.map P.π') := by
    infer_instance
  asIso (DerivedCategory.Q.map P.π') ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).symm

/-- Helper for Lemma 15.85.3: the cochain complex attached to a finite free resolution is
termwise finite free. -/
private lemma projectiveResolution_cochain_isTermwiseFiniteFree
    {N : ModuleCat R} {F : ChainComplex (ModuleCat R) ℕ}
    (π : F ⟶ CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) N)
    [hπ : ChainComplex.IsFiniteFreeResolution (R := R) (M := N) π] :
    (ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N)
      (π := π)).cochainComplex.IsTermwiseFiniteFree := by
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N) (π := π)
  refine ⟨fun i ↦ ?_⟩
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    let e : P.cochainComplex.X (-k) ≅ P.complex.X k :=
      P.cochainComplexXIso (-k) k rfl
    have hfree : Module.Free R (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFreeResolution.free (R := R) (M := N) π k
    have hfinite : Module.Finite R (P.complex.X k) := by
      simpa [P] using ChainComplex.IsFiniteFreeResolution.finite (R := R) (M := N) π k
    let _ : Module.Free R (P.complex.X k) := hfree
    let _ : Module.Finite R (P.complex.X k) := hfinite
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · have hi' : 0 < i := by
      omega
    have hzero : IsZero (P.cochainComplex.X i) := P.cochainComplex.isZero_of_isStrictlyLE 0 i hi'
    exact moduleCat_finite_free_of_isZero (R := R) (P.cochainComplex.X i) hzero

/-- Helper for Lemma 15.85.3: over a Noetherian ring, a finite module is pseudo-coherent. -/
private lemma moduleCat_isPseudoCoherent_of_finite
    [IsNoetherianRing R]
    (N : ModCat (R := R)) [Module.Finite R N] :
    N.IsPseudoCoherent := by
  -- Proof comment: choose a finite free resolution of `N`, pass to its cochain model, and use
  -- the canonical derived isomorphism to `N[0]`.
  rcases module_exists_finite_free_resolution (R := R) (M := N) with ⟨F, π, hπ⟩
  let P := ChainComplex.IsFreeResolution.toProjectiveResolution (R := R) (M := N) (π := π)
  rw [ModuleCat.IsPseudoCoherent]
  refine ⟨P.cochainComplex, ?_, ?_, ?_⟩
  · -- Proof comment: the cochain projective-resolution model is concentrated in degrees `≤ 0`.
    exact ⟨0, inferInstance⟩
  · exact projectiveResolution_cochain_isTermwiseFiniteFree (R := R) (π := π)
  · refine ⟨(projectiveResolution_cochain_single0_iso (R := R) P).hom, ?_⟩
    infer_instance

/-- Helper for Lemma 15.85.3: a finite module is `n`-pseudo-coherent for every nonpositive
bound `n`. -/
private lemma moduleCat_isMPseudoCoherent_of_nonpos_of_finite
    [IsNoetherianRing R]
    (N : ModCat (R := R)) [Module.Finite R N] (n : ℤ) (_hn : n ≤ 0) :
    N.IsMPseudoCoherent n := by
  -- Route correction: the finite-resolution truncation route is unnecessary here. A finite module
  -- is already pseudo-coherent, so the all-`m` criterion gives the requested nonpositive bound.
  have hN : N.IsPseudoCoherent :=
    moduleCat_isPseudoCoherent_of_finite (R := R) N
  rw [ModuleCat.IsPseudoCoherent, isPseudoCoherent_iff_forall_isMPseudoCoherent_local] at hN
  exact hN n

/-- Helper for Lemma 15.85.3: a degree-zero module object is `n`-pseudo-coherent for every
positive bound `n`. -/
private lemma moduleCat_isMPseudoCoherent_of_positive
    [IsNoetherianRing R]
    (N : ModCat (R := R)) (n : ℤ) (hn : 0 < n) :
    N.IsMPseudoCoherent n := by
  -- Proof comment: the degree-zero single complex has no homology in degrees `≥ n > 0`.
  refine isMPseudoCoherent_of_homology_vanishes_ge_local ?_
  intro i hi
  have hi0 : i ≠ 0 := by
    omega
  exact single_zero_complex_homology_isZero_of_ne (𝒜 := ModCat (R := R)) N i hi0

/-- Helper for Lemma 15.85.3: over a Noetherian ring, finite cohomology in degrees `-1` and `0`
plus the interval support bounds imply pseudo-coherence of the chosen `Q.objPreimage`
representative. -/
private theorem objPreimage_isPseudoCoherent_of_interval_finite_homology
    [IsNoetherianRing R]
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    (DerivedCategory.Q.objPreimage K).IsPseudoCoherent := by
  have hKLE : ∀ i : ℤ, 0 < i → IsZero ((H i).obj K) := by
    rw [DerivedCategory.isLE_iff] at hLE
    exact hLE
  have hKGE : ∀ i : ℤ, i < -1 → IsZero ((H i).obj K) := by
    rw [DerivedCategory.isGE_iff] at hGE
    exact hGE
  let Kminus : boundedAboveDerivedCategory (ModCat (R := R)) := by
    -- Proof comment: the given upper cohomological bound places `K` in `D^-(R)`.
    refine ⟨K, ?_⟩
    rw [derivedCategory_t_minus_iff]
    exact ⟨0, hKLE⟩
  have hKpseudo : K.IsPseudoCoherent := by
    -- Proof comment: prove every fixed `m`-pseudo-coherence bound using Lemma `15.65.10`
    -- degreewise, splitting into the positive and nonpositive module cases.
    rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local]
    intro m
    exact boundedAbove_isMPseudoCoherent_of_homology (R := R) Kminus m <| by
      intro i
      by_cases him : i < m
      · exact
          moduleCat_isMPseudoCoherent_of_positive
            (R := R) ((H i).obj K) (m - i) (by omega)
      · have hfinite : Module.Finite R ((H i).obj K) := by
          by_cases hi_lt : i < -1
          · exact moduleCat_finite_of_isZero (R := R) (hKGE i hi_lt)
          · by_cases hi_eq_neg1 : i = -1
            · subst hi_eq_neg1
              exact hHneg1
            · by_cases hi_eq_zero : i = 0
              · subst hi_eq_zero
                exact hH0
              · have hi_pos : 0 < i := by
                  omega
                exact moduleCat_finite_of_isZero (R := R) (hKLE i hi_pos)
        let _ : Module.Finite R ((H i).obj K) := hfinite
        exact
          moduleCat_isMPseudoCoherent_of_nonpos_of_finite
            (R := R) ((H i).obj K) (m - i) (by omega)
  -- Proof comment: transfer pseudo-coherence across the canonical comparison from the chosen
  -- preimage complex back to `K`.
  change (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage K)).IsPseudoCoherent
  exact isPseudoCoherent_of_iso_local (R := R) (DerivedCategory.Q.objObjPreimageIso K).symm hKpseudo

-- Proof sketch: choose a cochain-complex representative of `K`, truncate above degree `0`, then
-- replace it by a quasi-isomorphic bounded-above free complex using Lemma `13.15.4`. Finally
-- truncate below degree `-1`; the homology vanishing outside `{-1, 0}` ensures that this
-- truncation still represents `K`, and the degree-zero term remains free.
/-- Lemma 15.85.3 (1): if an object `K` of `D(R)` has cohomology only in degrees `-1` and `0`,
then `K` is represented by a cochain complex supported in degrees `-1` and `0` whose degree-zero
term is a free `R`-module. -/
@[stacks 0G9E]
theorem exists_twoTermFreeRepresentative
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0) :
    ∃ P : Cpx, IsTwoTermRepresentative (R := R) K P ∧ Module.Free R (P.X 0) := by
  let M : Cpx := DerivedCategory.Q.objPreimage K
  have hMabove : ∀ i : ℤ, 0 < i → IsZero (M.homology i) :=
    objPreimage_homology_isZero_above_of_isLE (R := R) K hLE
  obtain ⟨F, α, hF⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_above
      (P := FreeObj (R := R)) 0 M hMabove
  have hFbelow : ∀ i : ℤ, i < -1 → IsZero (F.homology i) := by
    intro i hi
    let eF : (H i).obj (DerivedCategory.Q.obj F) ≅ F.homology i :=
      (DerivedCategory.homologyFunctorFactors (ModCat (R := R)) i).app F
    let eM : (H i).obj (DerivedCategory.Q.obj M) ≅ M.homology i :=
      (DerivedCategory.homologyFunctorFactors (ModCat (R := R)) i).app M
    have htargetZero : IsZero ((H i).obj (DerivedCategory.Q.obj M)) := by
      exact eM.isZero_iff.2 (objPreimage_homology_isZero_below_of_isGE (R := R) K hGE i hi)
    have hQα : IsIso (DerivedCategory.Q.map α) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModCat (R := R)) α).2 hF.quasiIso
    have hsourceZero : IsZero ((H i).obj (DerivedCategory.Q.obj F)) := by
      letI : IsIso ((H i).map (DerivedCategory.Q.map α)) := Functor.map_isIso (H i) (DerivedCategory.Q.map α)
      exact (asIso ((H i).map (DerivedCategory.Q.map α))).isZero_iff.2 htargetZero
    exact eF.isZero_iff.1 hsourceZero
  refine ⟨F.truncGE (-1), ?_, ?_⟩
  · exact
      isTwoTermRepresentative_truncGE_negOne_of_quasiIso_preimage
        (R := R) α hF.quasiIso hF.strictlyLE hFbelow
  · let e0 : (F.truncGE (-1)).X 0 ≅ F.X 0 :=
      truncGE_term_iso_of_gt (K := F) (-1) 0 (by omega)
    let hfree0 : Module.Free R (F.X 0) := hF.term_mem 0
    let _ : Module.Free R (F.X 0) := hfree0
    exact Module.Free.of_equiv e0.symm.toLinearEquiv

-- Proof sketch: choose a bounded-above finite-free representative of `K` from Lemma `15.65.5`,
-- using the Noetherian and finite-cohomology hypotheses. Truncating this complex below degree
-- `-1` preserves the represented derived object because the other cohomology groups vanish. The
-- resulting degree-zero term is finite free, and the degree `-1` term is finite because it is a
-- subquotient of finite modules in the original finite-free complex.
/-- Lemma 15.85.3 (2): under the Noetherian and finite-cohomology hypotheses, the two-term
representative can be chosen with finite free degree-zero term and finite degree `-1` term. -/
@[stacks 0G9E]
theorem exists_twoTermFiniteFreeRepresentative
    [IsNoetherianRing R]
    (K : DMod)
    (hGE : K.IsGE (-1))
    (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H (-1)).obj K))
    (hH0 : Module.Finite R ((H 0).obj K)) :
    ∃ P : Cpx,
      IsTwoTermRepresentative (R := R) K P ∧
        Module.Free R (P.X 0) ∧
          Module.Finite R (P.X 0) ∧ Module.Finite R (P.X (-1)) := by
  let M : Cpx := DerivedCategory.Q.objPreimage K
  have hMpc :
      M.IsPseudoCoherent :=
    objPreimage_isPseudoCoherent_of_interval_finite_homology
      (R := R) K hGE hLE hHneg1 hH0
  have hMabove : ∀ i : ℤ, 0 < i → IsZero (M.homology i) :=
    objPreimage_homology_isZero_above_of_isLE (R := R) K hLE
  rcases exists_boundedAbove_termwiseFiniteFree_quasiIso
      (R := R) (K := M) hMpc hMabove with
    ⟨Fminus, hFle, α, hα⟩
  let F : Cpx := (Fminus : Cpx)
  have hFbelow : ∀ i : ℤ, i < -1 → IsZero (F.homology i) := by
    intro i hi
    let eF : (H i).obj (DerivedCategory.Q.obj F) ≅ F.homology i :=
      (DerivedCategory.homologyFunctorFactors (ModCat (R := R)) i).app F
    let eM : (H i).obj (DerivedCategory.Q.obj M) ≅ M.homology i :=
      (DerivedCategory.homologyFunctorFactors (ModCat (R := R)) i).app M
    have htargetZero : IsZero ((H i).obj (DerivedCategory.Q.obj M)) := by
      exact eM.isZero_iff.2 (objPreimage_homology_isZero_below_of_isGE (R := R) K hGE i hi)
    have hQα : IsIso (DerivedCategory.Q.map α) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModCat (R := R)) α).2 hα
    have hsourceZero : IsZero ((H i).obj (DerivedCategory.Q.obj F)) := by
      letI : IsIso ((H i).map (DerivedCategory.Q.map α)) := Functor.map_isIso (H i) (DerivedCategory.Q.map α)
      exact (asIso ((H i).map (DerivedCategory.Q.map α))).isZero_iff.2 htargetZero
    exact eF.isZero_iff.1 hsourceZero
  let e0 : (F.truncGE (-1)).X 0 ≅ F.X 0 :=
    truncGE_term_iso_of_gt (K := F) (-1) 0 (by omega)
  have hterm0 : Module.Free R (F.X 0) ∧ Module.Finite R (F.X 0) := by
    simpa [F] using Fminus.term_mem 0
  have htermNeg1 : Module.Free R (F.X (-1)) ∧ Module.Finite R (F.X (-1)) := by
    simpa [F] using Fminus.term_mem (-1)
  refine ⟨F.truncGE (-1), ?_, ?_, ?_, ?_⟩
  · exact
      isTwoTermRepresentative_truncGE_negOne_of_quasiIso_preimage
        (R := R) α hα hFle hFbelow
  · let _ : Module.Free R (F.X 0) := hterm0.1
    exact Module.Free.of_equiv e0.symm.toLinearEquiv
  · let _ : Module.Finite R (F.X 0) := hterm0.2
    exact Module.Finite.equiv e0.symm.toLinearEquiv
  · exact finite_truncGE_negOne_term_of_finite_term (R := R) F htermNeg1.2

end

end CategoryTheory
