import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.stacks_project.Chap10.Lemma_10_77_5
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_19_1
import StacksProject_2024.stacks_project.Chap13.Remark_13_12_4
import StacksProject_2024.stacks_project.Chap15.«15_60_1_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_8
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_20
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open CochainComplex
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "DModRI" => DerivedCategory ModRI
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "ProjectiveMinusR" => CochainComplex.ProjectiveMinus ModR
local notation "ProjectiveMinusRI" => CochainComplex.ProjectiveMinus ModRI
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "single₀R" => DerivedCategory.singleFunctor ModR (0 : ℤ)

/- Domain-style sampling:
- primary domain: lifting bounded-above projective derived representatives across quotient
  reduction modulo a nilpotent ideal;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `ModuleCat.extendScalars`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the bounded-above projective owners
  `CochainComplex.ProjectiveMinus ModR` and `CochainComplex.ProjectiveMinus ModRI`; the quotient
  representative should stay on the canonical owner `ProjectiveMinus`, while reduction remains the
  canonical cochain-level scalar-extension
  `(Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj`;
- primitive data: the derived object `K : D(R)`, the bounded-above projective quotient complex
  `E`, and the canonical reduction hypothesis that `E` represents `K ⊗[R]^L[(R ⧸ I)]`;
- derived API: existence of a bounded-above projective representative `P` of `K` together with
  the two resulting comparison isomorphism claims, exposed through the canonical Prop-level owner
  `CategoryTheory.IsIsomorphic` rather than through `Nonempty`.

Source/core/bridge triage:
- `source-facing`: the projective specialization of the lifting statement of Lemma `15.76.3`;
- `core/canonical`: `ProjectiveMinus`, `derivedTensorWithAlgebra`, and
  `CochainComplex.ProjectiveResolution`;
- `bridge/view`: the object-level comparison claims
  `IsIsomorphic K (DerivedCategory.Q.obj (P : CpxR))` and
  `IsIsomorphic
    ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj
      (P : CpxR))
    (E : CpxRI)`; the reduction hypothesis itself stays on the chapter owner
  `K ⊗[R]^L[(R ⧸ I)]`. -/

-- Proof sketch: start from the canonical derived reduction hypothesis
-- `(K ⊗[R]^L[(R ⧸ I)]).IsIsomorphic (Q(E))`, choose a K-projective model computing that derived
-- reduction,
-- truncate above using boundedness of `E`, lift each quotient-projective term across the nilpotent
-- ideal by Lemma `10.77.5`, and use K-projectivity to identify the resulting bounded-above lift
-- with `K`.
/-- Helper for Lemma 15.76.3: a bounded-above projective quotient complex can be repackaged as a
bounded-above complex whose terms lie in the image of reduction modulo `I` on projective
`R`-modules. -/
lemma projective_reduction_image_complex
    (E : ProjectiveMinusRI) (hInil : IsNilpotent I) :
    CochainComplex.MinusWithTermsIn ((isProjective ModR).map ReduceModI) := by
  refine ⟨⟨(E : CpxRI), E.minus⟩, ?_⟩
  intro i
  let _ : Module.Projective (R ⧸ I) ((E : CpxRI).X i) := by
    let _ : Projective ((E : CpxRI).X i) := E.term_mem i
    infer_instance
  obtain ⟨P, _, _, e, hP⟩ :=
    exists_projective_lift_of_projective_quotient_of_isNilpotent
      (I := I) hInil (show Module.Projective (R ⧸ I) ((E : CpxRI).X i) from inferInstance)
  let Pobj : ModR := ModuleCat.of R P
  let _ : Module.Projective R P := hP
  have hPobj : isProjective ModR Pobj := by
    infer_instance
  -- Proof comment: choose the lifted projective `R`-module in degree `i` and record that its
  -- reduction modulo `I` is identified with the given quotient term.
  refine ⟨Pobj, hPobj, ?_⟩
  exact ⟨(reduceModI_obj_iso_quotient (I := I) Pobj) ≪≫ e.toModuleIso⟩

/-- Helper for Lemma 15.76.3: surjectivity of a map between projective `R`-modules can be tested
after reduction modulo a nilpotent ideal. -/
lemma projective_surjective_of_reduceModI_surjective
    (hInil : IsNilpotent I)
    {P₁ P₂ : ModR} (f : P₁ ⟶ P₂)
    (hf : Function.Surjective ((ReduceModI.map f).hom)) :
    Function.Surjective f.hom := by
  have hquot : Function.Surjective (f.hom.quotientMapByIdeal I) := by
    exact (surjective_reduceModI_map_iff_quotientMapByIdeal (I := I) f).1 hf
  -- Proof comment: first rewrite reduced surjectivity as surjectivity on the concrete quotient
  -- map, then apply Nakayama's lemma for nilpotent ideals.
  exact surjective_of_quotientMap_surjective_of_isNilpotent (I := I) f.hom hquot hInil

/-- Helper for Lemma 15.76.3: a bounded-above derived `R`-module admits a bounded-above projective
representative. -/
lemma boundedAbove_projective_model_of_mem_t_minus
    (K : DModR)
    (hK : (t.minus : ObjectProperty DModR) K) :
    ∃ P : ProjectiveMinusR, K ≅ DerivedCategory.Q.obj (P : CpxR) := by
  let Kminus : D⁻(ModR) := ⟨K, hK⟩
  obtain ⟨b, hb⟩ :=
    boundedAbove_objPreimage_eventually_isZero_homology (𝒜 := ModR) Kminus
  obtain ⟨P⟩ :=
    nonempty_projectiveResolution_of_eventually_isZero_homology
      (K := DerivedCategory.Q.objPreimage K) ⟨b, hb⟩
  have hπ : IsIso (DerivedCategory.Q.map P.π) := by
    -- Proof comment: the projective-resolution comparison is a quasi-isomorphism, hence becomes
    -- an isomorphism in the derived category.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  exact ⟨P, (asIso (DerivedCategory.Q.map P.π)) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩

/-- Helper for Lemma 15.76.3: lower tor-amplitude is invariant under isomorphism in `D(R)`. -/
lemma hasTorAmplitudeGE_of_iso {K L : DModR} {a : ℤ} (e : K ≅ L) :
    HasTorAmplitudeGE K a ↔ HasTorAmplitudeGE L a := by
  -- Proof comment: transport the lower-bound vanishing condition across the tensor image of the
  -- chosen derived isomorphism.
  rw [hasTorAmplitudeGE_iff, hasTorAmplitudeGE_iff]
  constructor
  · intro h M i hi
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor ModR i).mapIso
          ((derivedTensorProduct (single₀R.obj M)).mapIso e.symm))
  · intro h M i hi
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor ModR i).mapIso
          ((derivedTensorProduct (single₀R.obj M)).mapIso e))

/-- Helper for Lemma 15.76.3: lower tor-amplitude for `Q(E)` forces ordinary homology of the
representative `E` to vanish below the lower bound. -/
lemma isZero_homology_of_hasTorAmplitudeGE_below
    (E : CpxR) (a i : ℤ)
    (hTor : HasTorAmplitudeGE (DerivedCategory.Q.obj E) a) (hi : i < a) :
    IsZero (E.homology i) := by
  let eUnit :=
    ((DerivedCategory.singleFunctorIsoCompQ ModR (0 : ℤ)).app (ModuleCat.of R R)) ≪≫
      ((DerivedCategory.quotientCompQhIso ModR).app
        ((CochainComplex.singleFunctor ModR (0 : ℤ)).obj (ModuleCat.of R R))).symm
  let eRing :
      (DerivedCategory.Q.obj E) ⊗[R]^L (single₀R.obj (ModuleCat.of R R)) ≅
        DerivedCategory.Q.obj E :=
    (derivedTensorProduct_comm (DerivedCategory.Q.obj E)
      (single₀R.obj (ModuleCat.of R R))) ≪≫
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        (single₀R.obj (ModuleCat.of R R)) (DerivedCategory.Q.obj E)).symm ≪≫
      whiskerRightIso eUnit (DerivedCategory.Q.obj E) ≪≫
      λ_ (DerivedCategory.Q.obj E)
  have hGEtensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L (single₀R.obj (ModuleCat.of R R))).IsGE a :=
    hTor (ModuleCat.of R R)
  rw [isGE_iff] at hGEtensor
  have hzero_tensor :
      IsZero
        ((DerivedCategory.homologyFunctor ModR i).obj
          ((DerivedCategory.Q.obj E) ⊗[R]^L (single₀R.obj (ModuleCat.of R R)))) := by
    -- Proof comment: evaluate lower tor-amplitude on the regular module `R`.
    exact hGEtensor i hi
  have hzero_Q :
      IsZero ((DerivedCategory.homologyFunctor ModR i).obj (DerivedCategory.Q.obj E)) :=
    hzero_tensor.of_iso
      ((DerivedCategory.homologyFunctor ModR i).mapIso eRing).symm
  -- Proof comment: compare derived homology of `Q(E)` with the ordinary homology of `E`.
  exact
    ((DerivedCategory.homologyFunctorFactors ModR i).app E).isZero_iff.1 hzero_Q

/-- Helper for Lemma 15.76.3: if the reduction modulo `I` of a derived object is zero, then the
source object has tor-amplitude in the empty interval `[1, 0]`. -/
lemma hasTorAmplitudeIn_empty_of_zero_nilpotent_baseChange
    (L : DModR)
    (hL : IsZero (L ⊗[R]^L[(R ⧸ I)]))
    (hInil : IsNilpotent I) :
    HasTorAmplitudeIn L 1 0 := by
  have hBase : HasTorAmplitudeIn (L ⊗[R]^L[(R ⧸ I)]) 1 0 :=
    hasTorAmplitudeIn_of_isZero (R := R ⧸ I) hL 1 0
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) :=
    Ideal.Quotient.mk_surjective
  -- Proof comment: descend the empty tor-amplitude interval across the nilpotent quotient map.
  exact
    (hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
      (R' := R) (R := R ⧸ I) hsurj (by simpa using hInil) L 1 0).1 hBase

/-- Helper for Lemma 15.76.3: if the shifted cohomology object `H^i(K)[-i]` has tor-amplitude in
the empty interval `[i + 1, i]`, then `H^i(K)` vanishes. -/
lemma isZero_homology_of_shiftedCohomology_empty_tor_amplitude
    (K : DModR) (i : ℤ)
    (hAmp : HasTorAmplitudeIn (shiftedCohomology ModR K i) (i + 1) i) :
    IsZero ((DerivedCategory.homologyFunctor ModR i).obj K) := by
  let E : CpxR :=
    (CochainComplex.singleFunctor ModR i).obj
      ((DerivedCategory.homologyFunctor ModR i).obj K)
  let eSingle : DerivedCategory.Q.obj E ≅ shiftedCohomology ModR K i :=
    (DerivedCategory.singleFunctorIsoCompQ ModR i).app
      ((DerivedCategory.homologyFunctor ModR i).obj K)
  have hGE : HasTorAmplitudeGE (shiftedCohomology ModR K i) (i + 1) :=
    hAmp.hasTorAmplitudeGE
  have hGE' : HasTorAmplitudeGE (DerivedCategory.Q.obj E) (i + 1) :=
    (hasTorAmplitudeGE_of_iso (I := I) eSingle).2 hGE
  have hzeroE : IsZero (E.homology i) :=
    isZero_homology_of_hasTorAmplitudeGE_below (I := I) E (i + 1) i hGE' (by omega)
  have hzeroQ :
      IsZero ((DerivedCategory.homologyFunctor ModR i).obj (DerivedCategory.Q.obj E)) :=
    hzeroE.of_iso ((DerivedCategory.homologyFunctorFactors ModR i).app E).symm
  have hzeroShift :
      IsZero ((DerivedCategory.homologyFunctor ModR i).obj (shiftedCohomology ModR K i)) :=
    hzeroQ.of_iso ((DerivedCategory.homologyFunctor ModR i).mapIso eSingle).symm
  -- Proof comment: `shiftedCohomology` is the canonical degree-`i` single object on `H^i(K)`.
  exact
    hzeroShift.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso ModR i).app
        ((DerivedCategory.homologyFunctor ModR i).obj K)).symm

/-- Helper for Lemma 15.76.3: once a strict quotient complex computes a bounded-above derived
object, its ordinary homology vanishes above the same cutoff. -/
lemma isZero_homology_of_strict_model_of_isLE
    (L : DModRI) (Pq : CpxRI) (e : DerivedCategory.Q.obj Pq ≅ L)
    {b i : ℤ} (hL : L.IsLE b) (hi : b < i) :
    IsZero (Pq.homology i) := by
  rw [DerivedCategory.isLE_iff] at hL
  have hzeroL : IsZero ((DerivedCategory.homologyFunctor ModRI i).obj L) := hL i hi
  have hzeroQ :
      IsZero ((DerivedCategory.homologyFunctor ModRI i).obj (DerivedCategory.Q.obj Pq)) :=
    -- Proof comment: transport quotient-side bounded-above vanishing across the chosen strict
    -- model comparison `Q(Pq) ≅ L`.
    hzeroL.of_iso ((DerivedCategory.homologyFunctor ModRI i).mapIso e).symm
  -- Proof comment: the standard comparison between derived homology of `Q(Pq)` and ordinary
  -- homology of `Pq` then turns the derived vanishing into the strict vanishing we need.
  exact ((DerivedCategory.homologyFunctorFactors ModRI i).app Pq).isZero_iff.1 hzeroQ

/-- Helper for Lemma 15.76.3: above a bounded-above cutoff, the successive upper truncation map
on the quotient-side object is already an isomorphism. -/
lemma truncLT_step_isIso_of_isLE
    (L : DModRI) {b i : ℤ}
    (hL : L.IsLE b) (hi : b < i) :
    IsIso ((t.natTransTruncLTOfLE i (i + 1) (by omega)).app L) := by
  have hLi : L.IsLE (i - 1) := by
    -- Proof comment: bounded-above membership is monotone in the cutoff, so `L ≤ b` upgrades to
    -- the smaller-stage bound `L ≤ i - 1`.
    rw [DerivedCategory.isLE_iff] at hL ⊢
    intro j hj
    exact hL j (lt_of_lt_of_le hj (by omega))
  have hLi' : L.IsLE i := by
    -- Proof comment: the same monotonicity also gives the bound needed for `τ_{< i + 1} L`.
    rw [DerivedCategory.isLE_iff] at hL ⊢
    intro j hj
    exact hL j (lt_of_lt_of_le hj (by omega))
  letI : IsIso ((t.truncLTι i).app L) :=
    (t.isLE_iff_isIso_truncLTι_app (i - 1) i (by omega) L).1 hLi
  letI : IsIso ((t.truncLTι (i + 1)).app L) :=
    (t.isLE_iff_isIso_truncLTι_app i (i + 1) (by omega) L).1 hLi'
  have hcomp :
      ((t.natTransTruncLTOfLE i (i + 1) (by omega)).app L) ≫
          (t.truncLTι (i + 1)).app L =
        (t.truncLTι i).app L := by
    -- Proof comment: this is the standard truncation naturality identity for consecutive stages.
    simpa using t.natTransTruncLTOfLE_ι_app i (i + 1) (by omega) L
  letI :
      IsIso
        (((t.natTransTruncLTOfLE i (i + 1) (by omega)).app L) ≫
          (t.truncLTι (i + 1)).app L) := by
    simpa [hcomp] using (show IsIso ((t.truncLTι i).app L) from inferInstance)
  exact IsIso.of_isIso_comp_right
    ((t.natTransTruncLTOfLE i (i + 1) (by omega)).app L)
    ((t.truncLTι (i + 1)).app L)

/-- Helper for Lemma 15.76.3: the derived image of a bounded-above projective complex is a
bounded-above derived object. -/
lemma q_obj_mem_t_minus_of_projectiveMinus
    {S : Type u} [CommRing S]
    (P : CochainComplex.ProjectiveMinus (ModuleCat S)) :
    (DerivedCategory.TStructure.t.minus :
      ObjectProperty (DerivedCategory (ModuleCat S)))
      (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat S) ℤ)) := by
  obtain ⟨b, hPb⟩ := P.exists_isStrictlyLE
  refine ⟨b, ?_⟩
  -- Proof comment: the strict upper support bound on `P` transfers directly to its derived image.
  change (DerivedCategory.Q.obj (P : CochainComplex (ModuleCat S) ℤ)).IsLE b
  exact (DerivedCategory.isLE_Q_obj_iff (P : CochainComplex (ModuleCat S) ℤ) b).2 inferInstance

/-- Helper for Lemma 15.76.3: derived reduction preserves the same upper cohomological bound on a
bounded-above object. -/
lemma derivedTensor_isLE_of_isLE
    (L : DModR) {c : ℤ}
    (hL : L.IsLE (c - 1)) :
    ((derivedTensorWithAlgebra (Ideal.Quotient.mk I)).obj L).IsLE (c - 1) := by
  have hLminus : (t.minus : ObjectProperty DModR) L := by
    refine (derivedCategory_t_minus_iff (K := L)).2 ?_
    refine ⟨c - 1, ?_⟩
    rw [isLE_iff] at hL
    intro j hj
    exact hL j hj
  obtain ⟨P, eP⟩ :=
    boundedAbove_projective_model_of_mem_t_minus (I := I) L hLminus
  have hQle : (DerivedCategory.Q.obj (P : CpxR)).IsLE (c - 1) := by
    let _ : L.IsLE (c - 1) := hL
    -- Proof comment: first transfer the truncation bound from `L` to the chosen bounded-above
    -- projective representative `P`.
    simpa using t.isLE_of_iso eP.symm (c - 1)
  have hPle : (P : CpxR).IsStrictlyLE (c - 1) := by
    -- Proof comment: on an honest cochain representative, the derived `IsLE` bound is exactly
    -- the strict upper support bound.
    rw [DerivedCategory.isLE_Q_obj_iff] at hQle
    exact hQle
  have hPflat : (P : CpxR).IsTermwiseFlat := by
    intro j
    let _ : Projective ((P : CpxR).X j) := P.term_mem j
    exact Module.Flat.of_projective
  let ReduceP : CpxRI :=
    ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj
      (P : CpxR))
  have hReducePle : ReduceP.IsStrictlyLE (c - 1) := by
    rw [CochainComplex.isStrictlyLE_iff] at hPle ⊢
    intro j hj
    -- Proof comment: degreewise scalar extension preserves zero terms in the bounded-above
    -- representative.
    simpa [ReduceP, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map_isZero (hPle j hj)
  let eReduce :
      ((derivedTensorWithAlgebra (Ideal.Quotient.mk I)).obj
          (DerivedCategory.Q.obj (P : CpxR))) ≅
        DerivedCategory.Q.obj ReduceP := by
    -- Proof comment: the bounded-above projective representative computes derived reduction
    -- termwise.
    simpa [ReduceP] using
      (derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
        (A := R) (B := R ⧸ I) (E := (P : CpxR)) hPflat hPle)
  have hReduceQle : (DerivedCategory.Q.obj ReduceP).IsLE (c - 1) := by
    -- Proof comment: the reduced strict representative stays strictly supported in degrees
    -- `≤ c - 1`, so its derived image lies in `D^{≤ c - 1}`.
    rw [DerivedCategory.isLE_Q_obj_iff]
    exact hReducePle
  have hReducedLE :
      ((derivedTensorWithAlgebra (Ideal.Quotient.mk I)).obj
        (DerivedCategory.Q.obj (P : CpxR))).IsLE (c - 1) := by
    let _ : (DerivedCategory.Q.obj ReduceP).IsLE (c - 1) := hReduceQle
    exact t.isLE_of_iso eReduce.symm (c - 1)
  let _ :
      ((derivedTensorWithAlgebra (Ideal.Quotient.mk I)).obj
        (DerivedCategory.Q.obj (P : CpxR))).IsLE (c - 1) := hReducedLE
  -- Proof comment: finally transport the bound back across the original representative
  -- isomorphism for `L`.
  exact t.isLE_of_iso ((derivedTensorWithAlgebra (Ideal.Quotient.mk I)).mapIso eP).symm (c - 1)

/-- Helper for Lemma 15.76.3: bounded-above membership descends from the nilpotent quotient
derived base change back to the original derived object. -/
lemma derivedTensor_mem_t_minus_of_nilpotent_quotient
    (K : DModR)
    (hKred : (t.minus : ObjectProperty DModRI) (K ⊗[R]^L[(R ⧸ I)]))
    (hInil : IsNilpotent I) :
    (t.minus : ObjectProperty DModR) K := by
  -- Route correction: the truncation-step descent detour obscured the source proof.
  -- The textbook route uses bounded-above descent across the nilpotent quotient directly,
  -- after observing that `K ⊗[R]^L (R ⧸ I)` is already in `D⁻(R ⧸ I)`.
  -- TODO: apply the dependency-closed bounded-above descent theorem for derived reduction along
  -- `R → R ⧸ I`, with surjective structure map and nilpotent kernel `I`.
  sorry

/-- Lemma 15.76.3: let `R` be a ring, let `I ⊆ R` be a nilpotent ideal, let `E^•` be a bounded-
above complex of projective `R / I`-modules, and let `K` be an object of `D(R)`. If a
derived reduction `K \otimes_R^{\mathbf L} (R / I)` is represented by `E^•`, then there exists a
bounded-above complex `P^•` of projective `R`-modules together with comparison isomorphisms
`K \cong Q(P^•)` and `P^•/IP^• \cong E^•`. -/
theorem exists_boundedAbove_projective_representative_lifting_mod_nilpotent
    (K : DModR) (E : ProjectiveMinusRI)
    (hErep : IsIsomorphic (K ⊗[R]^L[(R ⧸ I)]) (DerivedCategory.Q.obj (E : CpxRI)))
    (hInil : IsNilpotent I) :
    ∃ P : ProjectiveMinusR,
      IsIsomorphic K (DerivedCategory.Q.obj (P : CpxR)) ∧
        IsIsomorphic
          ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ)).obj
            (P : CpxR))
          (E : CpxRI) := by
  let Emap :=
    projective_reduction_image_complex (I := I) E hInil
  have hQminus : (t.minus : ObjectProperty DModRI) (DerivedCategory.Q.obj (E : CpxRI)) := by
    -- Proof comment: bounded-above projective representatives land in `D^-` after applying `Q`.
    exact q_obj_mem_t_minus_of_projectiveMinus (P := E)
  have hKredMinus : (t.minus : ObjectProperty DModRI) (K ⊗[R]^L[(R ⧸ I)]) := by
    rcases hErep with ⟨e⟩
    -- Proof comment: transport bounded-above membership across the chosen comparison isomorphism.
    exact (t.minus : ObjectProperty DModRI).prop_of_iso e.symm hQminus
  have hKminus : (t.minus : ObjectProperty DModR) K :=
    derivedTensor_mem_t_minus_of_nilpotent_quotient (I := I) K hKredMinus hInil
  obtain ⟨P₀, eK₀⟩ :=
    boundedAbove_projective_model_of_mem_t_minus (I := I) K hKminus
  have hprojective : ∀ ⦃P : ModR⦄, (isProjective ModR) P → Projective P := by
    intro P hP
    exact hP
  have hsurj :
      ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
        (isProjective ModR) P₁ → (isProjective ModR) P₂ →
          Function.Surjective ((ReduceModI.map f).hom) →
            Function.Surjective f.hom := by
    intro P₁ P₂ f _ _
    exact projective_surjective_of_reduceModI_surjective (I := I) hInil f
  obtain ⟨P, eK, eE⟩ :=
    exists_boundedAbove_representative_lifting_derivedReduction
      (I := I) (PClass := isProjective ModR) hprojective hsurj K Emap
      (by simpa using hErep) ⟨P₀, eK₀⟩
  -- Proof comment: the generic lifting theorem already returns the desired representative and the
  -- two concrete isomorphisms; only the Prop-level packaging remains.
  exact ⟨P, ⟨eK⟩, ⟨eE⟩⟩

end

end CategoryTheory
