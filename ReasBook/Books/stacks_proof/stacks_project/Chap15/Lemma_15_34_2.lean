import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Lemma_10_134_2
import stacks_proof.stacks_project.Chap10.Lemma_10_136_13
import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Lemma_10_158_11
import stacks_proof.stacks_project.Chap15.Definition_15_33_2
import stacks_proof.stacks_project.Chap15.Lemma_15_4_3
import stacks_proof.stacks_project.Chap15.Lemma_15_33_5
import stacks_proof.stacks_project.Chap15.Lemma_15_33_6
import stacks_proof.stacks_project.Chap15.Lemma_15_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u

namespace Algebra

section

variable {K L M : Type u}
variable [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/- Domain triage:
* primary domain: the Jacobi-Zariski sequence for a tower of field extensions `K → L → M`;
* sampled owner declarations:
  - `Algebra.H1Cotangent.exact_map_δ`,
  - `Algebra.H1Cotangent.exact_δ_mapBaseChange`,
  - `KaehlerDifferential.exact_mapBaseChange_map`,
  - `KaehlerDifferential.map_surjective`;
* best owner abstraction: the source-facing sequence is already organized by the canonical owner
  maps `H1Cotangent.map`, `H1Cotangent.δ`, `KaehlerDifferential.mapBaseChange`, and
  `KaehlerDifferential.map`, so the middle exactness and terminal surjectivity belong directly to
  those owners rather than to a new local wrapper;
* primitive data vs. derived API:
  - primitive data: the tower of fields `K → L → M`;
  - derived API: the Jacobi-Zariski exactness/surjectivity on the owner maps, plus the extra
    left-injectivity that is special to the field case;
* layer triage:
  - `source-facing`: Lemma `15.34.2`, namely the same Jacobi-Zariski sequence with zero terms
    adjoined on the left and right;
  - `core/canonical`: the four owner exactness/surjectivity theorems listed above;
  - `bridge/view`: no extra bridge is needed beyond the left-injectivity theorem below.

The old `FieldJacobiZariskiExactSequenceWithZeroEnds` structure duplicated owner declarations
without adding new mathematical data, so this file is refined to direct recall/use of the
canonical owners and one theorem for the genuinely new left edge.
-/

/- Lemma 15.34.2: the middle part
`H₁(L_{M/K}) → H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K]`
is exactly `Algebra.H1Cotangent.exact_map_δ` specialized to the tower `K → L → M`. -/
recall Algebra.H1Cotangent.exact_map_δ

/- Lemma 15.34.2: the next part
`H₁(L_{M/L}) → M ⊗[L] Ω[L⁄K] → Ω[M⁄K]`
is exactly `Algebra.H1Cotangent.exact_δ_mapBaseChange`. -/
recall Algebra.H1Cotangent.exact_δ_mapBaseChange

/- Lemma 15.34.2: the Kähler-differential tail
`M ⊗[L] Ω[L⁄K] → Ω[M⁄K] → Ω[M⁄L]`
is exactly `KaehlerDifferential.exact_mapBaseChange_map`. -/
recall KaehlerDifferential.exact_mapBaseChange_map

/- Lemma 15.34.2: the terminal map `Ω[M⁄K] → Ω[M⁄L]` is the canonical surjective map
`KaehlerDifferential.map_surjective`. -/
recall KaehlerDifferential.map_surjective

-- Proof sketch: the source proof factors the leftmost map through the tensorized kernel of the
-- self-presentation of `L/K`, then applies the left-extended Jacobi-Zariski theorem for filtered
-- colimits of local complete intersections. In the current workspace, that final owner theorem is
-- downstream of `Chap15/Lemma_15_28_7`, which is presently broken, so this file records the
-- source-kernel transport cleanly and isolates the remaining closure step below.

/-- Helper for Lemma 15.34.2: tensoring the self-presentation kernel of `L/K` up to `M` still
lands in the kernel of the tensorized self-presentation differential. -/
theorem self_presentation_source_to_kernel_mem
    (x : M ⊗[L] H1Cotangent K L) :
    (((LinearMap.ker (Generators.self K L).toExtension.cotangentComplex).subtype).baseChange M
        ((LinearMap.baseChange M
          ((Generators.self K L).equivH1Cotangent.symm.toLinearMap)) x)) ∈
      LinearMap.ker
        (LinearMap.baseChange M (Generators.self K L).toExtension.cotangentComplex) := by
  let d := (Generators.self K L).toExtension.cotangentComplex
  let i : LinearMap.ker d →ₗ[L] (Generators.self K L).toExtension.Cotangent :=
    (LinearMap.ker d).subtype
  have hzero : d ∘ₗ i = 0 := by
    -- The subtype inclusion of a kernel always composes trivially with the ambient map.
    ext y
    exact y.2
  have hbase :
      (LinearMap.baseChange M d) ∘ₗ (LinearMap.baseChange M i) = 0 := by
    -- Tensor the vanishing composite once, then rewrite it as a composite of tensorized maps.
    have hbase' : LinearMap.baseChange M (d ∘ₗ i) = 0 := by
      simpa [hzero] using congrArg (LinearMap.baseChange M) hzero
    rw [← LinearMap.baseChange_comp]
    exact hbase'
  rw [LinearMap.mem_ker]
  -- Apply the tensorized zero-composite identity to the transported source element.
  simpa [d, i, LinearMap.comp_apply] using
    LinearMap.congr_fun hbase
      ((LinearMap.baseChange M ((Generators.self K L).equivH1Cotangent.symm.toLinearMap)) x)

/-- Helper for Lemma 15.34.2: the source term `M ⊗[L] H₁(L_{L/K})` maps canonically to the kernel
of the tensorized self-presentation differential of `L/K`. -/
noncomputable def self_presentation_source_to_kernel_baseChange :
    M ⊗[L] H1Cotangent K L →ₗ[M]
      LinearMap.ker (LinearMap.baseChange M (Generators.self K L).toExtension.cotangentComplex) :=
  LinearMap.codRestrict
    (LinearMap.ker (LinearMap.baseChange M (Generators.self K L).toExtension.cotangentComplex))
    ((((LinearMap.ker (Generators.self K L).toExtension.cotangentComplex).subtype).baseChange M)
      ∘ₗ
        (LinearMap.baseChange M ((Generators.self K L).equivH1Cotangent.symm.toLinearMap)))
    (self_presentation_source_to_kernel_mem (K := K) (L := L) (M := M))

/-- Helper for Lemma 15.34.2: the canonical map from
`M ⊗[L] H₁(L_{L/K})` into the tensorized self-presentation kernel is injective because `M` is
flat over the field `L`. -/
theorem self_presentation_source_to_kernel_baseChange_injective :
    Function.Injective
      (self_presentation_source_to_kernel_baseChange (K := K) (L := L) (M := M)) := by
  have hEquivBaseChange :
      Function.Injective
        (LinearMap.baseChange M ((Generators.self K L).equivH1Cotangent.symm.toLinearMap)) := by
    -- Flatness preserves injectivity of the tensorized self-presentation `H₁` identification.
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := M)
        ((Generators.self K L).equivH1Cotangent.symm.toLinearMap)
        (Generators.self K L).equivH1Cotangent.symm.injective)
  have hSubtypeBaseChange :
      Function.Injective
        (((LinearMap.ker (Generators.self K L).toExtension.cotangentComplex).subtype).baseChange
          M) := by
    -- The tensorized subtype inclusion of the source kernel remains injective after base change.
    simpa [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := M)
        ((LinearMap.ker (Generators.self K L).toExtension.cotangentComplex).subtype)
        (Submodule.injective_subtype _))
  intro x y hxy
  apply hEquivBaseChange
  apply hSubtypeBaseChange
  exact congrArg Subtype.val hxy

/-- Helper for Lemma 15.34.2: on the self-presentation of `L/K`, the comparison through the
composite self-presentation of `M/K` computes the canonical owner map `H1Cotangent.map K K L M`.
-/
theorem self_presentation_owner_map_apply (x : H1Cotangent K L) :
    ((Generators.self L M).comp (Generators.self K L)).equivH1Cotangent
        (Extension.H1Cotangent.map
          (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom)
          ((Generators.self K L).equivH1Cotangent.symm x)) =
      H1Cotangent.map K K L M x := by
  -- Unfold only the linear-equivalence wrappers; the rest is functoriality of `H₁`.
  simp [H1Cotangent.map, Generators.equivH1Cotangent, Generators.H1Cotangent.equiv,
    Extension.H1Cotangent.equiv]
  have htoComp :
      Extension.H1Cotangent.map
          (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom)
          (Extension.H1Cotangent.map
            ((Generators.defaultHom (Generators.self K L) (Generators.self K L)).toExtensionHom) x) =
        Extension.H1Cotangent.map
          (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom) x := by
    -- The inverse half of the self-presentation equivalence is another map between the same
    -- self-presentations, hence it is identified with the identity by `map_eq`.
    have hcomp :
        Extension.H1Cotangent.map
            ((((Generators.self L M).toComp (Generators.self K L)).toExtensionHom).comp
              ((Generators.defaultHom (Generators.self K L) (Generators.self K L)).toExtensionHom))
            x =
          Extension.H1Cotangent.map
            (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom) x := by
      exact DFunLike.congr_fun (Extension.H1Cotangent.map_eq _ _) x
    exact
      (Extension.H1Cotangent.map_comp_apply
        ((Generators.defaultHom (Generators.self K L) (Generators.self K L)).toExtensionHom)
        (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom)
        x).symm.trans hcomp
  rw [htoComp]
  have hcomp :
      Extension.H1Cotangent.map
          (((Generators.defaultHom ((Generators.self L M).comp (Generators.self K L))
                (Generators.self K M)).toExtensionHom).comp
            (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom))
          x =
        Extension.H1Cotangent.map
          ((Generators.defaultHom (Generators.self K L) (Generators.self K M)).toExtensionHom)
          x := by
    -- The composite presentation morphism and the canonical direct owner map have the same source
    -- and target, so `map_eq` identifies their `H₁` actions.
    exact DFunLike.congr_fun (Extension.H1Cotangent.map_eq _ _) x
  exact
    (Extension.H1Cotangent.map_comp_apply
      (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom)
      ((Generators.defaultHom ((Generators.self L M).comp (Generators.self K L))
        (Generators.self K M)).toExtensionHom)
      x).symm.trans hcomp

/-- Helper for Lemma 15.34.2: the self-presentation comparison map computes the left edge of the
field-case Jacobi-Zariski sequence after transporting the source into the tensorized kernel. -/
theorem self_presentation_left_map_eq_liftBaseChange_h1_map :
    (tensor_presentation_cotangent_h1_to_h1_cotangent M (Generators.self K L)).comp
        (self_presentation_source_to_kernel_baseChange (K := K) (L := L) (M := M)) =
      LinearMap.liftBaseChange M (H1Cotangent.map K K L M) := by
  -- Compare the two `M`-linear maps on pure tensors and extend by bilinearity.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [self_presentation_source_to_kernel_baseChange]
  · intro m y
    -- On a pure tensor, the source-kernel transport followed by the presentation map is exactly
    -- the owner comparison from `self_presentation_owner_map_apply`.
    change
      ((Generators.self L M).comp (Generators.self K L)).equivH1Cotangent
          (m •
            Extension.H1Cotangent.map
              (((Generators.self L M).toComp (Generators.self K L)).toExtensionHom)
              ((Generators.self K L).equivH1Cotangent.symm y)) =
        m • H1Cotangent.map K K L M y
    rw [map_smul]
    exact congrArg (fun z : H1Cotangent K M ↦ m • z)
      (self_presentation_owner_map_apply (K := K) (L := L) (M := M) y)
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Lemma 15.34.2: once the self-presentation map into `H₁(L_{M/K})` is injective,
the source-facing left Jacobi-Zariski map is injective as well. -/
theorem field_jacobi_zariski_left_injective_of_presentation_injective
    (hPresentation :
      Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent M (Generators.self K L))) :
    Function.Injective (LinearMap.liftBaseChange M (H1Cotangent.map K K L M)) := by
  -- Route correction: the remaining field-case work is isolated in the presentation-level map, so
  -- the source-facing owner map follows by composing with the already-proved source-kernel
  -- injection and rewriting the composite once.
  intro x y hxy
  apply self_presentation_source_to_kernel_baseChange_injective (K := K) (L := L) (M := M)
  apply hPresentation
  have hxy' :
      ((tensor_presentation_cotangent_h1_to_h1_cotangent M (Generators.self K L)).comp
          (self_presentation_source_to_kernel_baseChange (K := K) (L := L) (M := M))) x =
        ((tensor_presentation_cotangent_h1_to_h1_cotangent M (Generators.self K L)).comp
          (self_presentation_source_to_kernel_baseChange (K := K) (L := L) (M := M))) y := by
    simpa [self_presentation_left_map_eq_liftBaseChange_h1_map (K := K) (L := L) (M := M)] using
      hxy
  simpa [LinearMap.comp_apply] using hxy'

/-- Helper for Lemma 15.34.2: the residue field at a prime of the base field is canonically the
base field itself. -/
private noncomputable def field_prime_residueField_algEquiv_self
    {A : Type u} [CommRing A] [Algebra L A] (p : PrimeSpectrum L) :
    p.asIdeal.ResidueField ≃ₐ[L] L := by
  let φ : L →ₐ[L] p.asIdeal.ResidueField := IsScalarTower.toAlgHom L L p.asIdeal.ResidueField
  have hκ : Function.Bijective φ := by
    constructor
    · exact RingHom.injective _
    · simpa using (Ideal.algebraMap_residueField_surjective p.asIdeal)
  exact (AlgEquiv.ofBijective φ hκ).symm

/-- Helper for Lemma 15.34.2: every fiber of an `L`-algebra over a prime of the field `L` is
canonically identified with the algebra itself. -/
private noncomputable def field_prime_fiber_algEquiv_self
    {A : Type u} [CommRing A] [Algebra L A] (p : PrimeSpectrum L) :
    p.asIdeal.Fiber A ≃ₐ[L] A :=
  (Algebra.TensorProduct.congr
      (field_prime_residueField_algEquiv_self (L := L) (A := A) p)
      (AlgEquiv.refl : A ≃ₐ[L] A)).trans
    (Algebra.TensorProduct.lid L A)

/-- Helper for Lemma 15.34.2: over a field base, every fiber of an `L`-algebra has the same
Krull dimension as the algebra itself. -/
private theorem ringKrullDim_field_fiber_eq
    {A : Type u} [CommRing A] [Algebra L A] (p : PrimeSpectrum L) :
    ringKrullDim (p.asIdeal.Fiber A) = ringKrullDim A := by
  -- Compare the fiber directly with the source algebra before invoking any relative-CI owner.
  simpa using
    ringKrullDim_eq_of_ringEquiv
      (field_prime_fiber_algEquiv_self (L := L) (A := A) p).toRingEquiv

/-- Helper for Lemma 15.34.2: over a field base, a global complete intersection algebra is already
relative global complete intersection. -/
theorem globalCompleteIntersection_isRelativeGlobalCompleteIntersection_over_field
    {A : Type u} [CommRing A] [Nontrivial A] [Algebra L A]
    [IsGlobalCompleteIntersection L A] :
    Algebra.IsRelativeGlobalCompleteIntersection L A := by
  rcases (show IsGlobalCompleteIntersection L A from inferInstance).presentation_or_subsingleton with
    hsub | ⟨n, c, P, hP⟩
  · exfalso
    exact one_ne_zero (Subsingleton.elim (1 : A) 0)
  · refine Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P) ?_
    intro p _hp
    -- Over a field base, every nonempty fiber is another copy of the stage algebra.
    calc
      ringKrullDim (p.asIdeal.Fiber A) = ringKrullDim A :=
        ringKrullDim_field_fiber_eq (L := L) (A := A) p
      _ = P.dimension := hP

/-- Helper for Lemma 15.34.2: a global-complete-intersection stage over a field packages into the
Chapter 15 ring-hom local complete intersection owner. -/
theorem globalCompleteIntersection_packages_ringHom_isLocalCompleteIntersection
    {A : Type u} [CommRing A] [Nontrivial A] [Algebra L A]
    [IsGlobalCompleteIntersection L A] :
    RingHom.IsLocalCompleteIntersection (algebraMap L A) := by
  -- The field-base relative-GCI bridge upgrades the stage to a syntomic map, and Lemma `15.33.5`
  -- then extracts the local-complete-intersection component of syntomicity.
  have hrel : Algebra.IsRelativeGlobalCompleteIntersection L A :=
    globalCompleteIntersection_isRelativeGlobalCompleteIntersection_over_field (L := L) (A := A)
  have hsyntomic : (algebraMap L A).Syntomic :=
    Algebra.IsRelativeGlobalCompleteIntersection.syntomic hrel
  exact (RingHom.Syntomic.iff_flat_and_isLocalCompleteIntersection (algebraMap L A)).mp
    hsyntomic |>.2

/-- Helper for Lemma 15.34.2: the base field is a global complete intersection over itself. -/
private theorem field_self_isGlobalCompleteIntersection :
    IsGlobalCompleteIntersection L L := by
  let e0 : Fin 0 ≃ PEmpty.{1} :=
    { toFun := Fin.elim0
      invFun := PEmpty.elim
      left_inv := fun i ↦ Fin.elim0 i
      right_inv := fun x : PEmpty.{1} ↦ PEmpty.elim x }
  let P : Algebra.Presentation L L (Fin 0) (Fin 0) :=
    (Algebra.Presentation.ofBijectiveAlgebraMap (R := L) (S := L)
        ⟨(algebraMap L L).injective, fun x ↦ ⟨x, rfl⟩⟩).reindex e0 e0
  refine
    { presentation_or_subsingleton := Or.inr ⟨0, 0, P, ?_⟩ }
  have hPdim : P.dimension = 0 := by
    simp [P, Algebra.Presentation.ofBijectiveAlgebraMap_dimension]
  rw [hPdim]
  exact ringKrullDim_eq_zero_of_field L

/-- Helper for Lemma 15.34.2: the bottom `L`-subalgebra of the ambient field is itself a global
complete intersection over `L`. -/
private theorem bot_subalgebra_isGlobalCompleteIntersection :
    IsGlobalCompleteIntersection L ↥(⊥ : Subalgebra L M) := by
  -- Transport the trivial complete-intersection presentation of `L` along the canonical bottom
  -- subalgebra equivalence.
  exact IsGlobalCompleteIntersection.of_algEquiv
    (field_self_isGlobalCompleteIntersection (L := L))
    (Algebra.botEquiv L M).symm

/-- Helper for Lemma 15.34.2: adjoining the bottom stage makes a directed local-complete-
intersection subalgebra family nonempty without changing its supremum. -/
theorem directed_lci_subalgebra_family_with_bottom_stage
    {ι : Type u} (S : ι → Subalgebra L M) (hdir : Directed (· ≤ ·) S)
    (hLCI : ∀ i, RingHom.IsLocalCompleteIntersection (algebraMap L ↥(S i)))
    (hSup : iSup S = (⊤ : Subalgebra L M)) :
    let T : Option ι → Subalgebra L M := fun a ↦ Option.elim a ⊥ S
    Directed (· ≤ ·) T ∧
      (∀ a, RingHom.IsLocalCompleteIntersection (algebraMap L ↥(T a))) ∧
      iSup T = (⊤ : Subalgebra L M) := by
  let T : Option ι → Subalgebra L M := fun a ↦ Option.elim a ⊥ S
  have hbotLCI : RingHom.IsLocalCompleteIntersection (algebraMap L ↥(⊥ : Subalgebra L M)) := by
    letI : IsGlobalCompleteIntersection L ↥(⊥ : Subalgebra L M) :=
      bot_subalgebra_isGlobalCompleteIntersection (L := L) (M := M)
    exact globalCompleteIntersection_packages_ringHom_isLocalCompleteIntersection
      (L := L) (A := ↥(⊥ : Subalgebra L M))
  refine ⟨?_, ?_, ?_⟩
  · -- The adjoined bottom stage is initial for inclusions, and the original family stays
    -- directed on the `some` branch.
    intro a b
    cases a with
    | none =>
        refine ⟨b, ?_, le_rfl⟩
        cases b with
        | none => exact le_rfl
        | some j => exact bot_le
    | some i =>
        cases b with
        | none => exact ⟨some i, le_rfl, bot_le⟩
        | some j =>
            rcases hdir i j with ⟨k, hik, hjk⟩
            exact ⟨some k, hik, hjk⟩
  · -- The new stage property is the old one on the `some` branch, and the bottom stage uses the
    -- explicit complete-intersection presentation above.
    intro a
    cases a with
    | none =>
        simpa [T] using hbotLCI
    | some i =>
        simpa [T] using hLCI i
  · -- The added bottom stage contributes no new elements, so the supremum stays `⊤`.
    apply le_antisymm le_top
    calc
      (⊤ : Subalgebra L M) = iSup S := hSup.symm
      _ ≤ iSup T := by
        refine iSup_le ?_
        intro i
        exact le_iSup T (some i)

/-- Helper for Lemma 15.34.2: the field-extension presentation input for Lemma `15.33.7`, kept as
the source-facing wrapper now that the upstream theorem compiles in the current workspace. -/
private abbrev algebraMap_isFilteredColimitOfLocalCompleteIntersection_core : Prop :=
  (algebraMap L M).IsFilteredColimitOfLocalCompleteIntersection

/-- Helper for Lemma 15.34.2: Koszul-regularity is invariant under transport by a ring
equivalence. -/
theorem isKoszulRegularIdeal_map_ringEquiv_iff
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (I : Ideal A) :
    I.IsKoszulRegularIdeal ↔ (I.map e.toRingHom).IsKoszulRegularIdeal := by
  constructor
  · intro hI
    let _ : Algebra B A := e.symm.toRingHom.toAlgebra
    have hff : (algebraMap B A).FaithfullyFlat := by
      -- A ring equivalence is faithfully flat when read as an algebra map.
      simpa [RingHom.algebraMap_toAlgebra] using
        (RingHom.FaithfullyFlat.of_bijective e.symm.bijective :
          e.symm.toRingHom.FaithfullyFlat)
    have hmap :
        Ideal.map (algebraMap B A) (I.map e.toRingHom) = I := by
      -- Mapping along the inverse equivalence recovers the original ideal.
      calc
        Ideal.map (algebraMap B A) (I.map e.toRingHom) =
            Ideal.map e.symm.toRingHom (I.map e.toRingHom) := by
              simp [RingHom.algebraMap_toAlgebra]
        _ = Ideal.comap e.toRingHom (I.map e.toRingHom) := by
              simpa using
                (Ideal.map_comap_of_equiv (f := e.symm) (I := I.map e.toRingHom))
        _ = I := by
              simpa using
                (Ideal.comap_map_of_bijective e.toRingHom e.bijective (I := I))
    -- Descend the transported ideal along the inverse equivalence.
    have htransport :
        (Ideal.map (algebraMap B A) (I.map e.toRingHom)).IsKoszulRegularIdeal := by
      rw [hmap]
      exact hI
    exact Ideal.IsKoszulRegularIdeal.of_faithfullyFlat hff htransport
  · intro hI
    let _ : Algebra A B := e.toRingHom.toAlgebra
    have hff : (algebraMap A B).FaithfullyFlat := by
      -- The forward equivalence is likewise faithfully flat.
      simpa [RingHom.algebraMap_toAlgebra] using
        (RingHom.FaithfullyFlat.of_bijective e.bijective :
          e.toRingHom.FaithfullyFlat)
    have htransport :
        (Ideal.map (algebraMap A B) I).IsKoszulRegularIdeal := by
      -- The mapped ideal is definitionally the ideal transported by `e`.
      simpa [RingHom.algebraMap_toAlgebra] using hI
    exact Ideal.IsKoszulRegularIdeal.of_faithfullyFlat hff htransport

/-- Helper for Lemma 15.34.2: the canonical `ULift` algebra map is exactly the `RingHom.ulift`
of the original algebra map. -/
theorem ulift_algebraMap_eq_ringHom_ulift
    {A : Type u} [CommRing A] [Algebra L A] :
    let _ : Algebra (ULift.{u} L) (ULift.{u} A) := ULift.algebra' L (ULift.{u} A)
    algebraMap (ULift.{u} L) (ULift.{u} A) = RingHom.ulift (algebraMap L A) := by
  let _ : Algebra (ULift.{u} L) (ULift.{u} A) := ULift.algebra' L (ULift.{u} A)
  -- Both ring maps send `ULift.up x` to `ULift.up (algebraMap L A x)`.
  ext x
  cases x
  rfl

/-- Helper for Lemma 15.34.2: `RingHom.ulift f` is the composite of the source `ULift`
equivalence, the original map `f`, and the target `ULift` equivalence. -/
theorem ringHom_ulift_eq_target_comp_source
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    RingHom.ulift f =
      ((ULift.ringEquiv.symm : B ≃+* ULift.{u} B).toRingHom).comp
        (f.comp ((ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom)) := by
  -- Compare both ring homomorphisms on a lifted element; they compute the same `ULift.up` value.
  ext x
  cases x
  rfl

/-- Helper for Lemma 15.34.2: local-complete-intersection algebra maps are preserved by the
canonical `ULift` source and target equivalences. -/
theorem isLocalCompleteIntersection_ulift_algebraMap
    {A : Type u} [CommRing A] [Algebra L A]
    (h : RingHom.IsLocalCompleteIntersection (algebraMap L A)) :
    RingHom.IsLocalCompleteIntersection (RingHom.ulift (algebraMap L A)) := by
  -- Route correction: abandon the unavailable owner-level `Syntomic.comp` transport. The source
  -- proof stays presentation-theoretic: extract a finite polynomial witness for `algebraMap L A`,
  -- transport its kernel across the coefficient equivalence
  -- `MvPolynomial.mapAlgEquiv (Fin n) (ULift.algEquiv : ULift L ≃ₐ[ULift L] L)`, apply
  -- `isKoszulRegularIdeal_map_ringEquiv_iff`, and then package the resulting lifted witness for
  -- `RingHom.ulift (algebraMap L A)`.
  letI : Algebra L A := (algebraMap L A).toAlgebra
  rcases h.exists_generators_ker_isKoszulRegular with ⟨n, P, hker⟩
  letI : Algebra (ULift.{u} L) L := ULift.ringEquiv.toRingHom.toAlgebra
  letI : Algebra (ULift.{u} L) P.Ring := ULift.algebra' L P.Ring
  letI : Algebra (ULift.{u} L) A := ULift.algebra' L A
  letI : Algebra P.Ring A := (algebraMap P.Ring A).toAlgebra
  letI : IsScalarTower (ULift.{u} L) P.Ring A := by
    -- The lifted base acts on the chosen polynomial presentation through the original coefficient
    -- map `L → P.Ring`, and this action agrees with the target action on `A`.
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    cases x with
    | up x =>
        have hright :
            ((algebraMap P.Ring A).comp (algebraMap (ULift.{u} L) P.Ring)) (ULift.up x) =
              algebraMap L A x := by
          rw [P.algebraMap_eq]
          simp
        simpa using hright.symm
  letI : Algebra (ULift.{u} L) (ULift.{u} A) :=
    (RingHom.ulift (algebraMap L A)).toAlgebra
  let ePoly : MvPolynomial (Fin n) (ULift.{u} L) ≃ₐ[ULift.{u} L] P.Ring :=
    MvPolynomial.mapAlgEquiv (Fin n)
      (ULift.algEquiv : ULift.{u} L ≃ₐ[ULift.{u} L] L)
  let alpha : P.Ring →ₐ[ULift.{u} L] A :=
    IsScalarTower.toAlgHom (ULift.{u} L) P.Ring A
  let alphaUp : MvPolynomial (Fin n) (ULift.{u} L) →ₐ[ULift.{u} L] ULift.{u} A :=
    (((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{u} L] A).symm.toAlgHom).comp alpha).comp
      ePoly.toAlgHom
  have hsurj : Function.Surjective alphaUp := by
    intro a
    rcases P.algebraMap_surjective a.down with ⟨p, hp⟩
    refine ⟨ePoly.symm p, ?_⟩
    -- First solve the equation in `A`, then lift it back to `ULift A`.
    cases a with
    | up down =>
        have hp' : (algebraMap P.Ring A) p = down := by
          change (algebraMap P.Ring A) p = ({ down := down } : ULift.{u} A).down
          exact hp
        change ULift.up ((alpha.comp ePoly.toAlgHom) (ePoly.symm p)) = ULift.up down
        exact congrArg ULift.up <| by
          simpa [alpha, IsScalarTower.coe_toAlgHom] using hp'
  let Q : Generators (ULift.{u} L) (ULift.{u} A) (Fin n) := Generators.ofAlgHom alphaUp hsurj
  have hkerAlpha : RingHom.ker alpha.toRingHom = P.ker := by
    -- The intermediate map `alpha` is just the presentation algebra map viewed over `ULift L`.
    simpa [alpha, IsScalarTower.coe_toAlgHom] using
      (show RingHom.ker (algebraMap P.Ring A) = P.ker by rfl)
  have hkerTgt :
      RingHom.ker alphaUp.toRingHom = RingHom.ker ((alpha.toRingHom).comp ePoly.toRingHom) := by
    -- Composing with the target `ULift` equivalence does not change the kernel.
    simpa [alphaUp, RingHom.comp_assoc] using
      (RingHom.ker_equiv_comp ((alpha.toRingHom).comp ePoly.toRingHom)
        ((ULift.algEquiv : ULift.{u} A ≃ₐ[ULift.{u} L] A).symm.toRingEquiv))
  have hkerSrc :
      RingHom.ker ((alpha.toRingHom).comp ePoly.toRingHom) = Ideal.comap ePoly.toRingHom P.ker := by
    -- The remaining kernel is the pullback of the original presentation kernel along `ePoly`.
    calc
      RingHom.ker ((alpha.toRingHom).comp ePoly.toRingHom) =
          Ideal.comap ePoly.toRingHom (RingHom.ker alpha.toRingHom) := by
            rw [RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot]
            simpa using (RingHom.comap_ker alpha.toRingHom ePoly.toRingHom).symm
      _ = Ideal.comap ePoly.toRingHom P.ker := by
            rw [hkerAlpha]
  have hkerMap :
      Ideal.comap ePoly.toRingHom P.ker = Ideal.map ePoly.symm.toRingHom P.ker := by
    -- For a ring equivalence, comap along `ePoly` is map along its inverse.
    simpa using
      (Ideal.map_comap_of_equiv (f := ePoly.symm.toRingEquiv) (I := P.ker)).symm
  have hQker :
      Q.ker = Ideal.map ePoly.symm.toRingHom P.ker := by
    -- Rewrite the kernel of the lifted presentation into the transported original kernel ideal.
    rw [Generators.ker_ofAlgHom alphaUp hsurj, hkerTgt, hkerSrc, hkerMap]
  have hQkoszul :
      Q.ker.IsKoszulRegularIdeal := by
    -- The earlier ring-equivalence transport lemma moves Koszul regularity across `ePoly.symm`.
    rw [hQker]
    exact
      (isKoszulRegularIdeal_map_ringEquiv_iff
        (e := ePoly.symm.toRingEquiv) (I := P.ker)).1 hker
  have hUlift :
      RingHom.IsLocalCompleteIntersection (algebraMap (ULift.{u} L) (ULift.{u} A)) := by
    -- Package the transported finite polynomial presentation into the Chapter 15 owner.
    refine RingHom.IsLocalCompleteIntersection.mk ?_
    exact ⟨n, Q, hQkoszul⟩
  -- Replace the lifted algebra map by the actual `RingHom.ulift` of the original structure map.
  simpa [ulift_algebraMap_eq_ringHom_ulift (L := L) (A := A)] using hUlift

/-- Helper for Lemma 15.34.2: in a nonempty directed family of `L`-subalgebras with supremum
`⊤`, every finite subset of the ambient field already lies in one stage. -/
private lemma exists_stage_subalgebra_contains_finset
    {ι : Type*} [Nonempty ι] (T : ι → Subalgebra L M) (hdir : Directed (· ≤ ·) T)
    (hSup : iSup T = (⊤ : Subalgebra L M)) (s : Finset M) :
    ∃ i, (↑s : Set M) ⊆ T i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨Classical.choice ‹Nonempty ι›, ?_⟩
      simp
  | @insert a s ha hs =>
      rcases hs with ⟨i, hi⟩
      have ha_mem : a ∈ iSup T := by
        simpa [hSup] using (show a ∈ (⊤ : Subalgebra L M) from trivial)
      have ha_mem' : ∃ j, a ∈ T j := by
        change a ∈ ((iSup T : Subalgebra L M) : Set M) at ha_mem
        rw [Subalgebra.coe_iSup_of_directed hdir] at ha_mem
        simpa [Set.mem_iUnion] using ha_mem
      rcases ha_mem' with ⟨j, hj⟩
      rcases hdir i j with ⟨m, him, hjm⟩
      refine ⟨m, ?_⟩
      intro x hx
      simp only [Finset.mem_insert, SetLike.mem_coe] at hx ⊢
      rcases hx with rfl | hx
      · exact hjm hj
      · exact him (hi hx)

/- Helper for Lemma 15.34.2: a directed local-complete-intersection family of `L`-subalgebras
with supremum `⊤` packages the field extension `L → M` into the owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
RingHom.IsLocalCompleteIntersection)` specialized to `algebraMap L M`. -/
theorem algebraMap_isFilteredColimitOfLocalCompleteIntersection_core_of_directed_lci_subalgebra_family
    {ι : Type u} (S : ι → Subalgebra L M) (hdir : Directed (· ≤ ·) S)
    (hLCI : ∀ i, RingHom.IsLocalCompleteIntersection (algebraMap L ↥(S i)))
    (hSup : iSup S = (⊤ : Subalgebra L M)) :
    algebraMap_isFilteredColimitOfLocalCompleteIntersection_core (L := L) (M := M) := by
  classical
  -- Route correction: the empty-index obstruction is now isolated by the previous helper, so the
  -- only remaining work is the categorical packaging of the nonempty `Option`-indexed stage
  -- family into the hidden `MorphismProperty.ind` witness.
  let T : Option ι → Subalgebra L M := fun a ↦ Option.elim a ⊥ S
  have hT :=
    directed_lci_subalgebra_family_with_bottom_stage (L := L) (M := M) S hdir hLCI hSup
  have hdirT : Directed (· ≤ ·) T := hT.1
  have hLCIT : ∀ a, RingHom.IsLocalCompleteIntersection (algebraMap L ↥(T a)) := hT.2.1
  have hSupT : iSup T = (⊤ : Subalgebra L M) := hT.2.2
  letI : Preorder (Option ι) :=
    { le := fun a b ↦ T a ≤ T b
      le_refl := fun a ↦ le_rfl
      le_trans := fun _ _ _ hab hbc ↦ hab.trans hbc }
  letI : Nonempty (Option ι) := ⟨none⟩
  letI : IsDirectedOrder (Option ι) :=
    { directed := fun a b ↦ hdirT a b }
  -- Package each stage inclusion as an actual morphism in `CommRingCat`.
  let stageTransition :
      ∀ {a b : Option ι}, a ≤ b →
        (CommRingCat.of (ULift ↥(T a)) ⟶ CommRingCat.of (ULift ↥(T b))) :=
    fun {a b} hab ↦
      let _ : Algebra ↥(T a) ↥(T b) := (Subalgebra.inclusion hab).toAlgebra
      let _ : Algebra (ULift ↥(T a)) (ULift ↥(T b)) := ULift.algebra' ↥(T a) (ULift ↥(T b))
      CommRingCat.ofHom (algebraMap (ULift ↥(T a)) (ULift ↥(T b)))
  let stageSource :
      ∀ a : Option ι, CommRingCat.of (ULift L) ⟶ CommRingCat.of (ULift ↥(T a)) :=
    fun a ↦
      let _ : Algebra (ULift L) (ULift ↥(T a)) := ULift.algebra' L (ULift ↥(T a))
      CommRingCat.ofHom (algebraMap (ULift L) (ULift ↥(T a)))
  let stageCocone :
      ∀ a : Option ι, CommRingCat.of (ULift ↥(T a)) ⟶ CommRingCat.of (ULift M) :=
    fun a ↦
      let _ : Algebra ↥(T a) M := (T a).val.toAlgebra
      let _ : Algebra (ULift ↥(T a)) (ULift M) := ULift.algebra' ↥(T a) (ULift M)
      CommRingCat.ofHom (algebraMap (ULift ↥(T a)) (ULift M))
  have hstageTransition_id :
      ∀ a : Option ι,
        stageTransition (a := a) (b := a) le_rfl =
          CommRingCat.ofHom (RingHom.id (ULift ↥(T a))) := by
    intro a
    ext x
    rfl
  let D : CategoryTheory.Functor (Option ι) CommRingCat :=
    { obj := fun a ↦ CommRingCat.of (ULift ↥(T a))
      map := fun {a b} g ↦ stageTransition (a := a) (b := b) (CategoryTheory.leOfHom g)
      map_id := hstageTransition_id
      map_comp := fun f g ↦ by
        ext x
        rfl }
  let t : (CategoryTheory.Functor.const (Option ι)).obj (CommRingCat.of (ULift L)) ⟶ D :=
    { app := stageSource
      naturality := fun {_ _} g ↦ by
        ext x
        rfl }
  let s : D ⟶ (CategoryTheory.Functor.const (Option ι)).obj (CommRingCat.of (ULift M)) :=
    { app := stageCocone
      naturality := fun {_ _} g ↦ by
        ext x
        rfl }
  have hs : CategoryTheory.Limits.IsColimit
      (CategoryTheory.Limits.Cocone.mk (CommRingCat.of (ULift M)) s) := by
    have hcontains_finset :
        ∀ s : Finset M, ∃ a : Option ι, (↑s : Set M) ⊆ T a :=
      exists_stage_subalgebra_contains_finset (L := L) (M := M) T hdirT hSupT
    -- Build the colimit desc map from compatible stage algebra maps on the directed union.
    refine CategoryTheory.Limits.IsColimit.ofExistsUnique ?_
    intro c
    let baseMap : L →+* c.pt :=
      (c.ι.app none).hom.comp
        (ULift.ringEquiv.symm.toRingHom.comp (Algebra.botEquiv L M).symm.toRingHom)
    letI : Algebra L c.pt := baseMap.toAlgebra
    have hstageComm :
        ∀ a : Option ι,
          ((c.ι.app a).hom.comp ULift.ringEquiv.symm.toRingHom).comp
              (algebraMap L ↥(T a)) =
            baseMap := by
      intro a
      have hnone : none ≤ a := by
        change T none ≤ T a
        simpa [T] using (bot_le : (⊥ : Subalgebra L M) ≤ T a)
      have hnat :=
        congrArg CommRingCat.Hom.hom
          (c.ι.naturality (CategoryTheory.homOfLE hnone))
      change
        (c.ι.app a).hom.comp
            (stageTransition (a := none) (b := a) hnone).hom =
          (c.ι.app none).hom at hnat
      ext r
      simpa [baseMap, stageTransition] using
        DFunLike.congr_fun hnat (ULift.up ((Algebra.botEquiv L M).symm r))
    have hphiComm :
        ∀ (a : Option ι) (r : L),
          ((c.ι.app a).hom.comp ULift.ringEquiv.symm.toRingHom)
              ((algebraMap L ↥(T a)) r) =
            (algebraMap L c.pt) r := by
      intro a r
      simpa [baseMap] using DFunLike.congr_fun (hstageComm a) r
    let phi : ∀ a : Option ι, T a →ₐ[L] c.pt :=
      fun a ↦
        { toRingHom := (c.ι.app a).hom.comp ULift.ringEquiv.symm.toRingHom
          commutes' := hphiComm a }
    have hphi :
        ∀ (a b : Option ι) (hab : T a ≤ T b),
          phi a = (phi b).comp (Subalgebra.inclusion hab) := by
      intro a b hab
      have hnat := congrArg CommRingCat.Hom.hom (c.ι.naturality (CategoryTheory.homOfLE hab))
      change (c.ι.app b).hom.comp (stageTransition (a := a) (b := b) hab).hom =
          (c.ι.app a).hom at hnat
      ext x
      simpa [phi, stageTransition] using (DFunLike.congr_fun hnat (ULift.up x)).symm
    have htop : (⊤ : Subalgebra L M) ≤ iSup T := by
      simpa [hSupT]
    let descAlg : ↥(⊤ : Subalgebra L M) →ₐ[L] c.pt :=
      Subalgebra.iSupLift T hdirT phi hphi ⊤ htop
    let descM : M →ₐ[L] c.pt :=
      descAlg.comp (Subalgebra.topEquiv.symm : M ≃ₐ[L] ↥(⊤ : Subalgebra L M)).toAlgHom
    let desc : ULift M →+* c.pt := descM.toRingHom.comp ULift.ringEquiv.toRingHom
    have hdesc_stage :
        ∀ (a : Option ι) (x : T a),
          desc (ULift.up x.1) = (c.ι.app a).hom (ULift.up x) := by
      intro a x
      have hxTop : x.1 ∈ (⊤ : Subalgebra L M) := by
        simp
      have hdescAlg_eq : descAlg ⟨x.1, hxTop⟩ = phi a x := by
        exact
          Subalgebra.iSupLift_mk (K := T) (dir := hdirT) (f := phi) (hf := hphi)
            (T := (⊤ : Subalgebra L M)) (hT := htop) (i := a) x hxTop
      -- On every stage element, the directed-union desc map agrees with the cocone leg.
      calc
        desc (ULift.up x.1) = descAlg ⟨x.1, hxTop⟩ := by
          rfl
        _ = phi a x := hdescAlg_eq
        _ = (c.ι.app a).hom (ULift.up x) := by
          rfl
    refine ⟨CommRingCat.ofHom desc, ?_, ?_⟩
    · intro a
      ext x
      cases x with
      | up x =>
          -- Factorization is exactly the stage comparison on the chosen stage element.
          simpa [desc, stageCocone] using hdesc_stage a x
    · intro m hm
      ext y
      cases y with
      | up x =>
          rcases hcontains_finset ({x} : Finset M) with ⟨a, ha⟩
          have hx : x ∈ T a := by
            exact ha (by simp)
          have hm_eq :=
            DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom (hm a))
              (ULift.up (⟨x, hx⟩ : T a))
          -- Uniqueness reduces to comparing both morphisms on a stage containing the element.
          simpa [CommRingCat.hom_comp, stageCocone, hdesc_stage a ⟨x, hx⟩] using hm_eq
  -- The stage property is already exactly the local-complete-intersection owner on the stage map.
  refine ⟨Option ι, inferInstance, inferInstance, D, t, s, hs, ?_⟩
  intro a
  constructor
  · have hstageHom :
        (t.app a).hom = RingHom.ulift (algebraMap L ↥(T a)) := by
      let _ : Algebra (ULift.{u} L) (ULift.{u} ↥(T a)) := ULift.algebra' L (ULift.{u} ↥(T a))
      simpa [RingHom.algebraMap_toAlgebra] using
        (ulift_algebraMap_eq_ringHom_ulift (L := L) (A := ↥(T a)))
    -- Route correction: the remaining gap is only an owner-level `ULift` transport, so rewrite
    -- the stage map once and apply the dedicated `isLocalCompleteIntersection_ulift_algebraMap`
    -- bridge instead of reopening the colimit construction.
    simpa [RingHom.toMorphismProperty, hstageHom] using
      isLocalCompleteIntersection_ulift_algebraMap (L := L) (A := ↥(T a)) (hLCIT a)
  · ext x
    rfl

/-- Helper for Lemma 15.34.2: Lemma `10.158.11` gives the field extension `L → M` in the owner
form expected by the left-extended Jacobi-Zariski theorem. -/
theorem field_extension_isFilteredColimitOfLocalCompleteIntersection_core :
    algebraMap_isFilteredColimitOfLocalCompleteIntersection_core (L := L) (M := M) := by
  -- Choose the directed global-complete-intersection approximation from Lemma `10.158.11` and
  -- feed it to the generic owner-level bridge above.
  obtain ⟨ι, S, hdir, hGCI, hSup⟩ :=
    exists_directed_globalCompleteIntersection_subalgebra_family (k := L) (K := M)
  have hLCI : ∀ i, RingHom.IsLocalCompleteIntersection (algebraMap L ↥(S i)) := by
    intro i
    letI : IsGlobalCompleteIntersection L ↥(S i) := hGCI i
    exact globalCompleteIntersection_packages_ringHom_isLocalCompleteIntersection
      (L := L) (A := ↥(S i))
  exact
    algebraMap_isFilteredColimitOfLocalCompleteIntersection_core_of_directed_lci_subalgebra_family
      (L := L) (M := M) S hdir hLCI hSup

theorem field_extension_left_jacobi_zariski_presentation_injective :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent M (Generators.self K L)) := by
  -- The source-kernel transport is now stabilized up to the filtered-colimit input required by
  -- Lemma `15.33.7`, so the presentation-level injectivity is exactly its left-edge conclusion.
  have hcolim :
      algebraMap_isFilteredColimitOfLocalCompleteIntersection_core (L := L) (M := M) :=
    field_extension_isFilteredColimitOfLocalCompleteIntersection_core (L := L) (M := M)
  exact
    (presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
      (P := Generators.self K L) hcolim).1

/-- Lemma 15.34.2: for field extensions `M/L/K`, the leftmost map
`H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K})`
in the Jacobi-Zariski sequence is injective. Together with the recalled canonical exactness and
surjectivity results above, this is the source-facing exact sequence
`0 → H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K}) → H₁(L_{M/L}) → Ω[L⁄K] ⊗[L] M → Ω[M⁄K] → Ω[M⁄L] → 0`. -/
@[stacks 07E2]
theorem field_jacobi_zariski_left_injective :
    Function.Injective (LinearMap.liftBaseChange M (H1Cotangent.map K K L M)) := by
  -- The source-facing left edge is now reduced to the single field-specific presentation-level
  -- injectivity statement above.
  exact field_jacobi_zariski_left_injective_of_presentation_injective
    (K := K) (L := L) (M := M)
    (field_extension_left_jacobi_zariski_presentation_injective (K := K) (L := L) (M := M))

end

end Algebra
