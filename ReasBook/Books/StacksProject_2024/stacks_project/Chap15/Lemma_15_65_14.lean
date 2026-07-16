import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_23_2
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_2
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_12
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_1
import StacksProject_2024.stacks_project.Chap15.Remark_15_90_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Away" => LocalizedModule.Away

/-- Helper for Lemma 15.65.14: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : CochainComplex (ModuleCat R) ℤ := HomologicalComplex.zero

/-- Helper for Lemma 15.65.14: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree :
    (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : CochainComplex (ModuleCat R) ℤ := zeroCpx (R := R)
    change Module.Free R ↥(E0.X i) ∧ Module.Finite R ↥(E0.X i)
    -- Proof comment: each degree of the chosen zero complex is the zero module, so freeness
    -- comes from subsingleton and finite generation is transported from the one-point module.
    let hzero : IsZero (E0.X i) := by
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero :
            IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
    letI : Subsingleton ↥(E0.X i) := ModuleCat.subsingleton_of_isZero hzero
    refine ⟨Module.Free.of_subsingleton (R := R) (N := ↥(E0.X i)), ?_⟩
    let e : ModuleCat.of R PUnit ≅ E0.X i :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
    exact Module.Finite.equiv e.toLinearEquiv

/-- Helper for Lemma 15.65.14: if a derived `R`-complex has vanishing homology in all degrees
`≥ m`, then it is `m`-pseudo-coherent. -/
private theorem derived_isMPseudoCoherent_of_homology_isZero_ge_local
    (K : DMod) (m : ℤ)
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero ((H i).obj K)) :
    K.IsMPseudoCoherent m := by
  let E0 : CochainComplex (ModuleCat R) ℤ := zeroCpx (R := R)
  let α : DerivedCategory.Q.obj E0 ⟶ K := 0
  refine ⟨E0, ?_, inferInstance, α, ?_, ?_⟩
  · -- Proof comment: the zero complex is bounded on both sides by any chosen cutoff.
    refine ⟨m, m, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero :
            IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      simpa [zeroCpx] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (HomologicalComplex.isZero_zero :
            IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ))
  · intro i hi
    -- Proof comment: both source and target homology vanish, so the zero morphism is an
    -- isomorphism in degree `i`.
    let hsrc : IsZero ((H i).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H i).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero :
              IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ)))
    let htgt : IsZero ((H i).obj K) := hvanish i (le_of_lt hi)
    exact hsrc.isIso htgt ((H i).map α)
  · -- Proof comment: the degree-`m` homology map is again a zero-map between zero objects.
    let hsrc : IsZero ((H m).obj (DerivedCategory.Q.obj E0)) := by
      simpa [zeroCpx] using
        (H m).map_isZero
          ((DerivedCategory.Q).map_isZero
            (HomologicalComplex.isZero_zero :
              IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat R) ℤ)))
    let htgt : IsZero ((H m).obj K) := hvanish m le_rfl
    letI : IsIso ((H m).map α) := hsrc.isIso htgt ((H m).map α)
    infer_instance

/-- Helper for Lemma 15.65.14: in a distinguished triangle, if the first morphism is an
isomorphism on homology above `m` and an epimorphism in degree `m`, then the cone has zero
homology in every degree `≥ m`. -/
private theorem approximation_cone_isLE_pred_local
    (T : Triangle DMod) (hT : T ∈ distTriang DMod) (m : ℤ)
    (hαiso : ∀ i : ℤ, m < i → IsIso ((H i).map T.mor₁))
    (hαepi : Epi ((H m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have him : m ≤ i := by
    omega
  have hmor₁_epi : Epi ((H i).map T.mor₁) := by
    by_cases him_eq : i = m
    · subst him_eq
      exact hαepi
    · have him_lt : m < i := lt_of_le_of_ne him fun h ↦ him_eq h.symm
      letI : IsIso ((H i).map T.mor₁) := hαiso i him_lt
      infer_instance
  have hmor₁_mono : Mono ((H (i + 1)).map T.mor₁) := by
    letI : IsIso ((H (i + 1)).map T.mor₁) := hαiso (i + 1) (by omega)
    infer_instance
  -- Proof comment: exactness first kills the cone map in degree `i`, and then the connecting map
  -- one degree higher vanishes because the next homology map is mono.
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hmor₁_epi
  have hδ_zero : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    exact
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1) rfl).1 hmor₁_mono
  have hmor₂_epi : Epi ((H i).map T.mor₂) := by
    exact
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        T hT i (i + 1) rfl).2 hδ_zero
  -- Proof comment: a zero epimorphism has zero codomain, which is the desired vanishing of the
  -- cone homology in degree `i`.
  exact IsZero.of_epi_eq_zero ((H i).map T.mor₂) hmor₂_zero

/-- Helper for Lemma 15.65.14: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso_local {K L : DMod} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free model and postcompose its comparison
  -- map with the given isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.65.14: a derived `R`-complex is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
private theorem isPseudoCoherent_iff_forall_isMPseudoCoherent_local (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) E
  have hiffE : E.IsPseudoCoherent ↔ ∀ m : ℤ, E.IsMPseudoCoherent m :=
    hTFAE.out 0 1
  constructor
  · intro hK m
    -- Proof comment: move to a chosen cochain representative where the cochain-level TFAE
    -- applies, then transport the fixed-degree conclusion back to `K`.
    have hQE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      isPseudoCoherent_of_iso_local e.symm hK
    have hQEm : (DerivedCategory.Q.obj E).IsMPseudoCoherent m :=
      (hiffE.mp hQE) m
    exact isMPseudoCoherent_of_iso e m hQEm
  · intro hK
    -- Proof comment: pull the degreewise hypotheses back to the chosen representative, apply the
    -- cochain-level characterization, and push the result forward along the comparison isomorphism.
    have hQEall : ∀ m : ℤ, (DerivedCategory.Q.obj E).IsMPseudoCoherent m := fun m ↦
      isMPseudoCoherent_of_iso e.symm m (hK m)
    have hQE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      hiffE.mpr hQEall
    exact isPseudoCoherent_of_iso_local e hQE

/-- Helper for Lemma 15.65.14: derived scalar extension preserves `m`-pseudo-coherence. -/
private theorem derivedTensorWithAlgebra_isMPseudoCoherent_local
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DMod) (m : ℤ) (hK : K.IsMPseudoCoherent m) :
    ((derivedTensorWithAlgebra (algebraMap R S)).obj K).IsMPseudoCoherent m := by
  -- Proof comment: reuse the earlier Chapter 15 scalar-extension theorem directly.
  simpa using
    (_root_.CategoryTheory.derivedTensorWithAlgebra_isMPseudoCoherent
      (A := R) (B := S) K m hK)

/-- Helper for Lemma 15.65.14: derived scalar extension preserves pseudo-coherence. -/
private theorem derivedTensorWithAlgebra_isPseudoCoherent_local
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DMod) (hK : K.IsPseudoCoherent) :
    ((derivedTensorWithAlgebra (algebraMap R S)).obj K).IsPseudoCoherent := by
  -- Proof comment: rewrite pseudo-coherence as degreewise `m`-pseudo-coherence and apply the
  -- preceding scalar-extension theorem degree by degree.
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local] at hK ⊢
  intro m
  simpa using derivedTensorWithAlgebra_isMPseudoCoherent_local (S := S) K m (hK m)

/- Domain-style sampling for Lemma 15.65.14:
- primary domain: descent of pseudo-coherence in `D(R)` from a finite principal-open cover;
- sampled owner-level declarations:
  `Module.FinitePresentationRelativeTo.iff_localizationAway_unitIdeal`,
  `quotient_torsionBy_fintypeLinearCombination_surjective_of_presentation_minorIdeal_eq_span_singleton`,
  and the underlying finite-family owner `Fintype.linearCombination`;
- best owner abstraction: this item stays `source-facing`, but its covering data should be an
  arbitrary finite family `f : ι → R`, not the coordinate model `Fin r → R`;
- primitive data: the family `f`, the unit-ideal hypothesis `Ideal.span (Set.range f) = ⊤`, and
  the localized pseudo-coherence hypotheses;
- derived API: the descent conclusions for `m`-pseudo-coherence and pseudo-coherence. -/

/-- Helper for Lemma 15.65.14: once the finite cover is replaced by the image of `Finset.univ`,
the generated ideal is still the unit ideal. -/
lemma ideal_span_image_univ_eq_top_of_span_range_eq_top [Fintype ι]
    [DecidableEq R]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) :
    Ideal.span ((Finset.univ.image f : Finset R) : Set R) = ⊤ := by
  classical
  -- The source proof only needs a finite generating set, and `Finset.univ.image f` has the same
  -- underlying subset as `Set.range f`.
  simpa [Finset.coe_image, Set.image_univ] using hunit

/-- Helper for Lemma 15.65.14: an `m`-pseudo-coherent object has vanishing homology in all
sufficiently large degrees. -/
lemma exists_homology_upper_bound_of_isMPseudoCoherent
    {K : DMod} {m : ℤ} (hK : K.IsMPseudoCoherent m) :
    ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((H j).obj K) := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
  -- Above `max m b`, the bounded finite-free witness `E` already has no cohomology, and the
  -- comparison map from the definition is an isomorphism.
  refine ⟨max m b, ?_⟩
  intro j hj
  have hbj : b < j := by
    omega
  have hmj : m < j := by
    omega
  have hsource : IsZero ((H j).obj (DerivedCategory.Q.obj E)) := by
    have hQ : (DerivedCategory.Q.obj E).IsLE b := by
      rw [DerivedCategory.isLE_Q_obj_iff]
      let _ : E.IsStrictlyLE b := hEb
      infer_instance
    let _ : (DerivedCategory.Q.obj E).IsLE b := hQ
    exact DerivedCategory.isZero_of_isLE _ b j hbj
  let eH : ((H j).obj (DerivedCategory.Q.obj E)) ≅ ((H j).obj K) := by
    let _ : IsIso ((H j).map α) := hαgt j hmj
    exact asIso ((H j).map α)
  exact eH.isZero_iff.1 hsource

/-- Helper for Lemma 15.65.14: an `m`-pseudo-coherent witness also works for every larger cutoff
index. -/
private theorem isMPseudoCoherent_mono_local
    {K : DMod} {m n : ℤ} (hmn : m ≤ n) (hK : K.IsMPseudoCoherent m) :
    K.IsMPseudoCoherent n := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Proof comment: keep the same bounded finite-free model and weaken the homology comparison
  -- window from `m` to the larger index `n`.
  refine ⟨E, hbounds, hfree, α, ?_, ?_⟩
  · intro j hj
    exact hαgt j (lt_of_le_of_lt hmn hj)
  · by_cases hnm : n = m
    · subst hnm
      simpa using hαm
    · have hmn' : m < n := by
        omega
      letI : IsIso ((H n).map α) := hαgt n hmn'
      infer_instance

/-- Helper for Lemma 15.65.14: for a finite family of integer-indexed predicates with an upper
bound in each component, either every component is everywhere true or there is a maximal index
where some component fails. -/
private theorem exists_top_localized_nonvanishing_or_all_zero
    (Z : ι → ℤ → Prop)
    (hbound : ∀ i, ∃ b : ℤ, ∀ j : ℤ, b < j → Z i j) :
    (∀ i j, Z i j) ∨
      ∃ n : ℤ, (∃ i, ¬ Z i n) ∧ ∀ i j, n < j → Z i j := by
  classical
  let _ := Fintype.ofFinite ι
  by_cases hι : IsEmpty ι
  · left
    intro i
    exact (hι.false i).elim
  · let g : ι → ℤ := fun i ↦ Classical.choose (hbound i)
    have hg : ∀ i j, g i < j → Z i j := fun i ↦ Classical.choose_spec (hbound i)
    haveI : Nonempty ι := not_isEmpty_iff.mp hι
    let B : ℤ := (Finset.univ.image g).max' (Finset.image_nonempty.2 Finset.univ_nonempty)
    have hB : ∀ i, g i ≤ B := by
      intro i
      have hmem : g i ∈ (Finset.image g (Finset.univ : Finset ι) : Finset ℤ) := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact Finset.le_max' (s := Finset.univ.image g) (x := g i) hmem
    have hAbove : ∀ i j, B < j → Z i j := by
      intro i j hj
      exact hg i j (lt_of_le_of_lt (hB i) hj)
    by_cases hall : ∀ i j, Z i j
    · exact Or.inl hall
    · right
      have hex : ∃ k : ℕ, ∃ i : ι, ¬ Z i (B - k) := by
        rcases not_forall.mp hall with ⟨i, hi⟩
        rcases not_forall.mp hi with ⟨j, hj⟩
        have hjB : j ≤ B := by
          by_contra hgt
          exact hj (hAbove i j (by omega))
        refine ⟨Int.toNat (B - j), i, ?_⟩
        have hnonneg : 0 ≤ B - j := by
          omega
        have hcast : ((Int.toNat (B - j) : ℤ)) = B - j := by
          exact Int.toNat_of_nonneg hnonneg
        have hEq : B - (Int.toNat (B - j) : ℤ) = j := by
          rw [hcast]
          omega
        rw [hEq]
        exact hj
      let k0 : ℕ := Nat.find hex
      have hk0 : ∃ i : ι, ¬ Z i (B - k0) := Nat.find_spec hex
      refine ⟨B - k0, hk0, ?_⟩
      intro i j hj
      by_contra hbad
      have hjB : j ≤ B := by
        by_contra hgt
        exact hbad (hAbove i j (by omega))
      have hnonneg : 0 ≤ B - j := by
        omega
      have hklt_int : ((Int.toNat (B - j) : ℤ) < (k0 : ℤ)) := by
        rw [Int.toNat_of_nonneg hnonneg]
        omega
      have hklt : Int.toNat (B - j) < k0 := by
        exact_mod_cast hklt_int
      have hcast : ((Int.toNat (B - j) : ℤ)) = B - j := by
        exact Int.toNat_of_nonneg hnonneg
      have hEq : B - (Int.toNat (B - j) : ℤ) = j := by
        rw [hcast]
        omega
      have hWitness : ∃ i : ι, ¬ Z i (B - Int.toNat (B - j)) := by
        refine ⟨i, ?_⟩
        rw [hEq]
        exact hbad
      exact (not_le_of_gt hklt) (Nat.find_min' hex hWitness)

/-- Helper for Lemma 15.65.14: scalar extension is additive, so it lifts from complexes to the
homotopy category and then to the derived category. -/
private instance extendScalars_additive
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap S T)).left_adjoint_additive

/-- Helper for Lemma 15.65.14: scalar extension is additive, so it lifts from complexes to the
homotopy category and then to the derived category. -/
private abbrev mapHomotopyCategoryToDerived
    {S T : Type u} [CommRing S] [CommRing T]
    (F : ModuleCat S ⥤ ModuleCat T) [F.Additive] :
    HomotopyCategory (ModuleCat S) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat T) :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Helper for Lemma 15.65.14: flat scalar extension preserves finite limits, so homology can be
commuted past exact scalar extension. -/
private instance extendScalars_preservesFiniteLimits
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat S T from inferInstance))

/-- Helper for Lemma 15.65.14: exact flat scalar extension already computes its own derived
scalar-extension functor. -/
private noncomputable def extendScalars_mapDerivedCategory_iso_of_flat
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T] :
    (ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory ≅
      derivedTensorWithAlgebra (algebraMap S T) := by
  let F₀ : ModuleCat S ⥤ ModuleCat T := ModuleCat.extendScalars (algebraMap S T)
  let F :
      HomotopyCategory (ModuleCat S) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat T) :=
    mapHomotopyCategoryToDerived F₀
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)) := by
    -- The owner `derivedTensorWithAlgebra` is the total left derived functor of scalar
    -- extension.
    simpa [F, F₀] using
      (extendScalarsToDerived_hasLeftDerivedFunctor
        (R := S) (A := T) (algebraMap S T))
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)) := by
    -- Exact flat scalar extension already inverts quasi-isomorphisms, so no further resolution
    -- step is needed here.
    simpa [F₀] using
      (Functor.isLeftDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ))
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactorsh)
  -- Compare the exact derived functor of flat scalar extension with the canonical owner
  -- `derivedTensorWithAlgebra`.
  simpa [derivedTensorWithAlgebra, F, F₀] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat S) (ComplexShape.up ℤ) ⥤
            DerivedCategory (ModuleCat S))
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)))
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit
        F
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat S) (ComplexShape.up ℤ) ⥤
            DerivedCategory (ModuleCat S))
        (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (ModuleCat S) (ComplexShape.up ℤ))
      (Iso.refl F))

/-- Helper for Lemma 15.65.14: flat exact scalar extension commutes with taking homology. -/
private noncomputable def extendScalars_homology_iso_of_flat
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (L : DerivedCategory (ModuleCat S)) (j : ℤ) :
    (ModuleCat.extendScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) j).obj L) ≅
      (DerivedCategory.homologyFunctor (ModuleCat T) j).obj
        (((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).obj L) := by
  let HS := DerivedCategory.homologyFunctor (ModuleCat S)
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.extendScalars (algebraMap S T)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eS : (HS j).obj L ≅ K.homology j :=
    ((HS j).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat S) j).app K
  let e :
      (HT j).obj (((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).obj L) ≅
        (ModuleCat.extendScalars (algebraMap S T)).obj ((HS j).obj L) :=
    (HT j).mapIso
        (((((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
          ((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) j).app FK ≪≫
      (K.sc j).mapHomologyIso (ModuleCat.extendScalars (algebraMap S T)) ≪≫
        (ModuleCat.extendScalars (algebraMap S T)).mapIso eS.symm
  -- Pass to the chosen `Q.objPreimage` representative and then invert the comparison to get the
  -- source-facing orientation.
  exact e.symm

/-- Helper for Lemma 15.65.14: away-localizing the global degree-`j` homology of `K` agrees with
the degree-`j` homology of the derived away-localization of `K`. -/
private noncomputable abbrev localizationAway_homology_iso
    (f : ι → R) (K : DMod) (i : ι) (j : ℤ) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))).obj ((H j).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
        (K ⊗[R]^L[Localization.Away (f i)]) := by
  -- First commute homology past the exact away-localization functor.
  let e₁ :=
    extendScalars_homology_iso_of_flat
      (S := R) (T := Localization.Away (f i)) K j
  -- Then replace exact scalar extension on the derived category by the canonical owner
  -- `K ⊗[R]^L[Localization.Away (f i)]`.
  let e₂ :=
    (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).mapIso
      ((extendScalars_mapDerivedCategory_iso_of_flat
        (S := R) (T := Localization.Away (f i))).app K)
  exact e₁ ≪≫ e₂

/-- Helper for Lemma 15.65.14: rewrite the exact scalar extension of global homology as the
canonical away localization used by Chapter 10. -/
private noncomputable abbrev away_homology_iso
    (f : ι → R) (K : DMod) (i : ι) (j : ℤ) :
    ModuleCat.of (Localization.Away (f i)) (Away (f i) ↑((H j).obj K)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
        (K ⊗[R]^L[Localization.Away (f i)]) := by
  -- Route correction: reuse the owner bridge `awayExtendScalarsIso` and only compose it with the
  -- already proved homology comparison.
  exact (_root_.awayExtendScalarsIso (f i) ((H j).obj K)).symm ≪≫
    localizationAway_homology_iso (f := f) (K := K) i j

/-- Helper for Lemma 15.65.14: the degree-`j` homology of a single derived object concentrated in
degree `n` vanishes away from `n`. -/
private theorem single_derived_homology_isZero_of_ne
    (E : ModuleCat R) (n j : ℤ) (hjn : j ≠ n) :
    IsZero ((H j).obj ((DerivedCategory.singleFunctor (ModuleCat R) n).obj E)) := by
  let e :
      (H j).obj ((DerivedCategory.singleFunctor (ModuleCat R) n).obj E) ≅
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj E).homology j :=
    ((H j).mapIso ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) n).app E)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) j).app
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj E)
  -- Proof comment: compare the derived single object with its strict single-complex model and use
  -- the standard chain-level vanishing of single-complex homology away from the unique degree.
  exact e.isZero_iff.2 <|
    HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) n E j hjn

/-- Helper for Lemma 15.65.14: after away localization, a single derived object still has no
homology above its unique degree. -/
private theorem away_single_homology_isZero_above
    (f : ι → R) (E : ModuleCat R) (i : ι) {n j : ℤ} (hnj : n < j) :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
        ((((DerivedCategory.singleFunctor (ModuleCat R) n).obj E) ⊗[R]^L[Localization.Away (f i)]))) := by
  let hsingle :
      IsZero ((H j).obj ((DerivedCategory.singleFunctor (ModuleCat R) n).obj E)) := by
    exact single_derived_homology_isZero_of_ne (R := R) E n j (by omega)
  -- Proof comment: the already established away-homology comparison transports the global
  -- single-degree vanishing statement to the localized homology object.
  exact
    (away_homology_iso (f := f)
      (K := (DerivedCategory.singleFunctor (ModuleCat R) n).obj E) i j).isZero_iff.1 hsingle

/-- Helper for Lemma 15.65.14: an epimorphism on global degree-`n` homology stays epimorphic after
away localization. -/
private theorem away_homology_iso_naturality_epi
    (f : ι → R) {K L : DMod} (α : K ⟶ L) (n : ℤ) (i : ι)
    [Epi ((H n).map α)] :
    Epi
      ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) n).map
        ((derivedTensorWithAlgebra (algebraMap R (Localization.Away (f i)))).map α)) := by
  -- TODO: prove the naturality square for `localizationAway_homology_iso`, then transport
  -- epimorphy from exact scalar extension of `((H n).map α)` across the two comparison
  -- isomorphisms.
  sorry

/-- Helper for Lemma 15.65.14: if every away-localized degree-`j` homology object vanishes on the
finite principal-open cover, then the global degree-`j` homology object vanishes. -/
private theorem homology_localizationAway_cover_reflects_zero
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (j : ℤ)
    (hzero :
      ∀ i : ι,
        IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
            (K ⊗[R]^L[Localization.Away (f i)]))) :
    IsZero ((H j).obj K) := by
  classical
  let _ := Fintype.ofFinite ι
  let s : Finset R := Finset.univ.image f
  have hs : Ideal.span (s : Set R) = ⊤ := by
    -- Proof comment: replace the finite family by the explicit finset image used by the Chapter
    -- 10 descent theorem.
    simpa [s] using
      ideal_span_image_univ_eq_top_of_span_range_eq_top (f := f) hunit
  have hsub :
      Subsingleton ↑((H j).obj K) := by
    -- Proof comment: each localized homology object is zero, so the corresponding away module is
    -- subsingleton after transporting along `away_homology_iso`; then descend subsingleton-ness
    -- from the principal-open cover.
    exact
      module_subsingleton_of_localizationAway
        (R := R) (s := s) (M := ↑((H j).obj K)) hs fun g ↦ by
          rcases Finset.mem_image.mp g.property with ⟨i, -, rfl⟩
          have hzeroAway :
              IsZero
                (ModuleCat.of (Localization.Away (f i))
                  (Away (f i) ↑((H j).obj K))) := by
            exact (away_homology_iso (f := f) (K := K) i j).isZero_iff.2 (hzero i)
          exact ModuleCat.subsingleton_of_isZero hzeroAway
  letI : Subsingleton ↑((H j).obj K) := hsub
  -- Proof comment: a subsingleton module object is zero in `ModuleCat`.
  simpa using ModuleCat.isZero_of_subsingleton ((H j).obj K)

/-- Helper for Lemma 15.65.14: finite generation of the degree-`j` homology modules on the away
cover descends to finite generation of the global degree-`j` homology module. -/
private theorem homology_localizationAway_cover_descends_finite
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (j : ℤ)
    (hfinite : ∀ i : ι,
      Module.Finite (Localization.Away (f i))
        ↑((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
          (K ⊗[R]^L[Localization.Away (f i)]))) :
    Module.Finite R ↑((H j).obj K) := by
  classical
  let _ := Fintype.ofFinite ι
  let s : Finset R := Finset.univ.image f
  have hs : Ideal.span (s : Set R) = ⊤ := by
    -- Proof comment: the finite image finset generates the same ideal as the original family.
    simpa [s] using
      ideal_span_image_univ_eq_top_of_span_range_eq_top (f := f) hunit
  -- Proof comment: transport finite generation on each chart back through `away_homology_iso`,
  -- then apply the standard finite-generation descent theorem for principal-open covers.
  exact
    Module.Finite.of_localizationSpan_finite s hs fun g ↦ by
      rcases Finset.mem_image.mp g.property with ⟨i, -, rfl⟩
      exact Module.Finite.equiv (away_homology_iso (f := f) (K := K) i j).symm.toLinearEquiv

/-- Helper for Lemma 15.65.14: if a localized derived object is `m`-pseudo-coherent and has no
homology above `n`, then its degree-`n` homology module is finite. -/
private theorem localized_top_homology_finite_of_isMPseudoCoherent
    (f : ι → R) (K : DMod) (i : ι) {m n : ℤ} (hmn : m ≤ n)
    (hloc : (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m)
    (hvanish :
      ∀ j : ℤ, n < j →
        IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj
            (K ⊗[R]^L[Localization.Away (f i)]))) :
    Module.Finite (Localization.Away (f i))
      ↑((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) n).obj
        (K ⊗[R]^L[Localization.Away (f i)])) := by
  let L := K ⊗[R]^L[Localization.Away (f i)]
  let C : CochainComplex (ModuleCat (Localization.Away (f i))) ℤ :=
    DerivedCategory.Q.objPreimage L
  let eC : DerivedCategory.Q.obj C ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hC : C.IsMPseudoCoherent m := by
    -- Proof comment: pass the localized pseudo-coherence witness to the chosen cochain
    -- representative of `L`.
    exact isMPseudoCoherent_of_iso eC.symm m hloc
  have hCn : C.IsMPseudoCoherent n := by
    -- Proof comment: the same witness is valid at the larger cutoff `n`.
    exact isMPseudoCoherent_mono_local hmn hC
  have hvanishC : ∀ j : ℤ, n < j → IsZero (C.homology j) := by
    intro j hj
    let eH :
        (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).obj L ≅
          C.homology j :=
      ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) j).mapIso eC).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat (Localization.Away (f i))) j).app C
    exact (hvanish j hj).of_iso eH.symm
  have hfiniteC : Module.Finite (Localization.Away (f i)) (C.homology n) :=
    CochainComplex.homology_finite_of_isMPseudoCoherent hCn hvanishC
  let eH :
      (DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) n).obj L ≅
        C.homology n :=
    ((DerivedCategory.homologyFunctor (ModuleCat (Localization.Away (f i))) n).mapIso eC).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat (Localization.Away (f i))) n).app C
  exact Module.Finite.equiv eH.symm.toLinearEquiv

/-- Helper for Lemma 15.65.14: the single degree-zero cochain complex on a finite free module is
termwise finite free. -/
private lemma single_zero_complex_isTermwiseFiniteFree
    (F : ModuleCat R) [Module.Free R F] [Module.Finite R F] :
    ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).IsTermwiseFiniteFree := by
  -- Proof comment: the degree-zero term is `F`, while every other term is a zero module.
  refine ⟨fun j ↦ ?_⟩
  by_cases hj : j = 0
  · let e :
        (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F).X j) ≅ F := by
        subst hj
        simpa using HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) F
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩
  · let E : CochainComplex (ModuleCat R) ℤ :=
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
    let hzero : IsZero (E.X j) := by
      simpa [E] using
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) F j hj)
    letI : Subsingleton ↥(E.X j) := ModuleCat.subsingleton_of_isZero hzero
    have hfree : Module.Free R (E.X j) :=
      Module.Free.of_subsingleton (R := R) (N := ↥(E.X j))
    have hfinite : Module.Finite R (E.X j) := by
      let e : ModuleCat.of R PUnit ≅ E.X j :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      exact Module.Finite.equiv e.toLinearEquiv
    exact ⟨hfree, hfinite⟩

/-- Helper for Lemma 15.65.14: a finite free module is `m`-pseudo-coherent in degree zero for
every `m`. -/
private theorem finite_free_module_isMPseudoCoherent_local
    (F : ModuleCat R) (m : ℤ) [Module.Free R F] [Module.Finite R F] :
    F.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat R) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj F
  let hEfree : E.IsTermwiseFiniteFree := single_zero_complex_isTermwiseFiniteFree F
  let α : DerivedCategory.Q.obj E ⟶ (ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj F :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app F).hom
  -- Proof comment: the single complex itself is the bounded finite-free witness, and the
  -- comparison map to the derived degree-zero object is already an isomorphism.
  refine ⟨E, ⟨0, 0, inferInstance, inferInstance⟩, hEfree, α, ?_, ?_⟩
  · intro j hj
    letI : IsIso ((H j).map α) := Functor.map_isIso (H j) α
    infer_instance
  · letI : IsIso ((H m).map α) := Functor.map_isIso (H m) α
    infer_instance

/-- Helper for Lemma 15.65.14: an `(m - n)`-pseudo-coherent module gives an `m`-pseudo-coherent
single derived object concentrated in degree `n`. -/
private theorem singleFunctor_isMPseudoCoherent_of_module_local
    (M : ModuleCat R) (n m : ℤ)
    (hM : M.IsMPseudoCoherent (m - n)) :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M).IsMPseudoCoherent m := by
  let e :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧) ≅
        ((ModuleCat.single0Functor : ModuleCat R ⥤ DMod).obj M) :=
    ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso n 0 n (by simp)).app M
  have hShift :
      (((DerivedCategory.singleFunctor (ModuleCat R) n).obj M)⟦n⟧).IsMPseudoCoherent (m - n) := by
    -- Proof comment: after shifting by `n`, the degree-`n` single object becomes the degree-zero
    -- single object on the same module.
    rw [ModuleCat.IsMPseudoCoherent] at hM
    exact isMPseudoCoherent_of_iso e.symm (m - n) hM
  -- Proof comment: shift the pseudo-coherence index back to the original unshifted object.
  exact
    (isMPseudoCoherent_shift_iff
      ((DerivedCategory.singleFunctor (ModuleCat R) n).obj M) n m).1 hShift

/-- Helper for Lemma 15.65.14: a finite free module placed in degree `n` is `m`-pseudo-coherent
for every `m`. -/
private theorem single_finite_free_isMPseudoCoherent
    (E : ModuleCat R) (n m : ℤ) [Module.Free R E] [Module.Finite R E] :
    ((DerivedCategory.singleFunctor (ModuleCat R) n).obj E).IsMPseudoCoherent m := by
  -- Proof comment: first view the finite free module as pseudo-coherent in degree zero, then
  -- shift that witness to degree `n`.
  exact
    singleFunctor_isMPseudoCoherent_of_module_local
      E n m (finite_free_module_isMPseudoCoherent_local E (m - n))

/-- Helper for Lemma 15.65.14: if `f ≫ e.hom` is epi and `e` is an isomorphism, then `f` is epi. -/
private theorem epi_of_epi_comp_iso
    {X Y Z : ModuleCat R} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  -- Proof comment: postcompose parallel arrows with `e.inv` and cancel the resulting epimorphism.
  rw [CategoryTheory.epi_iff_forall_injective]
  intro W
  let hcomp :=
    (CategoryTheory.epi_iff_forall_injective (f ≫ e.hom)).1
      (show Epi (f ≫ e.hom) by infer_instance) W
  intro u v huv
  have huv' : (f ≫ e.hom) ≫ (e.inv ≫ u) = (f ≫ e.hom) ≫ (e.inv ≫ v) := by
    simpa [Category.assoc] using huv
  have heq : e.inv ≫ u = e.inv ≫ v := hcomp huv'
  exact (cancel_epi e.inv).1 heq

/-- Helper for Lemma 15.65.14: a map into cycles kills the outgoing differential, so it supplies
the compatibility needed to build `mkHomFromSingle`. -/
private theorem single_cover_cycle_condition
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    (α : F ⟶ C.cycles n) :
    ∀ k, n + 1 = k → (α ≫ C.iCycles n) ≫ C.d n k = 0 := by
  intro k hk
  -- Proof comment: a morphism landing in cycles annihilates the outgoing differential by the
  -- defining equation of `C.iCycles n`.
  simpa [Category.assoc] using congrArg (fun t ↦ α ≫ t) (C.iCycles_d n k)

/-- Helper for Lemma 15.65.14: for a single complex concentrated in degree `n`, the canonical map
from cycles to homology is the inverse of the standard single-homology comparison. -/
private theorem single_cycles_to_homology_eq_single_homology_local
    (n : ℤ) (F : ModuleCat R) :
    (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
        ((CochainComplex.singleFunctor (ModuleCat R) n).obj F).homologyπ n =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv := by
  -- Proof comment: both sides are the canonical quotient map from the degree-`n` cycles of the
  -- single complex onto its degree-`n` homology.
  simp

/-- Helper for Lemma 15.65.14: the `mkHomFromSingle` map induced by a lift into cycles gives the
expected degree-`n` morphism on homology. -/
private theorem single_cover_to_complex_map_homology_comparison
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    (α : F ⟶ C.cycles n) :
    let β :
      (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C :=
      HomologicalComplex.mkHomFromSingle
        (K := C) (j := n) (α ≫ C.iCycles n)
        (single_cover_cycle_condition (C := C) n α)
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
        HomologicalComplex.homologyMap β n =
      α ≫ C.homologyπ n := by
  let β :
      (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C :=
    HomologicalComplex.mkHomFromSingle
      (K := C) (j := n) (α ≫ C.iCycles n)
      (single_cover_cycle_condition (C := C) n α)
  have hcycles :
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          HomologicalComplex.cyclesMap β n = α := by
    -- Proof comment: compare both cycles maps after postcomposing with the cycles inclusion of
    -- `C`; both reduce to the defining degree-`n` component of `β`.
    apply (cancel_mono (C.iCycles n)).1
    calc
      ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          HomologicalComplex.cyclesMap β n) ≫ C.iCycles n =
          (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
            (HomologicalComplex.cyclesMap β n ≫ C.iCycles n) := by
            simp [Category.assoc]
      _ =
          (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
            (((CochainComplex.singleFunctor (ModuleCat R) n).obj F).iCycles n ≫ β.f n) := by
            rw [HomologicalComplex.cyclesMap_i]
      _ =
          ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
            ((CochainComplex.singleFunctor (ModuleCat R) n).obj F).iCycles n) ≫ β.f n := by
            simp [Category.assoc]
      _ = β.f n := by
            simp
      _ =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).hom ≫
            (α ≫ C.iCycles n) := by
            simp [β, HomologicalComplex.mkHomFromSingle_f, Category.assoc]
      _ = α ≫ C.iCycles n := by
            simp
  -- Proof comment: rewrite homology naturality through the canonical cycles-to-homology map of
  -- the single complex and then substitute the cycles comparison above.
  calc
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
        HomologicalComplex.homologyMap β n =
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          ((CochainComplex.singleFunctor (ModuleCat R) n).obj F).homologyπ n) ≫
            HomologicalComplex.homologyMap β n := by
            rw [single_cycles_to_homology_eq_single_homology_local (R := R) n F]
    _ =
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          (((CochainComplex.singleFunctor (ModuleCat R) n).obj F).homologyπ n ≫
            HomologicalComplex.homologyMap β n) := by
            simp [Category.assoc]
    _ =
        (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          (HomologicalComplex.cyclesMap β n ≫ C.homologyπ n) := by
            rw [HomologicalComplex.homologyπ_naturality]
    _ =
        ((HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) n F).inv ≫
          HomologicalComplex.cyclesMap β n) ≫ C.homologyπ n := by
            simp [Category.assoc]
    _ = α ≫ C.homologyπ n := by
            rw [hcycles]
            simp [Category.assoc]

/-- Helper for Lemma 15.65.14: a projective cover of the degree-`n` homology of a cochain complex
lifts to a morphism from the degree-`n` single complex. -/
private theorem single_cover_to_complex_map
    {C : CochainComplex (ModuleCat R) ℤ} (n : ℤ) {F : ModuleCat R}
    [Module.Projective R F] (q : F ⟶ C.homology n) :
    ∃ β : (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n F).inv ≫
        HomologicalComplex.homologyMap β n = q := by
  have hsurj : Function.Surjective (C.homologyπ n) :=
    (CategoryTheory.epi_iff_surjective (C.homologyπ n)).1 inferInstance
  obtain ⟨αlin, hαlin⟩ :=
    Module.projective_lifting_property (C.homologyπ n).hom q.hom hsurj
  let α : F ⟶ C.cycles n := ModuleCat.ofHom αlin
  have hα : α ≫ C.homologyπ n = q := by
    -- Proof comment: projectivity lifts `q` through the canonical quotient map from cycles to
    -- homology.
    ext x
    exact LinearMap.congr_fun hαlin x
  let β :
      (CochainComplex.singleFunctor (ModuleCat R) n).obj F ⟶ C :=
    HomologicalComplex.mkHomFromSingle
      (K := C) (j := n) (α ≫ C.iCycles n)
      (single_cover_cycle_condition (C := C) n α)
  refine ⟨β, ?_⟩
  -- Proof comment: the dedicated normalization lemma turns the lifted cycles map back into the
  -- original quotient map `q`.
  simpa [β, hα] using
    (single_cover_to_complex_map_homology_comparison (R := R) (C := C) n α)

/-- Helper for Lemma 15.65.14: a finite free cover of the degree-`n` homology object of `K`
lifts to a map from the degree-`n` single derived object inducing an epimorphism on `H^n`. -/
private theorem exists_single_map_epi_on_top_homology
    (K : DMod) (n : ℤ) (E : ModuleCat R) [Module.Free R E] [Module.Finite R E]
    (π : E ⟶ (H n).obj K) [Epi π] :
    ∃ α : (DerivedCategory.singleFunctor (ModuleCat R) n).obj E ⟶ K,
      Epi ((H n).map α) := by
  let C : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj C ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eTarget : (H n).obj K ≅ C.homology n :=
    ((H n).mapIso eK).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app C
  let q : E ⟶ C.homology n := π ≫ eTarget.hom
  obtain ⟨β, hβq⟩ := single_cover_to_complex_map (R := R) (C := C) n q
  let α : (DerivedCategory.singleFunctor (ModuleCat R) n).obj E ⟶ K :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) n).app E).inv ≫
      DerivedCategory.Q.map β ≫ eK.hom
  refine ⟨α, ?_⟩
  have hq_epi : Epi q := by
    -- Proof comment: compose the given surjection onto `H^n(K)` with the canonical comparison
    -- isomorphism to the chosen cochain representative.
    dsimp [q]
    infer_instance
  have hHomologyMap_epi : Epi (HomologicalComplex.homologyMap β n) := by
    -- Proof comment: the chain-level normalization identifies the composite with the known epi
    -- `q`, so epimorphy descends to the homology map of `β`.
    have : Epi
        ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n E).inv ≫
          HomologicalComplex.homologyMap β n) := by
      simpa [hβq] using hq_epi
    exact epi_of_epi
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n E).inv
      (HomologicalComplex.homologyMap β n)
  have hQβ_epi : Epi ((H n).map (DerivedCategory.Q.map β)) := by
    -- Proof comment: the imported conjugation lemma transports epimorphy from the cochain model
    -- to the public derived homology map.
    exact (homologyMap_epi_iff_homologyFunctor_map_Q_epi (R := R) β n).1 hHomologyMap_epi
  -- Proof comment: `α` differs from `Q.map β` only by source and target isomorphisms, so its
  -- degree-`n` homology map is still epi.
  dsimp [α]
  simpa [Functor.map_comp, Category.assoc]

-- Proof sketch: use the finite principal-open cover `D(f i)` of `Spec R` coming from
-- `Ideal.span (Set.range f) = ⊤`. Descend the bounded finite-projective approximation from each
-- localization and glue the finite top cohomology modules by the standard local criterion for
-- finite generation, then induct on the highest nonvanishing cohomological degree as in the
-- Stacks proof.
/-- Lemma 15.65.14 (1): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := by
  -- Route correction: the source-faithful proof skeleton is now clear and dependency-closed in
  -- this file, but the remaining blockers are the localized descent helpers and the lifted
  -- single-object top-homology cover used in the cone step.
  -- TODO: combine `exists_top_localized_nonvanishing_or_all_zero`,
  -- `homology_localizationAway_cover_reflects_zero`,
  -- `homology_localizationAway_cover_descends_finite`,
  -- `localized_top_homology_finite_of_isMPseudoCoherent`, and
  -- `exists_single_map_epi_on_top_homology` into the intended induction on the maximal localized
  -- nonvanishing degree.
  let _ := hunit
  let _ := hloc
  sorry

/-- Combining Lemma `15.65.14 (1)` with scalar-extension preservation, `m`-pseudo-coherence is
local for finite principal-open covers of `Spec R`. -/
theorem isMPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) ↔
      K.IsMPseudoCoherent m := by
  constructor
  · exact isMPseudoCoherent_of_localizationAway_unitIdeal f hunit K m
  · intro hK i
    simpa using
      derivedTensorWithAlgebra_isMPseudoCoherent_local
        (S := Localization.Away (f i)) K m hK

-- Proof sketch: pseudo-coherence means `m`-pseudo-coherence for every `m`. Apply part `(1)` to
-- each integer `m`, using the localized pseudo-coherence hypotheses, and then invoke the standard
-- characterization of pseudo-coherence by uniform `m`-pseudo-coherence.
/-- Lemma 15.65.14 (2): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is pseudo-coherent, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) :
    K.IsPseudoCoherent := by
  -- Rewrite pseudo-coherence as degreewise `m`-pseudo-coherence and apply part `(1)` for each
  -- integer `m`.
  rw [isPseudoCoherent_iff_forall_isMPseudoCoherent_local]
  intro m
  exact isMPseudoCoherent_of_localizationAway_unitIdeal f hunit K m
    (fun i ↦ (isPseudoCoherent_iff_forall_isMPseudoCoherent_local _).1 (hloc i) m)

/-- Combining Lemma `15.65.14 (2)` with scalar-extension preservation, pseudo-coherence is local
for finite principal-open covers of `Spec R`. -/
theorem isPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) ↔
      K.IsPseudoCoherent := by
  constructor
  · exact isPseudoCoherent_of_localizationAway_unitIdeal f hunit K
  · intro hK i
    simpa using
      derivedTensorWithAlgebra_isPseudoCoherent_local
        (S := Localization.Away (f i)) K hK

end

end CategoryTheory
