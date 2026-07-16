import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_3_8.ConditionRBasic

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped Representation ZeroObject

namespace Representation

section PositiveGeneration

/-- Helper for Exercise 16-16.3-8: a nonnegative integer multiple of an element of an additive
submonoid still belongs to that additive submonoid. -/
private theorem zsmul_mem_addSubmonoid_of_nonneg
    {M : Type v} [AddCommGroup M]
    (T : AddSubmonoid M) {a : ℤ} (ha : 0 ≤ a) {x : M} (hx : x ∈ T) :
    a • x ∈ T := by
  -- Replace the nonnegative integer coefficient by the corresponding natural multiple.
  have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
  rw [← hcast]
  simpa only [natCast_zsmul] using T.nsmul_mem hx a.toNat

/-- Helper for Exercise 16-16.3-8: a finite `ℤ`-linear combination with nonnegative
coefficients lies in an additive submonoid when all basis vectors do. -/
private theorem linearCombination_mem_addSubmonoid_of_nonneg
    {ι : Type u} {M : Type v} [AddCommGroup M]
    (T : AddSubmonoid M) (b : ι → M) (c : ι →₀ ℤ)
    (hc : ∀ i, 0 ≤ c i) (hb : ∀ i, b i ∈ T) :
    Finsupp.linearCombination ℤ b c ∈ T := by
  -- Expand the linear combination as a finite sum and handle each nonnegative coefficient.
  rw [Finsupp.linearCombination_apply]
  exact AddSubmonoid.sum_mem T (t := c.support) (f := fun i ↦ c i • b i)
    (h := fun i _ ↦ zsmul_mem_addSubmonoid_of_nonneg T (hc i) (hb i))

/-- Helper for Exercise 16-16.3-8: choose representatives for all simple finite-dimensional
representations over a field. -/
theorem existsCompletePairwiseNonisomorphicSimpleFamilyField_e16338
    (L : Type u) [Field L] (G : Type u) [Group G] [Finite G] :
    ∃ (ι : Type (u + 1)) (π : ι → FDRep L G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep L G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨iso⟩
            exact ⟨iso.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep L G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Isomorphic chosen representatives determine the same quotient class.
    intro q q' hqq' hIso
    rcases hIso with ⟨iso⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨iso⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty ((Quotient.out q).1 ≅ τ) :=
        Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨iso⟩
      exact ⟨iso.symm⟩
  exact ⟨ι, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 16-16.3-8: the class of a binary product representation is the sum of
the two factor classes. -/
private theorem finiteRepGrothendieckClass_prod_eq_add_local
    {L : Type u} [Field L] {G : Type u} [Group G] (E F : FDRep L G) :
    [FDRep.of (Representation.prod E.ρ F.ρ)]₀ = ([E]₀ : R₀[L](G)) + [F]₀ := by
  -- Build the standard short exact sequence `0 → E → E × F → F → 0` in `FDRep`.
  let P : FDRep L G := FDRep.of (Representation.prod E.ρ F.ρ)
  let fRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj E ⟶ (forget₂ (FDRep L G) (Rep L G)).obj P) :=
    Rep.ofHom ⟨LinearMap.inl L E.V F.V, by
      intro g
      ext x
      change
        LinearMap.inl L E.V F.V (E.ρ g x) =
          ((E.ρ g).prodMap (F.ρ g)) (LinearMap.inl L E.V F.V x)
      simp [LinearMap.prodMap]⟩
  let gRep :
      ((forget₂ (FDRep L G) (Rep L G)).obj P ⟶ (forget₂ (FDRep L G) (Rep L G)).obj F) :=
    Rep.ofHom ⟨LinearMap.snd L E.V F.V, by
      intro g
      ext x <;> rfl⟩
  let f : E ⟶ P := (FDRep.forget₂HomLinearEquiv E P) fRep
  let g : P ⟶ F := (FDRep.forget₂HomLinearEquiv P F) gRep
  let S : ShortComplex (FDRep L G) := ShortComplex.mk f g (by
    apply (forget₂ (FDRep L G) (Rep L G)).map_injective
    ext x <;> rfl)
  let SRep : ShortComplex (Rep L G) := ShortComplex.mk fRep gRep (by ext x <;> rfl)
  have hRepMap : ((SRep.map (forget₂ (Rep L G) (ModuleCat L))).ShortExact) := by
    let SMod : ShortComplex (ModuleCat L) :=
      CategoryTheory.ShortComplex.moduleCatMk
        (LinearMap.inl L E.V F.V)
        (LinearMap.snd L E.V F.V)
        (by ext x <;> rfl)
    have hSMod : SMod.ShortExact := by
      refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
      · exact CategoryTheory.ShortComplex.Exact.moduleCat_of_range_eq_ker
          (ModuleCat.ofHom (LinearMap.inl L E.V F.V))
          (ModuleCat.ofHom (LinearMap.snd L E.V F.V))
          (by
            ext x
            constructor
            · rintro ⟨y, rfl⟩
              simp
            · intro hx
              refine ⟨x.1, ?_⟩
              ext
              · rfl
              · simpa using hx.symm)
      · exact (ModuleCat.mono_iff_injective _).mpr fun x y h ↦ by
          exact congrArg Prod.fst h
      · exact (ModuleCat.epi_iff_surjective _).mpr fun z ↦ ⟨(0, z), rfl⟩
    simpa [SRep, SMod, fRep, gRep] using hSMod
  have hRepShort : SRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep L G) (ModuleCat L))).1 hRepMap
  have hRep : ((S.map (forget₂ (FDRep L G) (Rep L G))).ShortExact) := by
    simpa [S, SRep, f, g, fRep, gRep] using hRepShort
  have hS : S.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := S) (F := forget₂ (FDRep L G) (Rep L G))).1 hRep
  -- The Grothendieck relation for this short exact sequence is exactly additivity.
  simpa [S, P] using finiteRepGrothendieckClass_middle_eq_left_add_right (L := L) (G := G) S hS

/-- Helper for Exercise 16-16.3-8: the actual finite-representation positive subset is closed
under addition. -/
theorem finiteRepPositiveSubset_add_mem
    {L : Type u} [Field L] {G : Type u} [Group G]
    {a b : R₀[L](G)} (ha : a ∈ R⁺[L](G)) (hb : b ∈ R⁺[L](G)) :
    a + b ∈ R⁺[L](G) := by
  -- Direct sum of representations realizes addition in the Grothendieck group.
  rcases ha with ⟨E, rfl⟩
  rcases hb with ⟨F, rfl⟩
  exact ⟨FDRep.of (Representation.prod E.ρ F.ρ),
    finiteRepGrothendieckClass_prod_eq_add_local (L := L) (G := G) E F⟩

/-- Helper for Exercise 16-16.3-8: the zero class is represented by the zero finite-dimensional
representation. -/
theorem finiteRepPositiveSubset_zero_mem
    {L : Type u} [Field L] {G : Type u} [Group G] :
    (0 : R₀[L](G)) ∈ R⁺[L](G) := by
  -- The zero representation gives the zero Grothendieck class.
  refine ⟨0, ?_⟩
  simpa using finiteRepGrothendieckClass_zero (L := L) (G := G)

/-- Helper for Exercise 16-16.3-8: package the actual positive cone as an additive submonoid. -/
def finiteRepPositiveAddSubmonoid (L : Type u) [Field L] (G : Type u) [Group G] :
    AddSubmonoid (R₀[L](G)) where
  carrier := R⁺[L](G)
  add_mem' := finiteRepPositiveSubset_add_mem (L := L) (G := G)
  zero_mem' := finiteRepPositiveSubset_zero_mem (L := L) (G := G)

/-- Helper for Exercise 16-16.3-8: membership in the packaged positive submonoid is ordinary
membership in Serre's actual positive subset. -/
@[simp] theorem mem_finiteRepPositiveAddSubmonoid
    {L : Type u} [Field L] {G : Type u} [Group G] {x : R₀[L](G)} :
    x ∈ finiteRepPositiveAddSubmonoid L G ↔ x ∈ R⁺[L](G) :=
  Iff.rfl

/-- Helper for Exercise 16-16.3-8: the positive finite-representation cone is generated, as an
additive submonoid, by the simple representation classes. -/
theorem finiteRepPositiveSubset_subset_addSubmonoid_of_simpleClasses
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (T : AddSubmonoid (R₀[L](G)))
    (hsimple : ∀ S : FDRep L G, Simple S → [S]₀ ∈ T) :
    R⁺[L](G) ⊆ (T : Set (R₀[L](G))) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField_e16338 (L := L) (G := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  intro x hx
  have hxcone : x ∈ b.positiveCone :=
    finiteRepPositiveSubset_subset_simpleBasis_positiveCone
      (K := L) (G := G) π hπ_pairwise hπ_complete hx
  rcases (Module.Basis.mem_positiveCone_iff_exists_nonneg_finsupp b x).1 hxcone with
    ⟨c, hc, hcx⟩
  -- Expand the positive element in the simple basis and add the nonnegative simple terms in `T`.
  rw [← hcx]
  refine linearCombination_mem_addSubmonoid_of_nonneg T (fun i ↦ b i) c hc ?_
  intro i
  letI : Simple (π i) := hπ_complete.isSimple i
  simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
    hsimple (π i) inferInstance

end PositiveGeneration

section DecompositionImage

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 16-16.3-8: package the image of the actual positive cone under the
decomposition map as an additive submonoid. -/
def decompositionPositiveImageSubmonoid :
    AddSubmonoid (R₀[k](G)) :=
  (finiteRepPositiveAddSubmonoid K G).map (decompositionHom A K G)

/-- Helper for Exercise 16-16.3-8: membership in the packaged decomposition-image submonoid is
ordinary membership in the set image of the actual positive cone. -/
theorem mem_decompositionPositiveImageSubmonoid {y : R₀[k](G)} :
    y ∈ decompositionPositiveImageSubmonoid (A := A) (K := K) (G := G) ↔
      y ∈ decompositionHom A K G '' R⁺[K](G) := by
  -- Unfold `AddSubmonoid.map` and preserve the source-facing set-image statement.
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Helper for Exercise 16-16.3-8: simple-class membership in the positive decomposition image
extends to all actual positive residue-field classes. -/
theorem finiteRepPositiveSubset_subset_decompositionHom_image_of_simpleClasses
    (hsimple : ∀ S : FDRep k G, Simple S →
      ([S]₀ : R₀[k](G)) ∈ decompositionHom A K G '' R⁺[K](G)) :
    R⁺[k](G) ⊆ decompositionHom A K G '' R⁺[K](G) := by
  -- Use the image as an additive submonoid and invoke simple-class positive generation.
  intro x hx
  have hxT :
      x ∈ decompositionPositiveImageSubmonoid (A := A) (K := K) (G := G) :=
    finiteRepPositiveSubset_subset_addSubmonoid_of_simpleClasses
      (L := k) (G := G)
      (decompositionPositiveImageSubmonoid (A := A) (K := K) (G := G))
      (fun S hS =>
        (mem_decompositionPositiveImageSubmonoid (A := A) (K := K) (G := G)).2
          (hsimple S hS))
      hx
  exact (mem_decompositionPositiveImageSubmonoid (A := A) (K := K) (G := G)).1 hxT

end DecompositionImage

end Representation
