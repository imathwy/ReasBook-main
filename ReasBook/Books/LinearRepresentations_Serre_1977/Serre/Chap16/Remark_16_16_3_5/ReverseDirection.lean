import Mathlib
import LinearRepresentations_Serre_1977.Chap16.Remark_16_16_3_5.Core
import LinearRepresentations_Serre_1977.Chap14.Proposition_14_14_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1.FiniteRepScalarExtension
import LinearRepresentations_Serre_1977.Chap16.Lemma_16_16_3_1.PositiveConeBridge
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_3_3.PositiveBasics

/-!
# Remark 16-16.3-5, reverse direction `(R') ⟹ (R)`

This file proves the "`(R') ⟹ (R)`" half of Serre's Remark 16.3.5 as a standalone theorem
`Representation.satisfiesConditionRPrime_imp_satisfiesConditionR`.

The witnesses for condition `(R)` are taken to be `A' := A` and `K' := K` themselves (a finite
local overring of `A` and its fraction field — vacuously `A` over `A`).  Under these witnesses the
scalar-extension map `R₀[K](G) → R₀[K](G)` is the identity (Conjunct 1), and the decomposition map
sends the actual positive cone over `K` onto the actual positive cone over the residue field
(Conjunct 2), the latter using `(R')` to lift simple residue-field modules.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Function
open scoped Representation TensorProduct MonoidAlgebra ZeroObject

universe u v

namespace Representation

section PositiveCone

variable {K : Type u} [Field K]
variable {G : Type u} [Group G]

-- `finiteRepPositiveSubset`, the scoped notation `R⁺[K](G)`, `mem_finiteRepPositiveSubset_iff` and
-- `SatisfiesConditionR` are reused from the owner module
-- `Serre.Chap16.Proposition_16_16_3_3.PositiveBasics` (imported above) to avoid duplicate
-- declarations under co-import; the definitions there are identical to the copies removed here.

variable [Finite G]

end PositiveCone

section PositiveGeneration

private theorem zsmul_mem_addSubmonoid_of_nonneg
    {M : Type v} [AddCommGroup M]
    (T : AddSubmonoid M) {a : ℤ} (ha : 0 ≤ a) {x : M} (hx : x ∈ T) :
    a • x ∈ T := by
  have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha
  rw [← hcast]
  simpa only [natCast_zsmul] using T.nsmul_mem hx a.toNat

private theorem linearCombination_mem_addSubmonoid_of_nonneg
    {ι : Type u} {M : Type v} [AddCommGroup M]
    (T : AddSubmonoid M) (b : ι → M) (c : ι →₀ ℤ)
    (hc : ∀ i, 0 ≤ c i) (hb : ∀ i, b i ∈ T) :
    Finsupp.linearCombination ℤ b c ∈ T := by
  rw [Finsupp.linearCombination_apply]
  exact AddSubmonoid.sum_mem T (t := c.support) (f := fun i ↦ c i • b i)
    (h := fun i _ ↦ zsmul_mem_addSubmonoid_of_nonneg T (hc i) (hb i))

private theorem existsCompletePairwiseNonisomorphicSimpleFamilyField
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
            rcases hab with ⟨isoab⟩
            rcases hbc with ⟨isobc⟩
            exact ⟨isoab.trans isobc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let π : ι → FDRep L G := fun q ↦ (Quotient.out q).1
  have hπ_pairwise : PairwiseNonisomorphic π := by
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

/-- Actual finite-dimensional classes have nonnegative coordinates in any complete simple-class
basis. -/
private theorem finiteRepPositiveSubset_subset_simpleBasis_positiveCone_r16335
    {K : Type u} [Field K] {G : Type u} [Group G]
    {ι : Type*}
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    {x : R₀[K](G)}
    (hx : x ∈ R⁺[K](G)) :
    x ∈
      (simple_finiteRep_classes_basis_of_complete_family
        π hπ_pairwise hπ_complete).positiveCone := by
  rcases (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hx with ⟨V, hV⟩
  subst hV
  intro i
  exact
    simple_finiteRep_classes_basis_repr_class_nonneg
      (L := K) (G := G) π hπ_pairwise hπ_complete V i

/-- The positive finite-representation cone is generated, as an additive submonoid, by the simple
representation classes. -/
private theorem finiteRepPositiveSubset_subset_addSubmonoid_of_simpleClasses
    {L : Type u} [Field L] {G : Type u} [Group G] [Finite G]
    (T : AddSubmonoid (R₀[L](G)))
    (hsimple : ∀ S : FDRep L G, Simple S → [S]₀ ∈ T) :
    R⁺[L](G) ⊆ (T : Set (R₀[L](G))) := by
  classical
  obtain ⟨ι, π, hπ_pairwise, hπ_complete⟩ :=
    existsCompletePairwiseNonisomorphicSimpleFamilyField (L := L) (G := G)
  let b : Module.Basis ι ℤ (R₀[L](G)) :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  intro x hx
  have hxcone : x ∈ b.positiveCone :=
    finiteRepPositiveSubset_subset_simpleBasis_positiveCone_r16335
      (K := L) (G := G) π hπ_pairwise hπ_complete hx
  rcases (Module.Basis.mem_positiveCone_iff_exists_nonneg_finsupp b x).1 hxcone with
    ⟨c, hc, hcx⟩
  rw [← hcx]
  refine linearCombination_mem_addSubmonoid_of_nonneg T (fun i ↦ b i) c hc ?_
  intro i
  letI : Simple (π i) := hπ_complete.isSimple i
  simpa [b, simple_finiteRep_classes_basis_of_complete_family_apply] using
    hsimple (π i) inferInstance

end PositiveGeneration

section Ext

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-- Helper: an additive homomorphism out of Serre's Grothendieck group `R₀[K](G)` is determined by
its values on the generator classes `[V]₀`. -/
theorem fdRepGrothendieck_addHom_ext {H : Type v} [AddCommGroup H]
    (f g : R₀[K](G) →+ H)
    (h : ∀ V : FDRep K G, f [V]₀ = g [V]₀) : f = g := by
  refine AddMonoidHom.ext ?_
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (finiteRepGrothendieckRelations K G) x
  have hcomp :
      f.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) =
        g.comp (QuotientAddGroup.mk' (finiteRepGrothendieckRelations K G)) := by
    apply FreeAbelianGroup.lift_ext
    intro V
    exact h V
  exact DFunLike.congr_fun hcomp y

end Ext

section SelfIso

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-- Helper: every finite-dimensional representation object is canonically isomorphic to the object
rebuilt from its underlying unbundled representation. -/
def fdRepIsoOfRho (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper: scalar extension of a representation along the identity field map `K → K` gives an
equivariantly isomorphic representation (the tensor left unitor). -/
private theorem nonempty_equiv_scalarExtension_self
    {k : Type u} [Field k] {Gg : Type u} [Group Gg]
    {V : Type u} [AddCommGroup V] [Module k V]
    (ρ : Representation k Gg V) :
    Nonempty (ρ.Equiv (Representation.scalarExtension ρ)) := by
  refine ⟨Representation.Equiv.mk (_root_.TensorProduct.lid k V).symm ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  change (1 : k) ⊗ₜ[k] (ρ g x) =
    LinearMap.baseChange k (ρ g) ((1 : k) ⊗ₜ[k] x)
  rw [LinearMap.baseChange_tmul]

/-- Helper: over the field `K` itself, scalar extension does not change the Grothendieck class. -/
theorem scalarExtension_self_class_eq (V : FDRep K G) :
    [FDRep.scalarExtension (k := K) V]₀ = ([V]₀ : R₀[K](G)) := by
  symm
  refine finiteRepGrothendieckClass_eq_of_nonempty_iso (L := K) (G := G) ?_
  obtain ⟨e⟩ := nonempty_equiv_scalarExtension_self (k := K) (Gg := G) V.ρ
  exact ⟨(fdRepIsoOfRho V).trans e.toFDRepIso⟩

/-- Helper: over the field `K` itself, the scalar-extension homomorphism on `R₀[K](G)` is the
identity. -/
theorem scalarExtensionHom_self_eq_id :
    finiteRepGrothendieckScalarExtensionHom K K G = AddMonoidHom.id (R₀[K](G)) := by
  apply fdRepGrothendieck_addHom_ext (K := K) (G := G)
  intro V
  rw [finiteRepGrothendieckScalarExtensionHom_class_eq, AddMonoidHom.id_apply]
  exact scalarExtension_self_class_eq V

end SelfIso

section ProdAdditivity

variable {L : Type u} [Field L] {G : Type u} [Group G]

/-- Helper: the Grothendieck class of a binary product representation is the sum of the classes of
its two factors. -/
theorem finiteRepGrothendieckClass_prod_eq_add (E F : FDRep L G) :
    [FDRep.of (Representation.prod E.ρ F.ρ)]₀ = ([E]₀ : R₀[L](G)) + [F]₀ := by
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
      · exact (ModuleCat.mono_iff_injective _).mpr fun x y h => by
          exact congrArg Prod.fst h
      · exact (ModuleCat.epi_iff_surjective _).mpr fun z => ⟨(0, z), rfl⟩
    simpa [SRep, SMod, fRep, gRep] using hSMod
  have hRepShort : SRep.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := forget₂ (Rep L G) (ModuleCat L))).1 hRepMap
  have hRep : ((S.map (forget₂ (FDRep L G) (Rep L G))).ShortExact) := by
    simpa [S, SRep, f, g, fRep, gRep] using hRepShort
  have hS : S.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff
      (S := S) (F := forget₂ (FDRep L G) (Rep L G))).1 hRep
  simpa [S, P] using finiteRepGrothendieckClass_middle_eq_left_add_right (L := L) (G := G) S hS

end ProdAdditivity

section ReverseDirection

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

local notation "κ" => IsLocalRing.ResidueField A

/-- The actual positive cone `R⁺[K](G)`, packaged as an additive submonoid of `R₀[K](G)`:
it is the range of `finiteRepGrothendieckClass K G`, closed under addition (via direct sums) and
containing zero. -/
def finiteRepPositiveSubmonoid (K : Type u) [Field K] (G : Type u) [Group G] :
    AddSubmonoid (R₀[K](G)) where
  carrier := R⁺[K](G)
  add_mem' := by
    rintro a b ⟨E, rfl⟩ ⟨F, rfl⟩
    exact ⟨FDRep.of (Representation.prod E.ρ F.ρ),
      finiteRepGrothendieckClass_prod_eq_add (L := K) (G := G) E F⟩
  zero_mem' := ⟨0, by simpa using finiteRepGrothendieckClass_zero (L := K) (G := G)⟩

@[simp] theorem mem_finiteRepPositiveSubmonoid {K : Type u} [Field K] {G : Type u} [Group G]
    {x : R₀[K](G)} :
    x ∈ finiteRepPositiveSubmonoid K G ↔ x ∈ R⁺[K](G) := Iff.rfl

/-- The image of the actual positive cone over `K` under the decomposition homomorphism, packaged
as an additive submonoid of `R₀[κ](G)`. -/
def decompositionImageSubmonoid : AddSubmonoid (R₀[κ](G)) :=
  (finiteRepPositiveSubmonoid K G).map (decompositionHom A K G)

theorem mem_decompositionImageSubmonoid {y : R₀[κ](G)} :
    y ∈ decompositionImageSubmonoid (A := A) (K := K) (G := G) ↔
      y ∈ decompositionHom A K G '' R⁺[K](G) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- For any simple residue-field representation `S`, its class lies in the image of the actual
positive cone over `K` under the decomposition map — using condition `(R')` to produce a lift. -/
theorem simple_class_mem_decompositionImage
    (hR' : SatisfiesConditionRPrime A K G)
    (S : FDRep κ G) (hS : Simple S) :
    ([S]₀ : R₀[κ](G)) ∈ decompositionImageSubmonoid (A := A) (K := K) (G := G) := by
  obtain ⟨X, _hXsimple, L, ⟨iso⟩⟩ := hR' S hS
  refine ⟨[X]₀, ?_, ?_⟩
  · exact (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).2 ⟨X, rfl⟩
  · rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) X L]
    exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := κ) (G := G) ⟨iso⟩

/-- Conjunct 2 of `(R)` for the witnesses `A' := A`, `K' := K`: the decomposition map sends the
actual positive cone over `K` onto the actual positive cone over the residue field `κ`. -/
theorem decompositionHom_image_eq
    (hR' : SatisfiesConditionRPrime A K G) :
    decompositionHom A K G '' R⁺[K](G) = R⁺[IsLocalRing.ResidueField A](G) := by
  apply Set.Subset.antisymm
  · -- ⊆ : the image of a class is the class of a reduction, hence positive.
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨V, rfl⟩ := (mem_finiteRepPositiveSubset_iff (K := K) (G := G)).1 hx
    obtain ⟨L⟩ := Representation.exists_stableLattice A V.ρ
    rw [decompositionHom_finiteRepClass_eq (A := A) (K := K) (G := G) V L]
    exact (mem_finiteRepPositiveSubset_iff (K := κ) (G := G)).2
      ⟨FDRep.of L.reductionRepresentation, rfl⟩
  · -- ⊇ : actual positive classes are generated by simple classes.
    intro w hw
    rw [← mem_decompositionImageSubmonoid (A := A) (K := K) (G := G)]
    exact
      finiteRepPositiveSubset_subset_addSubmonoid_of_simpleClasses
        (L := κ) (G := G)
        (decompositionImageSubmonoid (A := A) (K := K) (G := G))
        (fun S hS =>
          simple_class_mem_decompositionImage (A := A) (K := K) (G := G) hR' S hS)
        hw

/-- **Remark 16-16.3-5, reverse direction.**  If the modular system `(A, K, k)` satisfies condition
`(R')` — every simple `k[G]`-module is the reduction of a simple finite-dimensional
`K[G]`-representation — then `R⁺[K](G)` satisfies condition `(R)` (witnessed trivially by `A' := A`,
`K' := K`). -/
theorem satisfiesConditionRPrime_imp_satisfiesConditionR
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {G : Type u} [Group G] [Finite G]
    (hR' : Representation.SatisfiesConditionRPrime A K G) :
    Representation.SatisfiesConditionR (Representation.finiteRepPositiveSubset K G) A := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · -- Conjunct 1: scalar extension along `K → K` is the identity.
    rw [scalarExtensionHom_self_eq_id]
    ext x
    simp only [Set.mem_preimage, AddMonoidHom.coe_id, id_eq]
  · -- Conjunct 2: the decomposition map sends the positive cone onto the residue positive cone.
    exact decompositionHom_image_eq (A := A) (K := K) (G := G) hR'

end ReverseDirection

end Representation
