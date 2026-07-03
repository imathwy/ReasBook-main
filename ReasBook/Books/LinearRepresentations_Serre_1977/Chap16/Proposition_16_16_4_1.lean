import Serre.Chap16.Proposition_16_16_4_1.ReductionBridge
import Serre.Chap16.Proposition_16_16_4_1.FourierBridge
import Serre.Chap16.Proposition_16_16_4_1.CentralProjectorBridge

-- Stable theorem-local helper owners now live under the local index.
-- This target keeps the active declarations and the remaining unfinished proof blocks.

-- Declarations for this item will be appended below by the statement pipeline.


noncomputable section

open scoped BigOperators MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: in this defect-zero section we realize the finite group as
a `Fintype` whenever Serre's coefficient formulas sum over `G`. -/
local instance instFintypeGDefectZero : Fintype G := Fintype.ofFinite G

/-- Helper for Proposition 16-16.4-1: a defect-zero simple representation has nontrivial carrier.
Indeed, if the carrier were subsingleton then the irreducibility forced by `HasDefectZero` would
collapse `⊥` and `⊤`, contradicting simplicity of the subrepresentation lattice. -/
lemma carrier_nontrivial_of_defect_zero
    (hdefect : ρ.HasDefectZero p) : Nontrivial E := by
  letI : ρ.IsIrreducible := hdefect.isIrreducible
  -- An irreducible representation cannot live on a subsingleton carrier, or else `⊥ = ⊤`.
  by_contra hE
  letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
  have hbot_top : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) hbot_top

/-- Helper for Proposition 16-16.4-1: scalar extension of lattice endomorphisms along the
base-change inclusion `P ↪ E` is injective. This is the descent step from an ambient `K`-linear
identity back to the original `A`-linear endomorphism of the lattice. -/
lemma toSubmodule_endHom_injective :
    Function.Injective
      ((L.toSubmodule_subtype_isBaseChange).endHom :
        Module.End A L.toSubmodule → Module.End K E) := by
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  intro φ ψ hφψ
  ext x
  -- Evaluate the ambient equality on the image of the lattice and then drop back to the subtype.
  have hx := congrArg
    (fun f : Module.End K E ↦ f (((x : L.toSubmodule) : E))) hφψ
  calc
    ↑(φ x) = hf.endHom φ (((x : L.toSubmodule) : E)) := by
      symm
      simpa using hf.endHom_comp_apply φ x
    _ = hf.endHom ψ (((x : L.toSubmodule) : E)) := hx
    _ = ↑(ψ x) := by
      simpa using hf.endHom_comp_apply ψ x

/-- Helper for Proposition 16-16.4-1: once the mapped Fourier element acts on the ambient
representation as the scalar-extended endomorphism `φ`, injectivity of base change descends that
identity to the original lattice action. -/
lemma serre_fourier_action_eq_endHom_of_ambient
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hambient :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ) :
    L.toRepresentation.asAlgebraHom (L.serre_fourier_element hdefect φ) = φ := by
  -- Compare both lattice endomorphisms after scalar extension to `E`, where the ambient action is
  -- already known to compute coefficientwise.
  apply L.toSubmodule_endHom_injective
  rw [← L.ambient_action_map_eq_endHom (u := L.serre_fourier_element hdefect φ)]
  exact hambient

/-- Helper for Proposition 16-16.4-1: the fraction field of the valuation ring has either
characteristic zero or the same prime characteristic `p` as the residue field. This isolates the
remaining Fourier step into its mixed-characteristic and equal-characteristic branches. -/
lemma charZero_or_charP_fraction_field (_L : StableLattice A ρ)
    [hres : CharP (IsLocalRing.ResidueField A) p] :
    CharZero K ∨ CharP K p := by
  by_cases hchar0 : ringChar K = 0
  · -- If the fraction field has characteristic zero, record that branch explicitly.
    left
    exact (CharP.ringChar_zero_iff_CharZero (R := K)).mp hchar0
  · let q := ringChar K
    have hqprime : Nat.Prime q := by
      rcases CharP.char_is_prime_or_zero K q with hqprime | hqzero
      · exact hqprime
      · exact (hchar0 hqzero).elim
    letI : Fact q.Prime := ⟨hqprime⟩
    letI : CharP K q := ringChar.charP (R := K)
    letI : CharP A q :=
      RingHom.charP (algebraMap A K) (IsFractionRing.injective A K) q
    have hq0 : (q : IsLocalRing.ResidueField A) = 0 := by
      -- Push the characteristic-`q` vanishing from `A` to the residue field quotient.
      change
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (q : A) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) 0
      exact congrArg (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))
        (CharP.cast_eq_zero (R := A) q)
    letI : CharP (IsLocalRing.ResidueField A) q :=
      ringChar.of_eq
        (CharP.ringChar_of_prime_eq_zero
          (R := IsLocalRing.ResidueField A) hqprime hq0)
    have hpchar : ringChar (IsLocalRing.ResidueField A) = p :=
      @ringChar.eq _ _ p hres
    have hqchar : ringChar (IsLocalRing.ResidueField A) = q :=
      ringChar.eq (R := IsLocalRing.ResidueField A) q
    have hqp : q = p := by
      -- The residue field cannot carry two distinct prime characteristics.
      calc
        q = ringChar (IsLocalRing.ResidueField A) := hqchar.symm
        _ = p := hpchar
    right
    exact hqp ▸ (inferInstance : CharP K q)

/-- Helper for Proposition 16-16.4-1: base change carries the lattice action of a group element to
the ambient `K`-linear action. -/
lemma endHom_toRepresentation_eq_ambient_action
    (s : G) :
    (L.toSubmodule_subtype_isBaseChange).endHom (L.toRepresentation s) = ρ s := by
  -- Read the group element through the established action/base-change compatibility.
  simpa [Representation.asAlgebraHom_of] using
    (L.ambient_action_map_eq_endHom (u := MonoidAlgebra.of A G s)).symm

/-- Helper for Proposition 16-16.4-1: an injective map `c : ι → κ` has a unique preimage above
every point of `Finset.univ.image c`. This is the indexing normalization used to extend packet
families to a complete irreducible family by support. -/
lemma existsUnique_preimage_of_mem_image_support_local
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {c : ι → κ}
    (hc : Function.Injective c) {q : κ} (hq : q ∈ Finset.univ.image c) :
    ∃! i : ι, c i = q := by
  classical
  -- Read `q` as an actual image point and use injectivity to force uniqueness.
  rcases Finset.mem_image.mp hq with ⟨i, -, rfl⟩
  refine ⟨i, rfl, ?_⟩
  intro j hj
  exact hc hj

/-- Helper for Proposition 16-16.4-1: extend a packet-indexed family to the complete-family index
set by transporting along the unique preimage on `Finset.univ.image c` and setting every
off-support coordinate to `0`. -/
noncomputable def family_supported_on_image_local
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {V : κ → Type*} [∀ q, Zero (V q)]
    (c : ι → κ) (hc : Function.Injective c)
    (f : ∀ i, V (c i)) :
    ∀ q, V q :=
  fun q =>
    if hq : q ∈ Finset.univ.image c then
      let i := Classical.choose
        (existsUnique_preimage_of_mem_image_support_local (c := c) hc hq)
      let hi : c i = q :=
        (Classical.choose_spec
          (existsUnique_preimage_of_mem_image_support_local (c := c) hc hq)).1
      hi ▸ f i
    else
      0

/-- Helper for Proposition 16-16.4-1: off the packet image, the supported-family extension
vanishes definitionally. This is the off-support rewrite used to drop the complementary terms in
the characteristic-zero coefficient sum. -/
lemma family_supported_on_image_apply_of_not_mem_local
    {ι : Type*} [Fintype ι]
    {κ : Type*} [DecidableEq κ]
    {V : κ → Type*} [∀ q, Zero (V q)]
    {c : ι → κ} (hc : Function.Injective c)
    (f : ∀ i, V (c i)) {q : κ}
    (hq : q ∉ Finset.univ.image c) :
    family_supported_on_image_local c hc f q = 0 := by
  -- Off the image, the definition already uses the zero branch.
  simp [family_supported_on_image_local, hq]

/-- Helper for Proposition 16-16.4-1: the coefficient of the inverse-Wedderburn preimage of a
family supported on `Finset.univ.image c` is exactly the sum of the trace terms over the packet
labels. This isolates the first genuine characteristic-zero coefficient normalization before the
packet multiplicity formula is used. -/
lemma supported_family_symm_coeff_eq_sum_local
    [CharZero K]
    {ι : Type*} [Fintype ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → Rep (AlgebraicClosure K) G)
    [∀ q, FiniteDimensional (AlgebraicClosure K) (π q)]
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun q ↦ FDRep.of (π q).ρ))
    (c : ι → κ) (hc : Function.Injective c)
    (F : ∀ i, Module.End (AlgebraicClosure K) (π (c i))) (s : G) :
    let u : (AlgebraicClosure K)[G] :=
      (Representation.irreducibleFamilyEndAlgEquiv (π := π)
        hπ_pairwise hπ_complete).symm
        (family_supported_on_image_local
          (V := fun q ↦ Module.End (AlgebraicClosure K) (π q)) c hc F)
    u s =
      ((Nat.card G : AlgebraicClosure K)⁻¹) *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (π (c i)) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (π (c i))
            ((π (c i)).ρ s⁻¹ *
              family_supported_on_image_local
                (V := fun q ↦ Module.End (AlgebraicClosure K) (π q)) c hc F (c i)) := by
  classical
  dsimp
  have hcard_ne : (Nat.card G : AlgebraicClosure K) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : AlgebraicClosure K) := invertibleOfNonzero hcard_ne
  let term : κ → AlgebraicClosure K := fun q ↦
    (Module.finrank (AlgebraicClosure K) (π q) : AlgebraicClosure K) *
      LinearMap.trace (AlgebraicClosure K) (π q)
        ((π q).ρ s⁻¹ * family_supported_on_image_local c hc F q)
  calc
    ((Representation.irreducibleFamilyEndAlgEquiv (π := π)
        hπ_pairwise hπ_complete).symm
        (family_supported_on_image_local
          (V := fun q ↦ Module.End (AlgebraicClosure K) (π q)) c hc F)) s =
      ((Nat.card G : AlgebraicClosure K)⁻¹) * ∑ᶠ q : κ, term q := by
        -- Start from the Chapter `6` coefficient formula for the inverse-Wedderburn preimage.
        simpa [term] using
          (Representation.irreducibleFamilyEndAlgEquiv_symm_apply
            (π := π) hπ_pairwise hπ_complete
            (family_supported_on_image_local
              (V := fun q ↦ Module.End (AlgebraicClosure K) (π q)) c hc F) s)
    _ = ((Nat.card G : AlgebraicClosure K)⁻¹) * (∑ q : κ, term q) := by
        -- Replace the finite `finsum` by the ordinary `Finset.univ` sum on the complete-family
        -- index type.
        rw [Representation.finsum_eq_sum_univ (K := AlgebraicClosure K) term]
    _ = ((Nat.card G : AlgebraicClosure K)⁻¹) * ((Finset.univ.image c).sum term) := by
        congr 1
        symm
        refine Finset.sum_subset (by intro q hq; simp) ?_
        intro q hq_univ hq_not_mem
        -- Off the packet support, the family is zero, so the corresponding trace term vanishes.
        rw [family_supported_on_image_apply_of_not_mem_local (hc := hc) F hq_not_mem]
        simp [term]
    _ = ((Nat.card G : AlgebraicClosure K)⁻¹) * (∑ i : ι, term (c i)) := by
        congr 1
        -- Reindex the supported complete-family sum along the injective packet map `c`.
        simpa using
          (Finset.sum_image (s := Finset.univ) (g := c) (f := term) hc.injOn)
    _ = ((Nat.card G : AlgebraicClosure K)⁻¹) *
        ∑ i : ι, (Module.finrank (AlgebraicClosure K) (π (c i)) : AlgebraicClosure K) *
          LinearMap.trace (AlgebraicClosure K) (π (c i))
            ((π (c i)).ρ s⁻¹ *
              family_supported_on_image_local
                (V := fun q ↦ Module.End (AlgebraicClosure K) (π q)) c hc F (c i)) := by
        rfl

/-- Helper for Proposition 16-16.4-1: over `AlgebraicClosure K`, the remaining source-faithful
packet computation should identify the mapped Serre Fourier element with the supported complete
family attached to the scalar extension of `φ`. This extracted owner isolates the genuine
coefficient-comparison blocker from the later descent back to `K`. -/
lemma charZero_algClosure_fourier_action_eq_baseChange_local
    [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- Route correction: the characteristic-zero branch now starts from the repaired
  -- packet-to-complete-family owner instead of the placeholder `True` wrapper in `PacketBridge`.
  -- TODO: define the supported complete-family endomorphism carrying the transported copies of
  -- `φ`, use `supported_family_symm_coeff_eq_sum_local` to compute the inverse-Wedderburn
  -- preimage coefficients packetwise, collapse that sum to Serre's mapped coefficient formula
  -- with the trace-conjugation and packet-multiplicity identities, then reassemble the ambient
  -- action by
  -- `internal_decomposition_endomorphism_ext_local`.
  sorry

/-- Helper for Proposition 16-16.4-1: once the algebraic-closure packet calculation identifies
Serre's mapped Fourier element with the scalar-extended ambient endomorphism attached to `φ`,
faithful descent immediately recovers the ambient `K`-linear action identity. This isolates the
remaining characteristic-zero blocker to a single scalar-extension equality. -/
lemma charZero_fourier_branch_consequences_of_algClosure_action_local
    [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hbar :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
            (L.serre_fourier_element hdefect φ)) =
        LinearMap.baseChange (AlgebraicClosure K)
          ((L.toSubmodule_subtype_isBaseChange).endHom φ)) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Descend the scalar-extension action identity through the faithful base-change functor.
  exact
    StableLattice.ambient_action_eq_of_algClosure_baseChange_eq_local
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      hbar

/-- Helper for Proposition 16-16.4-1: the characteristic-zero branch of the remaining Fourier
packet argument. This target-local wrapper descends the algebraic-closure packet computation back
to `K` and keeps only the ambient action identity that the source proof actually needs as the
hard characteristic-sensitive step. -/
lemma charZero_fourier_branch_consequences
    [CharZero K]
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  intro φ
  -- Route correction: the wrapper now only descends the dedicated algebraic-closure owner back to
  -- `K`, so the remaining blocker is isolated in one place.
  exact
    L.charZero_fourier_branch_consequences_of_algClosure_action_local
      (p := p) (ρ := ρ) hdefect φ
      (L.charZero_algClosure_fourier_action_eq_baseChange_local
        (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K` and
reuses the corresponding projector-annihilator statement. -/
lemma algClosure_fourier_action_eq_baseChange_of_ambient_action_local
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule)
    (hambient :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- Lift the ambient `K`-action identity through scalar extension to the algebraic closure.
  exact
    StableLattice.algClosure_ambient_action_eq_of_local_action_eq
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      hambient

/-- Helper for Proposition 16-16.4-1: with respect to a finite `A`-basis of the stable lattice,
every lattice endomorphism is the sum of its matrix coefficients times the corresponding rank-one
basis endomorphisms. This is the source-faithful linear-algebra normalization used before proving
the equal-characteristic Fourier identity on one matrix unit at a time. -/
lemma endHom_eq_sum_matrix_units_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (φ : Module.End A L.toSubmodule) :
    φ =
      ∑ i : ι, ∑ j : ι,
        (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)) := by
  -- Evaluate both endomorphisms on each basis vector and collapse the rank-one terms by the
  -- coordinate identities of `b`.
  have hbasis :
      ∀ i0 : ι,
        φ (b i0) =
          (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) := by
    intro i0
    have hφk :
        φ (b i0) = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := by
      simpa using
        (Matrix.toLin_self (v₁ := b) (v₂ := b)
          (M := LinearMap.toMatrix b b φ) i0)
    calc
      φ (b i0) = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := hφk
      _ = (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) := by
            symm
            calc
              (∑ i : ι, ∑ j : ι,
                  (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) (b i0) =
                  ∑ i : ι, ∑ j : ι,
                    (LinearMap.toMatrix b b φ j i) • (((b.coord i).smulRight (b j)) (b i0)) := by
                      simp
              _ = ∑ i : ι, if i = i0 then ∑ j : ι, (LinearMap.toMatrix b b φ j i) • b j else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      by_cases hik : i = i0
                      · subst hik
                        simp [LinearMap.smulRight_apply, Module.Basis.coord_apply]
                      · simp [LinearMap.smulRight_apply, Module.Basis.coord_apply, hik]
              _ = ∑ j : ι, (LinearMap.toMatrix b b φ j i0) • b j := by
                      simp
  exact Module.Basis.ext b hbasis

/-- Helper for Proposition 16-16.4-1: the rank-one endomorphism built from `b.coord i` and `b j`
is exactly the `(j,i)` standard basis endomorphism attached to `b`. This is the bridge from the
source proof's basis-unit language to mathlib's `b.end`. -/
lemma basis_unit_eq_end_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι) :
    ((b.coord i).smulRight (b j)) = b.end (j, i) := by
  -- Compare the two endomorphisms on basis vectors; both send `b i` to `b j` and kill the other
  -- basis vectors.
  apply b.ext
  intro a
  by_cases hk : i = a
  · subst hk
    simp [Module.Basis.end_apply_apply, Module.Basis.coord_apply]
  · have hki : a ≠ i := by
      simpa [eq_comm] using hk
    simp [Module.Basis.end_apply_apply, Module.Basis.coord_apply, hk, hki]

/-- Helper for Proposition 16-16.4-1: after scalar extension to the ambient representation, the
rank-one lattice endomorphism attached to `b i` and `b j` is still the standard matrix unit in
the extended basis. -/
lemma basis_unit_endHom_toMatrix_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
      ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) =
        Matrix.stdBasis K ι ι (j, i) :=
  by
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  have hbasis : hf.basis b = b.extendOfIsLattice K := by
    ext a
    simp [IsBaseChange.basis_apply, Module.Basis.extendOfIsLattice_apply]
  -- First compute the lattice matrix of the rank-one operator, then transport it coefficientwise
  -- to the ambient basis provided by base change.
  calc
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) =
      LinearMap.toMatrix (hf.basis b) (hf.basis b)
        (hf.endHom ((b.coord i).smulRight (b j))) := by
          rw [hbasis]
    _ =
      (LinearMap.toMatrix b b (((b.coord i).smulRight (b j)))).map (algebraMap A K) := by
        simpa using
          (IsBaseChange.endHom_toMatrix (ibcM := hf) (b := b)
            (f := ((b.coord i).smulRight (b j))))
    _ = (LinearMap.toMatrix b b (b.end (j, i))).map (algebraMap A K) := by
      rw [L.basis_unit_eq_end_local (b := b) i j]
    _ = (Matrix.stdBasis A ι ι (j, i)).map (algebraMap A K) := by
      rw [Module.Basis.end_apply, LinearMap.toMatrix_toLin]
    _ = Matrix.stdBasis K ι ι (j, i) := by
      ext a m
      by_cases hja : j = a
      · by_cases him : i = m
        · subst hja
          subst him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply]
        · have hmi : ¬m = i := by simpa [eq_comm] using him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, him, hmi]
      · by_cases him : i = m
        · have hne : ¬a = j := by simpa [eq_comm] using hja
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, hne, him]
        · have hne : ¬a = j := by simpa [eq_comm] using hja
          have hmi : ¬m = i := by simpa [eq_comm] using him
          simp [Matrix.stdBasis_eq_single, Matrix.map_apply, hja, hne, him, hmi]

/-- Helper for Proposition 16-16.4-1: the `(a,m)` entry of the scalar-extended basis unit is the
corresponding entry of the standard matrix unit. This packages the target side of the remaining
equal-characteristic matrix-coefficient comparison into a direct rewrite lemma. -/
lemma basis_unit_endHom_toMatrix_entry_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
      ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the established matrix-unit identity at the chosen `(a,m)` entry.
  exact congrArg (fun M : Matrix ι ι K ↦ M a m)
    (L.basis_unit_endHom_toMatrix_local (ρ := ρ) (b := b) i j)

/-- Helper for Proposition 16-16.4-1: the trace coefficient appearing in Serre's integral Fourier
formula for a basis matrix unit is exactly the corresponding ambient matrix entry of `ρ s⁻¹`. -/
lemma trace_comp_basis_unit_eq_matrix_entry_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (s : G) (i j : ι) :
    algebraMap A K
        (LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) =
      LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j :=
  by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  have hbasis : hf.basis b = e := by
    ext a
    simp [e, IsBaseChange.basis_apply, Module.Basis.extendOfIsLattice_apply]
  have htrace :
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j))) =
        LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j := by
    -- Rewrite the basis unit as `b.end (j,i)` and compute the trace on matrices by multiplying by
    -- a single-entry matrix.
    calc
      LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j))) =
        LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp (b.end (j, i))) := by
            rw [L.basis_unit_eq_end_local (b := b) i j]
      _ = Matrix.trace
            (LinearMap.toMatrix b b ((L.toRepresentation s⁻¹).comp (b.end (j, i)))) := by
            rw [LinearMap.trace_eq_matrix_trace A b]
      _ = Matrix.trace
            (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) *
              Matrix.stdBasis A ι ι (j, i)) := by
            change Matrix.trace
                (LinearMap.toMatrix b b (L.toRepresentation s⁻¹ * b.end (j, i))) =
              Matrix.trace
                (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) *
                  Matrix.stdBasis A ι ι (j, i))
            rw [LinearMap.toMatrix_mul, Module.Basis.end_apply, LinearMap.toMatrix_toLin]
      _ = LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j := by
            rw [Matrix.stdBasis_eq_single, Matrix.trace_mul_single]
            simp
  have hmatrix :
      LinearMap.toMatrix e e (ρ s⁻¹) =
        (LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K) := by
    -- Base change identifies the ambient action matrix with the coefficientwise image of the
    -- lattice action matrix.
    calc
      LinearMap.toMatrix e e (ρ s⁻¹) =
        LinearMap.toMatrix e e (hf.endHom (L.toRepresentation s⁻¹)) := by
          rw [L.endHom_toRepresentation_eq_ambient_action (ρ := ρ) (s := s⁻¹)]
      _ = LinearMap.toMatrix (hf.basis b) (hf.basis b) (hf.endHom (L.toRepresentation s⁻¹)) := by
          rw [hbasis]
      _ = (LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K) := by
          simpa using
            (IsBaseChange.endHom_toMatrix (ibcM := hf) (b := b) (f := L.toRepresentation s⁻¹))
  calc
    algebraMap A K
        (LinearMap.trace A L.toSubmodule
          ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) =
      algebraMap A K (LinearMap.toMatrix b b (L.toRepresentation s⁻¹) i j) := by
        rw [htrace]
    _ = ((LinearMap.toMatrix b b (L.toRepresentation s⁻¹)).map (algebraMap A K)) i j := by
        rfl
    _ = LinearMap.toMatrix e e (ρ s⁻¹) i j := by
        simpa [Matrix.map_apply] using congrArg (fun M : Matrix ι ι K ↦ M i j) hmatrix.symm

/-- Helper for Proposition 16-16.4-1: taking one coordinate of `e.repr` after a finite sum of
scalar multiples turns the expression into the corresponding scalar-weighted sum of coordinates. -/
lemma basis_repr_sum_smul_apply_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : Type*} [Fintype β]
    (e : Module.Basis ι K E) (c : β → K) (v : β → E) (a : ι) :
    e.repr (∑ s : β, c s • v s) a = ∑ s : β, c s * e.repr (v s) a := by
  -- Push `repr` through the sum and each scalar action, then read the chosen coordinate.
  rw [map_sum]
  calc
    (∑ s : β, e.repr (c s • v s)) a =
      ((↑(∑ s : β, c s • e.repr (v s) : ι →₀ K) : ι → K) a) := by
        refine congrArg (fun z : ι →₀ K ↦ z a) ?_
        refine Finset.sum_congr rfl ?_
        intro s hs
        simpa using (e.repr.map_smul (c s) (v s))
    _ = ∑ s : β, c s * e.repr (v s) a := by
        rw [Finsupp.coe_finset_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro s hs
        simp [Finsupp.smul_apply, smul_eq_mul]

/-- Helper for Proposition 16-16.4-1: the `(a,m)` matrix entry of the ambient action of Serre's
integral Fourier element attached to one basis matrix unit is exactly the explicit defect-zero
coefficient sum appearing in the source orthogonality formula. -/
lemma integral_fourier_matrix_unit_action_entry_eq_sum_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  let u : A[G] := L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))
  have hu :
      MonoidAlgebra.mapRingHom G (algebraMap A K) u =
        ∑ s : G, MonoidAlgebra.single s (algebraMap A K (u s)) := by
    -- Expand the mapped Fourier element in the delta basis of `K[G]`.
    simpa [MonoidAlgebra.mapRingHom_apply] using
      (Finsupp.univ_sum_single (MonoidAlgebra.mapRingHom G (algebraMap A K) u)).symm
  -- Follow Serre's source route entrywise: first expand the group-algebra action as a finite sum,
  -- then rewrite the coefficient attached to each group element.
  calc
    LinearMap.toMatrix e e (ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u)) a m =
      LinearMap.toMatrix e e
        (ρ.asAlgebraHom (∑ s : G, MonoidAlgebra.single s (algebraMap A K (u s)))) a m := by
          rw [hu]
    _ =
      LinearMap.toMatrix e e (∑ s : G, algebraMap A K (u s) • ρ s) a m := by
          rw [map_sum]
          simp [Representation.asAlgebraHom_single]
    _ =
      ∑ s : G, algebraMap A K (u s) * LinearMap.toMatrix e e (ρ s) a m := by
          simpa [LinearMap.toMatrix_apply] using
            basis_repr_sum_smul_apply_local
              (e := e)
              (c := fun s : G ↦ algebraMap A K (u s))
              (v := fun s : G ↦ ρ s (e m))
              (a := a)
    _ =
      ∑ s : G,
        algebraMap A K
            (L.defect_zero_dim_ratio hdefect *
              LinearMap.trace A L.toSubmodule
                ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) *
          LinearMap.toMatrix e e (ρ s) a m := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          simp [u, L.serre_fourier_element_apply]
    _ =
      ∑ s : G,
        algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          algebraMap A K
            (LinearMap.trace A L.toSubmodule
              ((L.toRepresentation s⁻¹).comp ((b.coord i).smulRight (b j)))) *
          LinearMap.toMatrix e e (ρ s) a m := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [map_mul]
    _ =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
        (LinearMap.toMatrix e e (ρ s) a m) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [L.trace_comp_basis_unit_eq_matrix_entry_local (ρ := ρ) (b := b) (s := s) (i := i)
            (j := j)]

/-- Helper for Proposition 16-16.4-1: once the source coefficient sum for one basis matrix unit is
identified entrywise with the standard matrix unit, matrix extensionality upgrades that
coefficient formula to the full ambient operator identity. This isolates the formal matrix
reassembly from the remaining equal-characteristic coefficient computation. -/
lemma basis_unit_action_eq_of_matrix_entry_formula_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p)
    (hentry :
      ∀ a m : ι,
        ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
            (Matrix.stdBasis K ι ι (j, i)) a m) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  apply (LinearMap.toMatrix e e).injective
  ext a m
  -- Read the source action entrywise, substitute the coefficient formula, and then rewrite the
  -- target basis unit as the same standard matrix unit.
  calc
    LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
        (LinearMap.toMatrix e e (ρ s) a m) := by
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := hentry a m
    _ =
      LinearMap.toMatrix e e
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m := by
          symm
          exact L.basis_unit_endHom_toMatrix_entry_local (ρ := ρ) (b := b) i j a m

/-- Helper for Proposition 16-16.4-1: once Serre's source coefficient identity is known for one
basis unit, the corresponding operator-level Proposition `11` specialization follows immediately
by matrix extensionality. This isolates the formal reassembly from the still-missing coefficient
calculation. -/
lemma basis_unit_operator_of_entry_formula_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p)
    (hentry :
      ∀ a m : ι,
        ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
          (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
            (Matrix.stdBasis K ι ι (j, i)) a m) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- This is exactly the matrix-extensionality bridge proved just above, now packaged under the
  -- Proposition `11` owner layer.
  exact
    L.basis_unit_action_eq_of_matrix_entry_formula_local
      (p := p) (ρ := ρ) (b := b) i j hdefect hentry

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the primitive owner is
the raw matrix-coefficient orthogonality formula for one basis unit. This isolates the exact
source Proposition `11` coefficient computation before any operator-level reassembly. -/
lemma defect_zero_matrix_coefficient_orthogonality_owner_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Route correction: make the coefficient identity the primitive equal-characteristic owner, so
  -- the Proposition `11` operator theorem below is now only a matrix-extensionality wrapper.
  -- TODO: prove the source coefficient identity directly from Proposition `11` for the basis unit
  -- `((b.coord i).smulRight (b j))`, rewriting the trace term by
  -- `trace_comp_basis_unit_eq_matrix_entry_local` and the target operator entry by
  -- `basis_unit_endHom_toMatrix_entry_local`.
  sorry

/-- Helper for Proposition 16-16.4-1: once the basis-unit Fourier action is known as an ambient
operator identity, reading the `(a,m)` matrix entry recovers the corresponding source
orthogonality coefficient formula. This isolates the formal entry-extraction step from the
remaining basis-unit action blocker. -/
lemma defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p)
    (hact :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
        (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  let e : Module.Basis ι K E := b.extendOfIsLattice K
  -- Read the source coefficient sum as the `(a,m)` entry of the Fourier action operator.
  calc
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix e e (ρ s⁻¹) i j) *
      (LinearMap.toMatrix e e (ρ s) a m) =
      LinearMap.toMatrix e e
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m := by
          symm
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ =
      LinearMap.toMatrix e e
        ((L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j))) a m := by
          -- Apply `toMatrix` to the assumed primitive basis-unit action identity.
          exact congrArg (fun M : Matrix ι ι K ↦ M a m)
            (congrArg (LinearMap.toMatrix e e) hact)
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := by
          exact
            L.basis_unit_endHom_toMatrix_entry_local
              (ρ := ρ) (b := b) i j a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, Serre's source
Proposition `11` should first identify the Fourier element of one basis matrix unit with the
corresponding scalar-extended rank-one operator. This operator-level owner is the primitive
equal-characteristic step; the entrywise orthogonality formula is only a later matrix-coordinate
corollary. -/
lemma prop11_basis_unit_operator_specialization_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Route correction: the primitive owner in equal characteristic is now the operator theorem
  -- matching Serre's Proposition `11`, rather than another entrywise restatement of the same
  -- orthogonality computation.
  refine
    L.basis_unit_operator_of_entry_formula_local
      (p := p) (ρ := ρ) (b := b) i j hdefect ?_
  intro a m
  -- Consume the primitive coefficient owner; the operator theorem is now just the formal wrapper.
  exact
    L.defect_zero_matrix_coefficient_orthogonality_owner_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma defect_zero_basis_unit_entry_formula_from_prop11_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∀ a m : ι,
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
          (Matrix.stdBasis K ι ι (j, i)) a m := by
  intro a m
  -- Read the desired entry from the operator-level Proposition `11` specialization for the same
  -- basis unit. This keeps the entry formula as a thin matrix-coordinate corollary.
  exact
    L.defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect
      (L.prop11_basis_unit_operator_specialization_local
        (p := p) (ρ := ρ) (b := b) i j hdefect)

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the raw source
matrix-coefficient sum for one basis unit should already collapse to the corresponding standard
matrix entry. This extracted owner isolates the sole remaining orthogonality calculation from the
later matrix-extensionality wrapper. -/
lemma equalChar_basis_unit_entry_sum_eq_stdBasis_owner_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the desired entry directly from the primitive Proposition `11` specialization.
  exact
    L.defect_zero_basis_unit_entry_formula_from_prop11_local
      (p := p) (ρ := ρ) (b := b) i j hdefect a m

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the source matrix
coefficient attached to one basis matrix unit already collapses directly to the corresponding
standard matrix entry. This isolates the single remaining orthogonality computation before the
matrix-extensionality wrapper reconstructs the full basis-unit operator identity. -/
lemma basis_unit_fourier_action_eq_baseChange_direct_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- The direct basis-unit action theorem is now exactly the operator-level Proposition `11`
  -- specialization introduced above.
  exact
    L.prop11_basis_unit_operator_specialization_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, once the basis-unit
operator identity is known, the source matrix coefficient attached to one basis matrix unit is the
corresponding standard matrix entry. This is now only the formal entry-extraction corollary of
the operator-level owner. -/
lemma defect_zero_basis_unit_entry_formula_direct_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Read the desired coefficient identity from the basis-unit operator theorem, following the
  -- source route "operator first, entries second".
  exact
    L.defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect
      (L.basis_unit_fourier_action_eq_baseChange_direct_local
        (p := p) (ρ := ρ) (b := b) i j hdefect)

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_entry_sum_eq_stdBasis_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Route correction: the equal-characteristic branch has been reduced to this single entrywise
  -- source identity for one basis unit, and the cyclic dependency has been removed by isolating
  -- the primitive basis-unit action as its own helper theorem.
  have hact :
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
        (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) :=
    L.basis_unit_fourier_action_eq_baseChange_direct_local
      (p := p) (ρ := ρ) (b := b) i j hdefect
  -- Read the desired coefficient identity from the still-missing primitive basis-unit action
  -- equality.
  exact
    L.defect_zero_basis_unit_entry_sum_eq_stdBasis_of_action_eq_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect hact

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_fourier_action_eq_baseChange_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- The primitive equal-characteristic basis-unit action is now isolated in the direct helper
  -- above, so this legacy theorem name is only an adapter.
  exact
    L.basis_unit_fourier_action_eq_baseChange_direct_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_matrix_coefficient_orthogonality_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
      (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- The legacy theorem name is now just an adapter to the primitive coefficient owner above.
  exact
    L.defect_zero_matrix_coefficient_orthogonality_owner_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_basis_unit_action_entry_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- First rewrite the matrix entry to the source coefficient sum, then apply the formal corollary
  -- of the primitive basis-unit operator identity.
  calc
    LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K)
        (ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K)
            (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j))))) a m =
      ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
        (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) := by
          -- Rewrite the Fourier action entry to the explicit source-side coefficient sum.
          exact
            L.integral_fourier_matrix_unit_action_entry_eq_sum_local
              (ρ := ρ) (b := b) i j a m hdefect
    _ = (Matrix.stdBasis K ι ι (j, i)) a m := by
          exact
            L.defect_zero_matrix_coefficient_orthogonality_local
              (p := p) (ρ := ρ) (b := b) i j a m hdefect

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the coefficient of the
ambient action of Serre's Fourier element on one basis matrix unit collapses to the corresponding
Kronecker delta. This is the remaining matrix-coefficient orthogonality step from the source
proof, isolated as the only open equal-characteristic subgoal. -/
lemma defect_zero_matrix_coefficient_convolution_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j a m : ι)
    (hdefect : ρ.HasDefectZero p) :
    ∑ s : G, algebraMap A K (L.defect_zero_dim_ratio hdefect) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s⁻¹) i j) *
      (LinearMap.toMatrix (b.extendOfIsLattice K) (b.extendOfIsLattice K) (ρ s) a m) =
        (Matrix.stdBasis K ι ι (j, i)) a m := by
  -- Reduce the consumer theorem to the single isolated orthogonality identity above.
  exact
    L.defect_zero_matrix_coefficient_orthogonality_local
      (p := p) (ρ := ρ) (b := b) i j a m hdefect

/-- Helper for Proposition 16-16.4-1: for a single basis matrix unit on the stable lattice, the
ambient action of Serre's integral Fourier element is exactly the scalar-extended matrix unit.
This is the unreduced source Proposition `11` specialization that still has to be formalized in
the equal-characteristic branch. -/
lemma integral_fourier_matrix_unit_action_local
    [CharP K p]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Reuse the stronger basis-unit owner so downstream consumers still keep the original name.
  exact
    L.defect_zero_basis_unit_fourier_action_eq_baseChange_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: once the equal-characteristic Fourier identity is proved on
the basis matrix units of the stable lattice, additivity and `A`-linearity of Serre's integral
Fourier section extend it to every lattice endomorphism. -/
lemma integral_fourier_self_action_local
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  classical
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  let F : Module.End A L.toSubmodule →ₗ[A] Module.End K E :=
    { toFun := fun ψ ↦
        ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect ψ))
      map_add' := by
        intro ψ η
        simp [L.serre_fourier_add_local]
      map_smul' := by
        intro a ψ
        change
          ρ.asAlgebraHom
              (MonoidAlgebra.mapRingHom G (algebraMap A K)
                (L.serre_fourier_element hdefect (a • ψ))) =
            a • ρ.asAlgebraHom
              (MonoidAlgebra.mapRingHom G (algebraMap A K)
                (L.serre_fourier_element hdefect ψ))
        rw [L.serre_fourier_smul_local]
        have hmap :
            MonoidAlgebra.mapRingHom G (algebraMap A K)
                (a • L.serre_fourier_element hdefect ψ) =
              a •
                MonoidAlgebra.mapRingHom G (algebraMap A K)
                  (L.serre_fourier_element hdefect ψ) := by
          ext g
          simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
        rw [hmap]
        exact
          AlgHom.map_smul_of_tower (ρ.asAlgebraHom) a
            (MonoidAlgebra.mapRingHom G (algebraMap A K)
              (L.serre_fourier_element hdefect ψ)) }
  have hdecomp :
      φ =
        ∑ i : ι, ∑ j : ι,
          (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)) :=
    L.endHom_eq_sum_matrix_units_local (ρ := ρ) (b := b) φ
  have hF :
      F φ =
        ∑ i : ι, ∑ j : ι,
          algebraMap A K (LinearMap.toMatrix b b φ j i) •
            F ((b.coord i).smulRight (b j)) := by
    -- The ambient Fourier action is `A`-linear in the lifted endomorphism, so applying `F` to the
    -- matrix-unit decomposition of `φ` produces the corresponding coefficientwise sum.
    simpa [F] using congrArg F hdecomp
  have hend :
      (L.toSubmodule_subtype_isBaseChange).endHom φ =
        ∑ i : ι, ∑ j : ι,
          algebraMap A K (LinearMap.toMatrix b b φ j i) •
            (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
    -- Apply the base-change endomorphism functor to the same matrix-unit decomposition.
    simpa using congrArg hf.endHom hdecomp
  calc
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      F φ := by
          rfl
    _ =
      ∑ i : ι, ∑ j : ι,
        algebraMap A K (LinearMap.toMatrix b b φ j i) •
          F ((b.coord i).smulRight (b j)) := by
          exact hF
    _ =
      ∑ i : ι, ∑ j : ι,
        algebraMap A K (LinearMap.toMatrix b b φ j i) •
          (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
          -- Substitute the primitive basis-unit Fourier action on each summand.
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact congrArg
            (fun t : Module.End K E ↦
              algebraMap A K (LinearMap.toMatrix b b φ j i) • t)
            (L.basis_unit_fourier_action_eq_baseChange_direct_local
              (p := p) (ρ := ρ) (b := b) i j hdefect)
    _ = (L.toSubmodule_subtype_isBaseChange).endHom φ := by
          simpa using hend.symm

/-- Helper for Proposition 16-16.4-1: in the equal-characteristic branch, the only missing source
step is the ambient `K`-linear Fourier inversion identity for the simple representation `ρ`
itself. Once this is known, the algebraic-closure statement is the formal scalar-extension wrapper
just above. -/
lemma equalChar_hambient_local
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Route correction: reduce the ambient self-action theorem to the basis-unit owner from the
  -- source Proposition `11`, instead of leaving the whole arbitrary-`φ` statement as one block.
  exact L.integral_fourier_self_action_local (p := p) (ρ := ρ) hdefect φ

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation should first identify the ambient
`K`-action of Serre's Fourier element; this lemma then lifts that identity to
`AlgebraicClosure K`. -/
lemma equalChar_algClosure_fourier_action_eq_baseChange
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K))
          (L.serre_fourier_element hdefect φ)) =
      LinearMap.baseChange (AlgebraicClosure K)
        ((L.toSubmodule_subtype_isBaseChange).endHom φ) := by
  -- Route correction: the scalar-extension step is formal once the ambient `K`-action equality is
  -- known, so this theorem only consumes the dedicated ambient owner.
  exact
    L.algClosure_fourier_action_eq_baseChange_of_ambient_action_local
      (p := p) (ρ := ρ) hdefect φ
      (L.equalChar_hambient_local (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K` and
reuses the corresponding projector-annihilator statement. -/
lemma equalChar_ambient_action_eq_of_projector_bridge
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  -- Descend the scalar-extension identity from the dedicated equal-characteristic packet theorem.
  exact
    StableLattice.ambient_action_eq_of_algClosure_baseChange_eq_local
      (ρ := ρ)
      (u := L.serre_fourier_element hdefect φ)
      (f := (L.toSubmodule_subtype_isBaseChange).endHom φ)
      (by
        simpa using
          L.equalChar_algClosure_fourier_action_eq_baseChange
            (p := p) (ρ := ρ) hdefect φ)

/-- Helper for Proposition 16-16.4-1: the equal-characteristic branch of the remaining Fourier
packet argument. The local distinguished-block computation already identifies the scalar-extended
action of Serre's Fourier element, so this wrapper only performs the descent back to `K`. -/
lemma equalChar_packet_block_action_eq_transport
    [CharP K p]
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  intro φ
  -- Consume the dedicated target-local descent wrapper so the branch theorem only records the
  -- source-level ambient action computation.
  exact
    L.equalChar_ambient_action_eq_of_projector_bridge
      (p := p) (ρ := ρ) hdefect φ

/-- Helper for Proposition 16-16.4-1: the sole remaining source-faithful Fourier inversion step
over `AlgebraicClosure K` identifies the ambient action of the integral Fourier section `u_φ`.
The later kernel and idempotence consequences are now derived formally from this single bridge. -/
lemma algClosure_complete_family_fourier_consequences
    (hdefect : ρ.HasDefectZero p) :
    ∀ φ : Module.End A L.toSubmodule,
      ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
        (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  have hcharSplit : CharZero K ∨ CharP K p :=
    L.charZero_or_charP_fraction_field (p := p)
  -- Route correction: the remaining source step is now explicitly split by the verified
  -- characteristic dichotomy of the fraction field, rather than hidden behind one undifferentiated
  -- algebraic-closure packet goal.
  rcases hcharSplit with hchar0 | hcharp
  · letI : CharZero K := hchar0
    -- Dispatch the semisimple branch to the target-local Fourier workbench.
    exact L.charZero_fourier_branch_consequences (p := p) (ρ := ρ) hdefect
  · letI : CharP K p := hcharp
    -- Dispatch the equal-characteristic branch to the target-local packet-block workbench.
    exact L.equalChar_packet_block_action_eq_transport (p := p) (ρ := ρ) hdefect

/-- Helper for Proposition 16-16.4-1: Serre's explicit integral Fourier element `u_φ`
acts on the stable lattice as the prescribed `A`-linear endomorphism `φ`. -/
lemma serre_fourier_action_eq_endHom
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    L.toRepresentation.asAlgebraHom (L.serre_fourier_element hdefect φ) = φ := by
  -- Route correction: the only remaining source step now lives in the single theorem just above as
  -- one ambient complete-family Fourier bridge, so this consumer only performs the previously
  -- isolated descent from ambient action to the lattice.
  apply L.serre_fourier_action_eq_endHom_of_ambient (hdefect := hdefect) (φ := φ)
  exact L.algClosure_complete_family_fourier_consequences (p := p) (ρ := ρ) hdefect φ

/-- Helper for Proposition 16-16.4-1: right multiplication of Serre's Fourier element by the basis
monomial `[g]` rotates the lifted endomorphism by the lattice action of `g`. This is the
coefficientwise trace computation at the heart of Serre's section law. -/
-- TODO: rewrite the trace calculation using the composition-friendly `LinearMap.trace_mul_comm`
-- and `LinearMap.trace_mul_cycle` API at the ambient endomorphism level.
lemma serre_fourier_mul_single_one_eq_action_local
    (hdefect : ρ.HasDefectZero p)
    (φ : Module.End A L.toSubmodule) (g : G) :
    L.serre_fourier_element hdefect φ * MonoidAlgebra.single g (1 : A) =
      L.serre_fourier_element hdefect (φ * L.toRepresentation g) :=
  by
  ext s
  -- Read the coefficient after multiplying by `[g]`, rewrite the source trace in terms of
  -- `g`, `s⁻¹`, and `φ`, and then rotate the three factors cyclically.
  calc
    (L.serre_fourier_element hdefect φ * MonoidAlgebra.single g (1 : A)) s =
      L.serre_fourier_element hdefect φ (s * g⁻¹) := by
        simp
    _ = L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule ((L.toRepresentation ((s * g⁻¹)⁻¹)).comp φ) := by
          simp [StableLattice.serre_fourier_element_apply]
    _ = L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule (((L.toRepresentation g) * (L.toRepresentation s⁻¹)) * φ) := by
          rw [show (L.toRepresentation ((s * g⁻¹)⁻¹)).comp φ =
              ((L.toRepresentation g) * (L.toRepresentation s⁻¹)) * φ by
                ext x
                simp [mul_assoc]]
    _ = L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule (((L.toRepresentation s⁻¹) * φ) * L.toRepresentation g) := by
          have hcomm :
              LinearMap.trace A L.toSubmodule
                  (((L.toRepresentation g) * (L.toRepresentation s⁻¹)) * φ) =
                LinearMap.trace A L.toSubmodule
                  (φ * ((L.toRepresentation g) * (L.toRepresentation s⁻¹))) := by
            simpa [mul_assoc] using
              (LinearMap.trace_mul_comm (R := A) (M := L.toSubmodule)
                ((L.toRepresentation g) * (L.toRepresentation s⁻¹)) φ)
          have hcycle :
              LinearMap.trace A L.toSubmodule
                  (φ * ((L.toRepresentation g) * (L.toRepresentation s⁻¹))) =
                LinearMap.trace A L.toSubmodule
                  (((L.toRepresentation s⁻¹) * φ) * L.toRepresentation g) := by
            simpa [mul_assoc] using
              (LinearMap.trace_mul_cycle (R := A) (M := L.toSubmodule)
                φ (L.toRepresentation g) (L.toRepresentation s⁻¹))
          rw [hcomm, hcycle]
    _ = L.defect_zero_dim_ratio hdefect *
        LinearMap.trace A L.toSubmodule ((L.toRepresentation s⁻¹).comp (φ * L.toRepresentation g)) := by
          rfl
    _ = L.serre_fourier_element hdefect (φ * L.toRepresentation g) s := by
          simp [StableLattice.serre_fourier_element_apply]

/-- Helper for Proposition 16-16.4-1: Serre's integral Fourier section intertwines right
multiplication in `A[G]` with postcomposition by the lattice action. This is the formal section law
used later to derive the kernel criterion and the idempotence of `u_{LinearMap.id}`. -/
-- TODO: prove the section law by induction on `u`, reducing the basis step to the repaired
-- `serre_fourier_mul_single_one_eq_action_local`.
lemma serre_fourier_mul_eq_action_local
    (hdefect : ρ.HasDefectZero p)
    (φ : Module.End A L.toSubmodule) (u : A[G]) :
    L.serre_fourier_element hdefect φ * u =
      L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u) :=
  by
  refine MonoidAlgebra.induction_on
    (p := fun u : A[G] =>
      L.serre_fourier_element hdefect φ * u =
        L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u)) u
    ?_ ?_ ?_
  · intro g
    -- The group-element basis case is the coefficient computation proved just above.
    simpa [Representation.asAlgebraHom_single_one] using
      L.serre_fourier_mul_single_one_eq_action_local hdefect φ g
  · intro u v hu hv
    -- Extend the section law from two summands using additivity on both the group algebra and
    -- the lifted endomorphism.
    calc
      L.serre_fourier_element hdefect φ * (u + v) =
        L.serre_fourier_element hdefect φ * u +
          L.serre_fourier_element hdefect φ * v := by
            rw [mul_add]
      _ =
        L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u) +
          L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom v) := by
            rw [hu, hv]
      _ =
        L.serre_fourier_element hdefect
          (φ * L.toRepresentation.asAlgebraHom u +
            φ * L.toRepresentation.asAlgebraHom v) := by
            rw [← L.serre_fourier_add_local]
      _ =
        L.serre_fourier_element hdefect
          (φ * L.toRepresentation.asAlgebraHom (u + v)) := by
            rw [map_add, mul_add]
  · intro a u hu
    have hmul_smul :
        φ * (a • L.toRepresentation.asAlgebraHom u) =
          a • (φ * L.toRepresentation.asAlgebraHom u) := by
      -- Postcomposition by an `A`-linear endomorphism commutes with the scalar action.
      ext x
      simp [Module.End.mul_apply]
    -- Extend the section law from one monomial to its `A`-scalar multiples.
    calc
      L.serre_fourier_element hdefect φ * (a • u) =
        a • (L.serre_fourier_element hdefect φ * u) := by
          simp [smul_eq_mul, mul_assoc]
      _ = a • L.serre_fourier_element hdefect (φ * L.toRepresentation.asAlgebraHom u) := by
            rw [hu]
      _ =
        L.serre_fourier_element hdefect
          (a • (φ * L.toRepresentation.asAlgebraHom u)) := by
            rw [← L.serre_fourier_smul_local]
      _ =
        L.serre_fourier_element hdefect
          (φ * (a • L.toRepresentation.asAlgebraHom u)) := by
            rw [hmul_smul]
      _ =
        L.serre_fourier_element hdefect
          (φ * L.toRepresentation.asAlgebraHom (a • u)) := by
            congr 1
            exact congrArg (fun ψ : Module.End A L.toSubmodule ↦ φ * ψ)
              (AlgHom.map_smul_of_tower (L.toRepresentation.asAlgebraHom) a u).symm

/-- Helper for Proposition 16-16.4-1: Serre's special Fourier element
`u_{LinearMap.id}` acts on the stable lattice as the identity endomorphism. This is the
`φ = LinearMap.id` specialization of the integral Fourier lift. -/
lemma serre_fourier_id_action_eq_id
    (hdefect : ρ.HasDefectZero p) :
    L.toRepresentation.asAlgebraHom
        (L.serre_fourier_element hdefect
          (LinearMap.id : Module.End A L.toSubmodule)) =
      (LinearMap.id : Module.End A L.toSubmodule) := by
  -- Specialize the already isolated Fourier action identity at `φ = id`.
  simpa using
    (L.serre_fourier_action_eq_endHom hdefect
      (LinearMap.id : Module.End A L.toSubmodule))

/-- Helper for Proposition 16-16.4-1: under the defect-zero hypothesis, the source proof's
integral Fourier projector should realize every `A`-linear endomorphism of the stable lattice as
the action of an element of `A[G]`. -/
lemma exists_groupAlgebra_preimage_of_endomorphism
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ∃ u : A[G], L.toRepresentation.asAlgebraHom u = φ := by
  -- Lock in Serre's concrete integral Fourier element, then invoke the isolated action packet.
  refine ⟨L.serre_fourier_element hdefect φ, ?_⟩
  exact L.serre_fourier_action_eq_endHom hdefect φ

/-- Helper for Proposition 16-16.4-1: for Serre's special Fourier element
`e = u_{LinearMap.id}`, the implication `e * u = 0 → ρ_P(u) = 0` is already forced by the
established identity `ρ_P(e) = id`. This isolates the easy half of the kernel criterion, so the
remaining source-faithful projector work only has to prove the converse implication and
idempotence of `e`. -/
lemma serre_fourier_id_action_zero_of_left_mul_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu : L.serre_fourier_element hdefect LinearMap.id * u = 0) :
    L.toRepresentation.asAlgebraHom u = 0 := by
  let e := L.serre_fourier_element hdefect LinearMap.id
  have he :
      L.toRepresentation.asAlgebraHom e =
        (LinearMap.id : Module.End A L.toSubmodule) := by
    -- Reuse the dedicated `φ = id` specialization so the kernel calculation stays flat.
    simpa [e] using L.serre_fourier_id_action_eq_id hdefect
  -- Apply the action map to `e * u = 0`; since `e` acts as the identity, the remaining factor is
  -- exactly the action of `u`.
  calc
    L.toRepresentation.asAlgebraHom u =
        (LinearMap.id : Module.End A L.toSubmodule) * L.toRepresentation.asAlgebraHom u := by
          symm
          exact one_mul (L.toRepresentation.asAlgebraHom u)
    _ = L.toRepresentation.asAlgebraHom e * L.toRepresentation.asAlgebraHom u := by
          rw [he]
    _ = L.toRepresentation.asAlgebraHom (e * u) := by
          symm
          simpa using L.toRepresentation.asAlgebraHom.map_mul e u
    _ = 0 := by
          rw [hu]
          simp

/-- Helper for Proposition 16-16.4-1: the remaining source-faithful `φ = LinearMap.id` packet
step is the forward annihilator implication. Once this is known, applying it to `e - 1` yields
the idempotence of Serre's projector `e = u_{LinearMap.id}`. -/
lemma serre_fourier_id_left_mul_zero_of_action_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu : L.toRepresentation.asAlgebraHom u = 0) :
    L.serre_fourier_element hdefect LinearMap.id * u = 0 := by
  -- Route correction: Serre's source proof gets the annihilator implication from the section law
  -- `u_φ * u = u_{φ * ρ_P(u)}`, not from a second independent packet theorem.
  calc
    L.serre_fourier_element hdefect LinearMap.id * u =
      L.serre_fourier_element hdefect
        ((LinearMap.id : Module.End A L.toSubmodule) * L.toRepresentation.asAlgebraHom u) := by
          simpa using
            L.serre_fourier_mul_eq_action_local
              hdefect (LinearMap.id : Module.End A L.toSubmodule) u
    _ = L.serre_fourier_element hdefect (0 : Module.End A L.toSubmodule) := by
          rw [hu]
          simp
    _ = 0 := L.serre_fourier_zero_local hdefect

/-- Helper for Proposition 16-16.4-1: once the scalar-extended ambient action of `u` is already
zero, the source-faithful route descends that vanishing to the lattice action and then applies the
formal section law for `u_{LinearMap.id}`. -/
lemma serre_fourier_id_left_mul_zero_of_algClosure_action_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G])
    (hu :
      (@Representation.scalarExtension (AlgebraicClosure K) _ K _ inferInstance G _ E _ _ ρ).asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A (AlgebraicClosure K)) u) = 0) :
    L.serre_fourier_element hdefect LinearMap.id * u = 0 := by
  -- First descend the ambient zero action to `K`, then apply the already isolated section law.
  have hlocal :
      ρ.asAlgebraHom (MonoidAlgebra.mapRingHom G (algebraMap A K) u) = 0 :=
    StableLattice.ambient_action_zero_of_algClosure_action_zero_local (ρ := ρ) (u := u) hu
  have hlattice : L.toRepresentation.asAlgebraHom u = 0 := by
    apply L.toSubmodule_endHom_injective
    rw [← L.ambient_action_map_eq_endHom (u := u), map_zero]
    simpa using hlocal
  simpa using L.serre_fourier_id_left_mul_zero_of_action_zero hdefect u hlattice

/-- Helper for Proposition 16-16.4-1: Serre's special Fourier element `u_{LinearMap.id}` cuts
out exactly the kernel of the lattice action map by left multiplication. This packages the two
directions of the kernel criterion that are proved separately around the remaining ambient packet
bridge. -/
lemma serre_fourier_id_action_zero_iff_left_mul_zero
    (hdefect : ρ.HasDefectZero p) (u : A[G]) :
    L.toRepresentation.asAlgebraHom u = 0 ↔
      L.serre_fourier_element hdefect
        (LinearMap.id : Module.End A L.toSubmodule) * u = 0 := by
  constructor
  · -- The forward implication is the isolated ambient-packet consequence specialized at `φ = id`.
    intro hu
    simpa using L.serre_fourier_id_left_mul_zero_of_action_zero hdefect u hu
  · -- The reverse implication follows because `u_id` acts as the identity on the lattice.
    intro hu
    simpa using L.serre_fourier_id_action_zero_of_left_mul_zero hdefect u hu

/-- Helper for Proposition 16-16.4-1: the special Fourier element attached to `LinearMap.id`
should simultaneously produce the averaging endomorphism used for projectivity and the
complementary two-sided ideal used for the kernel splitting. -/
lemma serre_fourier_id_consequences
    (hdefect : ρ.HasDefectZero p) :
    letI : Fintype G := Fintype.ofFinite G
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    (∃ u : Module.End A L.toSubmodule, u.sumOfConjugates G = LinearMap.id) ∧
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  -- Route correction: specialize Serre's Fourier element at `φ = LinearMap.id` before consuming
  -- it. The same block projector should supply both the Chapter `14` averaging operator and the
  -- direct-factor description of the kernel ideal.
  let e := L.serre_fourier_element hdefect LinearMap.id
  have hkernel_criterion :
      ∀ u : A[G], L.toRepresentation.asAlgebraHom u = 0 ↔ e * u = 0 := by
    -- Reuse the dedicated `u_id` kernel criterion instead of reproving its two directions inline.
    intro u
    simpa [e] using L.serre_fourier_id_action_zero_iff_left_mul_zero hdefect u
  have hsurj :
      Function.Surjective L.toRepresentation.asAlgebraHom := by
    intro φ
    exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  have hkernel_split :
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
    have he_action :
        L.toRepresentation.asAlgebraHom e =
          (LinearMap.id : Module.End A L.toSubmodule) := by
      -- Reuse the dedicated `φ = id` specialization of the Fourier lift.
      simpa [e] using L.serre_fourier_id_action_eq_id hdefect
    have he_idem : IsIdempotentElem e := by
      have he_minus_one :
          L.toRepresentation.asAlgebraHom (e - 1) = 0 := by
        -- Since `e` acts as the identity, `e - 1` lies in the action kernel.
        rw [map_sub, he_action, map_one]
        change (LinearMap.id : Module.End A L.toSubmodule) - LinearMap.id = 0
        simp
      have hmul_zero : e * (e - 1) = 0 := (hkernel_criterion (e - 1)).mp he_minus_one
      have hsub : e * e - e = 0 := by
        -- Expanding `e * (e - 1)` turns the forward annihilator into the idempotence equation.
        simpa [sub_eq_add_neg, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using
          hmul_zero
      exact sub_eq_zero.mp hsub
    -- Combine centrality, idempotence, and the two annihilator implications to split the kernel.
    exact
      L.isCompl_ker_of_central_idempotent_annihilator
        (e := e)
        (he_center := by simpa [e] using L.serre_fourier_id_mem_center hdefect)
        (he_idem := he_idem)
        (hker := hkernel_criterion)
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.toSubmodule := L.toSubmodule_nontrivial
  have hproj :
      Module.Projective A[G] L.toRepresentation.asModule := by
    -- Once the action map is surjective with split kernel, Serre's part `(a)` is formal.
    exact L.projective_of_action_hom_surjective_and_ker_isCompl hsurj hkernel_split
  have havg :
      ∃ u : Module.End A L.toSubmodule, u.sumOfConjugates G = LinearMap.id := by
    let hprojSubmodule : Module.Projective A[G] L.toSubmodule := by
      simpa using hproj
    have hcriterion :=
      (projective_groupAlgebra_iff_projective_and_exists_averaging_endomorphism
        (Λ := A) (G := G) (P := L.toSubmodule)).mp hprojSubmodule
    exact hcriterion.2
  exact ⟨havg, hkernel_split⟩

-- Proof sketch: the defect-zero divisibility hypothesis makes the integral Fourier idempotent for
-- `ρ` lie in `A[G]`; the resulting averaging operator gives the projective splitting criterion for
-- the induced `A[G]`-module structure on the lattice.
/-- Proposition 16-16.4-1 (1): under the defect-zero divisibility hypothesis, a `G`-stable lattice
in a simple `K[G]`-module is projective as an `A[G]`-module. -/
theorem projective_of_defect_zero
    (hdefect : ρ.HasDefectZero p) :
    Module.Projective A[G] L.toRepresentation.asModule := by
  -- Reuse the isolated irreducibility-to-nontriviality bridge before passing to the lattice.
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.toSubmodule := L.toSubmodule_nontrivial
  have hsurj :
      Function.Surjective L.toRepresentation.asAlgebraHom := by
    intro φ
    exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  have hkernel_split :
      ∃ I : TwoSidedIdeal A[G],
        IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
    exact (L.serre_fourier_id_consequences hdefect).2
  -- Route correction: follow Serre's actual part `(b) ⇒ (a)` implication. Once
  -- `A[G] → End_A(P)` is onto with split kernel, projectivity descends formally from the
  -- endomorphism ring.
  exact L.projective_of_action_hom_surjective_and_ker_isCompl hsurj hkernel_split

-- Proof sketch: the defect-zero Fourier idempotent attached to each `A`-linear endomorphism of the
-- lattice produces an element of `A[G]` mapping to that endomorphism, giving surjectivity of the
-- canonical action map.
/-- Proposition 16-16.4-1 (2): assuming `K` is algebraically closed, the defect-zero divisibility
hypothesis makes the canonical homomorphism `A[G] → End_A(P)` of a stable lattice `P`
surjective. -/
theorem action_hom_surjective_of_defect_zero
    [IsAlgClosed K]
    (hdefect : ρ.HasDefectZero p) :
    Function.Surjective L.toRepresentation.asAlgebraHom := by
  -- The source-faithful Fourier step has been isolated as the preimage lemma above.
  intro φ
  exact L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ

/-- Helper for Proposition 16-16.4-1: once the source-faithful Fourier lift exists over `A[G]`,
reducing that lift coefficientwise along `A[G] → k[G]` makes the reduced action map hit every
`k`-linear endomorphism of the reduction. -/
theorem reduction_action_hom_surjective_of_defect_zero
    (hdefect : ρ.HasDefectZero p) :
    Function.Surjective L.reductionRepresentation.asAlgebraHom := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : Module A (Module.End k L.reduction) :=
    Module.compHom (Module.End k L.reduction) (algebraMap A k)
  letI : IsScalarTower A k (Module.End k L.reduction) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ rfl
  let hf : IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) :=
    L.reduction_mkQ_isBaseChange
  intro ψ
  -- First lift the reduced endomorphism to the lattice, then realize that lift by Serre's
  -- integral Fourier element upstairs.
  obtain ⟨φ, hφlift⟩ := L.reduction_endomorphism_lift_exists ψ
  obtain ⟨u, hu⟩ := L.exists_groupAlgebra_preimage_of_endomorphism hdefect φ
  refine ⟨MonoidAlgebra.mapRingHom G (algebraMap A k) u, ?_⟩
  -- The reduced action of the coefficientwise image of `u` is exactly the base-changed action of
  -- `u` on the lattice, because the quotient map intertwines arbitrary `A[G]`-actions.
  have htransport :
      L.reductionRepresentation.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A k) u) =
        hf.endHom (L.toRepresentation.asAlgebraHom u) := by
    let q : L.toSubmodule →ₗ[A] L.reduction := Submodule.mkQ L.maximalIdealSubmodule
    apply hf.algHom_ext
    intro x
    change
      (MonoidAlgebra.mapRingHom G (algebraMap A k) u) • q x =
        hf.endHom (L.toRepresentation.asAlgebraHom u) (q x)
    calc
      (MonoidAlgebra.mapRingHom G (algebraMap A k) u) • q x = q (u • x) := by
        symm
        exact L.reduction_mkQ_map_monoidAlgebra u x
      _ = hf.endHom (L.toRepresentation.asAlgebraHom u) (q x) := by
        symm
        simpa [q] using hf.endHom_comp_apply (L.toRepresentation.asAlgebraHom u) x
  calc
    L.reductionRepresentation.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A k) u) =
      hf.endHom (L.toRepresentation.asAlgebraHom u) := htransport
    _ = hf.endHom φ := by rw [hu]
    _ = ψ := by
      have hφ : hf.endHom φ = ψ := by
        exact hφlift
      exact hφ

-- Proof sketch: once the canonical action map is split by the defect-zero averaging construction,
-- its kernel is the kernel of an idempotent endomorphism of `A[G]`, hence a complementary
-- two-sided ideal.
/-- Proposition 16-16.4-1 (3): assuming `K` is algebraically closed, the kernel of the canonical
homomorphism `A[G] → End_A(P)` is a direct factor as a two-sided ideal of `A[G]`. -/
theorem action_hom_ker_isCompl_of_defect_zero
    [IsAlgClosed K]
    (hdefect : ρ.HasDefectZero p) :
    ∃ I : TwoSidedIdeal A[G],
      IsCompl (TwoSidedIdeal.ker L.toRepresentation.asAlgebraHom) I := by
  -- The same specialized Fourier packet already contains the direct-factor statement for the
  -- kernel ideal.
  exact (L.serre_fourier_id_consequences hdefect).2

section Reduction

/-- Helper for Proposition 16-16.4-1: once the reduced action map hits every `k`-linear
endomorphism, the reduction has no nontrivial proper `k[G]`-submodules. -/
lemma reduction_irreducible_of_surjective_reduction_action_hom
    [Nontrivial L.reduction]
    (hsurj : Function.Surjective L.reductionRepresentation.asAlgebraHom) :
    L.reductionRepresentation.IsIrreducible := by
  -- Work directly with subrepresentations so the Burnside argument stays on the canonical
  -- invariant-subspace owner attached to `L.reductionRepresentation`.
  refine
    { toNontrivial := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : L.reduction)
    have hxmem : x ∈ (⊥ : Subrepresentation L.reductionRepresentation).toSubmodule := by
      simpa [h] using
        (show x ∈ (⊤ : Subrepresentation L.reductionRepresentation).toSubmodule from trivial)
    exact hx (by simpa using hxmem)
  · intro N
    by_cases hNbot : N = ⊥
    · exact Or.inl hNbot
    · by_cases hNtop : N = ⊤
      · exact Or.inr hNtop
      · -- Pick a nonzero vector in `N` and a target vector outside `N`; surjectivity then
        -- produces a `G`-equivariant endomorphism sending the first to the second, contradicting
        -- the defining `G`-stability of `N`.
        have hNbot_sub : N.toSubmodule ≠ ⊥ := by
          intro h
          exact hNbot (Subrepresentation.toSubmodule_injective h)
        obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hNbot_sub
        have hNtop_sub : N.toSubmodule ≠ ⊤ := by
          intro h
          exact hNtop (Subrepresentation.toSubmodule_injective h)
        have hnot_all : ¬ ∀ y : L.reduction, y ∈ N.toSubmodule := by
          simpa [Submodule.eq_top_iff'] using hNtop_sub
        push_neg at hnot_all
        obtain ⟨y, hyN⟩ := hnot_all
        let b := Module.Free.chooseBasis k L.reduction
        have hxrepr : b.repr x ≠ 0 := by
          intro hxrepr0
          apply hx0
          exact b.repr.injective (by simpa using hxrepr0)
        have hsupport : (b.repr x).support.Nonempty :=
          Finsupp.support_nonempty_iff.mpr hxrepr
        obtain ⟨i, hi⟩ := hsupport
        let f : L.reduction →ₗ[k] k := (b.repr x i)⁻¹ • b.coord i
        have hfx : f x = 1 := by
          have hcoeff : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
          change (b.repr x i)⁻¹ * b.repr x i = 1
          exact inv_mul_cancel₀ hcoeff
        let T : Module.End k L.reduction := f.smulRight y
        obtain ⟨u, hu⟩ := hsurj T
        letI : Module k[G] L.reductionRepresentation.asModule := by
          change Module k[G] L.reductionRepresentation.asModule
          infer_instance
        have hTx_mem : T x ∈ N := by
          rw [← hu]
          simpa using (Subrepresentation.asSubmodule N).smul_mem u hxN
        have hTx : T x = y := by
          calc
            T x = f x • y := by
              simp [T]
            _ = y := by
              simp [hfx]
        exact False.elim (hyN (hTx ▸ hTx_mem))

-- Proof sketch: the same integral Fourier idempotent identifies the reduction modulo `𝔪_A` with a
-- defect-zero irreducible representation, so the induced representation on `P / 𝔪_A P` has no
-- nontrivial proper subrepresentations.
/-- Proposition 16-16.4-1 (4): under the defect-zero divisibility hypothesis, the reduction
`P / 𝔪_A P` of a stable lattice `P` is simple as a representation of `G` over `A / 𝔪_A`. -/
theorem reduction_irreducible_of_defect_zero
    (hdefect : ρ.HasDefectZero p) :
    L.reductionRepresentation.IsIrreducible := by
  letI : ρ.IsIrreducible := hdefect.isIrreducible
  -- Route correction: the Burnside/simple-module part is now isolated in the previous helper, so
  -- the only remaining source-faithful gap is descending the integral Fourier lift to the reduced
  -- action map.
  -- First make the ambient carrier nontrivial using the same defect-zero simplicity input.
  letI : Nontrivial E :=
    StableLattice.carrier_nontrivial_of_defect_zero (K := K) (G := G) (E := E)
      (p := p) (ρ := ρ) hdefect
  letI : Nontrivial L.reduction :=
    StableLattice.reduction_nontrivial_monoid (A := A) (K := K) L
  have hsurj :
      Function.Surjective L.reductionRepresentation.asAlgebraHom := by
    -- The reduction lift was isolated above, so this is now exactly the descended Fourier lift.
    exact L.reduction_action_hom_surjective_of_defect_zero hdefect
  exact L.reduction_irreducible_of_surjective_reduction_action_hom hsurj

-- Proof sketch: after part (1), the same averaging argument descends through the quotient
-- `P → P / 𝔪_A P`, so the reduced module inherits projectivity over `(A / 𝔪_A)[G]`.
/-- Proposition 16-16.4-1 (5): under the defect-zero divisibility hypothesis, the reduction
`P / 𝔪_A P` of a stable lattice `P` is projective as an `(A / 𝔪_A)[G]`-module. -/
theorem reduction_projective_of_defect_zero
    (hdefect : ρ.HasDefectZero p) :
    Module.Projective k[G]
      L.reductionRepresentation.asModule := by
  -- Descend the lattice projectivity statement through the residue-field reduction comparison.
  have hprojA : Module.Projective A[G] L.toRepresentation.asModule :=
    L.projective_of_defect_zero hdefect
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  have hprojA' : Module.Projective A[G] L.toSubmodule := by
    simpa using hprojA
  have hprojk : Module.Projective k[G] L.reduction :=
    (L.projective_iff_reduction_projective).mp hprojA'
  simpa using hprojk

end Reduction

end DefectZero

end StableLattice

end
