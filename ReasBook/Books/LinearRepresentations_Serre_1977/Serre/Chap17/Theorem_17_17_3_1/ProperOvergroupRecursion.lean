import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Serre.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type (max u v w)} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance properOvergroupResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)

/-- Helper for Theorem 17-17.3-1: any subgroup containing the cyclic normal Hall factor inherits
the same cyclic-normal-by-`p` decomposition. -/
lemma subgroup_cyclicNormalByPGroupDecomposition_of_le
    {H : Subgroup G}
    (hCH : C ≤ H)
    (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P) :
    let C0 : Subgroup H := C.subgroupOf H
    let P0 : Subgroup H := (H ⊓ P).subgroupOf H
    C0.Normal ∧ C0.IsComplement' P0 ∧ IsCyclic C0 ∧ Nat.Coprime p (Nat.card C0) ∧ IsPGroup p P0 :=
    by
  let C0 : Subgroup H := C.subgroupOf H
  let P0 : Subgroup H := (H ⊓ P).subgroupOf H
  have hC0card : Nat.card C0 = Nat.card C := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv
  have hPsub : IsPGroup p ↥((H ⊓ P).subgroupOf P) := by
    exact hP.to_subgroup ((H ⊓ P).subgroupOf P)
  have hPinf : IsPGroup p ↥(H ⊓ P) := by
    exact hPsub.of_equiv (Subgroup.subgroupOfEquivOfLe (show H ⊓ P ≤ P from inf_le_right))
  have hP0 : IsPGroup p P0 := by
    exact hPinf.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show H ⊓ P ≤ H from inf_le_left)).symm
  refine ⟨hC.subgroupOf H, ?_, ?_, ?_, hP0⟩
  · refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxC hxP
      apply Subtype.ext
      have hxCG : ((x : H) : G) ∈ C := Subgroup.mem_subgroupOf.mp hxC
      have hxPG : ((x : H) : G) ∈ P := (Subgroup.mem_subgroupOf.mp hxP).2
      have hxbot : ((x : H) : G) ∈ (⊥ : Subgroup G) := by
        have hbot : C ⊓ P = (⊥ : Subgroup G) := disjoint_iff.mp hCP.disjoint
        simpa [hbot] using show ((x : H) : G) ∈ C ⊓ P from ⟨hxCG, hxPG⟩
      simpa using hxbot
    · apply Set.eq_univ_iff_forall.mpr
      intro h
      obtain ⟨⟨c, p⟩, hcp⟩ := hCP.2 ((h : H) : G)
      have hpH : (p : G) ∈ H := by
        have hcH : (c : G) ∈ H := hCH c.2
        have : c⁻¹ * ((h : H) : G) ∈ H := by
          exact H.mul_mem (H.inv_mem hcH) h.2
        have hpEq : (p : G) = c⁻¹ * ((h : H) : G) := by
          calc
            (p : G) = c⁻¹ * (c * p) := by simp
            _ = c⁻¹ * ((h : H) : G) := by
              simpa using congrArg (fun x : G ↦ c⁻¹ * x) hcp
        exact hpEq.symm ▸ this
      have hpHP : (p : G) ∈ H ⊓ P := ⟨hpH, p.2⟩
      let cH : H := ⟨(c : G), hCH c.2⟩
      let pH : H := ⟨(p : G), hpH⟩
      refine ⟨cH, Subgroup.mem_subgroupOf.mpr c.2, pH, Subgroup.mem_subgroupOf.mpr hpHP, ?_⟩
      apply Subtype.ext
      simpa [cH, pH] using hcp
  · letI : IsCyclic ↥C := hCyclic
    simpa [C0] using
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hCH).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCH).symm.surjective
  · rw [hC0card]
    exact hCoprime

/-- Helper for Theorem 17-17.3-1: once an outer cardinal induction supplies the theorem on every
strictly smaller cyclic-normal-by-`p` group, any proper subgroup with the inherited decomposition
can be handled by the recursive hypothesis. -/
lemma exists_residueFieldLift_of_isIrreducible_of_cyclicNormalByPGroupDecomposition_of_prime_of_proper_subgroup
    {n : ℕ}
    (hrec :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type w} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        {C' P' : Subgroup G'}
        (hC' : C'.Normal) (hC'P' : C'.IsComplement' P') (hCyclic' : IsCyclic C')
        (hCoprime' : Nat.Coprime p (Nat.card C')) (hP' : IsPGroup p P')
        (hcard' : Nat.card G' ≤ n)
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (W' : Type x) (_ : AddCommGroup W') (_ : Module A W')
            (_ : Module.Free A W') (_ : Module.Finite A W')
            (ρA' : Representation A G' W')
            (red' : W' →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA' red')
    (H : Subgroup G) (hH : H < ⊤)
    {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {C0 P0 : Subgroup H}
    (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
    (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
    (σ : Representation k H W) [σ.IsIrreducible]
    (hcardG : Nat.card G ≤ n.succ) :
    ∃ (W' : Type x) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρA' : Representation A H W')
      (red' : W' →ₗ[A] W),
        IsResidueFieldLift σ ρA' red' := by
  have hcardH : Nat.card H ≤ n := by
    exact
      Nat.lt_succ_iff.mp <|
        lt_of_lt_of_le (subgroup_natCard_lt_of_ne_top_c1731 H hH.ne) hcardG
  exact hrec hC0 hC0P0 hC0cyc hC0cop hP0 hcardH σ

/-- Helper for Theorem 17-17.3-1: the Chapter `7` canonical induced morphism becomes an explicit
representation equivalence once `ρ` is known to be induced from `W`. -/
noncomputable def inducedFromSubrepresentation_explicit_equiv
    (ρ : Representation k G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInd : ρ.IsInducedFromSubrepresentation H W) :
    (Representation.ind H.subtype W.toRepresentation).Equiv ρ := by
  have hIso : CategoryTheory.IsIso (ρ.inducedFromSubrepresentationHom H W) := by
    -- Route correction: turn the Chapter `7` inducedness criterion into a concrete ambient
    -- equivalence once, instead of reopening the `asIso` transport inside the target proof.
    exact
      (Representation.isInducedFromSubrepresentation_iff_isIso_inducedFromSubrepresentationHom
        (ρ := ρ) (H := H) (W := W)).mp hInd
  let eIso := CategoryTheory.asIso (ρ.inducedFromSubrepresentationHom H W)
  let f :
      (Rep.of (Representation.ind H.subtype W.toRepresentation)).ρ.IntertwiningMap (Rep.of ρ).ρ :=
    (Rep.homLinearEquiv
      (Rep.of (Representation.ind H.subtype W.toRepresentation)) (Rep.of ρ)) eIso.hom
  let g :
      (Rep.of ρ).ρ.IntertwiningMap (Rep.of (Representation.ind H.subtype W.toRepresentation)).ρ :=
    (Rep.homLinearEquiv
      (Rep.of ρ) (Rep.of (Representation.ind H.subtype W.toRepresentation))) eIso.inv
  have hfg : f.toLinearMap.comp g.toLinearMap = LinearMap.id := by
    -- The categorical inverse gives the right inverse on the underlying linear maps.
    apply LinearMap.ext
    intro y
    change ((eIso.inv ≫ eIso.hom).hom) y = y
    simpa using congrArg (fun h : Rep.of ρ ⟶ Rep.of ρ ↦ h.hom y) eIso.inv_hom_id
  have hgf : g.toLinearMap.comp f.toLinearMap = LinearMap.id := by
    -- The categorical inverse gives the left inverse on the induced source as well.
    apply LinearMap.ext
    intro y
    change ((eIso.hom ≫ eIso.inv).hom) y = y
    simpa using
      congrArg
        (fun h :
          Rep.of (Representation.ind H.subtype W.toRepresentation) ⟶
              Rep.of (Representation.ind H.subtype W.toRepresentation) ↦
            h.hom y)
        eIso.hom_inv_id
  refine Representation.Equiv.mk (LinearEquiv.ofLinear f g hfg hgf) ?_
  intro g₀
  -- The forward linear equivalence is the underlying intertwining map of the induced isomorphism.
  apply LinearMap.ext
  intro y
  exact Representation.IntertwiningMap.isIntertwining _ _ f g₀ y

end

end Representation
