import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RepresentationTheory.Irreducible
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_3_3
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_2
import LinearRepresentations_Serre_1977.Chap14.Lemma_14_14_4_2
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_2_5

noncomputable section

open scoped MonoidAlgebra
open Representation

universe u v w x

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

namespace Representation

/-- An irreducible finite-dimensional `K`-representation of a group has defect zero at the
prime `p` when the `p`-part of `|G|` divides its dimension. -/
@[mk_iff hasDefectZero_iff]
class HasDefectZero (ρ : Representation K G E) [FiniteDimensional K E] (p : ℕ)
    [Finite G] [Fact p.Prime] : Prop where
  isIrreducible : ρ.IsIrreducible
  dvd_finrank : p ^ Nat.factorization (Nat.card G) p ∣ Module.finrank K ρ.asModule

attribute [simp] hasDefectZero_iff

/-- Helper for Proposition 16-16.4-1: a representation equivalence conjugates the action of every
group-algebra element. This is the slot-transport adapter needed to compare LinearRepresentations_Serre_1977's explicit
Fourier coefficients with the Chapter `6` Wedderburn packet. -/
lemma equiv_conj_asAlgebraHom
    {V : Type*} [AddCommGroup V] [Module K V]
    {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (e : ρ.Equiv σ) (u : K[G]) :
    e.toLinearEquiv.conj (ρ.asAlgebraHom u) = σ.asAlgebraHom u := by
  -- Check the intertwining identity on group elements and extend linearly across `K[G]`.
  ext x
  refine MonoidAlgebra.induction_on
    (p := fun v : K[G] =>
      e.toLinearEquiv (ρ.asAlgebraHom v (e.symm.toLinearEquiv x)) = σ.asAlgebraHom v x) u
    ?_ ?_ ?_
  · intro g
    simpa [Representation.asAlgebraHom_of] using
      (Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g
        (e.symm.toLinearEquiv x))
  · intro a b ha hb
    simpa using congrArg₂ HAdd.hAdd ha hb
  · intro a b hb
    simpa using congrArg (fun y ↦ a • y) hb

end Representation

/- `Representation.HasDefectZero` is the source-facing defect-zero condition itself. In the source
setting the stable lattice lives over the valuation ring `A`, so the downstream projectivity and
surjectivity consequences are stated here only in that discrete-valuation context rather than for
an arbitrary local domain. Burnside-style surjectivity of the action algebra onto `End_K(E)` is
not part of this owner over an arbitrary field: the corresponding consequences below are stated
with the extra ambient hypothesis `[IsAlgClosed K]`, which ensures the needed splitting-field /
absolute-irreducibility input. -/

local notation "k" => IsLocalRing.ResidueField A

namespace LinearMap

/-- Helper for Proposition 16-16.4-1: quotienting an `A`-module by
`𝔪_A • ⊤` realizes the canonical residue-field base change. -/
theorem isBaseChange_mkQ_maximalIdeal_smul_top
    (M : Type x) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (Module (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
      inferInstanceAs
        (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
          (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
    IsBaseChange (A ⧸ IsLocalRing.maximalIdeal A)
      (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) :
        M →ₗ[A] M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  let e :=
    LinearEquiv.extendScalarsOfSurjective
      (R := A)
      (S := A ⧸ IsLocalRing.maximalIdeal A)
      (M := TensorProduct A (A ⧸ IsLocalRing.maximalIdeal A) M)
      (N := M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)))
      (by
        simpa [IsLocalRing.ResidueField.algebraMap_eq] using
          (IsLocalRing.residue_surjective (R := A)))
      (TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A))
  letI : Module (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (Module (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  letI : IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
      (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) :=
    inferInstanceAs
      (IsScalarTower A (A ⧸ IsLocalRing.maximalIdeal A)
        (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))))
  -- The standard tensor/quotient equivalence sends `1 ⊗ x` to the class of `x`.
  refine IsBaseChange.of_equiv e ?_
  intro x
  simpa [e] using
    (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul
      (R := A) (M := M) (I := IsLocalRing.maximalIdeal A) x)

end LinearMap

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: a stable lattice over the discrete valuation ring `A` is
free as an `A`-module. -/
theorem toSubmodule_free :
    Module.Free A L.toSubmodule := by
  -- A lattice over a PID is torsion-free and finite, hence free.
  infer_instance

/-- Helper for Proposition 16-16.4-1: a stable lattice spanning a nontrivial representation is
itself nontrivial. -/
theorem toSubmodule_nontrivial [Nontrivial E] :
    Nontrivial L.toSubmodule := by
  -- If the lattice were zero, its scalar extension could not span the ambient representation.
  have hne_bot : L.toSubmodule ≠ (⊥ : Submodule A E) := by
    intro hbot
    have hspan : Submodule.span K (L.toSubmodule : Set E) = (⊤ : Submodule K E) := by
      exact Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)
    simpa [hbot] using hspan
  exact (Submodule.nontrivial_iff_ne_bot (p := L.toSubmodule)).2 hne_bot

/-- Helper for Proposition 16-16.4-1: the underlying `A`-module of a stable lattice is
projective. -/
theorem toSubmodule_projective :
    Module.Projective A L.toSubmodule := by
  -- Once the lattice is free over `A`, projectivity is immediate.
  infer_instance

/-- Helper for Proposition 16-16.4-1: once the lattice is nontrivial, evaluation at a chosen basis
vector splits the left `End_A(P)`-module `End_A(P)` onto `P`. Hence the lattice is projective over
its own endomorphism ring, matching LinearRepresentations_Serre_1977's source reduction from part `(b)` to part `(a)`. -/
theorem toSubmodule_projective_over_endomorphismRing [Nontrivial L.toSubmodule] :
    Module.Projective (Module.End A L.toSubmodule) L.toSubmodule := by
  let b : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule) A L.toSubmodule :=
    Module.Free.chooseBasis A L.toSubmodule
  obtain ⟨x, hx⟩ := exists_ne (0 : L.toSubmodule)
  have hxrepr : b.repr x ≠ 0 := by
    intro hxrepr0
    apply hx
    exact b.repr.injective (by simpa using hxrepr0)
  have hsupport : (b.repr x).support.Nonempty := Finsupp.support_nonempty_iff.mpr hxrepr
  obtain ⟨i0, -⟩ := hsupport
  let emb : L.toSubmodule →ₗ[Module.End A L.toSubmodule] Module.End A L.toSubmodule :=
    { toFun := fun y ↦ (b.coord i0).smulRight y
      map_add' := by
        -- The embedding is linear because evaluation against a fixed coordinate is linear.
        intro y z
        ext w
        simp [LinearMap.smulRight_apply, smul_add]
      map_smul' := by
        -- Left multiplication in the endomorphism ring transports directly to evaluation on `P`.
        intro f y
        ext w
        simp [LinearMap.smulRight_apply, Module.End.smul_def] }
  let ev : Module.End A L.toSubmodule →ₗ[Module.End A L.toSubmodule] L.toSubmodule :=
    { toFun := fun f ↦ f (b i0)
      map_add' := by
        intro f g
        rfl
      map_smul' := by
        -- Evaluating after left multiplication is just the module action on the chosen basis
        -- vector.
        intro f g
        rfl }
  have hsplit : ev.comp emb = LinearMap.id := by
    -- The chosen coordinate sends the chosen basis vector back to `1`, so evaluation recovers the
    -- original vector.
    ext y
    simp [emb, ev, LinearMap.smulRight_apply]
  letI : Module.Projective (Module.End A L.toSubmodule) (Module.End A L.toSubmodule) :=
    Module.Projective.of_basis
      (Module.Basis.singleton Unit (Module.End A L.toSubmodule))
  exact Module.Projective.of_split emb ev hsplit

/-- Helper for Proposition 16-16.4-1: the reduction of a stable lattice is projective over the
residue field. -/
theorem reduction_projective_over_residueField :
    Module.Projective k L.reduction := by
  -- Over a field, every module is free and therefore projective.
  infer_instance

/-- Helper for Proposition 16-16.4-1: the canonical quotient map onto the reduction is
surjective. -/
theorem reduction_mkQ_surjective :
    Function.Surjective
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) := by
  -- The reduction is a quotient of the lattice by construction.
  exact Submodule.mkQ_surjective L.maximalIdealSubmodule

/-- Helper for Proposition 16-16.4-1: the kernel of the canonical quotient map is exactly the
maximal-ideal multiple defining the reduction. -/
theorem reduction_mkQ_ker :
    LinearMap.ker
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) =
        L.maximalIdealSubmodule := by
  -- This is the standard kernel computation for a quotient map.
  ext x
  simp

/-- Helper for Proposition 16-16.4-1: the standard quotient `k`-module on
`L.toSubmodule ⧸ (𝔪_A • ⊤)` identifies linearly with the Chapter `15` reduction owner
`L.reduction`. -/
noncomputable def reduction_standard_quotient_linear_equiv :
    letI : Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
      inferInstanceAs
        (Module k
          (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
    (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
      L.reduction := by
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  -- Route correction: the quotient type is already correct; only the residue-field module
  -- structure has to be transported from the standard quotient owner to `L.reduction`.
  refine
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl
      map_add' := by
        intro x y
        rfl
      map_smul' := ?_ }
  -- Check linearity on represented scalars and quotient classes, where `reduction_smul_mk`
  -- computes the Chapter `15` scalar action explicitly.
  intro c x
  refine Quotient.inductionOn' c ?_
  intro a
  refine Quotient.inductionOn' x ?_
  intro y
  simp [StableLattice.reduction_smul_mk (L := L) a y]

/-- Helper for Proposition 16-16.4-1: after transporting the standard quotient owner to
`L.reduction`, the usual quotient class is still represented by the same lattice element. -/
theorem reduction_standard_quotient_linear_equiv_comp_mkQ :
    ∀ x : L.toSubmodule,
      L.reduction_standard_quotient_linear_equiv
          (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule)) x) =
        (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
  -- Both quotient maps send a lattice element to the same underlying quotient class.
  intro x
  rfl

/-- Helper for Proposition 16-16.4-1: the quotient map from the lattice to its reduction sends the
action of `g` upstairs to the induced action of `g` on the reduction. -/
theorem reduction_mkQ_commutes (g : G) (x : L.toSubmodule) :
    (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
        ((L.toRepresentation g) x) =
      L.reductionRepresentation g
        ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
  -- The reduced representation was defined by quotienting the lattice action, so this is exactly
  -- its computation rule on quotient classes.
  simpa using (StableLattice.reductionRepresentation_apply_mk (L := L) g x)

/-- Helper for Proposition 16-16.4-1: in the reduced `k[G]`-module, the group-algebra generator
`[g]` acts through `L.reductionRepresentation g`. -/
theorem reduction_monoidAlgebra_of_smul :
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    ∀ g : G, ∀ x : L.reduction, MonoidAlgebra.of k G g • x = L.reductionRepresentation g x := by
  -- Rewrite the `k[G]`-action through `asAlgebraHom`, then use the standard generator formula.
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  intro g x
  rw [← Representation.asAlgebraHom_single_one (ρ := L.reductionRepresentation) g]
  rfl

/-- Helper for Proposition 16-16.4-1: after transporting the standard quotient owner to the
Chapter `15` reduction owner, the class of `g • x` is sent to the reduced action of `g` on the
class of `x`. -/
theorem reduction_standard_quotient_linear_equiv_apply_action_mkQ
    (g : G) (x : L.toSubmodule) :
    L.reduction_standard_quotient_linear_equiv
      (Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))
        ((L.toRepresentation g) x)) =
      L.reductionRepresentation g
        ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
  -- Move the standard quotient class across the owner identification before applying the
  -- quotient-action computation already available on `L.reduction`.
  simpa [L.reduction_standard_quotient_linear_equiv_comp_mkQ] using
    L.reduction_mkQ_commutes g x

/-- Helper for Proposition 16-16.4-1: the quotient map from the lattice to its reduction is the
canonical residue-field base change on the underlying `A`-module. -/
theorem reduction_mkQ_isBaseChange :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
    IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) :=
    inferInstanceAs
      (Module k
        (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))))
  let hstd :=
    LinearMap.isBaseChange_mkQ_maximalIdeal_smul_top
      (A := A) (M := L.toSubmodule)
  let e :
      (L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A L.toSubmodule))) ≃ₗ[k]
        L.reduction :=
    L.reduction_standard_quotient_linear_equiv
  -- Compose the standard quotient base-change equivalence with the Chapter `15` owner
  -- identification of the quotient with `L.reduction`.
  refine IsBaseChange.of_equiv
    { toFun := fun z ↦ e (hstd.equiv z)
      invFun := fun y ↦ hstd.equiv.symm (e.symm y)
      left_inv := by
        intro z
        simp [e, hstd]
      right_inv := by
        intro y
        simp [e, hstd]
      map_add' := by
        intro z w
        calc
          e (hstd.equiv (z + w)) = e (hstd.equiv z + hstd.equiv w) := by
            exact congrArg e (hstd.equiv.map_add z w)
          _ = e (hstd.equiv z) + e (hstd.equiv w) := by
            exact e.map_add _ _
      map_smul' := by
        intro c z
        refine Quotient.inductionOn' c ?_
        intro a
        calc
          e (hstd.equiv ((IsLocalRing.residue A a) • z)) =
              e ((IsLocalRing.residue A a) • hstd.equiv z) := by
                exact congrArg e (hstd.equiv.map_smul (IsLocalRing.residue A a) z)
          _ = (IsLocalRing.residue A a) • e (hstd.equiv z) := by
                exact e.map_smul _ _ } ?_
  intro x
  calc
    e (hstd.equiv (1 ⊗ₜ[A] x)) =
        e ((Submodule.mkQ (IsLocalRing.maximalIdeal A •
          (⊤ : Submodule A L.toSubmodule)) : L.toSubmodule →ₗ[A]
            L.toSubmodule ⧸ (IsLocalRing.maximalIdeal A •
              (⊤ : Submodule A L.toSubmodule))) x) := by
          simp [e, hstd]
    _ = (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x := by
          simpa [e] using L.reduction_standard_quotient_linear_equiv_comp_mkQ x

/-- Helper for Proposition 16-16.4-1: after restricting scalars along `A[G] → k[G]`, the quotient
map from the lattice still sees the source generator `[g]` through `L.toRepresentation g`. -/
theorem toRepresentation_monoidAlgebra_of_smul :
    letI : Module A[G] L.toSubmodule := by
      change Module A[G] L.toRepresentation.asModule
      infer_instance
    letI : IsScalarTower A A[G] L.toSubmodule := by
      change IsScalarTower A A[G] L.toRepresentation.asModule
      infer_instance
    ∀ g : G, ∀ x : L.toSubmodule, MonoidAlgebra.of A G g • x = L.toRepresentation g x := by
  letI : Module A[G] L.toSubmodule := by
    change Module A[G] L.toRepresentation.asModule
    infer_instance
  letI : IsScalarTower A A[G] L.toSubmodule := by
    change IsScalarTower A A[G] L.toRepresentation.asModule
    infer_instance
  intro g x
  -- Expand the source action through `asAlgebraHom` on the monomial generator `[g]`.
  rw [← Representation.asAlgebraHom_single_one (ρ := L.toRepresentation) g]
  rfl

/-- Helper for Proposition 16-16.4-1: the reduced `A[G]`-action obtained by restriction of
scalars along `A[G] → k[G]` is compatible with the ambient `A`-scalar action. -/
private theorem reduction_restrict_groupAlgebra_isScalarTower_early :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    IsScalarTower A A[G] L.reduction := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module k[G] L.reduction := by
    change Module k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower k k[G] L.reduction := by
    change IsScalarTower k k[G] L.reductionRepresentation.asModule
    infer_instance
  letI : IsScalarTower A k[G] L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a y ↦ by
      change algebraMap A (k[G]) a • y = a • y
      rw [show algebraMap A (k[G]) a =
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp [IsLocalRing.ResidueField.algebraMap_eq]]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k (k[G]) (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • y
            = (IsLocalRing.residue A a) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (k[G])
                    (IsLocalRing.residue A a) y)
        _ = a • y := by
              rfl
  letI : Module A[G] L.reduction :=
    Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
  refine IsScalarTower.of_algebraMap_smul ?_
  intro a x
  change
    (MonoidAlgebra.mapRingHom G (algebraMap A k))
        (MonoidAlgebra.single (1 : G) a) • x =
      a • x
  rw [MonoidAlgebra.mapRingHom_single]
  have hsingle :
      MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
        algebraMap k (k[G]) (IsLocalRing.residue A a) := by
    rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
    simp
  calc
    MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
        = (IsLocalRing.residue A a) • x := by
            simpa only [hsingle] using
              (IsScalarTower.algebraMap_smul (k[G]) (IsLocalRing.residue A a) x)
    _ = a • x := by
          rfl

set_option maxHeartbeats 400000
/-- Helper for Proposition 16-16.4-1: after restricting scalars along `A[G] → k[G]`, the quotient
map intertwines the source and reduced actions of the group-algebra generators. -/
theorem reduction_mkQ_map_monoidAlgebra_of :
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
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) a) • x =
            a • x
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
              algebraMap k (k[G]) (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
              = (IsLocalRing.residue A a) • x := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul (k[G])
                      (IsLocalRing.residue A a) x)
          _ = a • x := by
                rfl
    ∀ g : G, ∀ x : L.toSubmodule,
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
          (MonoidAlgebra.of A G g • x) =
        MonoidAlgebra.of A G g •
          ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
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
  letI : IsScalarTower A k[G] L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a y ↦ by
      change algebraMap A (k[G]) a • y = a • y
      rw [show algebraMap A (k[G]) a =
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp [IsLocalRing.ResidueField.algebraMap_eq]]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k (k[G]) (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • y
            = (IsLocalRing.residue A a) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (k[G])
                    (IsLocalRing.residue A a) y)
        _ = a • y := by
              rfl
  letI : Module A[G] L.reduction :=
    Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
  have htower : IsScalarTower A A[G] L.reduction :=
    L.reduction_restrict_groupAlgebra_isScalarTower_early
  letI : IsScalarTower A A[G] L.reduction := htower
  intro g x
  -- Route correction: avoid the earlier transport-heavy `calc` block and instead rewrite directly
  -- through the quotient-action compatibility and the reduced generator formula.
  rw [L.toRepresentation_monoidAlgebra_of_smul g x]
  let q : L.toSubmodule →ₗ[A] L.reduction := Submodule.mkQ L.maximalIdealSubmodule
  let y := q x
  have hy :
      L.reductionRepresentation g y = MonoidAlgebra.of k G g • y := by
    simpa [y] using (L.reduction_monoidAlgebra_of_smul g y).symm
  refine (L.reduction_mkQ_commutes g x).trans ?_
  calc
    L.reductionRepresentation g y = MonoidAlgebra.of k G g • y := hy
    _ = MonoidAlgebra.of A G g • y := by
          rw [show MonoidAlgebra.of k G g =
            (MonoidAlgebra.mapRingHom G (algebraMap A k)) (MonoidAlgebra.of A G g) by simp]
          rfl

/-- Helper for Proposition 16-16.4-1: the quotient map from the lattice to its reduction
intertwines the action of every element of `A[G]` with the reduced action of its coefficientwise
image in `k[G]`. -/
theorem reduction_mkQ_map_monoidAlgebra :
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
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) a) • x =
            a • x
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
              algebraMap k (k[G]) (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
              = (IsLocalRing.residue A a) • x := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul (k[G])
                      (IsLocalRing.residue A a) x)
          _ = a • x := by
                rfl
    ∀ u : A[G], ∀ x : L.toSubmodule,
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)
          (u • x) =
        (MonoidAlgebra.mapRingHom G (algebraMap A k) u) •
          ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) x) := by
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
  letI : IsScalarTower A k[G] L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a y ↦ by
      change algebraMap A (k[G]) a • y = a • y
      rw [show algebraMap A (k[G]) a =
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp [IsLocalRing.ResidueField.algebraMap_eq]]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k (k[G]) (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • y
            = (IsLocalRing.residue A a) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul (k[G])
                    (IsLocalRing.residue A a) y)
        _ = a • y := by
              rfl
  letI : Module A[G] L.reduction :=
    Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
  let htower : IsScalarTower A A[G] L.reduction :=
    L.reduction_restrict_groupAlgebra_isScalarTower_early
  letI : IsScalarTower A A[G] L.reduction := htower
  let q : L.toSubmodule →ₗ[A] L.reduction := Submodule.mkQ L.maximalIdealSubmodule
  intro u x
  -- Route correction: extend the generator identity coefficientwise across `A[G]` instead of
  -- rebuilding the quotient/base-change transport from scratch.
  refine MonoidAlgebra.induction_on
    (p := fun a : A[G] ↦ q (a • x) = (MonoidAlgebra.mapRingHom G (algebraMap A k) a) • q x)
    u ?_ ?_ ?_
  · intro g
    change q (MonoidAlgebra.of A G g • x) = MonoidAlgebra.of A G g • q x
    simpa [q] using L.reduction_mkQ_map_monoidAlgebra_of g x
  · intro a b ha hb
    simp [add_smul, ha, hb]
  · intro c a ha
    calc
      q ((c • a) • x) = c • q (a • x) := by
        simp [smul_smul]
      _ = c • ((MonoidAlgebra.mapRingHom G (algebraMap A k) a) • q x) := by
        rw [ha]
      _ = (c • MonoidAlgebra.mapRingHom G (algebraMap A k) a) • q x := by
        rw [smul_assoc]
      _ = (MonoidAlgebra.mapRingHom G (algebraMap A k) (c • a)) • q x := by
        rw [Algebra.smul_def]
        rw [Algebra.smul_def, RingHom.map_mul]
        simp

set_option maxHeartbeats 200000

/-- Helper for Proposition 16-16.4-1: the quotient map from a stable lattice to its reduction is
the canonical residue-field base change. -/
private theorem reduction_restrict_groupAlgebra_isScalarTower :
    letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
    letI : IsScalarTower A k L.reduction :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
    letI : Module k[G] L.reduction := by
      change Module k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : IsScalarTower k k[G] L.reduction := by
      change IsScalarTower k k[G] L.reductionRepresentation.asModule
      infer_instance
    letI : Module A[G] L.reduction :=
      Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
    IsScalarTower A A[G] L.reduction := by
  exact L.reduction_restrict_groupAlgebra_isScalarTower_early

theorem reduction_mkQ_isResidueFieldReduction :
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
    LinearMap.IsResidueFieldReduction G
      ((Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction)) :=
  -- Route correction: the unresolved step is packaging the standard quotient/base-change map and
  -- the transported quotient action into the Chapter `14` owner `LinearMap.IsResidueFieldReduction`.
  -- The pointwise action bridge has now been isolated in
  -- `reduction_standard_quotient_linear_equiv_apply_action_mkQ`.
  by
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
    constructor
    · -- The quotient map is already the canonical residue-field base change on the lattice.
      simpa using L.reduction_mkQ_isBaseChange
    · letI : Module A[G] L.reduction :=
        Module.compHom L.reduction (MonoidAlgebra.mapRingHom G (algebraMap A k))
      letI : IsScalarTower A A[G] L.reduction :=
        L.reduction_restrict_groupAlgebra_isScalarTower
      -- Repackage the generator-level quotient-action theorem into the exact `ofModule'`
      -- intertwining statement expected by Chapter `14`.
      refine Representation.IsIntertwiningMap.mk ?_
      intro g x
      -- The preceding generator theorem already has exactly the right content; only the owner
      -- needs to be rewritten from the restricted `A[G]`-module to `Representation.ofModule'`.
      simpa [Representation.ofModule'] using L.reduction_mkQ_map_monoidAlgebra_of g x

/-- Helper for Proposition 16-16.4-1: projectivity of the lattice over `A[G]` is equivalent to
projectivity of its reduction over `k[G]`. -/
theorem projective_iff_reduction_projective :
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
    Module.Projective A[G] L.toSubmodule ↔ Module.Projective k[G] L.reduction :=
  -- Once `reduction_mkQ_isResidueFieldReduction` is packaged, the Chapter `14` criterion applies
  -- directly to the canonical quotient map `L → L / 𝔪_A L`.
  by
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
    letI : Module.Free A L.toSubmodule := L.toSubmodule_free
    -- Apply the Chapter `14` residue-field comparison theorem to the canonical quotient map.
    simpa using
      (projective_monoidAlgebra_iff_projective_of_isResidueFieldReduction
        (Λ := A) (G := G)
        (P := L.toSubmodule) (Pbar := L.reduction)
        (f := (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction))
        (hf := L.reduction_mkQ_isResidueFieldReduction))

/-- Helper for Proposition 16-16.4-1: every `k`-linear endomorphism of the reduction lifts along
the canonical residue-field base change to an `A`-linear endomorphism of the lattice. -/
theorem reduction_endomorphism_lift_exists
    (ψ : Module.End k L.reduction) :
    ∃ φ : Module.End A L.toSubmodule,
      letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
      letI : IsScalarTower A k L.reduction :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
      let hf : IsBaseChange k
          (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) :=
        L.reduction_mkQ_isBaseChange
      hf.endHom φ = ψ := by
  letI : Module A L.reduction := Module.compHom L.reduction (algebraMap A k)
  letI : IsScalarTower A k L.reduction :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ rfl
  letI : Module A (Module.End k L.reduction) :=
    Module.compHom (Module.End k L.reduction) (algebraMap A k)
  letI : IsScalarTower A k (Module.End k L.reduction) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ rfl
  let hf : IsBaseChange k
      (Submodule.mkQ L.maximalIdealSubmodule : L.toSubmodule →ₗ[A] L.reduction) :=
    L.reduction_mkQ_isBaseChange
  let hend : IsBaseChange k hf.endHom := IsBaseChange.end (S := k) hf
  have hres :
      Function.Surjective (algebraMap A k) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using
      (IsLocalRing.residue_surjective (R := A))
  -- First write the reduced endomorphism as a pure tensor in the scalar-extension owner.
  obtain ⟨t, rfl⟩ := hend.equiv.surjective ψ
  -- Then rewrite that pure tensor as `1 ⊗ φ` using surjectivity of `A → k`.
  obtain ⟨φ, rfl⟩ := TensorProduct.mk_surjective
    (R := A) (S := k) (M := Module.End A L.toSubmodule) hres t
  refine ⟨φ, ?_⟩
  calc
    hf.endHom φ = (1 : k) • hf.endHom φ := by simp
    _ = hend.equiv ((1 : k) ⊗ₜ[A] φ) := by
          symm
          exact hend.equiv_tmul (1 : k) φ

end DefectZero

end StableLattice

end
