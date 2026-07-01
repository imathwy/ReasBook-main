import Mathlib
import Serre.Chap12.CharacterRingOverFieldScalarExtension
import Serre.Chap18.Proposition_18_18_1_2
import Serre.Chap18.Remark_18_18_1_3
import Serre.Chap18.Theorem_18_18_2_1.RegularConjClassCore

noncomputable section

universe u x

open CategoryTheory

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

/-- Helper for Theorem 18-18.2-1: a field-valued lift of prime-to-`p` roots canonically upgrades
to a units-valued lift by viewing each image as a unit in the target field. -/
noncomputable def unitsLift_of_fieldLift
    {A : Type u} [Field A]
    (lift : PrimeToPRoot p k →* A) :
    PrimeToPRoot p k →* Aˣ where
  toFun x :=
    Units.mk0 (lift x) <|
      (show IsUnit (lift x) by
        refine ⟨⟨lift x, lift x⁻¹, ?_, ?_⟩, rfl⟩
        · rw [← map_mul, mul_inv_cancel, map_one]
        · rw [← map_mul, inv_mul_cancel, map_one])
      |>.ne_zero
  map_one' := by
    apply Units.ext
    simp
  map_mul' x y := by
    apply Units.ext
    simp

omit [IsAlgClosed k] [CharP k p] in
/-- Helper for Theorem 18-18.2-1: forgetting the units packaging on
`unitsLift_of_fieldLift` recovers the original field-valued lift. -/
@[simp] theorem toFieldLift_unitsLift_of_fieldLift
    {A : Type u} [Field A]
    (lift : PrimeToPRoot p k →* A) :
    PrimeToPRoot.toFieldLift (p := p) (k := k) (unitsLift_of_fieldLift (p := p) (k := k) lift) =
      lift := by
  funext x
  rfl

omit [IsAlgClosed k] [CharP k p] in
/-- Helper for Theorem 18-18.2-1: injectivity of a field-valued lift upgrades to injectivity of
its units-valued packaging. -/
theorem unitsLift_of_fieldLift_injective
    {A : Type u} [Field A]
    (lift : PrimeToPRoot p k →* A)
    (hlift : Function.Injective lift) :
    Function.Injective (unitsLift_of_fieldLift (p := p) (k := k) lift) := by
  intro x y hxy
  apply hlift
  exact congrArg ((↑) : Aˣ → A) hxy

omit [IsAlgClosed k] [CharP k p] in
/-- Helper for Theorem 18-18.2-1: the field-valued lift on prime-to-`p` roots is injective as
soon as the units-valued lift is injective. -/
theorem toFieldLift_injective_of_units_lift_injective
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Injective (PrimeToPRoot.toFieldLift lift) := by
  -- Equality in the ambient field already forces equality of units, so injectivity descends
  -- across the coercion `Kˣ → K`.
  intro x y hxy
  apply hlift
  exact Units.val_injective hxy

-- Route correction: the original thin wrapper depended on `Exercise_18_18_2_9`, but that import
-- currently has no usable `.olean` in this workspace. We therefore restate only the
-- coefficient-ring Exercise `18.4` companion locally and keep Theorem `42` itself field-valued.
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: a finite-support relation among descended
Brauer characters vanishes pointwise on every chosen `p`-regular representative. -/
theorem sum_smul_modularCharacterOnPRegularConjClass_eq_zero_on_support_local
    {A : Type u} [CommRing A]
    (lift : PrimeToPRoot p k → A)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    (hsum :
      (Finset.sum s
          fun j ↦ a j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) =
        (0 : PRegularConjClass G p → A))
    (t : { g : G // IsPRegular p g }) :
    (Finset.sum s fun j ↦ a j * (φ[lift]((E j).ρ) t)) = 0 := by
  -- Evaluate the functional relation at the regular conjugacy class of `t`, then rewrite each
  -- descended Brauer character back to the original modular-character value on that
  -- representative.
  have hEval := congrFun hsum (PRegularConjClass.ofSubtype (G := G) p t)
  simpa [FDRep.modularCharacterOnPRegularConjClass_ofSubtype] using hEval

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: once the coefficient lift admits a
compatible reduction map, a vanishing Brauer-character relation on `PRegularConjClass G p`
rewrites to Serre's trace relation on group elements. -/
private theorem trace_relation_of_zero_brauer_relation_on_group_support_local
    {A : Type u} [CommRing A] [Fact p.Prime]
    (lift : PrimeToPRoot p k →* A)
    (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    (hsum :
      (Finset.sum s
          fun j ↦ a j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) =
        (0 : PRegularConjClass G p → A))
    (g : G) :
    (Finset.sum s fun j ↦ red (a j) * LinearMap.trace k (E j).V ((E j).ρ g)) = 0 := by
  let t : { x : G // IsPRegular p x } :=
    ⟨pRegularComponent p g, isPRegular_pRegularComponent g⟩
  -- Evaluate the relation at the source-chosen regular representative and then reduce the
  -- resulting scalar identity through `red`.
  have hpoint :
      (Finset.sum s fun j ↦ a j * (φ[lift]((E j).ρ) t)) = 0 :=
    sum_smul_modularCharacterOnPRegularConjClass_eq_zero_on_support_local
      (p := p) lift E s a hsum t
  have hredPoint :
      (Finset.sum s fun j ↦ red (a j) * red (φ[lift]((E j).ρ) t)) = 0 := by
    simpa [map_sum, map_mul] using congrArg red hpoint
  have hrewrite :
      (Finset.sum s fun j ↦ red (a j) * red (φ[lift]((E j).ρ) t)) =
        (Finset.sum s fun j ↦ red (a j) * LinearMap.trace k (E j).V ((E j).ρ g)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    -- Route correction: Proposition `18-18.1-2 (5)` is used only after freezing the pointwise
    -- relation on the `p`-regular representative `pRegularComponent p g`.
    rw [← trace_eq_reduction_modularCharacter_pRegularComponent
      (p := p) (lift := lift) (red := red) hred (E j).ρ g]
  rw [hrewrite] at hredPoint
  exact hredPoint

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: after the same reduction-compatible
rewrite, Serre's trace relation extends linearly from `G` to the group algebra `k[G]`. -/
private theorem trace_relation_of_zero_brauer_relation_on_monoidAlgebra_support_local
    {A : Type u} [CommRing A] [Fact p.Prime]
    (lift : PrimeToPRoot p k →* A)
    (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    (hsum :
      (Finset.sum s
          fun j ↦ a j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) =
        (0 : PRegularConjClass G p → A)) :
    ∀ t : MonoidAlgebra k G,
      (Finset.sum s fun j ↦
        red (a j) * LinearMap.trace k (E j).V (Representation.asAlgebraHom (E j).ρ t)) = 0 := by
  intro t
  induction t using MonoidAlgebra.induction_on with
  | hM g =>
      -- On a group basis element, the group-algebra action is exactly the original group action.
      simpa [Representation.asAlgebraHom_of] using
        trace_relation_of_zero_brauer_relation_on_group_support_local
          (p := p) lift red hred E s a hsum g
  | hadd t₁ t₂ ht₁ ht₂ =>
      -- Extend Serre's group-level relation to sums in the group algebra one summand at a time.
      calc
        (Finset.sum s fun j ↦
          red (a j) *
            LinearMap.trace k (E j).V
              (Representation.asAlgebraHom (E j).ρ (t₁ + t₂))) =
            (Finset.sum s fun j ↦
              (red (a j) *
                  LinearMap.trace k (E j).V
                    (Representation.asAlgebraHom (E j).ρ t₁)) +
                (red (a j) *
                  LinearMap.trace k (E j).V
                    (Representation.asAlgebraHom (E j).ρ t₂))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [map_add, (LinearMap.trace k (E j).V).map_add, mul_add]
        _ =
            (Finset.sum s fun j ↦
              red (a j) *
                LinearMap.trace k (E j).V
                  (Representation.asAlgebraHom (E j).ρ t₁)) +
              (Finset.sum s fun j ↦
                red (a j) *
                  LinearMap.trace k (E j).V
                    (Representation.asAlgebraHom (E j).ρ t₂)) := by
                  rw [Finset.sum_add_distrib]
        _ = 0 := by rw [ht₁, ht₂, add_zero]
  | hsmul r t ht =>
      -- Scalar multiplication in `k[G]` scales the trace relation linearly.
      simpa [map_smul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (r * ·) ht

omit [IsAlgClosed k] in
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: a nontrivial finite-dimensional
`k`-vector space admits a rank-one endomorphism with trace `1`. This isolates the source choice of
"a projection on a line" before the Jacobson-density lift to `k[G]`. -/
private theorem exists_endomorphism_trace_one_local
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V] :
    ∃ u : Module.End k V, LinearMap.trace k V u = 1 := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv
  refine ⟨φ.smulRight v, ?_⟩
  -- Choose the normalized rank-one projector `x ↦ φ x • v`; its trace is exactly `φ v = 1`.
  calc
    LinearMap.trace k V (φ.smulRight v) = φ v := by
      simp [LinearMap.trace_smulRight]
    _ = 1 := hφ

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: pairwise nonisomorphism of the chosen
simple `FDRep` family forbids equivalences of the underlying representations at distinct indices. -/
private theorem not_nonempty_equiv_of_pairwiseNonisomorphic_local
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    {i j : ι} (hij : i ≠ j) :
    ¬ Nonempty (Representation.Equiv (E i).ρ (E j).ρ) := by
  -- Any representation equivalence upgrades to an owner-level `FDRep` isomorphism, contradicting
  -- pairwise nonisomorphism.
  intro hij_equiv
  exact hE_pairwise hij ⟨hij_equiv.some.toFDRepIso⟩

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: in the finite support product of pairwise
nonisomorphic simple modules, every off-diagonal `k[G]`-linear component vanishes. -/
private theorem support_product_offDiagonal_component_eq_zero_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    {i j : s.attach} (hij : i ≠ j)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    (LinearMap.proj j).comp
        (f.comp
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i)) =
      0 := by
  classical
  letI : Simple (E i.1) := hE_simple i.1
  letI : Simple (E j.1) := hE_simple j.1
  letI : Representation.IsIrreducible (E i.1).ρ := FDRep.isIrreducible_of_simple (E i.1)
  letI : Representation.IsIrreducible (E j.1).ρ := FDRep.isIrreducible_of_simple (E j.1)
  have hij_val : (i : ι) ≠ (j : ι) := by
    intro h
    have hval : i.val = j.val := by
      simpa using h
    exact hij (Subtype.ext hval)
  have hneq :
      ¬ Nonempty (Representation.Equiv (E i.1).ρ (E j.1).ρ) :=
    not_nonempty_equiv_of_pairwiseNonisomorphic_local
      (E := E) hE_pairwise hij_val
  letI : IsEmpty (Representation.Equiv (E i.1).ρ (E j.1).ρ) := not_nonempty_iff.mp hneq
  let fij : Representation.IntertwiningMap (E i.1).ρ (E j.1).ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (E i.1).ρ) (σ := (E j.1).ρ)).symm
      ((LinearMap.proj j).comp
        (f.comp
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i)))
  have hfij : fij = 0 := Subsingleton.elim _ _
  -- Convert the vanishing intertwiner back to the corresponding `k[G]`-linear component.
  simpa [fij] using
    congrArg
      (Representation.IntertwiningMap.equivLinearMapAsModule
        (ρ := (E i.1).ρ) (σ := (E j.1).ρ))
      hfij

omit [Finite G] in
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: in the finite support product of simple
modules, each diagonal `k[G]`-linear component is a scalar multiple of the identity by Schur's
lemma. -/
private theorem support_product_diagonal_component_eq_smul_id_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    ∃ c : k,
      (LinearMap.proj i).comp
          (f.comp
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i)) =
        c • 1 := by
  classical
  letI : Simple (E i.1) := hE_simple i.1
  letI : Representation.IsIrreducible (E i.1).ρ := FDRep.isIrreducible_of_simple (E i.1)
  let fii : Representation.IntertwiningMap (E i.1).ρ (E i.1).ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := (E i.1).ρ) (σ := (E i.1).ρ)).symm
      ((LinearMap.proj i).comp
        (f.comp
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i)))
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := (E i.1).ρ)).surjective fii
  refine ⟨c, ?_⟩
  have hfii : fii = c • 1 := by
    -- Schur's lemma identifies the self-intertwiner with the unique scalar acting the same way.
    calc
      fii = algebraMap k (Representation.IntertwiningMap (E i.1).ρ (E i.1).ρ) c := hc.symm
      _ = c • 1 := by simp
  -- Read the scalar identity back in the owner `k[G]`-linear endomorphism ring.
  simpa [fii] using
    congrArg
      (Representation.IntertwiningMap.equivLinearMapAsModule
        (ρ := (E i.1).ρ) (σ := (E i.1).ρ))
      hfii

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on the finite support product of pairwise
nonisomorphic simple modules, the `i`-th input column of any `k[G]`-linear endomorphism is a
single scalar multiple of the obvious inclusion. This is the diagonal half of the block-map
package needed before the final Jacobson-density step. -/
private theorem support_product_component_and_single_eq_smul_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    ∃ c : k,
      f.comp
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i) =
        (LinearMap.single (MonoidAlgebra k G)
          (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
            (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))) := by
  classical
  obtain ⟨c, hcdiag⟩ :=
    support_product_diagonal_component_eq_smul_id_local
      (E := E) hE_simple (s := s) i f
  refine ⟨c, ?_⟩
  -- The scalar `c` controls the `i`-th column: every off-diagonal output coordinate vanishes,
    -- while the diagonal output is exactly `c • id`.
  apply LinearMap.ext
  intro x
  ext j
  by_cases hji : j = i
  · subst hji
    have hdiag_eval := congrArg (fun l ↦ l x) hcdiag
    simpa [LinearMap.comp_apply] using hdiag_eval
  · have hoff :=
      support_product_offDiagonal_component_eq_zero_local
        (E := E) hE_simple hE_pairwise (s := s) (i := i) (j := j)
        (by
          intro hij
          exact hji hij.symm) f
    have hzero_eval := congrArg (fun l ↦ l x) hoff
    simpa [LinearMap.comp_apply, hji] using hzero_eval

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on the same multiplicity-free finite
support product, the `i`-th output row of any `k[G]`-linear endomorphism is the same scalar
multiple of the obvious projection. This is the row half of the block-map package needed before the
final Jacobson-density step. -/
private theorem support_product_proj_comp_eq_smul_proj_of_diagonal_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ))
    {c : k}
    (hcdiag :
      (LinearMap.proj i).comp
          (f.comp
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i)) =
        c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))) :
    (LinearMap.proj i).comp f =
      (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))).comp
        (LinearMap.proj i) := by
  classical
  apply LinearMap.ext
  intro x
  have hx :
      x = ∑ j : s.attach,
        LinearMap.single (MonoidAlgebra k G)
          (fun a : s.attach ↦ asModule (E a.1).ρ) j (x j) := by
    ext j
    simp
  have hx_apply :
      ((LinearMap.proj i).comp f) x =
        ∑ j : s.attach,
          ((LinearMap.proj i).comp f)
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) j (x j)) := by
    rw [hx, map_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    congr 1
    simp
  -- Expand `x` into its coordinate columns, then only the `i`-column survives in the `i`-row.
  calc
    ((LinearMap.proj i).comp f) x =
        ∑ j : s.attach,
          ((LinearMap.proj i).comp f)
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) j (x j)) := hx_apply
    _ =
        ((LinearMap.proj i).comp f)
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i (x i)) := by
          rw [Finset.sum_eq_single_of_mem i (by simp)]
          intro j hj hji
          have hoff :=
            support_product_offDiagonal_component_eq_zero_local
              (E := E) hE_simple hE_pairwise (s := s) (i := j) (j := i)
              (by
                intro hij
                exact hji hij) f
          have hzero_eval := congrArg (fun l ↦ l (x j)) hoff
          simpa [LinearMap.comp_apply] using hzero_eval
    _ = ((c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))).comp
          (LinearMap.proj i)) x := by
          have hdiag_eval := congrArg (fun l ↦ l (x i)) hcdiag
          simpa [LinearMap.comp_apply] using hdiag_eval

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on the same multiplicity-free finite
support product, the `i`-th output row of any `k[G]`-linear endomorphism is the same scalar
multiple of the obvious projection. This is the row half of the block-map package needed before the
final Jacobson-density step. -/
private theorem support_product_proj_comp_eq_smul_proj_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι)
    (i : s.attach)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    ∃ c : k,
      (LinearMap.proj i).comp f =
        (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))).comp
          (LinearMap.proj i) := by
  classical
  obtain ⟨c, hcdiag⟩ :=
    support_product_diagonal_component_eq_smul_id_local
      (E := E) hE_simple (s := s) i f
  exact ⟨c,
    support_product_proj_comp_eq_smul_proj_of_diagonal_local
      (E := E) hE_simple hE_pairwise (s := s) i f hcdiag⟩

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: the block endomorphism supported on a
single simple factor commutes with every `k[G]`-linear endomorphism of the multiplicity-free finite
support product. This is the exact bicommutant check needed before applying Jacobson density. -/
private theorem support_product_block_endomorphism_commutes_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (u : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    let q : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ) :=
      (LinearMap.single (MonoidAlgebra k G)
        (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
        (u.comp (LinearMap.proj i))
    q.comp f = f.comp q := by
  classical
  let q : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ) :=
    (LinearMap.single (MonoidAlgebra k G)
      (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
      (u.comp (LinearMap.proj i))
  obtain ⟨c, hcdiag⟩ :=
    support_product_diagonal_component_eq_smul_id_local
      (E := E) hE_simple (s := s) i f
  have hcol :
      f.comp
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i) =
        (LinearMap.single (MonoidAlgebra k G)
          (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
            (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))) := by
    apply LinearMap.ext
    intro x
    ext j
    by_cases hji : j = i
    · subst hji
      have hdiag_eval := congrArg (fun l ↦ l x) hcdiag
      simpa [LinearMap.comp_apply] using hdiag_eval
    · have hoff :=
        support_product_offDiagonal_component_eq_zero_local
          (E := E) hE_simple hE_pairwise (s := s) (i := i) (j := j)
          (by
            intro hij
            exact hji hij.symm) f
      have hzero_eval := congrArg (fun l ↦ l x) hoff
      simpa [LinearMap.comp_apply, hji] using hzero_eval
  have hrow :
      (LinearMap.proj i).comp f =
        (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))).comp
          (LinearMap.proj i) :=
    support_product_proj_comp_eq_smul_proj_of_diagonal_local
      (E := E) hE_simple hE_pairwise (s := s) i f hcdiag
  -- Both composites reduce to the same scalar action on the distinguished factor.
  change q.comp f = f.comp q
  apply LinearMap.ext
  intro x
  ext j
  by_cases hji : j = i
  · subst j
    have hrow_eval := congrArg (fun l ↦ l x) hrow
    have hcol_eval := congrArg (fun l ↦ l (u (x i))) hcol
    calc
      (q.comp f) x i = u (((LinearMap.proj i).comp f) x) := by
        simp [q, LinearMap.comp_apply]
      _ = c • u (x i) := by
            have hrow_u := congrArg u hrow_eval
            simpa [LinearMap.comp_apply] using hrow_u
      _ = (f.comp q) x i := by
            have hcol_i := congrArg (fun y ↦ y i) hcol_eval
            simpa [q, LinearMap.comp_apply] using hcol_i.symm
  · have hoff :=
      support_product_offDiagonal_component_eq_zero_local
        (E := E) hE_simple hE_pairwise (s := s) (i := i) (j := j)
        (by
          intro hij
          exact hji hij.symm) f
    have hzero_eval := congrArg (fun l ↦ l (u (x i))) hoff
    simpa [q, LinearMap.comp_apply, hji] using hzero_eval.symm

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: the supported block map on the finite
support product is linear over the endomorphism ring of the product. This packages the commuting
calculation above into the exact owner required by Jacobson density. -/
private def support_product_block_endomorphism_is_EndLinear_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (u : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ)) :
    Module.End
      (Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ))
      (∀ a : s.attach, asModule (E a.1).ρ) := by
  classical
  let q : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ) :=
    (LinearMap.single (MonoidAlgebra k G)
      (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
      (u.comp (LinearMap.proj i))
  refine
    { toFun := q
      map_add' := q.map_add
      map_smul' := ?_ }
  intro f x
  -- The previous block-commutation lemma is exactly the `End`-linearity check.
  have hcomm :=
    support_product_block_endomorphism_commutes_local
      (E := E) hE_simple hE_pairwise (s := s) i u f
  have hcomm' : q.comp f = f.comp q := by
    simpa [q] using hcomm
  change (q.comp f) x = (f.comp q) x
  exact congrArg (fun l ↦ l x) hcomm'

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on the multiplicity-free finite support
product, every `k[G]`-linear endomorphism acts on the distinguished input column by one scalar on
that factor. This is the coordinate-level Schur package that the Jacobson-density separator should
ultimately realize by an element of `k[G]`. -/
theorem support_product_column_is_scalar_single_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (f : Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ)) :
    ∃ c : k,
      ∀ v : asModule (E i.1).ρ,
        f (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i v) =
          LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i (c • v) := by
  classical
  obtain ⟨c, hc⟩ :=
    support_product_component_and_single_eq_smul_local
      (E := E) hE_simple hE_pairwise (s := s) i f
  refine ⟨c, ?_⟩
  intro v
  -- Evaluate the column identity on the chosen vector so the scalar action becomes explicit.
  have hcol_eval := congrArg (fun l ↦ l v) hc
  simpa [LinearMap.comp_apply] using hcol_eval

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: Serre part `(a)` needs an arbitrary
`k`-linear endomorphism on the chosen simple factor, not merely a `k[G]`-linear one. The
supported block map built from such a base-field endomorphism is still linear over the endomorphism
ring of the multiplicity-free support product, so it is the correct Jacobson-density input before
realizing the block map by an element of `k[G]`. -/
def support_product_baseFieldBlockEndomorphism_is_EndLinear_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (u : Module.End k (asModule (E i.1).ρ)) :
    Module.End
      (Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ))
      (∀ a : s.attach, asModule (E a.1).ρ) := by
  classical
  let qvec :
      (∀ a : s.attach, asModule (E a.1).ρ) →
        (∀ a : s.attach, asModule (E a.1).ρ) :=
    fun x a ↦ if h : a = i then cast (by cases h; rfl) (u (x i)) else 0
  refine
    { toFun := qvec
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    -- The block map acts only on the distinguished factor, so additivity is coordinatewise.
    ext a
    by_cases h : a = i
    · subst h
      simp [qvec]
    · simp [qvec, h]
  · intro f x
    obtain ⟨c, hcdiag⟩ :=
      support_product_diagonal_component_eq_smul_id_local
        (E := E) hE_simple (s := s) i f
    have hqvec_single :
        qvec x =
          LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i (u (x i)) := by
      -- The base-field block map is the same underlying supported vector as the usual `single`.
      ext a
      by_cases h : a = i
      · subst h
        simp [qvec]
      · simp [qvec, h]
    have hcol :
        f.comp
            (LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i) =
          (LinearMap.single (MonoidAlgebra k G)
            (fun a : s.attach ↦ asModule (E a.1).ρ) i).comp
              (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))) := by
      -- The distinguished input column is controlled by the same scalar coming from Schur's lemma.
      apply LinearMap.ext
      intro v
      ext j
      by_cases hji : j = i
      · subst hji
        have hdiag_eval := congrArg (fun l ↦ l v) hcdiag
        simpa [LinearMap.comp_apply] using hdiag_eval
      · have hoff :=
          support_product_offDiagonal_component_eq_zero_local
            (E := E) hE_simple hE_pairwise (s := s) (i := i) (j := j)
            (by
              intro hij
              exact hji hij.symm) f
        have hzero_eval := congrArg (fun l ↦ l v) hoff
        simpa [LinearMap.comp_apply, hji] using hzero_eval
    have hrow :
        (LinearMap.proj i).comp f =
          (c • (1 : Module.End (MonoidAlgebra k G) (asModule (E i.1).ρ))).comp
            (LinearMap.proj i) :=
      support_product_proj_comp_eq_smul_proj_of_diagonal_local
        (E := E) hE_simple hE_pairwise (s := s) i f hcdiag
    -- Route correction: for the `End`-linearity check we only need `u` to commute with the scalar
    -- `c • 1` singled out by Schur's lemma, and any `k`-linear map does.
    ext a
    by_cases hji : a = i
    · subst a
      have hrow_eval := congrArg (fun l ↦ l x) hrow
      have hrow_u := congrArg u hrow_eval
      have hcol_eval := congrArg (fun l ↦ l (u (x i))) hcol
      have hcol_i := congrArg (fun y ↦ y i) hcol_eval
      calc
        qvec (f x) i = u (((LinearMap.proj i).comp f) x) := by
          simp [qvec, LinearMap.comp_apply]
        _ = c • u (x i) := by
              simpa [LinearMap.comp_apply] using hrow_u
        _ = (f (qvec x)) i := by
              rw [hqvec_single]
              simpa [LinearMap.comp_apply] using hcol_i.symm
    · have hoff :=
        support_product_offDiagonal_component_eq_zero_local
          (E := E) hE_simple hE_pairwise (s := s) (i := i) (j := a)
          (by
            intro hij
            exact hji hij.symm) f
      have hzero_eval := congrArg (fun l ↦ l (u (x i))) hoff
      calc
        qvec (f x) a = 0 := by
          simp [qvec, hji]
        _ = (f (qvec x)) a := by
              rw [hqvec_single]
              simpa [LinearMap.comp_apply, hji] using hzero_eval.symm

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: applying the supported base-field block
endomorphism only reads the distinguished coordinate and writes back to that same factor. This
keeps the Jacobson-density separator proof focused on the source block map rather than on the
definition of the bundled endomorphism. -/
@[simp] private theorem support_product_baseFieldBlockEndomorphism_apply_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (u : Module.End k (asModule (E i.1).ρ))
    (x : ∀ a : s.attach, asModule (E a.1).ρ)
    (a : s.attach) :
    support_product_baseFieldBlockEndomorphism_is_EndLinear_local
        (E := E) hE_simple hE_pairwise (s := s) i u x a =
      if h : a = i then cast (by cases h; rfl) (u (x i)) else 0 :=
  rfl

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on a vector supported in the distinguished
factor, the base-field block endomorphism simply applies `u` in that factor and leaves every other
coordinate zero. This is the concrete source formula the later Jacobson-density separator must
match on chosen basis vectors. -/
@[simp] theorem support_product_baseFieldBlockEndomorphism_single_self_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i : s.attach)
    (u : Module.End k (asModule (E i.1).ρ))
    (v : asModule (E i.1).ρ) :
    support_product_baseFieldBlockEndomorphism_is_EndLinear_local
        (E := E) hE_simple hE_pairwise (s := s) i u
        (LinearMap.single (MonoidAlgebra k G)
          (fun a : s.attach ↦ asModule (E a.1).ρ) i v) =
      LinearMap.single (MonoidAlgebra k G)
        (fun a : s.attach ↦ asModule (E a.1).ρ) i (u v) := by
  -- Evaluate coordinatewise: the distinguished coordinate is `u v`, and every other coordinate
  -- stays zero because both maps are supported only at `i`.
  ext a
  by_cases h : a = i
  · subst h
    simp [support_product_baseFieldBlockEndomorphism_apply_local]
  · simp [support_product_baseFieldBlockEndomorphism_apply_local, h]

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on a vector supported away from the
distinguished factor, the base-field block endomorphism vanishes. This is the off-diagonal source
formula the later Jacobson-density separator must match on the remaining basis vectors. -/
@[simp] theorem support_product_baseFieldBlockEndomorphism_single_offDiag_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    [DecidableEq ι]
    (s : Finset ι)
    (i j : s.attach)
    (hji : j ≠ i)
    (u : Module.End k (asModule (E i.1).ρ))
    (v : asModule (E j.1).ρ) :
    support_product_baseFieldBlockEndomorphism_is_EndLinear_local
        (E := E) hE_simple hE_pairwise (s := s) i u
        (LinearMap.single (MonoidAlgebra k G)
          (fun a : s.attach ↦ asModule (E a.1).ρ) j v) =
      0 := by
  -- The block map only reads the `i`-coordinate, and that coordinate is zero on an input
  -- supported at some `j ≠ i`.
  ext a
  by_cases h : a = i
  · subst h
    simp [support_product_baseFieldBlockEndomorphism_apply_local, hji]
  · simp [support_product_baseFieldBlockEndomorphism_apply_local, h]

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Theorem 18-18.2-1: the finite support product of simple factors is semisimple as a
`k[G]`-module. This is the exact Jacobson-density owner used in Serre part `(a)`. -/
theorem support_product_isSemisimpleModule_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (s : Finset ι) :
    IsSemisimpleModule (MonoidAlgebra k G)
      (∀ a : s.attach, asModule (E a.1).ρ) := by
  classical
  -- Expose the owner `k[G]`-module structure on each factor before transporting simplicity.
  letI (a : s.attach) : Module (MonoidAlgebra k G) (E a.1) :=
    Representation.instModuleMonoidAlgebraAsModule (ρ := (E a.1).ρ)
  let eFactor (a : s.attach) :
      asModule (E a.1).ρ ≃ₗ[MonoidAlgebra k G] E a.1 :=
    { toFun := fun x ↦ Representation.asModuleEquiv (E a.1).ρ x
      invFun := fun x ↦ (Representation.asModuleEquiv (E a.1).ρ).symm x
      left_inv := fun x ↦ (Representation.asModuleEquiv (E a.1).ρ).symm_apply_apply x
      right_inv := fun x ↦ (Representation.asModuleEquiv (E a.1).ρ).apply_symm_apply x
      map_add' := fun x y ↦ (Representation.asModuleEquiv (E a.1).ρ).map_add x y
      map_smul' := by
        intro r x
        exact Representation.asModuleEquiv_map_smul (ρ := (E a.1).ρ) r x }
  letI (a : s.attach) : Simple (E a.1) := hE_simple a.1
  letI (a : s.attach) : Representation.IsIrreducible (E a.1).ρ :=
    FDRep.isIrreducible_of_simple (E a.1)
  letI (a : s.attach) : IsSimpleModule (MonoidAlgebra k G) (E a.1) := by
    let ρa : Representation k G (E a.1).V := (E a.1).ρ
    -- Move simplicity from the canonical `asModule` owner back to the frozen `FDRep` carrier.
    exact
      @IsSimpleModule.congr (MonoidAlgebra k G) _ (E a.1) (by infer_instance) (by infer_instance)
        (asModule ρa) ρa.instAddCommGroupAsModule
        (Representation.instModuleMonoidAlgebraAsModule (ρ := ρa))
        (eFactor a).symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρa).mp
          (by simpa [ρa] using (inferInstance : Representation.IsIrreducible ρa)))
  let ePi :
      (∀ a : s.attach, asModule (E a.1).ρ) ≃ₗ[MonoidAlgebra k G]
        ∀ a : s.attach, E a.1 :=
    LinearEquiv.piCongrRight eFactor
  -- Transport the finite-product semisimplicity instance back along the coordinatewise
  -- `asModule` equivalence.
  exact (LinearEquiv.isSemisimpleModule_iff ePi).2 inferInstance

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: transport a `k`-basis of the underlying
vector space of a finite-dimensional representation to the associated module synonym
`ρ.asModule`. This isolates the coordinate vectors that the final Jacobson-density separator must
match on the finite support product. -/
private def FDRep.asModule_basis_local
    (E : FDRep k G) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex k E.V) k (asModule E.ρ) :=
  -- The synonym `E.ρ.asModule` is the same `k`-space as `E.V`; we only transport the basis across
  -- the bookkeeping equivalence that remembers the `k[G]`-action.
  (Module.Basis.ofVectorSpace k E.V).map (Representation.asModuleEquiv E.ρ).symm

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: under the bookkeeping equivalence
`asModuleEquiv`, the transported basis vector is exactly the original basis vector of `E.V`. -/
@[simp] private theorem FDRep.asModuleEquiv_asModule_basis_local
    (E : FDRep k G)
    (b : Module.Basis.ofVectorSpaceIndex k E.V) :
    Representation.asModuleEquiv E.ρ (FDRep.asModule_basis_local E b) =
      Module.Basis.ofVectorSpace k E.V b := by
  rfl

/-- Helper for Theorem 18-18.2-1: the finite support product of the chosen simple factors carries
the obvious `k`-basis obtained by taking a basis in each coordinate. This is the finite sample fed
to Jacobson density in Serre part `(a)`. -/
private def support_product_basis_local
    (E : ι → FDRep k G)
    (s : Finset ι) :
    Module.Basis
      (Sigma fun a : s.attach ↦ Module.Basis.ofVectorSpaceIndex k (E a.1).V)
      k (∀ a : s.attach, asModule (E a.1).ρ) :=
  Pi.basis fun a ↦ FDRep.asModule_basis_local (E a.1)

/-- Helper for Theorem 18-18.2-1: Jacobson density realizes Serre's separator on a finite support
of pairwise nonisomorphic simple factors by matching the supported block endomorphism on a basis of
the support product. -/
  theorem support_product_separator_exists_local
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E)
    (s : Finset ι)
    {i : ι} (hi : i ∈ s) :
    ∃ t : MonoidAlgebra k G,
      LinearMap.trace k (E i).V
          (Representation.asAlgebraHom (E i).ρ t) = 1 ∧
        ∀ j, j ∈ s → j ≠ i →
          LinearMap.trace k (E j).V
            (Representation.asAlgebraHom (E j).ρ t) = 0 := by
  classical
  let i' : s.attach := ⟨⟨i, hi⟩, by simp⟩
  letI : DecidableEq ι := Classical.decEq ι
  letI : Simple (E i) := hE_simple i
  let ρi : Representation k G (E i) := (E i).ρ
  letI : Representation.IsIrreducible ρi := by
    simpa [ρi] using (FDRep.isIrreducible_of_simple (E i))
  let modEi : Module (MonoidAlgebra k G) (E i) := ρi.instModuleMonoidAlgebraAsModule
  let eOwner : asModule ρi ≃ₗ[MonoidAlgebra k G] E i :=
    { toFun := fun x ↦ Representation.asModuleEquiv ρi x
      invFun := fun x ↦ (Representation.asModuleEquiv ρi).symm x
      left_inv := fun x ↦ (Representation.asModuleEquiv ρi).symm_apply_apply x
      right_inv := fun x ↦ (Representation.asModuleEquiv ρi).apply_symm_apply x
      map_add' := fun x y ↦ (Representation.asModuleEquiv ρi).map_add x y
      map_smul' := by
        intro r x
        exact Representation.asModuleEquiv_map_smul (ρ := ρi) r x }
  letI : IsSimpleModule (MonoidAlgebra k G) (E i) := by
    exact
      @IsSimpleModule.congr (MonoidAlgebra k G) _ (E i) (by infer_instance) modEi
        (asModule ρi) ρi.instAddCommGroupAsModule ρi.instModuleMonoidAlgebraAsModule
        eOwner.symm
        ((Representation.irreducible_iff_isSimpleModule_asModule ρi).mp inferInstance)
  letI : Nontrivial (E i) := IsSimpleModule.nontrivial (R := MonoidAlgebra k G) (M := E i)
  obtain ⟨uV, huV_trace⟩ :=
    exists_endomorphism_trace_one_local (k := k) (V := E i)
  let baseModEi : Module k (asModule (E i).ρ) := Representation.instModuleAsModule (E i).ρ
  letI : Module k (asModule (E i).ρ) := baseModEi
  let e0 : asModule (E i).ρ ≃ₗ[k] E i := Representation.asModuleEquiv (E i).ρ
  let u : Module.End k (asModule (E i).ρ) := e0.symm.conj uV
  let q :
      Module.End
        (Module.End (MonoidAlgebra k G) (∀ a : s.attach, asModule (E a.1).ρ))
        (∀ a : s.attach, asModule (E a.1).ρ) :=
    support_product_baseFieldBlockEndomorphism_is_EndLinear_local
      (E := E) hE_simple hE_pairwise (s := s) i' u
  let B := support_product_basis_local (k := k) (G := G) E s
  let sample : Finset (∀ a : s.attach, asModule (E a.1).ρ) := Finset.univ.image B
  haveI :
      IsSemisimpleModule (MonoidAlgebra k G)
        (∀ a : s.attach, asModule (E a.1).ρ) :=
    support_product_isSemisimpleModule_local (k := k) (G := G) E hE_simple s
  obtain ⟨t, ht⟩ := jacobson_density q sample
  refine ⟨t, ?_, ?_⟩
  · let eρi : asModule (E i).ρ ≃ₗ[k] (E i).V := Representation.asModuleEquiv (E i).ρ
    have hself :
        Representation.asAlgebraHom (E i).ρ t = eρi.conj u := by
      apply (Module.Basis.ofVectorSpace k (E i).V).ext
      intro b
      have hbasis :
          q (B ⟨i', b⟩) = t • B ⟨i', b⟩ :=
        ht (B ⟨i', b⟩) (by simp [sample])
      -- Evaluate the Jacobson-density comparison on the distinguished coordinate and convert
      -- back to the ambient carrier `E i.V`.
      have hbasis_i := congrArg (fun x ↦ x i') hbasis
      have hcoord :
          Representation.asModuleEquiv (E i).ρ (q (B ⟨i', b⟩) i') =
            ((Representation.asAlgebraHom (E i).ρ) t)
              (Representation.asModuleEquiv (E i).ρ ((B ⟨i', b⟩) i')) := by
        simpa [Representation.asModuleEquiv_map_smul] using
          congrArg (Representation.asModuleEquiv (E i).ρ) hbasis_i
      have hqsingle :=
        support_product_baseFieldBlockEndomorphism_single_self_local
          (E := E) hE_simple hE_pairwise (s := s) i' u
          (FDRep.asModule_basis_local (E i) b)
      have hbasis_vector :
          B ⟨i', b⟩ =
            LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) i'
              (FDRep.asModule_basis_local (E i) b) := by
        simp [B, support_product_basis_local, i']
      have hqcoord :
          q (B ⟨i', b⟩) i' = u (FDRep.asModule_basis_local (E i) b) := by
        rw [hbasis_vector, hqsingle]
        simp [LinearMap.single_apply]
        rfl
      have hu_basis :
          Representation.asModuleEquiv (E i).ρ (u (FDRep.asModule_basis_local (E i) b)) =
            uV ((Module.Basis.ofVectorSpace k (E i).V) b) := by
        simp [u, e0, LinearEquiv.conj_apply]
      have hfinal :
          uV ((Module.Basis.ofVectorSpace k (E i).V) b) =
            ((Representation.asAlgebraHom (E i).ρ) t)
              ((Module.Basis.ofVectorSpace k (E i).V) b) := by
        calc
          uV ((Module.Basis.ofVectorSpace k (E i).V) b) =
              Representation.asModuleEquiv (E i).ρ (q (B ⟨i', b⟩) i') := by
                rw [hqcoord, hu_basis]
          _ = ((Representation.asAlgebraHom (E i).ρ) t)
                (Representation.asModuleEquiv (E i).ρ ((B ⟨i', b⟩) i')) := hcoord
          _ = ((Representation.asAlgebraHom (E i).ρ) t)
                ((Module.Basis.ofVectorSpace k (E i).V) b) := by
                simp [B, support_product_basis_local, i',
                  FDRep.asModuleEquiv_asModule_basis_local]
      simpa [u, e0, eρi, LinearEquiv.conj_apply] using hfinal.symm
    -- The realized action is conjugate to `u`, so its trace is still `1`.
    have hu_eq : eρi.conj u = uV := by
      ext x
      simp [u, e0, eρi, LinearEquiv.conj_apply]
    calc
      LinearMap.trace k (E i).V (Representation.asAlgebraHom (E i).ρ t) =
          LinearMap.trace k (E i).V (eρi.conj u) := by rw [hself]
      _ = LinearMap.trace k (E i) uV := by rw [hu_eq]
      _ = 1 := huV_trace
  · intro j hj hji
    let j' : s.attach := ⟨⟨j, hj⟩, by simp⟩
    have hji' : j' ≠ i' := by
      intro h
      apply hji
      exact congrArg (fun x : s.attach ↦ (x.1 : ι)) h
    have hzero :
        Representation.asAlgebraHom (E j).ρ t = 0 := by
      apply (Module.Basis.ofVectorSpace k (E j).V).ext
      intro b
      have hbasis :
          q (B ⟨j', b⟩) = t • B ⟨j', b⟩ :=
        ht (B ⟨j', b⟩) (by simp [sample])
      -- On every other factor, the supported block endomorphism is zero, so the realized action
      -- vanishes on a basis and hence vanishes identically.
      have hbasis_j := congrArg (fun x ↦ x j') hbasis
      have hcoord :
          Representation.asModuleEquiv (E j).ρ (q (B ⟨j', b⟩) j') =
            ((Representation.asAlgebraHom (E j).ρ) t)
              (Representation.asModuleEquiv (E j).ρ ((B ⟨j', b⟩) j')) := by
        simpa [Representation.asModuleEquiv_map_smul] using
          congrArg (Representation.asModuleEquiv (E j).ρ) hbasis_j
      have hqzero :=
        support_product_baseFieldBlockEndomorphism_single_offDiag_local
          (E := E) hE_simple hE_pairwise (s := s) i' j' hji' u
          (FDRep.asModule_basis_local (E j) b)
      have hbasis_vector :
          B ⟨j', b⟩ =
            LinearMap.single (MonoidAlgebra k G)
              (fun a : s.attach ↦ asModule (E a.1).ρ) j'
              (FDRep.asModule_basis_local (E j) b) := by
        simp [B, support_product_basis_local, j']
      have hqcoord :
          q (B ⟨j', b⟩) j' = 0 := by
        rw [hbasis_vector, hqzero]
        rfl
      have hfinal :
          0 =
            ((Representation.asAlgebraHom (E j).ρ) t)
              ((Module.Basis.ofVectorSpace k (E j).V) b) := by
        calc
          0 = Representation.asModuleEquiv (E j).ρ (q (B ⟨j', b⟩) j') := by
                rw [hqcoord]
                simp
          _ = ((Representation.asAlgebraHom (E j).ρ) t)
                (Representation.asModuleEquiv (E j).ρ ((B ⟨j', b⟩) j')) := hcoord
          _ = ((Representation.asAlgebraHom (E j).ρ) t)
                ((Module.Basis.ofVectorSpace k (E j).V) b) := by
                simp [B, support_product_basis_local, j',
                  FDRep.asModuleEquiv_asModule_basis_local]
      simpa using hfinal.symm
    simp [hzero]

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: once a separator `t` has trace `1` on the
chosen factor and trace `0` on every other supported factor, Serre's finite trace sum collapses to
the single surviving coefficient. -/
private theorem separated_trace_sum_eq_coefficient_local
    {A : Type u} [CommRing A]
    (red : A →+* k)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    {i : ι} (hi : i ∈ s)
    (t : MonoidAlgebra k G)
    (ht_i :
      LinearMap.trace k (E i).V
        (Representation.asAlgebraHom (E i).ρ t) = 1)
    (ht_others :
      ∀ j, j ∈ s → j ≠ i →
        LinearMap.trace k (E j).V
          (Representation.asAlgebraHom (E j).ρ t) = 0) :
    (Finset.sum s fun j ↦
      red (a j) * LinearMap.trace k (E j).V
        (Representation.asAlgebraHom (E j).ρ t)) =
      red (a i) := by
  -- The separator annihilates every off-diagonal summand, so only the distinguished coefficient
  -- remains.
  rw [Finset.sum_eq_single_of_mem i hi]
  · simp [ht_i]
  · intro j hj hji
    rw [ht_others j hj hji]
    simp

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on a finite support, a coefficient in a
vanishing Brauer-character relation must vanish. This is the exact Serre part `(a)` frontier:
reduce the relation on `PRegularConjClass G p` to a residue trace relation on the chosen support,
then apply Jacobson density to the singled-out simple factor. -/
private theorem coefficient_zero_of_trace_relation_with_separator_local
    {A : Type u} [CommRing A]
    (red : A →+* k)
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    {i : ι} (hi : i ∈ s)
    (htrace :
      ∀ t : MonoidAlgebra k G,
        (Finset.sum s fun j ↦
          red (a j) * LinearMap.trace k (E j).V
            (Representation.asAlgebraHom (E j).ρ t)) = 0)
    (t : MonoidAlgebra k G)
    (ht_i :
      LinearMap.trace k (E i).V
        (Representation.asAlgebraHom (E i).ρ t) = 1)
    (ht_others :
      ∀ j, j ∈ s → j ≠ i →
        LinearMap.trace k (E j).V
          (Representation.asAlgebraHom (E j).ρ t) = 0) :
    red (a i) = 0 := by
  -- Once a separator `t` kills every simple factor except `E i` and gives trace `1` on `E i`,
  -- the finite-support trace relation collapses to the single surviving coefficient.
  have hsingle :
      (Finset.sum s fun j ↦
        red (a j) * LinearMap.trace k (E j).V
          (Representation.asAlgebraHom (E j).ρ t)) =
        red (a i) :=
    separated_trace_sum_eq_coefficient_local
      (red := red) (E := E) (s := s) (a := a) hi t ht_i ht_others
  -- The trace relation evaluated at the separator therefore forces the reduced coefficient to be
  -- zero.
  calc
    red (a i) =
        (Finset.sum s fun j ↦
          red (a j) * LinearMap.trace k (E j).V
            (Representation.asAlgebraHom (E j).ρ t)) := hsingle.symm
    _ = 0 := htrace t

/-- Helper for Theorem 18-18.2-1 / Exercise 18-18.2-9: on a finite support, a coefficient in a
vanishing Brauer-character relation must vanish. This is the exact Serre part `(a)` frontier:
reduce the relation on `PRegularConjClass G p` to a residue trace relation on the chosen support,
then apply Jacobson density to the singled-out simple factor. -/
theorem
    coefficient_vanishes_on_support_of_zero_brauer_relation_with_residue_reduction_local
    {A : Type u} [CommRing A] [Fact p.Prime]
    (lift : PrimeToPRoot p k →* A)
    (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (E : ι → FDRep k G)
    (s : Finset ι)
    (a : ι → A)
    (hsum :
      (Finset.sum s
          fun j ↦ a j • FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) lift) =
        (0 : PRegularConjClass G p → A))
    {i : ι} (hi : i ∈ s)
    (t : MonoidAlgebra k G)
    (ht_i :
      LinearMap.trace k (E i).V
        (Representation.asAlgebraHom (E i).ρ t) = 1)
    (ht_others :
      ∀ j, j ∈ s → j ≠ i →
        LinearMap.trace k (E j).V
          (Representation.asAlgebraHom (E j).ρ t) = 0) :
    red (a i) = 0 := by
  -- First convert the Brauer-character relation to Serre's trace relation on the support.
  have htrace :
      ∀ t' : MonoidAlgebra k G,
        (Finset.sum s fun j ↦
          red (a j) * LinearMap.trace k (E j).V
            (Representation.asAlgebraHom (E j).ρ t')) = 0 :=
    trace_relation_of_zero_brauer_relation_on_monoidAlgebra_support_local
      (p := p) lift red hred E s a hsum
  -- Then evaluate the trace relation at the supplied separator `t`.
  exact
    coefficient_zero_of_trace_relation_with_separator_local
      (red := red) (E := E) (s := s) (a := a) hi htrace t ht_i ht_others


end

end Representation
