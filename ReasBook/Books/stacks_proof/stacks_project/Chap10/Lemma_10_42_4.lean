import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import stacks_proof.stacks_project.Chap09.Lemma_9_14_5
import stacks_proof.stacks_project.Chap09.Lemma_9_26_11
import stacks_proof.stacks_project.Chap09.Lemma_9_28_2
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_42_3
import Mathlib.Tactic.StacksAttribute
import stacks_proof.stacks_project.Chap10.Lemma_10_42_4.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u1 v1

section

open Algebra

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

namespace Chap10Lemma10424ProofTarget

/-- Helper for Chap10 Lemma 10 42 4: the restarted `p`-root absorption stage constructed from a
normalized Frobenius-range premise over the finite purely inseparable coefficient extension. -/
theorem exists_restarted_stage_absorbing_degree_p_step_of_frobenius_range
    {F : Type u} {B : Type u} {E : Type v}
    [Field F] [Field B] [Field E] [Algebra F E] [Algebra F B]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP B p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E)
    (hFrobRange :
      (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom).map
        (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) ∈
        Set.range
          (Polynomial.map
            (frobenius (FractionRing (MvPolynomial (Fin r) B)) p))) :
    ∃ (B' : Type u) (_ : Field B') (_ : Algebra F B')
      (_ : FiniteDimensional F B') (_ : IsPurelyInseparable F B')
      (L : Type v) (_ : Field L) (_ : Algebra F L) (_ : Algebra E L) (_ : Algebra B' L)
      (_ : IsScalarTower F E L) (_ : IsScalarTower F B' L)
      (_ : FiniteDimensional E L) (_ : IsPurelyInseparable E L)
      (_ : Algebra.EssFiniteType B' L)
      (y : Fin r → L),
          IsTranscendenceBasis B' y ∧
            Field.finInsepDegree (IntermediateField.adjoin B' (Set.range y)) L <
              Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  -- The proof-stage active declaration is a thin wrapper around the support theorem proved in
  -- the p-root absorption module; the public source-facing theorem below is unchanged.
  exact
    _root_.exists_restarted_stage_absorbing_degree_p_step_of_frobenius_range
      (F := F) (B := B) (E := E) (p := p) (r := r) (x := x) hx
      hβ_deg hβ_pow_mem hFrobRange

end Chap10Lemma10424ProofTarget

/-- Helper for Chap10 Lemma 10 42 4: after identifying the transcendence-basis stage with a
rational-function field, the minimal polynomial of `β ^ p` has a finite purely inseparable
coefficient base change whose transported support coefficients are `p`th powers. -/
lemma exists_finite_purelyInseparable_extension_for_pulledBack_stage_minpoly
    {F : Type u} {E : Type*} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x) {β : E} :
    ∃ (B : Type u) (_ : Field B) (_ : Algebra F B),
      FiniteDimensional F B ∧
        IsPurelyInseparable F B ∧
          ∀ n ∈ (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
              hx.1.aevalEquivField.symm.toRingHom).support),
            ∃ w : FractionRing (MvPolynomial (Fin r) B),
              ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
                  ((((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
                    hx.1.aevalEquivField.symm.toRingHom).coeff n)) =
                w ^ p := by
  -- The previously isolated rational-function descent lemma applies directly to the polynomial
  -- obtained by pulling `minpoly F(x) (β ^ p)` back along `hx.1.aevalEquivField`.
  exact
      exists_finite_purelyInseparable_extension_for_transported_minpoly_coefficients
        (k := F) (r := r) (p := p)
        ((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom)

/-- Helper for Chap10 Lemma 10 42 4: coefficientwise `p`th-root witnesses for the pulled-back
minimal polynomial assemble into a Frobenius-range statement over the finite purely inseparable
coefficient extension. -/
lemma pulledBack_stage_minpoly_mem_frobenius_range_after_coeff_roots
    {F : Type u} {B : Type u} {E : Type*}
    [Field F] [Field B] [Field E] [Algebra F E] [Algebra F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [CharP B p]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hcoeff :
      ∀ n ∈ (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom).support),
        ∃ w : FractionRing (MvPolynomial (Fin r) B),
          ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
              ((((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
                hx.1.aevalEquivField.symm.toRingHom).coeff n)) =
            w ^ p) :
    (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
        hx.1.aevalEquivField.symm.toRingHom).map
      (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) ∈
      Set.range
        (Polynomial.map
          (frobenius (FractionRing (MvPolynomial (Fin r) B)) p)) := by
  -- The characteristic transfers through the finite purely inseparable coefficient extension, so
  -- the already proved support-coefficient descent lemma applies directly to this pulled-back
  -- minimal polynomial.
  exact
    transported_minpoly_mem_frobenius_range_after_support_descent
      (k := F) (k' := B) (r := r) (p := p)
      ((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
        hx.1.aevalEquivField.symm.toRingHom)
      hcoeff

/-- Helper for Chap10 Lemma 10 42 4: a finite purely inseparable coefficient base change with
Frobenius support witnesses can be completed to the restarted p-root stage that absorbs the
degree-`p` simple step. -/
lemma exists_restarted_stage_absorbing_degree_p_step_of_pulledBack_coeff_roots
    {F : Type u} {B : Type u} {E : Type v}
    [Field F] [Field B] [Field E] [Algebra F E] [Algebra F B]
    [FiniteDimensional F B] [IsPurelyInseparable F B]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E)
    (hcoeff :
      ∀ n ∈ (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
          hx.1.aevalEquivField.symm.toRingHom).support),
        ∃ w : FractionRing (MvPolynomial (Fin r) B),
          ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p)
              ((((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
                hx.1.aevalEquivField.symm.toRingHom).coeff n)) =
            w ^ p) :
    ∃ (B' : Type u) (_ : Field B') (_ : Algebra F B')
      (_ : FiniteDimensional F B') (_ : IsPurelyInseparable F B')
      (L : Type v) (_ : Field L) (_ : Algebra F L) (_ : Algebra E L) (_ : Algebra B' L)
      (_ : IsScalarTower F E L) (_ : IsScalarTower F B' L)
      (_ : FiniteDimensional E L) (_ : IsPurelyInseparable E L)
      (_ : Algebra.EssFiniteType B' L)
      (y : Fin r → L),
          IsTranscendenceBasis B' y ∧
            Field.finInsepDegree (IntermediateField.adjoin B' (Set.range y)) L <
              Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  -- Route correction: the old final drop helper only applies to an algebra-equivalent copy of
  -- `E`, while the source construction needs a finite purely inseparable top extension.  The
  -- coefficient descent prefix is now isolated; the remaining gap is the concrete p-root
  -- compositum stage plus its extension-aware degree drop.
  letI : CharP B p := charP_of_injective_algebraMap (algebraMap F B).injective p
  have hFrobRange :
        (((minpoly (IntermediateField.adjoin F (Set.range x)) (β ^ p)).map
            hx.1.aevalEquivField.symm.toRingHom).map
          (ratFunc_frobenius_baseChangeHom (k := F) (k' := B) (r := r) (p := p))) ∈
          Set.range
            (Polynomial.map
              (frobenius (FractionRing (MvPolynomial (Fin r) B)) p)) :=
      pulledBack_stage_minpoly_mem_frobenius_range_after_coeff_roots
        (F := F) (B := B) (E := E) (p := p) (r := r) (x := x) hx hcoeff
  -- The remaining construction now consumes only the normalized Frobenius-range statement, so the
  -- coefficient witnesses do not leak past this boundary.
  exact
    exists_restarted_stage_absorbing_degree_p_step_of_frobenius_range
      (F := F) (B := B) (E := E) (p := p) (r := r) (x := x) hx
      hβ_deg hβ_pow_mem hFrobRange

/-- Helper for Chap10 Lemma 10 42 4: the omitted Stacks successor step can be packaged as one
restarted stage `(B, L, y)` with finite purely inseparable side edges and strictly smaller
inseparable degree over the lifted transcendence-basis stage. -/
lemma exists_base_change_absorbing_degree_p_step_into_separableClosure
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E) :
    ∃ (B : Type u) (_ : Field B) (_ : Algebra F B)
      (_ : FiniteDimensional F B) (_ : IsPurelyInseparable F B)
      (L : Type v) (_ : Field L) (_ : Algebra F L) (_ : Algebra E L) (_ : Algebra B L)
      (_ : IsScalarTower F E L) (_ : IsScalarTower F B L)
      (_ : FiniteDimensional E L) (_ : IsPurelyInseparable E L)
      (_ : Algebra.EssFiniteType B L)
      (y : Fin r → L),
        IsTranscendenceBasis B y ∧
          Field.finInsepDegree (IntermediateField.adjoin B (Set.range y)) L <
            Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
  obtain ⟨B, hBField, hFB, hBfd, hBpi, hcoeff⟩ :=
    exists_finite_purelyInseparable_extension_for_pulledBack_stage_minpoly
      (F := F) (E := E) (p := p) (r := r) (x := x) hx (β := β)
  letI : Field B := hBField
  letI : Algebra F B := hFB
  letI : FiniteDimensional F B := hBfd
  letI : IsPurelyInseparable F B := hBpi
  -- The remaining p-root/compositum construction absorbs the coefficient field, including any
  -- final universe transport needed by the unrestricted existential witnesses.
  exact
    exists_restarted_stage_absorbing_degree_p_step_of_pulledBack_coeff_roots
      (F := F) (B := B) (E := E) (p := p) (r := r) (x := x) hx
      hβ_deg hβ_pow_mem hcoeff

/-- Helper for Chap10 Lemma 10 42 4: the successor branch is packaged as one next-stage object
already in the exact form consumed by the recursive call. -/
structure SuccessorBranchRecursiveStageData
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    (n : ℕ) (r : ℕ) where
  /-- The new purely inseparable base field in the successor branch. -/
  F' : Type u
  /-- The new base field carries a field structure. -/
  instFieldF' : Field F'
  /-- The new base field extends the original base field. -/
  instAlgFF' : Algebra F F'
  /-- The new ambient top field after the source base change and compositum construction. -/
  E' : Type v
  /-- The new ambient top field carries a field structure. -/
  instFieldE' : Field E'
  /-- The new ambient top field still extends the original base. -/
  instAlgFE' : Algebra F E'
  /-- The new ambient top field extends the original top field. -/
  instAlgEE' : Algebra E E'
  /-- The new ambient top field extends the new base field. -/
  instAlgF'E' : Algebra F' E'
  /-- The old base-to-top tower persists after the successor step. -/
  instTowerFEE' : IsScalarTower F E E'
  /-- The new base-to-top tower needed by the recursive call. -/
  instTowerFF'E' : IsScalarTower F F' E'
  /-- The new base edge is finite. -/
  finiteDimensional_base : FiniteDimensional F F'
  /-- The new base edge is purely inseparable. -/
  purelyInseparable_base : IsPurelyInseparable F F'
  /-- The new top edge is finite. -/
  finiteDimensional_top : FiniteDimensional E E'
  /-- The new top edge is purely inseparable. -/
  purelyInseparable_top : IsPurelyInseparable E E'
  /-- The lifted transcendence basis at the restarted stage. -/
  x' : Fin r → E'
  /-- The restarted stage remains finitely generated over the new base. -/
  essFiniteType_top : Algebra.EssFiniteType F' E'
  /-- The lifted variables remain a transcendence basis over the new base. -/
  hx' : IsTranscendenceBasis F' x'
  /-- The restarted stage already satisfies the recursive inseparable-degree bound. -/
  bound : Field.finInsepDegree (IntermediateField.adjoin F' (Set.range x')) E' ≤ n

/-- Helper for Chap10 Lemma 10 42 4: the omitted Stacks successor step can be packaged directly as
one restarted stage whose output already matches the recursive-call interface. -/
lemma exists_successor_branch_recursive_stage_data
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    (n : ℕ) {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ Nat.succ n)
    {β : E}
    (hβ_deg :
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p)
    (hβ_pow_mem : β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E) :
    Nonempty (SuccessorBranchRecursiveStageData F E n r) := by
  obtain ⟨B, hBField, hFB, hBfd, hBpi, L, hLField, hFL, hEL, hBL, hFEL, hFBL,
      hELfd, hELpi, hBLEss, y, hy, hdrop⟩ :=
    exists_base_change_absorbing_degree_p_step_into_separableClosure
      (F := F) (E := E) (p := p) hx hβ_deg hβ_pow_mem
  refine ⟨{
    F' := B
    instFieldF' := hBField
    instAlgFF' := hFB
    E' := L
    instFieldE' := hLField
    instAlgFE' := hFL
    instAlgEE' := hEL
    instAlgF'E' := hBL
    instTowerFEE' := hFEL
    instTowerFF'E' := hFBL
    finiteDimensional_base := hBfd
    purelyInseparable_base := hBpi
    finiteDimensional_top := hELfd
    purelyInseparable_top := hELpi
    x' := y
    essFiniteType_top := hBLEss
    hx' := hy
    bound := by omega }⟩

/-- Helper for Chap10 Lemma 10 42 4: if the inseparable degree over the transcendence-basis stage
is already `1`, then the source induction is in its separable base case and the identity lift
finishes immediately. -/
lemma exists_identity_lift_with_separablyGenerated_of_stage_finInsepDegree_eq_one
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hsepdeg :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E = 1) :
    ∃ (F' : Type (max u w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v (max u w))) (_ : Field E') (_ : Algebra F E') (_ : Algebra E E')
      (_ : Algebra F' E') (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  -- Convert the source degree-one condition into separability over the generated stage.
  have hsep : Algebra.IsSeparable F0 E := by
    rw [isSeparable_iff_finInsepDegree_eq_one]
    exact hsepdeg
  have hsepgen : IsSeparablyGenerated F E :=
    isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
      (F := F) (E := E) hx hsep
  -- The separable base case is exactly the identity-lift theorem already proved above.
  simpa [F0] using
    exists_identity_lift_with_separablyGenerated_of_isSeparablyGenerated
      (k := F) (K := E) hsepgen

/-- Helper for Chap10 Lemma 10 42 4: if the inseparable degree over the transcendence-basis stage
is strictly larger than `1`, then the source proof extracts one degree-`p` simple purely
inseparable step whose `p`th power lies in the relative separable closure. -/
lemma exists_degree_p_simple_step_over_transcendence_basis_stage
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hgt :
      1 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E) :
    ∃ β : E,
      Module.finrank (separableClosure (IntermediateField.adjoin F (Set.range x)) E)
        (IntermediateField.adjoin
          (separableClosure (IntermediateField.adjoin F (Set.range x)) E) ({β} : Set E)) = p ∧
      β ^ p ∈ separableClosure (IntermediateField.adjoin F (Set.range x)) E := by
  let F0 : IntermediateField F E := IntermediateField.adjoin F (Set.range x)
  letI : Algebra.IsAlgebraic F0 E := by
    -- The transcendence-basis stage is algebraic over the ambient field extension.
    simpa [F0] using hx.isAlgebraic_field
  let A : IntermediateField F0 E := separableClosure F0 E
  letI : FiniteDimensional A E := by
    -- Finite generation over the original base makes the inseparable tail over `F0` finite.
    simpa [A, F0] using
      finiteDimensional_over_separableClosure_of_isTranscendenceBasis
        (k := F) (K := E) hx
  letI : CharP F0 p := charP_of_injective_algebraMap (algebraMap F F0).injective p
  letI : CharP A p := charP_of_injective_algebraMap (algebraMap F0 A).injective p
  letI : IsPurelyInseparable A E := separableClosure.isPurelyInseparable (F := F0) (E := E)
  have hgt_rank : 1 < Module.finrank A E := by
    simpa [Field.finInsepDegree, A, F0] using hgt
  obtain ⟨β, hβ_deg, hβ_pow_mem_bot, _⟩ :=
    exists_degree_p_simple_step_of_nontrivial
      (K := A) (L := E) p hgt_rank
  refine ⟨β, hβ_deg, ?_⟩
  -- Membership in the bottom field over `A` means exactly membership in the embedded closure `A`.
  simpa [A, IntermediateField.mem_bot] using hβ_pow_mem_bot

/-- Helper for Chap10 Lemma 10 42 4: the source induction on inseparable degree must quantify over
the current stage before recursing, so the induction hypothesis can be reused after one
successor-step base change. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_stage_univ
    (n : ℕ) {F : Type u1} {E : Type v1} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn : Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ n) :
    ∃ (F' : Type (max u1 w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v1 (max u1 w))) (_ : Field E') (_ : Algebra F E')
      (_ : Algebra E E') (_ : Algebra F' E')
      (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  classical
  induction n generalizing F E r with
  | zero =>
      -- The source inseparable-degree measure is always positive, so a bound by `0` is impossible.
      have hpos :
          0 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E :=
        finInsepDegree_pos_over_transcendence_basis_stage_aux
          (F := F) (E := E) hx
      omega
  | succ n ih =>
      by_cases hdeg_one :
        Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E = 1
      · -- Degree `1` is the separable base case of the source induction.
        exact
          exists_identity_lift_with_separablyGenerated_of_stage_finInsepDegree_eq_one
            (F := F) (E := E) (r := r) (x := x) hx hdeg_one
      · have hdeg_pos :
            0 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E :=
          finInsepDegree_pos_over_transcendence_basis_stage_aux
            (F := F) (E := E) hx
        have hdeg_gt :
            1 < Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E := by
          omega
        obtain ⟨β, hβ_deg, hβ_pow_mem⟩ :=
          exists_degree_p_simple_step_over_transcendence_basis_stage
            (F := F) (E := E) (p := p) (r := r) (x := x) hx hdeg_gt
        obtain ⟨stage⟩ :=
          exists_successor_branch_recursive_stage_data
            (F := F) (E := E) (p := p) n (r := r) (x := x) hx hn
            hβ_deg hβ_pow_mem
        letI : Field stage.F' := stage.instFieldF'
        letI : Algebra F stage.F' := stage.instAlgFF'
        letI : Field stage.E' := stage.instFieldE'
        letI : Algebra F stage.E' := stage.instAlgFE'
        letI : Algebra E stage.E' := stage.instAlgEE'
        letI : Algebra stage.F' stage.E' := stage.instAlgF'E'
        letI : IsScalarTower F E stage.E' := stage.instTowerFEE'
        letI : IsScalarTower F stage.F' stage.E' := stage.instTowerFF'E'
        letI : FiniteDimensional F stage.F' := stage.finiteDimensional_base
        letI : IsPurelyInseparable F stage.F' := stage.purelyInseparable_base
        letI : FiniteDimensional E stage.E' := stage.finiteDimensional_top
        letI : IsPurelyInseparable E stage.E' := stage.purelyInseparable_top
        letI : Algebra.EssFiniteType stage.F' stage.E' := stage.essFiniteType_top
        letI : CharP stage.F' p :=
          charP_of_injective_algebraMap (algebraMap F stage.F').injective p
        obtain ⟨B', hB'Field, hStageB', L', hL'Field, hStageL', hTopL', hB'L',
            hStageTopL', hStageB'L', hLift⟩ :=
          ih (F := stage.F') (E := stage.E') (r := r) (x := stage.x')
            stage.hx' stage.bound
        letI : Field B' := hB'Field
        letI : Algebra stage.F' B' := hStageB'
        letI : Field L' := hL'Field
        letI : Algebra stage.F' L' := hStageL'
        letI : Algebra stage.E' L' := hTopL'
        letI : Algebra B' L' := hB'L'
        letI : IsScalarTower stage.F' stage.E' L' := hStageTopL'
        letI : IsScalarTower stage.F' B' L' := hStageB'L'
        letI : Algebra F B' :=
          RingHom.toAlgebra ((algebraMap stage.F' B').comp (algebraMap F stage.F'))
        letI : IsScalarTower F stage.F' B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI : Algebra F L' :=
          RingHom.toAlgebra ((algebraMap stage.F' L').comp (algebraMap F stage.F'))
        letI : Algebra E L' :=
          RingHom.toAlgebra ((algebraMap stage.E' L').comp (algebraMap E stage.E'))
        letI : IsScalarTower F stage.F' L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI : IsScalarTower E stage.E' L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        letI : IsScalarTower F E L' := by
          -- The two routes from the original base to the final top agree through the restarted
          -- stage: first through `E`, or through the new base `stage.F'`.
          exact IsScalarTower.of_algebraMap_eq fun a ↦ by
            calc
              (algebraMap F L') a =
                  (algebraMap stage.F' L') ((algebraMap F stage.F') a) := rfl
              _ = (algebraMap stage.E' L')
                    ((algebraMap stage.F' stage.E') ((algebraMap F stage.F') a)) :=
                    IsScalarTower.algebraMap_apply stage.F' stage.E' L'
                      ((algebraMap F stage.F') a)
              _ = (algebraMap stage.E' L') ((algebraMap F stage.E') a) := by
                    rw [(IsScalarTower.algebraMap_apply F stage.F' stage.E' a).symm]
              _ = (algebraMap stage.E' L') ((algebraMap E stage.E') ((algebraMap F E) a)) := by
                    rw [IsScalarTower.algebraMap_apply F E stage.E' a]
              _ = (algebraMap E L') ((algebraMap F E) a) := rfl
        letI : IsScalarTower F B' L' := by
          -- The final base tower follows from the recursive tower over the restarted base.
          exact IsScalarTower.of_algebraMap_eq fun a ↦ by
            calc
              (algebraMap F L') a =
                  (algebraMap stage.F' L') ((algebraMap F stage.F') a) := rfl
              _ = (algebraMap B' L')
                    ((algebraMap stage.F' B') ((algebraMap F stage.F') a)) :=
                    IsScalarTower.algebraMap_apply stage.F' B' L'
                      ((algebraMap F stage.F') a)
              _ = (algebraMap B' L') ((algebraMap F B') a) := rfl
        -- Compose the finite purely inseparable successor square with the recursive lift by
        -- transitivity of the top and base edges, avoiding any further universe transport.
        refine ⟨B', inferInstance, inferInstance, L', inferInstance, inferInstance,
          inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · letI : FiniteDimensional stage.E' L' := hLift.finiteDimensional_top
          exact FiniteDimensional.trans E stage.E' L'
        · letI : IsPurelyInseparable stage.E' L' := hLift.purelyInseparable_top
          exact IsPurelyInseparable.trans (F := E) (E := stage.E') (K := L')
        · letI : FiniteDimensional stage.F' B' := hLift.finiteDimensional_base
          exact FiniteDimensional.trans F stage.F' B'
        · letI : IsPurelyInseparable stage.F' B' := hLift.purelyInseparable_base
          exact IsPurelyInseparable.trans (F := F) (E := stage.F') (K := B')
        · exact hLift.separablyGenerated_top

/-- Helper for Chap10 Lemma 10 42 4: source-faithful induction on the inseparable degree works over
an arbitrary current stage `(F, E, x)` rather than only over the original `(k, K)`. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_aux
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    {p : ℕ} [Fact p.Prime] [CharP F p] [Algebra.EssFiniteType F E]
    (n : ℕ) {r : ℕ} {x : Fin r → E}
    (hx : IsTranscendenceBasis F x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin F (Set.range x)) E ≤ n) :
    ∃ (F' : Type (max u w)) (_ : Field F') (_ : Algebra F F')
      (E' : Type (max v (max u w))) (_ : Field E') (_ : Algebra F E') (_ : Algebra E E')
      (_ : Algebra F' E') (_ : IsScalarTower F E E') (_ : IsScalarTower F F' E'),
        IsPurelyInseparableLiftWithSeparablyGenerated F E F' E' := by
  -- The old fixed-stage helper is now only the specialization of the stage-universe induction.
  exact
    exists_purelyInseparable_lift_with_separablyGenerated_bounded_stage_univ
      n (F := F) (E := E) (p := p) (r := r) (x := x) hx hn

/-- Helper for Chap10 Lemma 10 42 4: the original fixed-index positivity statement is now just the
specialization of the generic stage-positivity lemma to `(k, K)`. -/
lemma finInsepDegree_pos_over_transcendence_basis_stage
    [Algebra.EssFiniteType k K]
    {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x) :
    0 < Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K := by
  -- This is the original stage-indexed wrapper around the generic positivity lemma.
  exact
    finInsepDegree_pos_over_transcendence_basis_stage_aux
      (F := k) (E := K) hx

/-- Helper for Chap10 Lemma 10 42 4: separability over the field generated by a transcendence basis
is exactly the Stacks notion of separably generated. -/
lemma isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage
    {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K) :
    IsSeparablyGenerated k K := by
  -- This is the original stage-indexed wrapper around the generic separable-generation lemma.
  exact
    isSeparablyGenerated_of_isSeparable_over_transcendence_basis_stage_aux
      (F := k) (E := K) hx hsep

/-- Helper for Chap10 Lemma 10 42 4: a bound on the inseparable degree over the
transcendence-basis stage is the source induction parameter for constructing the purely
inseparable lift. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_bounded_by_finInsepDegree
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K]
    (n : ℕ) {x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K}
    (hx : IsTranscendenceBasis k x)
    (hn :
      Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K ≤ n) :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  -- Route correction: the actual induction is stage-generic, so this theorem is now only the
  -- original-index wrapper used by the public positive-characteristic proof.
  exact
    exists_purelyInseparable_lift_with_separablyGenerated_bounded_aux
      (F := k) (E := K) (p := p) n hx hn

/-- Helper for Chap10 Lemma 10 42 4: the mathlib Frobenius linear-independence criterion upgrades
a finitely generated characteristic-`p` extension to a separably generated one. -/
lemma isSeparablyGenerated_of_linearIndepOn_pow
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K]
    (hlin :
      ∀ s : Finset K,
        LinearIndepOn k _root_.id (s : Set K) →
          LinearIndepOn k (fun x ↦ x ^ p) (s : Set K)) :
    IsSeparablyGenerated k K := by
  -- Apply the owner theorem producing a separating transcendence basis from the Frobenius
  -- linear-independence hypothesis.
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      (k := k) (K := K) (p := p) (hp := Fact.out) hlin
  refine ⟨(s : Set K), ?_, ?_⟩
  · -- The finite-set witness is the required transcendence basis after forgetting finiteness.
    simpa using hs
  · -- The resulting extension over the generated intermediate field is separable.
    simpa using hsep

/-- Helper for Chap10 Lemma 10 42 4: after a finite purely inseparable lift satisfies the
Frobenius linear-independence criterion, the lifted top field is already separably generated over
the lifted base field. -/
lemma lift_with_separablyGenerated_of_linearIndepOn_pow
    {k' : Type (max u w)} [Field k'] [Algebra k k']
    {K' : Type (max v (max u w))} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    [FiniteDimensional k k'] [IsPurelyInseparable k k']
    [FiniteDimensional K K'] [IsPurelyInseparable K K']
    {p : ℕ} [Fact p.Prime] [CharP k' p] [Algebra.EssFiniteType k' K']
    (hlin :
      ∀ s : Finset K',
        LinearIndepOn k' _root_.id (s : Set K') →
          LinearIndepOn k' (fun x ↦ x ^ p) (s : Set K')) :
    IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  have hsepgen : IsSeparablyGenerated k' K' :=
    isSeparablyGenerated_of_linearIndepOn_pow (k := k') (K := K') (p := p) hlin
  -- The lift data are already purely inseparable and finite; only separable generation remains.
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hsepgen⟩

/-- Helper for Chap10 Lemma 10 42 4: in positive characteristic, the remaining work is the
source-style induction on the purely inseparable degree over a separating transcendence basis. -/
lemma exists_purelyInseparable_lift_with_separablyGenerated_of_positiveCharacteristic
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  classical
  by_cases hperfect : PerfectField k
  · -- If the characteristic-`p` base is already perfect, the identity square is enough.
    letI : PerfectField k := hperfect
    exact exists_identity_lift_with_separablyGenerated_of_perfectField (k := k) (K := K)
  · -- Route correction: the source induction is only needed in the imperfect positive-characteristic
    -- case. Choose the source transcendence-basis stage and recurse directly on its inseparable
    -- degree instead of detouring through the stronger Frobenius linear-independence criterion.
    obtain ⟨x, hx, _⟩ :=
      exists_fin_reindexed_transcendence_basis_with_finiteDimensional_over_separableClosure
        (k := k) (K := K)
    exact
      exists_purelyInseparable_lift_with_separablyGenerated_bounded_by_finInsepDegree
        (k := k) (K := K) (p := p)
        (n := Field.finInsepDegree (IntermediateField.adjoin k (Set.range x)) K) hx le_rfl

-- Proof sketch: choose a separating transcendence basis after passing to the separable closure
-- decomposition from Lemma `9.14.6`. In positive characteristic, adjoin finitely many `p`th
-- roots to the base so that one step of the purely inseparable part descends into the separable
-- closure using Lemma `9.28.2`, reducing the inseparable degree. Induct on that degree.
/-- Chap10 Lemma 10 42 4: for a finitely generated field extension `K/k`, there exist fields `k'`
and `K'` forming a commutative square of extensions over `k`, with `K' / K` and `k' / k` finite
purely inseparable and `K' / k'` separably generated. -/
@[stacks 04KM]
theorem exists_purelyInseparable_lift_with_separablyGenerated
    [Algebra.EssFiniteType k K] :
    ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
      (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
      (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
        IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' := by
  -- Route correction: the witness universes must be widened to `Type (max u w)` and
  -- `Type (max v (max u w))`; otherwise even the characteristic-zero identity lift is not typable
  -- when the requested witness universes are smaller than the source universes.
  obtain hchar0 | ⟨p, hp, hcharp⟩ := CharP.exists' k
  · -- Characteristic zero is perfect, so the identity square already works.
    letI : CharZero k := hchar0
    letI : PerfectField k := PerfectField.ofCharZero
    exact exists_identity_lift_with_separablyGenerated_of_perfectField (k := k) (K := K)
  · -- The positive-characteristic case is the remaining source-style induction.
    letI : Fact p.Prime := hp
    letI : CharP k p := hcharp
    exact
      exists_purelyInseparable_lift_with_separablyGenerated_of_positiveCharacteristic
        (k := k) (K := K)

end
