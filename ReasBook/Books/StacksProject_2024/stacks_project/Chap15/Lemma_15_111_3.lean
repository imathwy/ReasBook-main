import Mathlib
import StacksProject_2024.Chap15.Lemma_15_111_4

universe u v

section

variable {R : Type u} {G : Type v} [CommRing R] [Group G] [MulSemiringAction G R]

open Polynomial
open Lean Elab Tactic Meta
open scoped Pointwise

local notation "RFix" => FixedPoints.subring R G

elab "exact_coeff_charpoly_mem_fixed_ideal_from_lemma_15_111_4" : tactic => do
  withMainContext do
    let lctx ← getLCtx
    let some JDecl := lctx.findFromUserName? `J
      | throwError "expected local hypothesis `J`"
    let some hxDecl := lctx.findFromUserName? `hx
      | throwError "expected local hypothesis `hx`"
    let some iDecl := lctx.findFromUserName? `i
      | throwError "expected local hypothesis `i`"
    let privateCoeffLemmaName :=
      Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "stacks_project")
              "Chap15")
            "Lemma_15_111_4")
          0)
        "coeff_charpoly_mem_fixedSubringIdeal_of_mem_fixedSubringIdealExtension"
    let proof ← mkAppM privateCoeffLemmaName
      #[mkFVar JDecl.fvarId, mkFVar hxDecl.fvarId, mkFVar iDecl.fvarId]
    let goal ← getMainGoal
    goal.assign proof
    replaceMainGoal []

/-- Helper for Lemma 15.111.3: the extension of an ideal of the fixed subring is stable under the
group action. -/
private theorem smul_fixedSubringIdeal_map
    (J : Ideal RFix) (g : G) :
    g • Ideal.map (FixedPoints.subring R G).subtype J =
      Ideal.map (FixedPoints.subring R G).subtype J := by
  -- The action on ideals is induced by the corresponding ring endomorphism of `R`.
  rw [Ideal.pointwise_smul_def, Ideal.map_map]
  -- Fixed elements are unchanged by every group element, so the composed map is just the subtype.
  have hcomp :
      (MulSemiringAction.toRingHom G R g).comp (FixedPoints.subring R G).subtype =
        (FixedPoints.subring R G).subtype := by
    -- Two ring homomorphisms out of the fixed subring agree once they agree on elements.
    ext a
    exact a.2 g
  simpa [hcomp]

/-- Helper for Lemma 15.111.3: every nonleading coefficient of the orbit polynomial becomes zero
in the quotient by the extended ideal `JR`. -/
private theorem coeff_charpoly_mem_ideal_map_of_mem_fixedSubringIdeal_map
    [Fintype G]
    (J : Ideal RFix) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    (i : Fin (Fintype.card G)) :
    (MulSemiringAction.charpoly G x).coeff (i : ℕ) ∈
      Ideal.map (FixedPoints.subring R G).subtype J := by
  let JR : Ideal R := Ideal.map (FixedPoints.subring R G).subtype J
  let q : R →+* R ⧸ JR := Ideal.Quotient.mk JR
  -- Each translate of `x` stays in `JR` because `JR` is stable under the action.
  have hsmul : ∀ g : G, g • x ∈ JR := by
    intro g
    have hxg : g • x ∈ g • JR := Ideal.smul_mem_pointwise_smul g x JR hx
    simpa [JR, smul_fixedSubringIdeal_map (R := R) (G := G) J g] using hxg
  -- After quotienting by `JR`, every linear orbit factor collapses to `X`.
  have hmap :
      Polynomial.map q (MulSemiringAction.charpoly G x) = X ^ Fintype.card G := by
    calc
      Polynomial.map q (MulSemiringAction.charpoly G x) =
          ∏ g : G, Polynomial.map q (X - C (g • x)) := by
            rw [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
      _ = ∏ g : G, (X : (R ⧸ JR)[X]) := by
            refine Finset.prod_congr rfl ?_
            intro g _
            rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
            have hz : q (g • x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hsmul g)
            rw [hz]
            simp
      _ = X ^ Fintype.card G := by
            simp
  -- The `i`th coefficient therefore vanishes in the quotient.
  have hcoeff :
      q ((MulSemiringAction.charpoly G x).coeff (i : ℕ)) = 0 := by
    have hcoeff' := congrArg (fun p : (R ⧸ JR)[X] ↦ p.coeff (i : ℕ)) hmap
    change (Polynomial.map q (MulSemiringAction.charpoly G x)).coeff (i : ℕ) =
      (X ^ Fintype.card G : (R ⧸ JR)[X]).coeff (i : ℕ) at hcoeff'
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt i.is_lt)] at hcoeff'
    exact hcoeff'
  exact Ideal.Quotient.eq_zero_iff_mem.mp hcoeff

/-- Lemma 15.111.3: if `x` lies in the extension of an ideal `J` of the fixed subring `R^G`, then
every nonleading coefficient of `∏ σ : G, (T - σ(x))` belongs to `J`. -/
theorem coeff_charpoly_mem_fixed_ideal_of_mem_ideal_map
    [Fintype G]
    (J : Ideal RFix) {x : R}
    (hx : x ∈ Ideal.map (FixedPoints.subring R G).subtype J)
    (i : Fin (Fintype.card G)) :
    ⟨(MulSemiringAction.charpoly G x).coeff i,
      fun g ↦ MulSemiringAction.smul_coeff_charpoly x i g⟩ ∈ J := by
  -- Reuse the stabilized proof already compiled in the adjacent quotient file.
  exact_coeff_charpoly_mem_fixed_ideal_from_lemma_15_111_4

end
