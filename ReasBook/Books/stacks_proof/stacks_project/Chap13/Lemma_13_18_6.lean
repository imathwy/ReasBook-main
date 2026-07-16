import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_18_1
import stacks_proof.stacks_project.Chap13.«13_18_6_1»
import stacks_proof.stacks_project.Chap13.Remark_13_18_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex
open HomComplex
open scoped ZeroObject

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: lifting morphisms of cochain complexes into bounded-below injective complexes,
  viewed through the homotopy and derived categories, and strictified via the canonical cochain
  lifting obstruction theory;
- sampled owner declarations:
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`,
  `CochainComplex.Lifting.hasLift`,
  `cokernel_acyclic_of_termwiseMono_quasiIso`;
- best owner abstraction: the chapter bridge theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`, whose core owner is
  the K-injective comparison theorem `CochainComplex.IsKInjective.Qh_map_bijective`; for the
  strict lifting statement, the owner abstraction is the canonical obstruction-theoretic lifting
  engine `CochainComplex.Lifting.hasLift`;
- primitive data: a quasi-isomorphism `α : K ⟶ L`, a map `γ : K ⟶ I`, and the bounded-below
  injective structure on `I`;
- derived API: existence of a lift up to homotopy, and the stricter source-facing exact lift when
  `α` is termwise monomorphic.

Source/core/bridge triage:
- `source-facing`: the two lifting statements in this file;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective` for part (1), and
  `CochainComplex.Lifting.hasLift` for part (2);
- `bridge/view`: the chapter theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`, from which the
  homotopy-level existence result is derived directly, together with the acyclic obstruction
  calculation on `cokernel α` for the strict lift.
-/

-- Proof sketch: pass to the homotopy category and apply the owner theorem
-- `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` to the class of
-- `γ`. Surjectivity gives a class of maps `L^• ⟶ I^•` whose precomposition with `α` equals the
-- class of `γ`, and equality in the homotopy category is exactly homotopy.
/-- Lemma 13.18.6 (1): if `α : K^• ⟶ L^•` is a quasi-isomorphism and `I^•` is a bounded-below
cochain complex of injective objects, then every map `γ : K^• ⟶ I^•` extends along `α` to a map
`β : L^• ⟶ I^•` for which `β ∘ α` and `γ` are homotopic. -/
@[stacks 013P]
theorem exists_homotopy_lift_to_boundedBelow_injective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]
    (I : InjectivePlus 𝒜) (γ : K ⟶ I) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  let Q := HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)
  let hα := homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective α I
  obtain ⟨β, hβ⟩ := hα.surjective (Q.map γ)
  obtain ⟨β, rfl⟩ := Q.map_surjective β
  refine ⟨β, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa [Functor.map_comp] using hβ

-- Proof sketch: apply the canonical cochain lifting engine to the square with right edge
-- `I^• ⟶ 0`. Degreewise liftings exist because each `α.f n` is monic and `I.X n` is injective.
-- The obstruction cocycle lies in `Cocycle (cokernel α) I 1`; the cokernel complex is acyclic by
-- 13.18.6.1, while `I⟦1⟧` is K-injective, so the corresponding map `cokernel α ⟶ I⟦1⟧` is
-- null-homotopic. Converting that null-homotopy back to a degree-zero cochain shows that the
-- obstruction is a coboundary, and `CochainComplex.Lifting.hasLift` then produces the desired
-- strict lift.
/-- Lemma 13.18.6 (2): if, in addition, each component `α^n` is a monomorphism, then the lift
`β : L^• ⟶ I^•` can be chosen so that `β ∘ α = γ` exactly. -/
@[stacks 013P]
theorem exists_strict_lift_to_boundedBelow_injective_of_termwiseMono
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]
    (I : InjectivePlus 𝒜) (γ : K ⟶ I)
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  let J : CochainComplex 𝒜 ℤ := I
  let sq : CommSq γ α (0 : J ⟶ 0) (0 : L ⟶ 0) := CommSq.mk (by simp)
  let hsq : ∀ n : ℤ, (sq.map (eval 𝒜 (ComplexShape.up ℤ) n)).LiftStruct := by
    intro n
    let _ : Injective (J.X n) := I.term_mem n
    refine
      { l := (Injective.factorThru (γ.f n) (α.f n) : L.X n ⟶ J.X n)
        fac_left := ?_
        fac_right := ?_ }
    · exact Injective.comp_factorThru (γ.f n) (α.f n)
    · exact comp_zero
  have hQ : IsColimit (CokernelCofork.ofπ (cokernel.π α) (cokernel.condition α)) :=
    CokernelCofork.IsColimit.ofπ' (cokernel.π α) (cokernel.condition α)
      (fun k hk ↦ ⟨cokernel.desc α k hk, by exact cokernel.π_desc α k hk⟩)
  have hK :
      IsLimit
        ((KernelFork.ofι (𝟙 J) (by simp)) : KernelFork (0 : J ⟶ 0)) :=
    KernelFork.IsLimit.ofId (0 : J ⟶ 0) rfl
  let obstruction : Cocycle (cokernel α) J 1 :=
    CochainComplex.Lifting.cocycle₁ sq hsq hQ hK
  have hac : (cokernel α).Acyclic :=
    cokernel_acyclic_of_termwiseMono_quasiIso α hmono
  let hnull :
      Homotopy
        (Cocycle.equivHomShift.symm obstruction)
        0 :=
    IsKInjective.homotopyZero (Cocycle.equivHomShift.symm obstruction) hac
  obtain ⟨cochainShift, hcochainShift⟩ :=
    Cochain.equivHomotopy (Cocycle.equivHomShift.symm obstruction) 0 hnull
  have hcochainShift :
      Cochain.ofHom (Cocycle.equivHomShift.symm obstruction) =
        δ (-1) 0 cochainShift := by
    simpa using hcochainShift
  have hobstruction :
      (Cochain.ofHom (Cocycle.equivHomShift.symm obstruction)).rightUnshift 1 (by simp) =
        obstruction.1 := by
    change
      (Cocycle.equivHomShift (Cocycle.equivHomShift.symm obstruction)).1 = obstruction.1
    exact
      congrArg
        (fun z : Cocycle (cokernel α) J 1 ↦ z.1)
        (Cocycle.equivHomShift.apply_symm_apply obstruction)
  let cochain :
      Cochain (cokernel α) J 0 :=
    (-cochainShift).rightUnshift 0 (by simp)
  have hδ : δ 0 1 cochain = obstruction.1 := by
    dsimp [cochain]
    rw [Cochain.δ_rightUnshift (-cochainShift) 0 (by simp) 1 0 (by simp)]
    simp only [Int.negOnePow_one, Int.reduceNeg, δ_neg, Cochain.rightUnshift_neg, smul_neg,
      Units.neg_smul, one_smul, neg_neg]
    rw [← hcochainShift]
    exact hobstruction
  letI : sq.HasLift := CochainComplex.Lifting.hasLift sq hsq hQ hK cochain hδ
  exact ⟨sq.lift, sq.fac_left⟩

end CochainComplex
