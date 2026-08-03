module

public import Topology_Munkres_2000.Book.Theorem_54_4
public import Topology_Munkres_2000.Book.Notation_52_1.RightCosets
import all Topology_Munkres_2000.Book.Definition_54_2.LiftingCorrespondence

public section

universe u v

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) {e₀ : E} {b₀ : B}

/-- Helper for Theorem 54.6: casting a path class along reflexive endpoint equalities leaves
the class unchanged. -/
private lemma pathClassCast_self {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path.Homotopic.Quotient x y) (hx : x = x) (hy : y = y) :
    γ.cast hx hy = γ := by
  -- Proof irrelevance reduces both endpoint witnesses to reflexivity.
  rw [Subsingleton.elim hx rfl, Subsingleton.elim hy rfl,
    Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The image in `π₁(B, b₀)` of the fundamental-group homomorphism induced by a covering map. -/
@[expose]
noncomputable def fundamentalGroupMapRange (he₀ : p e₀ = b₀) : Subgroup (FundamentalGroup B b₀) :=
  (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀).range

/-- The point `e₀`, regarded as an element of the fiber over `b₀`. -/
def basepointInFiber (p : E → B) (he₀ : p e₀ = b₀) : p ⁻¹' {b₀} :=
  ⟨e₀, he₀⟩

/-- A covering map induces an injective homomorphism on fundamental groups. -/
theorem fundamentalGroupMap_injective (he₀ : p e₀ = b₀) :
    Function.Injective (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀) := by
  -- Normalize the transported base point, then use injectivity on path-homotopy classes.
  cases he₀
  intro γ δ hγδ
  have hmapped := congrArg FundamentalGroup.toPath hγδ
  have hmappedPaths :
      (FundamentalGroup.toPath γ).map ⟨p, hp.continuous⟩ =
        (FundamentalGroup.toPath δ).map ⟨p, hp.continuous⟩ := by
    simpa only [FundamentalGroup.mapOfEq_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl] using hmapped
  have hpaths : FundamentalGroup.toPath γ = FundamentalGroup.toPath δ :=
    hp.injective_path_homotopic_map e₀ e₀ hmappedPaths
  exact congrArg FundamentalGroup.fromPath hpaths

/-- Membership in the induced subgroup is equivalent to fixing the selected fiber point under
monodromy. -/
theorem mem_fundamentalGroupMapRange_iff_monodromy (he₀ : p e₀ = b₀)
    (γ : FundamentalGroup B b₀) :
    γ ∈ hp.fundamentalGroupMapRange he₀ ↔
      hp.monodromy γ (basepointInFiber p he₀) = basepointInFiber p he₀ := by
  -- Remove the base-point transport so mapped loops and canonical lifts have reflexive casts.
  cases he₀
  constructor
  · rintro ⟨Γ, rfl⟩
    -- A loop coming from upstairs fixes its starting point by uniqueness of lifting.
    refine hp.monodromy_eq_of_map_eq Γ ?_
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_cast]
    exact (pathClassCast_self (X := B)
      (Path.Homotopic.Quotient.map (FundamentalGroup.toPath Γ) ⟨p, hp.continuous⟩) _ _).symm
  · intro hγ
    -- A fixed lifted endpoint turns the canonical lifted path into an upstairs loop.
    use (hp.liftPathQuotient γ (basepointInFiber p rfl)).cast rfl
      (congrArg Subtype.val hγ).symm
    simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      hp.map_liftPathQuotient, Path.Homotopic.Quotient.cast_cast,
      Path.Homotopic.Quotient.cast_rfl_rfl]

/-- Helper for Theorem 54.6: the induced right-coset relation is equality of inverse
representatives under the lifting correspondence. -/
theorem rightRel_iff_liftingCorrespondence_inv_eq (he₀ : p e₀ = b₀)
    {γ δ : FundamentalGroup B b₀} :
    QuotientGroup.rightRel (hp.fundamentalGroupMapRange he₀) γ δ ↔
      hp.liftingCorrespondence (basepointInFiber p he₀) γ⁻¹ =
        hp.liftingCorrespondence (basepointInFiber p he₀) δ⁻¹ := by
  -- Route correction: direct representatives encode the opposite coset relation, so evaluate
  -- inverse representatives to match mathlib's `rightRel` orientation.
  -- Interpret subgroup membership as stabilization under the monodromy action.
  letI : MulAction (FundamentalGroup B b₀) (p ⁻¹' {b₀}) :=
    hp.fundamentalGroupMulAction b₀
  rw [QuotientGroup.rightRel_apply,
    hp.mem_fundamentalGroupMapRange_iff_monodromy he₀]
  -- The action law converts `δ * γ⁻¹` fixing the base point into equality of inverses.
  unfold liftingCorrespondence
  change (δ * γ⁻¹) • basepointInFiber p he₀ = basepointInFiber p he₀ ↔
    γ⁻¹ • basepointInFiber p he₀ = δ⁻¹ • basepointInFiber p he₀
  rw [mul_smul, smul_eq_iff_eq_inv_smul]

/-- The endpoint map from right cosets of the induced subgroup to the covering fiber. -/
noncomputable def monodromyRightCosetMap (he₀ : p e₀ = b₀) :
    FundamentalGroup B b₀ ⧸ᵣ hp.fundamentalGroupMapRange he₀ → p ⁻¹' {b₀} :=
  Quotient.lift
    (fun γ ↦ hp.liftingCorrespondence (basepointInFiber p he₀) γ⁻¹)
    (fun _ _ h ↦ (hp.rightRel_iff_liftingCorrespondence_inv_eq he₀).mp h)

/-- The right-coset endpoint map evaluates inverse representatives by the lifting
correspondence. -/
theorem monodromyRightCosetMap_mk (he₀ : p e₀ = b₀) (γ : FundamentalGroup B b₀) :
    hp.monodromyRightCosetMap he₀ (Quotient.mk'' γ) =
      hp.liftingCorrespondence (basepointInFiber p he₀) γ⁻¹ := by
  -- Quotient evaluation exposes the inverse-representative function used in the definition.
  rfl

/-- The endpoint map from right cosets of the induced subgroup is injective. -/
theorem monodromyRightCosetMap_injective (he₀ : p e₀ = b₀) :
    Function.Injective (hp.monodromyRightCosetMap he₀) := by
  intro q₁ q₂ hq
  -- Reduce both quotient classes to representatives and recover the defining relation.
  refine Quotient.inductionOn₂ q₁ q₂ ?_ hq
  intro γ δ hγδ
  apply Quotient.sound
  apply (hp.rightRel_iff_liftingCorrespondence_inv_eq he₀).mpr
  simpa only [hp.monodromyRightCosetMap_mk] using hγδ

/-- For a path-connected covering space, right cosets of the induced subgroup correspond
bijectively to the covering fiber. -/
theorem monodromyRightCosetMap_bijective (he₀ : p e₀ = b₀) [PathConnectedSpace E] :
    Function.Bijective (hp.monodromyRightCosetMap he₀) := by
  -- Injectivity is the coset criterion; surjectivity comes from Theorem 54.4.
  constructor
  · exact hp.monodromyRightCosetMap_injective he₀
  · intro e
    obtain ⟨γ, hγ⟩ := hp.liftingCorrespondence_surjective
      (basepointInFiber p he₀) e
    use Quotient.mk'' γ⁻¹
    rw [hp.monodromyRightCosetMap_mk]
    simpa only [inv_inv] using hγ

/-- A based loop class belongs to the induced subgroup exactly when its canonical lift from
`e₀` ends again at `e₀`. -/
theorem loopClass_mem_range_iff_liftPath_one (he₀ : p e₀ = b₀) (f : Path b₀ b₀) :
    FundamentalGroup.fromPath (.mk f) ∈ hp.fundamentalGroupMapRange he₀ ↔
      hp.liftPath f e₀ (f.source.trans he₀.symm) 1 = e₀ := by
  -- Use the stabilizer characterization, then compare the underlying points in the fiber.
  rw [hp.mem_fundamentalGroupMapRange_iff_monodromy he₀]
  rw [Subtype.ext_iff]
  rfl

end IsCoveringMap
