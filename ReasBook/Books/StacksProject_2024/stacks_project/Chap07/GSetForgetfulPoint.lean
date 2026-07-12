import Mathlib
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksProject_2024.Chap07.Example_7_6_5
import StacksProject_2024.Chap07.Proposition_7_33_3

open CategoryTheory Limits Opposite

universe u v

namespace CategoryTheory

noncomputable section

variable (G : Type u) [Group G]

-- Proof sketch: the category of elements of the forgetful functor on `G`-sets is essentially
-- small in the ambient universes, hence it is initially small.
private instance gSetForgetful_elements_initiallySmall :
    InitiallySmall.{u} (Functor.Elements (Action.forget (Type u) G)) := sorry

-- Proof sketch: apply `Action.mem_jointlySurjectiveTopology_iff`; by covering-surjectivity, the chosen point
-- `x : X.V` lies in the image of some arrow belonging to the covering sieve.
/-- Covering sieves in `\mathcal T_G` act jointly surjectively on the forgetful fiber functor. -/
theorem gSetForgetful_jointly_surjective
    {X : Action (Type u) G} (R : Sieve X)
    (hR : R ∈ Action.jointlySurjectiveTopology G X) (x : X.V) :
    ∃ (Y : Action (Type u) G) (f : Y ⟶ X), R f ∧
      ∃ y : Y.V, (Action.forget (Type u) G).map f y = x := sorry

/-- Example 7.33.7: the forgetful functor from the surjective site of `G`-sets to sets defines a
canonical point of the site `\mathcal T_G`. -/
def gSetForgetfulPoint : (Action.jointlySurjectiveTopology G).Point := by
  let u : Action (Type u) G ⥤ Type u := Action.forget (Type u) G
  letI : IsCofiltered u.Elements := Functor.isCofiltered_elements u
  exact
    { fiber := u
      jointly_surjective := by
        intro X R hR x
        rcases gSetForgetful_jointly_surjective G R hR x with ⟨Y, f, hf, y, hy⟩
        exact ⟨Y, f, hf, y, hy⟩ }

-- Proof sketch: right multiplication commutes with the left regular action by associativity in
-- the group `G`.
private theorem gSetForgetfulPointLeftRegularRightMul_comm (g : G) :
    ∀ h : G,
      (Action.leftRegular G).ρ h ≫ (fun x : G ↦ x * g) =
        (fun x : G ↦ x * g) ≫ (Action.leftRegular G).ρ h := sorry

/-- The endomorphism of the left regular `G`-set given by right multiplication by `g`. -/
def gSetForgetfulPointLeftRegularRightMul (g : G) : Action.leftRegular G ⟶ Action.leftRegular G
    where
  hom := fun x : G ↦ x * g
  comm := gSetForgetfulPointLeftRegularRightMul_comm G g

@[simp] theorem gSetForgetfulPointLeftRegularRightMul_one :
    gSetForgetfulPointLeftRegularRightMul G 1 = 𝟙 (Action.leftRegular G) := by
  apply Action.hom_ext
  ext x
  simp [gSetForgetfulPointLeftRegularRightMul]

@[simp] theorem gSetForgetfulPointLeftRegularRightMul_mul (g h : G) :
    gSetForgetfulPointLeftRegularRightMul G (g * h) =
      gSetForgetfulPointLeftRegularRightMul G g ≫ gSetForgetfulPointLeftRegularRightMul G h := by
  apply Action.hom_ext
  ext x
  simp [gSetForgetfulPointLeftRegularRightMul, mul_assoc]

/-- The right-translation action of `G` on `Map(G, S)` from Example 7.33.7. -/
instance gSetForgetfulPointMapMulAction (S : Type v) : MulAction G (G → S) where
  smul g ψ := fun x ↦ ψ (x * g)
  one_smul ψ := by
    ext x
    change ψ (x * (1 : G)) = ψ x
    simp
  mul_smul g h ψ := by
    ext x
    change ψ (x * (g * h)) = ψ ((x * g) * h)
    simp [mul_assoc]

/-- In the right-translation action on `Map(G, S)`, the element `g` acts by precomposition with
right multiplication by `g`. -/
@[simp] theorem gSetForgetfulPointMapMulAction_smul_apply
    (S : Type v) (g x : G) (ψ : G → S) :
    (g • ψ) x = ψ (x * g) :=
  rfl

end

end CategoryTheory
