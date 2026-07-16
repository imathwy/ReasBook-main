import Mathlib.Algebra.Category.Grp.Zero
import stacks_proof.stacks_project.Chap14.Definition_14_31_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open CategoryTheory.Limits

open scoped SSet.modelCategoryQuillen Simplicial ZeroObject

universe u

noncomputable section

section

variable {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y)

/-- Helper for Lemma 14.31.7: use the zero object of `GrpCat` to supply the zero morphisms needed
for categorical kernels in this file. -/
local instance hasZeroMorphismsGrpCat : HasZeroMorphisms GrpCat :=
  CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject (C := GrpCat)

/- Domain-style sampling for Lemma 14.31.7:
- primary domain: simplicial groups as functor-category objects, together with the Quillen
  fibration predicate on the underlying simplicial-set map;
- sampled owner declarations:
  `NatTrans.epi_iff_epi_app'`,
  `GrpCat.epi_iff_surjective`,
  `HomotopicalAlgebra.Fibration`,
  the source-facing owner theorem `simplicialGroup_kanComplex X`;
- best owner abstraction: the canonical owner bridge from `[Epi f]` to
  `Fibration (Functor.whiskerRight f (forget GrpCat))`, with termwise surjectivity obtained as the
  source-facing bridge to `Epi f`;
- primitive-vs-derived split:
  primitive data: the morphism `f : X ⟶ Y`;
  derived API: the owner hypothesis `[Epi f]`, the induced `Fibration` instance on the underlying
  simplicial-set map, and the termwise-surjectivity bridge to that instance.

Source/core/bridge triage:
- `source-facing`: termwise-surjective morphisms of simplicial groups;
- `core/canonical`: the owner instance
  `[Epi f] : Fibration (Functor.whiskerRight f (forget GrpCat))`;
- `bridge/view`: `NatTrans.epi_iff_epi_app'` together with `GrpCat.epi_iff_surjective`.

The simplicial-abelian-group statements below are only a specialization layer for downstream use;
they are not a second owner abstraction. -/
-- Proof sketch: choose a degreewise preimage of any simplex in `Y`, divide it out to reduce the
-- lifting problem to the kernel simplicial group of `f`, and then apply the canonical
-- Kan-complex theorem from Lemma 14.31.6 to the underlying simplicial set of that simplicial
-- group.
/-- Helper for Lemma 14.31.7: the constant-unit map into the underlying simplicial set of a
simplicial group is natural in the simplicial direction. -/
lemma one_hom_naturality {S : SSet.{u}} {K : SimplicialObject GrpCat.{u}}
    (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m) :
    (fun _x : S.obj n ↦ (1 : K.obj m)) =
      fun _x : S.obj n ↦ (K ⋙ forget GrpCat).map φ (1 : K.obj n) := by
  -- The unit simplex stays the unit under every face and degeneracy map.
  funext x
  simp

/-- Helper for Lemma 14.31.7: the constant-unit map into the underlying simplicial set of a
simplicial group. -/
def one_hom {S : SSet.{u}} (K : SimplicialObject GrpCat.{u}) :
    S ⟶ K ⋙ forget GrpCat where
  app _ _ := 1
  naturality n m φ := one_hom_naturality (S := S) (K := K) n m φ

/-- Helper for Lemma 14.31.7: pointwise multiplication of simplicial maps is natural. -/
lemma mul_hom_naturality {S : SSet.{u}} {K : SimplicialObject GrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget GrpCat) (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m) :
    (fun x : S.obj n ↦ σ.app m (S.map φ x) * τ.app m (S.map φ x)) =
      fun x : S.obj n ↦ (K ⋙ forget GrpCat).map φ (σ.app n x * τ.app n x) := by
  -- Naturality of both factors and preservation of multiplication reduce this to `map_mul`.
  funext x
  have hσ :=
    (FunctorToTypes.naturality S (K ⋙ forget GrpCat) σ φ x :
      σ.app m (S.map φ x) = (K ⋙ forget GrpCat).map φ (σ.app n x))
  have hτ :=
    (FunctorToTypes.naturality S (K ⋙ forget GrpCat) τ φ x :
      τ.app m (S.map φ x) = (K ⋙ forget GrpCat).map φ (τ.app n x))
  dsimp at hσ hτ ⊢
  rw [hσ, hτ]
  simpa using
    (map_mul (ConcreteCategory.hom (K.map φ)) (σ.app n x) (τ.app n x)).symm

/-- Helper for Lemma 14.31.7: pointwise multiplication of simplicial maps into a simplicial
group. -/
def mul_hom {S : SSet.{u}} {K : SimplicialObject GrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget GrpCat) :
    S ⟶ K ⋙ forget GrpCat where
  app n x := σ.app n x * τ.app n x
  naturality n m φ := mul_hom_naturality (σ := σ) (τ := τ) n m φ

/-- Helper for Lemma 14.31.7: pointwise division of simplicial maps is natural. -/
lemma div_hom_naturality {S : SSet.{u}} {K : SimplicialObject GrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget GrpCat) (n m : SimplexCategoryᵒᵖ) (φ : n ⟶ m) :
    (fun x : S.obj n ↦ σ.app m (S.map φ x) * (τ.app m (S.map φ x))⁻¹) =
      fun x : S.obj n ↦ (K ⋙ forget GrpCat).map φ (σ.app n x * (τ.app n x)⁻¹) := by
  -- Naturality of both terms and preservation of inversion reduce this to `map_mul`.
  funext x
  have hσ :=
    (FunctorToTypes.naturality S (K ⋙ forget GrpCat) σ φ x :
      σ.app m (S.map φ x) = (K ⋙ forget GrpCat).map φ (σ.app n x))
  have hτ :=
    (FunctorToTypes.naturality S (K ⋙ forget GrpCat) τ φ x :
      τ.app m (S.map φ x) = (K ⋙ forget GrpCat).map φ (τ.app n x))
  dsimp at hσ hτ ⊢
  rw [hσ, hτ]
  simpa using
    (map_mul (ConcreteCategory.hom (K.map φ)) (σ.app n x) ((τ.app n x)⁻¹)).symm

/-- Helper for Lemma 14.31.7: pointwise division of simplicial maps into a simplicial group. -/
def div_hom {S : SSet.{u}} {K : SimplicialObject GrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget GrpCat) :
    S ⟶ K ⋙ forget GrpCat where
  app n x := σ.app n x * (τ.app n x)⁻¹
  naturality n m φ := div_hom_naturality (σ := σ) (τ := τ) n m φ

/-- Helper for Lemma 14.31.7: an element with trivial image under a group homomorphism lifts to
the categorical kernel. -/
lemma exists_kernel_element_of_one {G H : GrpCat.{u}} (g : G ⟶ H) (x : G)
    (hx : g x = 1) :
    ∃ z : (CategoryTheory.Limits.kernel g : GrpCat), CategoryTheory.Limits.kernel.ι g z = x := by
  let xHom : GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶ G :=
    GrpCat.ofHom ((uliftZPowersHom G) x)
  have hxHom : xHom ≫ g = 0 := by
    -- The corepresenting cyclic group records all powers of `x`, which map to powers of `1`.
    apply GrpCat.ext
    intro n
    change g (((uliftZPowersHom G) x) n) =
      (0 : GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶ H) n
    have hzero : (0 : GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶ H) n = 1 := by
      change
        (ConcreteCategory.hom (default : (0 : GrpCat) ⟶ H))
            ((ConcreteCategory.hom (default : GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶
                (0 : GrpCat))) n) = 1
      letI : Subsingleton (0 : GrpCat) :=
        GrpCat.subsingleton_of_isZero (CategoryTheory.Limits.isZero_zero (C := GrpCat))
      have htriv :
          (ConcreteCategory.hom (default : GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶
              (0 : GrpCat))) n = (1 : (0 : GrpCat)) := by
        exact Subsingleton.elim _ _
      rw [htriv]
      simp
    rw [hzero]
    simp [uliftZPowersHom, hx]
  refine ⟨
    (CategoryTheory.Limits.kernel.lift g xHom hxHom)
      (show ULift.{u} (Multiplicative ℤ) from
        ULift.up (Multiplicative.ofAdd (1 : ℤ))), ?_⟩
  -- Evaluating the lifted map at the generator recovers the original element.
  have hz :=
    ConcreteCategory.congr_hom
      (CategoryTheory.Limits.kernel.lift_ι g xHom hxHom)
      (show ULift.{u} (Multiplicative ℤ) from ULift.up (Multiplicative.ofAdd (1 : ℤ)))
  have hxgen :
      xHom (show ULift.{u} (Multiplicative ℤ) from
        ULift.up (Multiplicative.ofAdd (1 : ℤ))) = x := by
    change x ^ Multiplicative.toAdd
        ((show ULift.{u} (Multiplicative ℤ) from
          ULift.up (Multiplicative.ofAdd (1 : ℤ))).down) = x
    simp
  exact hz.trans hxgen

/-- Helper for Lemma 14.31.7: a chosen lift of an element with trivial image to the categorical
kernel of a group homomorphism. -/
noncomputable def kernel_element_of_one {G H : GrpCat.{u}} (g : G ⟶ H) (x : G)
    (hx : g x = 1) : (CategoryTheory.Limits.kernel g : GrpCat) :=
  Classical.choose (exists_kernel_element_of_one g x hx)

/-- Helper for Lemma 14.31.7: the chosen kernel lift maps back to the original element. -/
lemma kernel_element_of_one_comp_ι {G H : GrpCat.{u}} (g : G ⟶ H) (x : G)
    (hx : g x = 1) :
    CategoryTheory.Limits.kernel.ι g (kernel_element_of_one g x hx) = x :=
  Classical.choose_spec (exists_kernel_element_of_one g x hx)

/-- Helper for Lemma 14.31.7: the zero morphism in `GrpCat` sends every element to the unit. -/
lemma zero_hom_apply_eq_one {G H : GrpCat.{u}} (x : G) :
    (0 : G ⟶ H) x = 1 := by
  change
    (ConcreteCategory.hom (default : (0 : GrpCat) ⟶ H))
        ((ConcreteCategory.hom (default : G ⟶ (0 : GrpCat))) x) = 1
  letI : Subsingleton (0 : GrpCat) :=
    GrpCat.subsingleton_of_isZero (CategoryTheory.Limits.isZero_zero (C := GrpCat))
  have htriv : (ConcreteCategory.hom (default : G ⟶ (0 : GrpCat))) x = (1 : (0 : GrpCat)) := by
    exact Subsingleton.elim _ _
  rw [htriv]
  simp

/-- Helper for Lemma 14.31.7: a simplicial map into `X` whose image under `f` is pointwise the
unit factors through the underlying simplicial set of the simplicial kernel of `f`. -/
lemma kernel_underlying_lift_of_one {S : SSet.{u}} (σ : S ⟶ X ⋙ forget GrpCat)
    (hσ : ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n, f.app n (σ.app n x) = 1) :
    ∃ σK : S ⟶ (CategoryTheory.Limits.kernel f) ⋙ forget GrpCat,
      σK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat) = σ := by
  classical
  let liftApp :
      ∀ n : SimplexCategoryᵒᵖ, S.obj n → (CategoryTheory.Limits.kernel f).obj n := fun n x =>
    (PreservesKernel.iso ((evaluation SimplexCategoryᵒᵖ GrpCat).obj n) f).inv
      (kernel_element_of_one (f.app n) (σ.app n x) (hσ n x))
  have hcomp :
      ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n,
        ((CategoryTheory.Limits.kernel.ι f).app n) (liftApp n x) = σ.app n x := by
    intro n x
    have h₁ :=
      ConcreteCategory.congr_hom
        (PreservesKernel.iso_inv_ι ((evaluation SimplexCategoryᵒᵖ GrpCat).obj n) f)
        (kernel_element_of_one (f.app n) (σ.app n x) (hσ n x))
    have h₂ :=
      kernel_element_of_one_comp_ι (f.app n) (σ.app n x) (hσ n x)
    exact h₁.trans h₂
  refine ⟨
    { app := liftApp
      naturality := ?_ }, ?_⟩
  · intro n m φ
    funext x
    -- Compare after applying the monomorphism `kernel.ι f` in degree `m`.
    apply (GrpCat.mono_iff_injective ((CategoryTheory.Limits.kernel.ι f).app m)).1 inferInstance
    change ((CategoryTheory.Limits.kernel.ι f).app m) (liftApp m (S.map φ x)) =
      ((CategoryTheory.Limits.kernel.ι f).app m)
        (((CategoryTheory.Limits.kernel f).map φ) (liftApp n x))
    rw [hcomp m (S.map φ x)]
    rw [FunctorToTypes.naturality S (X ⋙ forget GrpCat) σ φ x]
    rw [← hcomp n x]
    exact
      (FunctorToTypes.naturality ((CategoryTheory.Limits.kernel f) ⋙ forget GrpCat)
        (X ⋙ forget GrpCat)
        (Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat))
        φ (liftApp n x)).symm
  · -- Each component was chosen so that it lands back on the original simplex.
    ext n x
    exact hcomp n x

/-- Helper for Lemma 14.31.7: any simplicial map landing in the simplicial kernel of `f`
becomes the constant-unit map after composing with `f`. -/
lemma kernel_lift_comp_whiskerRight_eq_one_hom {S : SSet.{u}}
    (σK : S ⟶ (CategoryTheory.Limits.kernel f) ⋙ forget GrpCat) :
    (σK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)) ≫
        Functor.whiskerRight f (forget GrpCat) =
      one_hom Y := by
  ext n x
  have hcond :
      (((CategoryTheory.Limits.kernel.ι f).app n) ≫ f.app n) (σK.app n x) =
        (0 : (CategoryTheory.Limits.kernel f).obj n ⟶ Y.obj n) (σK.app n x) := by
    exact
      ConcreteCategory.congr_hom
        (congrArg
          (fun η : CategoryTheory.Limits.kernel f ⟶ Y ↦ η.app n)
          (CategoryTheory.Limits.kernel.condition f))
        (σK.app n x)
  -- Evaluate the kernel relation in degree `n`; the zero morphism in `GrpCat` is constant `1`.
  calc
    (((σK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)) ≫
          Functor.whiskerRight f (forget GrpCat)).app n) x
        = (((CategoryTheory.Limits.kernel.ι f).app n) ≫ f.app n) (σK.app n x) := by
            rfl
    _ = (0 : (CategoryTheory.Limits.kernel f).obj n ⟶ Y.obj n) (σK.app n x) := hcond
    _ = 1 := zero_hom_apply_eq_one (x := σK.app n x)

/-- Helper for Lemma 14.31.7: dividing a horn map by a chosen lift of the bottom simplex makes
its image under `f` pointwise trivial. -/
lemma div_hom_comp_whiskerRight_eq_one_hom
    {n : ℕ} {i : Fin (n + 2)}
    {α : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    {τ : (Δ[n + 1] : SSet.{u}) ⟶ Y ⋙ forget GrpCat}
    {σx : (Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    (hσx : σx ≫ Functor.whiskerRight f (forget GrpCat) = τ)
    (hsq : α ≫ Functor.whiskerRight f (forget GrpCat) = Λ[n + 1, i].ι ≫ τ) :
    div_hom α (Λ[n + 1, i].ι ≫ σx) ≫ Functor.whiskerRight f (forget GrpCat) = one_hom Y := by
  ext m x
  have hsqEval :
      f.app m (α.app m x) =
        τ.app m ((Λ[n + 1, i].ι).app m x) := by
    exact congrFun (congrArg (fun η ↦ η.app m) hsq) x
  have hσxEval :
      f.app m (σx.app m ((Λ[n + 1, i].ι).app m x)) =
        τ.app m ((Λ[n + 1, i].ι).app m x) := by
    exact congrFun (congrArg (fun η ↦ η.app m) hσx) ((Λ[n + 1, i].ι).app m x)
  -- After applying `f`, the corrected horn is the quotient of an element by itself.
  change f.app m (α.app m x * (σx.app m ((Λ[n + 1, i].ι).app m x))⁻¹) = 1
  have hmap :
      f.app m (α.app m x * (σx.app m ((Λ[n + 1, i].ι).app m x))⁻¹) =
        f.app m (α.app m x) * (f.app m (σx.app m ((Λ[n + 1, i].ι).app m x)))⁻¹ := by
    simpa using
      (map_mul (ConcreteCategory.hom (f.app m))
        (α.app m x) ((σx.app m ((Λ[n + 1, i].ι).app m x))⁻¹))
  rw [hmap, hsqEval, hσxEval]
  simp

/-- Helper for Lemma 14.31.7: multiplying a corrected horn filler back by the chosen simplex lift
recovers the original horn map. -/
lemma mul_hom_recovers_horn_after_division
    {n : ℕ} {i : Fin (n + 2)}
    {α : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    {σx : (Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    {τcorr : (Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    (hτcorr : Λ[n + 1, i].ι ≫ τcorr = div_hom α (Λ[n + 1, i].ι ≫ σx)) :
    Λ[n + 1, i].ι ≫ mul_hom τcorr σx = α := by
  ext m x
  have hτcorrEval :
      τcorr.app m ((Λ[n + 1, i].ι).app m x) =
        α.app m x * (σx.app m ((Λ[n + 1, i].ι).app m x))⁻¹ := by
    exact congrFun (congrArg (fun η ↦ η.app m) hτcorr) x
  -- The horn correction cancels against the chosen lift by group multiplication.
  change
    τcorr.app m ((Λ[n + 1, i].ι).app m x) *
        σx.app m ((Λ[n + 1, i].ι).app m x) =
      α.app m x
  rw [hτcorrEval]
  change α.app m x * (σx.app m ↑x)⁻¹ * σx.app m ↑x = α.app m x
  calc
    α.app m x * (σx.app m ↑x)⁻¹ * σx.app m ↑x
        = α.app m x * ((σx.app m ↑x)⁻¹ * σx.app m ↑x) := by
            rw [mul_assoc]
    _ = α.app m x * 1 := by
          rw [inv_mul_cancel]
    _ = α.app m x := by
          rw [mul_one]

/-- Helper for Lemma 14.31.7: a kernel filler of the corrected horn can be multiplied with a
chosen simplex lift to solve the original horn square. -/
lemma horn_lift_of_kernel_correction
    {n : ℕ} {i : Fin (n + 2)}
    {α : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    {τ : (Δ[n + 1] : SSet.{u}) ⟶ Y ⋙ forget GrpCat}
    {σx : (Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget GrpCat}
    (hσx : σx ≫ Functor.whiskerRight f (forget GrpCat) = τ)
    {σK : (Λ[n + 1, i] : SSet.{u}) ⟶ (CategoryTheory.Limits.kernel f) ⋙ forget GrpCat}
    (hσK : σK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat) =
      div_hom α (Λ[n + 1, i].ι ≫ σx))
    {τK : (Δ[n + 1] : SSet.{u}) ⟶ (CategoryTheory.Limits.kernel f) ⋙ forget GrpCat}
    (hτK : σK = Λ[n + 1, i].ι ≫ τK) :
    (Λ[n + 1, i].ι ≫
        mul_hom
          (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat))
          σx = α) ∧
      (mul_hom
          (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat))
          σx ≫ Functor.whiskerRight f (forget GrpCat) = τ) := by
  have hτcorr :
      Λ[n + 1, i].ι ≫
          (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)) =
        div_hom α (Λ[n + 1, i].ι ≫ σx) := by
    -- Transport the corrected horn filler from the kernel back into `X`.
    calc
      Λ[n + 1, i].ι ≫
          (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat))
          = (Λ[n + 1, i].ι ≫ τK) ≫
              Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat) := by
              simp [Category.assoc]
      _ = σK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat) := by
            rw [← hτK]
      _ = div_hom α (Λ[n + 1, i].ι ≫ σx) := hσK
  have hkernel :
      (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)) ≫
          Functor.whiskerRight f (forget GrpCat) =
        one_hom Y := by
    -- Every simplex coming from the kernel maps to the unit in `Y`.
    simpa [Category.assoc] using
      kernel_lift_comp_whiskerRight_eq_one_hom (f := f) τK
  constructor
  · -- The corrected horn filler and the chosen simplex lift cancel back to the original horn.
    exact mul_hom_recovers_horn_after_division (α := α) (σx := σx) hτcorr
  · ext m x
    have hkernelEval :
        f.app m
            ((τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)).app m
              x) = 1 := by
      exact congrFun (congrArg (fun η ↦ η.app m) hkernel) x
    have hσxEval : f.app m (σx.app m x) = τ.app m x := by
      exact congrFun (congrArg (fun η ↦ η.app m) hσx) x
    -- Over `Y`, the kernel correction is invisible, so multiplication leaves only `τ`.
    change
      f.app m
          (((τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)).app m
              x) * σx.app m x) =
        τ.app m x
    have hmap :
        f.app m
            (((τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)).app m
                x) * σx.app m x) =
          f.app m
              ((τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)).app
                m x) *
            f.app m (σx.app m x) := by
      simpa using
        (map_mul (ConcreteCategory.hom (f.app m))
          ((τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat)).app m x)
          (σx.app m x))
    rw [hmap, hkernelEval, hσxEval]
    simp

/-- Helper for Lemma 14.31.7: the standard lower-sweep correction changes the chosen lower face
to the prescribed simplex. -/
lemma lowerFaceCorrection (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (x : K.obj (op ⦋n⦌))
    (y : K.obj (op ⦋n + 1⦌)) (j : Fin (n + 1)) :
    (K.δ j.castSucc) (y * (K.σ j) (((K.δ j.castSucc) y)⁻¹ * x)) = x := by
  let defect : K.obj (op ⦋n⦌) := ((K.δ j.castSucc) y)⁻¹ * x
  -- Apply the chosen face map to the correction term and collapse the degeneracy by `δ_j σ_j = id`.
  change (K.δ j.castSucc) (y * (K.σ j) defect) = x
  rw [map_mul]
  have hδσ : (K.δ j.castSucc) ((K.σ j) defect) = defect := by
    exact ConcreteCategory.congr_hom (show K.σ j ≫ K.δ j.castSucc = 𝟙 _ from K.δ_comp_σ_self)
      defect
  rw [hδσ]
  -- The defect was chosen so that the old face cancels and only the target simplex remains.
  simp [defect]

/-- Helper for Chap14 Lemma 14 31 7: a lower correction step preserves every earlier lower face
once the prescribed boundary simplices satisfy the matching codimension-two compatibility. -/
lemma lowerFaceCorrectionPreservesFace (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (xj xk : K.obj (op ⦋n + 1⦌))
    (y : K.obj (op ⦋n + 2⦌))
    {j k : Fin (n + 2)} (hkj : k < j)
    (hy : (K.δ k.castSucc) y = xk)
    (hcompat :
      (K.δ k) xj = (K.δ (j.pred (Fin.ne_zero_of_lt hkj)).castSucc) xk) :
    (K.δ k.castSucc) (y * (K.σ j) (((K.δ j.castSucc) y)⁻¹ * xj)) = xk := by
  let defect : K.obj (op ⦋n + 1⦌) := ((K.δ j.castSucc) y)⁻¹ * xj
  have hj0 : j ≠ 0 := Fin.ne_zero_of_lt hkj
  have hkj' : k ≤ (j.pred hj0).castSucc := by
    exact Fin.le_iff_val_le_val.mpr <|
      by
        simpa [Fin.val_castSucc, Fin.val_pred] using
          Nat.le_pred_of_lt (show (k : ℕ) < j by exact Fin.lt_def.mp hkj)
  have hjCast : (j.pred hj0).castSucc.succ = j.castSucc := by
    rw [Fin.castSucc_pred_eq_pred_castSucc]
    exact Fin.succ_pred _ _
  have hδσ :
      (K.δ k.castSucc) ((K.σ j) defect) =
        (K.σ (j.pred hj0)) ((K.δ k) defect) := by
    -- Move the earlier face map past the correction degeneracy using the simplicial identity.
    exact ConcreteCategory.congr_hom
      (by
        simpa [Fin.succ_pred j hj0] using
          (show K.σ (j.pred hj0).succ ≫ K.δ k.castSucc = K.δ k ≫ K.σ (j.pred hj0) from
            K.δ_comp_σ_of_le (i := k) (j := j.pred hj0) hkj'))
      defect
  have hδδ :
      (K.δ k) ((K.δ j.castSucc) y) =
        (K.δ (j.pred hj0).castSucc) ((K.δ k.castSucc) y) := by
    -- Normalize the two consecutive face maps to the codimension-two compatibility shape.
    change (ConcreteCategory.hom (K.δ j.castSucc ≫ K.δ k)) y =
      (ConcreteCategory.hom (K.δ k.castSucc ≫ K.δ (j.pred hj0).castSucc)) y
    exact ConcreteCategory.congr_hom
      (by
        simpa [hjCast] using
          (show K.δ ((j.pred hj0).castSucc).succ ≫ K.δ k =
              K.δ k.castSucc ≫ K.δ (j.pred hj0).castSucc from
            K.δ_comp_δ (i := k) (j := (j.pred hj0).castSucc) hkj'))
      y
  have hδdef : (K.δ k) defect = 1 := by
    -- The compatibility hypothesis makes the correction defect invisible on earlier faces.
    change (K.δ k) (((K.δ j.castSucc) y)⁻¹ * xj) = 1
    rw [map_mul, map_inv, hδδ, hy, hcompat]
    simp
  -- The extra correction term restricts to the unit on earlier faces, so the old face survives.
  change (K.δ k.castSucc) (y * (K.σ j) defect) = xk
  rw [map_mul, hy, hδσ, hδdef]
  simp

/-- Helper for Lemma 14.31.7: the standard upper-sweep correction changes the chosen upper face
to the prescribed simplex. -/
lemma upperFaceCorrection (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (x : K.obj (op ⦋n⦌))
    (y : K.obj (op ⦋n + 1⦌)) (j : Fin (n + 1)) :
    (K.δ j.succ) ((K.σ j) (x * ((K.δ j.succ) y)⁻¹) * y) = x := by
  let defect : K.obj (op ⦋n⦌) := x * ((K.δ j.succ) y)⁻¹
  -- Apply the chosen face map to the correction term and collapse the degeneracy by `δ_{j+1} σ_j = id`.
  change (K.δ j.succ) ((K.σ j) defect * y) = x
  rw [map_mul]
  have hδσ : (K.δ j.succ) ((K.σ j) defect) = defect := by
    exact ConcreteCategory.congr_hom (show K.σ j ≫ K.δ j.succ = 𝟙 _ from K.δ_comp_σ_succ)
      defect
  rw [hδσ]
  -- The defect was chosen on the left so that the corrected upper face becomes exactly `x`.
  simp [defect]

/-- Helper for Chap14 Lemma 14 31 7: a single upper correction step leaves every earlier lower
face unchanged. -/
lemma upperFaceCorrectionPreservesLowerFace (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (xj xk : K.obj (op ⦋n + 1⦌))
    (y : K.obj (op ⦋n + 2⦌))
    {j k : Fin (n + 2)} (hkj : k < j)
    (hy : (K.δ k.castSucc) y = xk)
    (hcompat : (K.δ k) xj = (K.δ j) xk) :
    (K.δ k.castSucc) ((K.σ j) (xj * ((K.δ j.succ) y)⁻¹) * y) = xk := by
  let defect : K.obj (op ⦋n + 1⦌) := xj * ((K.δ j.succ) y)⁻¹
  -- The prescribed compatibility kills the defect on every lower face below `j`.
  have hδdef : (K.δ k) defect = 1 := by
    change (K.δ k) (xj * ((K.δ j.succ) y)⁻¹) = 1
    rw [map_mul, map_inv, hcompat]
    have hδδ : (K.δ k) ((K.δ j.succ) y) = (K.δ j) ((K.δ k.castSucc) y) := by
      change (ConcreteCategory.hom (K.δ j.succ ≫ K.δ k)) y =
        (ConcreteCategory.hom (K.δ k.castSucc ≫ K.δ j)) y
      exact ConcreteCategory.congr_hom (K.δ_comp_δ (i := k) (j := j) hkj.le) y
    rw [hδδ, hy]
    simp
  have hj0 : j ≠ 0 := Fin.ne_zero_of_lt hkj
  have hkLe : k ≤ (j.pred hj0).castSucc := by
    exact Fin.le_iff_val_le_val.mpr <|
      by
        simpa [Fin.val_castSucc, Fin.val_pred] using
          Nat.le_pred_of_lt (show (k : ℕ) < j by exact Fin.lt_def.mp hkj)
  have hδσ :
      (K.δ k.castSucc) ((K.σ j) defect) = (K.σ (j.pred hj0)) ((K.δ k) defect) := by
    -- Move the earlier lower face map past the upper correction degeneracy.
    exact ConcreteCategory.congr_hom
      (show K.σ j ≫ K.δ k.castSucc = K.δ k ≫ K.σ (j.pred hj0) from by
        simpa [Fin.succ_pred j hj0] using
          (show K.σ (j.pred hj0).succ ≫ K.δ k.castSucc = K.δ k ≫ K.σ (j.pred hj0) from
            K.δ_comp_σ_of_le (i := k) (j := j.pred hj0) hkLe))
      defect
  -- After the degeneracy term restricts to the unit, only the old lower face remains.
  change (K.δ k.castSucc) ((K.σ j) defect * y) = xk
  rw [map_mul, hδσ, hδdef, hy]
  simp

/-- Helper for Chap14 Lemma 14 31 7: the later upper face matched against `j` inside the
codimension-two compatibility relation. -/
def upperFaceBoundaryIndex {n : ℕ} {j k : Fin (n + 2)} (hjk : j < k) : Fin (n + 2) :=
  j.succ.castLT
    (lt_of_lt_of_le (Nat.succ_lt_succ (show (j : ℕ) < k from hjk)) (Nat.succ_le_of_lt k.is_lt))

/-- Helper for Chap14 Lemma 14 31 7: in the lower region below the missing face, the horn-face
composites already satisfy the standard codimension-two simplex identity before evaluation in the
target simplicial group. -/
private lemma hornLowerFaceCompositeEq {n : ℕ} {i : Fin (n + 3)} {j k : Fin (n + 2)}
    (hkj : k < j) (hji : j.castSucc < i) :
    SSet.stdSimplex.δ k ≫ SSet.horn.ι i (i.succAbove j) (Fin.succAbove_ne i j) =
      SSet.stdSimplex.δ ((j.pred (Fin.ne_zero_of_lt hkj)).castSucc) ≫
        SSet.horn.ι i (i.succAbove k) (Fin.succAbove_ne i k) := by
  have hki : k.castSucc < i := lt_trans (Fin.castSucc_lt_castSucc_iff.mpr hkj) hji
  have hkj' : k ≤ (j.pred (Fin.ne_zero_of_lt hkj)).castSucc := by
    exact Fin.le_iff_val_le_val.mpr <|
      by
        simpa [Fin.val_castSucc, Fin.val_pred] using
          Nat.le_pred_of_lt (show (k : ℕ) < j by exact Fin.lt_def.mp hkj)
  have hpredsucc : ((j.pred (Fin.ne_zero_of_lt hkj)).castSucc).succ = j.castSucc := by
    rw [Fin.castSucc_pred_eq_pred_castSucc]
    exact Fin.succ_pred _ _
  -- Compare the two horn composites after forgetting the horn and rewriting in the simplex.
  apply (cancel_mono (Λ[n + 2, i].ι)).1
  rw [Category.assoc, Category.assoc, SSet.horn.ι_ι, SSet.horn.ι_ι]
  simpa [hpredsucc, Fin.succAbove_of_castSucc_lt _ _ hji,
    Fin.succAbove_of_castSucc_lt _ _ hki] using
    (SSet.stdSimplex.δ_comp_δ (i := k) (j := (j.pred (Fin.ne_zero_of_lt hkj)).castSucc) hkj')

/-- Helper for Chap14 Lemma 14 31 7: when one boundary face lies below the missing index and the
other lies above it, the horn composites normalize to the mixed codimension-two simplex identity
before evaluation in the target simplicial group. -/
private lemma hornCrossFaceCompositeEq {n : ℕ} {i : Fin (n + 3)} {j k : Fin (n + 2)}
    (hki : k.castSucc < i) (hij : i ≤ j.castSucc) :
    SSet.stdSimplex.δ k ≫ SSet.horn.ι i (i.succAbove j) (Fin.succAbove_ne i j) =
      SSet.stdSimplex.δ j ≫ SSet.horn.ι i (i.succAbove k) (Fin.succAbove_ne i k) := by
  have hkj : k ≤ j := by
    exact Fin.castSucc_le_castSucc_iff.mp (lt_of_lt_of_le hki hij).le
  -- Once both horn faces are in their lower/upper normal forms, this is the usual `δδ` identity.
  apply (cancel_mono (Λ[n + 2, i].ι)).1
  rw [Category.assoc, Category.assoc, SSet.horn.ι_ι, SSet.horn.ι_ι]
  simpa [Fin.succAbove_of_castSucc_lt _ _ hki, Fin.succAbove_of_le_castSucc _ _ hij] using
    (SSet.stdSimplex.δ_comp_δ (i := k) (j := j) hkj)

/-- Helper for Chap14 Lemma 14 31 7: in the upper region above the missing face, the horn-face
composites normalize to the shifted codimension-two simplex identity before evaluation in the
target simplicial group. -/
private lemma hornUpperFaceCompositeEq {n : ℕ} {i : Fin (n + 3)} {j k : Fin (n + 2)}
    (hjk : j < k) (hij : i ≤ j.castSucc) :
    SSet.stdSimplex.δ k ≫ SSet.horn.ι i (i.succAbove j) (Fin.succAbove_ne i j) =
      SSet.stdSimplex.δ (upperFaceBoundaryIndex hjk) ≫
        SSet.horn.ι i (i.succAbove k) (Fin.succAbove_ne i k) := by
  have hik : i ≤ k.castSucc := le_trans hij
    (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_of_lt hjk))
  -- After pushing both composites back to the standard simplex, the upper branch is exactly
  -- `δ_comp_δ''`.
  apply (cancel_mono (Λ[n + 2, i].ι)).1
  rw [Category.assoc, Category.assoc, SSet.horn.ι_ι, SSet.horn.ι_ι]
  simpa [upperFaceBoundaryIndex, Fin.succAbove_of_le_castSucc _ _ hij,
    Fin.succAbove_of_le_castSucc _ _ hik] using
    (SSet.stdSimplex.δ_comp_δ'' (i := j.succ) (j := k)
      (Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt (show (j : ℕ) < k from hjk)))).symm

/-- Helper for Chap14 Lemma 14 31 7: a single upper correction step also preserves every later
upper face whose codimension-two boundary already matches the prescribed target family. -/
lemma upperFaceCorrectionPreservesUpperFace (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (xj xk : K.obj (op ⦋n + 1⦌))
    (y : K.obj (op ⦋n + 2⦌))
    {j k : Fin (n + 2)} (hjk : j < k)
    (hy : (K.δ k.succ) y = xk)
    (hcompat : (K.δ k) xj = (K.δ (upperFaceBoundaryIndex hjk)) xk) :
    (K.δ k.succ) ((K.σ j) (xj * ((K.δ j.succ) y)⁻¹) * y) = xk := by
  let defect : K.obj (op ⦋n + 1⦌) := xj * ((K.δ j.succ) y)⁻¹
  -- The shifted codimension-two compatibility again makes the defect invisible on the face `k`.
  have hδdef : (K.δ k) defect = 1 := by
    change (K.δ k) (xj * ((K.δ j.succ) y)⁻¹) = 1
    rw [map_mul, map_inv, hcompat]
    have hδδ :
        (K.δ k) ((K.δ j.succ) y) = (K.δ (upperFaceBoundaryIndex hjk)) ((K.δ k.succ) y) := by
      simpa [upperFaceBoundaryIndex] using
        (ConcreteCategory.congr_hom
          (K.δ_comp_δ'' (i := j.succ) (j := k)
            (Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt (show (j : ℕ) < k from hjk)))) y).symm
    rw [hδδ, hy]
    simp
  have hδσ :
      (K.δ k.succ) ((K.σ j) defect) =
        (K.σ (j.castLT (lt_of_lt_of_le (show (j : ℕ) < k from hjk) (Nat.le_of_lt_succ k.is_lt))))
          ((K.δ k) defect) := by
    -- Move the later upper face map past the correction degeneracy using the `δσ` identity for
    -- the strict-inequality case.
    simpa using
      (ConcreteCategory.congr_hom
        (K.δ_comp_σ_of_gt' (i := k.succ) (j := j)
          (show j.succ < k.succ from
            Fin.lt_def.mpr (Nat.succ_lt_succ (show (j : ℕ) < k from hjk))))
        defect)
  -- The preserved later upper face sees only the original simplex once the defect vanishes.
  change (K.δ k.succ) ((K.σ j) defect * y) = xk
  rw [map_mul, hδσ, hδdef, hy]
  simp

/-- Helper for Chap14 Lemma 14 31 7: a compatible `Fin.succAbove`-indexed boundary family in
positive degree admits a simplex whose non-missing faces realize that family. -/
lemma existsHornFillerOfCompatibleFaces (K : SimplicialObject GrpCat.{u}) {n : ℕ}
    (i : Fin (n + 3))
    (x : Fin (n + 2) → K.obj (op ⦋n + 1⦌))
    (hlower :
      ∀ {j k : Fin (n + 2)} (hkj : k < j), j.castSucc < i →
        (K.δ k) (x j) = (K.δ (j.pred (Fin.ne_zero_of_lt hkj)).castSucc) (x k))
    (hcross :
      ∀ {j k : Fin (n + 2)}, k.castSucc < i → i ≤ j.castSucc →
        (K.δ k) (x j) = (K.δ j) (x k))
    (hupper :
      ∀ {j k : Fin (n + 2)} (hjk : j < k), i ≤ j.castSucc →
        (K.δ k) (x j) = (K.δ (upperFaceBoundaryIndex hjk)) (x k)) :
    ∃ y : K.obj (op ⦋n + 2⦌), ∀ j : Fin (n + 2), (K.δ (i.succAbove j)) y = x j := by
  -- First sweep upward through the lower faces below the missing index.
  have lowerSweep :
      ∀ m : ℕ, m ≤ i →
        ∃ y : K.obj (op ⦋n + 2⦌),
          ∀ k : Fin (n + 2), k.1 < m → (K.δ k.castSucc) y = x k := by
    intro m hm
    induction m with
    | zero =>
        refine ⟨1, ?_⟩
        intro k hk
        exact False.elim (Nat.not_lt_zero _ hk)
    | succ m ih =>
        have hm' : m ≤ i := Nat.le_of_succ_le hm
        obtain ⟨y, hy⟩ := ih hm'
        have hjlt : m < n + 2 := by
          exact lt_of_lt_of_le
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm)
            (Nat.le_of_lt_succ i.is_lt)
        let j : Fin (n + 2) := ⟨m, hjlt⟩
        have hji : j.castSucc < i := by
          exact Fin.lt_iff_val_lt_val.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm)
        let y' : K.obj (op ⦋n + 2⦌) := y * (K.σ j) (((K.δ j.castSucc) y)⁻¹ * x j)
        refine ⟨y', ?_⟩
        intro k hk
        by_cases hkj : k < j
        · -- Earlier lower faces are preserved by the lower correction step.
          exact
            lowerFaceCorrectionPreservesFace
              (K := K) (xj := x j) (xk := x k) y hkj
              (hy k (Fin.lt_iff_val_lt_val.mp hkj))
              (hlower hkj hji)
        · have hkeq : k = j := by
            apply Fin.ext
            apply le_antisymm
            · exact Nat.lt_succ_iff.mp hk
            · exact le_of_not_gt (fun hkm ↦ hkj (Fin.lt_iff_val_lt_val.mpr hkm))
          subst hkeq
          -- The new lower face is set exactly by `lowerFaceCorrection`.
          simpa [y'] using lowerFaceCorrection (K := K) (x := x j) y j
  obtain ⟨yLower, hyLowerRange⟩ := lowerSweep i (le_rfl : (i : ℕ) ≤ i)
  have hyLower :
      ∀ k : Fin (n + 2), k.castSucc < i → (K.δ k.castSucc) yLower = x k := by
    intro k hk
    exact hyLowerRange k (Fin.lt_iff_val_lt_val.mp hk)
  -- Then sweep downward through the upper faces above the missing index.
  have upperSweep :
      ∀ m : ℕ, m ≤ n + 2 → i ≤ m →
        ∃ y : K.obj (op ⦋n + 2⦌),
          (∀ k : Fin (n + 2), k.castSucc < i → (K.δ k.castSucc) y = x k) ∧
            (∀ k : Fin (n + 2), m ≤ k.1 → (K.δ k.succ) y = x k) := by
    intro m hm
    induction hm using Nat.decreasingInduction with
    | self =>
        intro him
        refine ⟨yLower, hyLower, ?_⟩
        intro k hk
        exact False.elim (Nat.not_lt_of_ge hk k.is_lt)
    | of_succ m hm IH =>
        intro him
        obtain ⟨y, hyLower', hyUpper⟩ := IH (Nat.le_trans him (Nat.le_succ m))
        let j : Fin (n + 2) := ⟨m, hm⟩
        have hij : i ≤ j.castSucc := by
          exact Fin.le_iff_val_le_val.mpr him
        let y' : K.obj (op ⦋n + 2⦌) := (K.σ j) (x j * ((K.δ j.succ) y)⁻¹) * y
        refine ⟨y', ?_, ?_⟩
        · intro k hki
          have hkj : k < j := by
            exact Fin.lt_iff_val_lt_val.mpr <|
              lt_of_lt_of_le (by simpa using hki) him
          -- Every lower face fixed by the first sweep stays fixed during the reverse upper sweep.
          exact
            upperFaceCorrectionPreservesLowerFace
              (K := K) (xj := x j) (xk := x k) y hkj
              (hyLower' k hki) (hcross hki hij)
        · intro k hk
          by_cases hEq : k = j
          · subst hEq
            -- The current upper face is corrected exactly by `upperFaceCorrection`.
            simpa [y'] using upperFaceCorrection (K := K) (x := x j) y j
          · have hjk : j < k := by
              exact Fin.lt_iff_val_lt_val.mpr <|
                lt_of_le_of_ne hk (by
                  intro hVal
                  apply hEq
                  exact Fin.ext hVal.symm)
            -- Later upper faces stay fixed during the reverse sweep.
            exact
              upperFaceCorrectionPreservesUpperFace
                (K := K) (xj := x j) (xk := x k) y hjk
                (hyUpper k (Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hjk)))
                (hupper hjk hij)
  obtain ⟨y, hyLowerFinal, hyUpperFinal⟩ :=
    upperSweep i (Nat.le_of_lt_succ i.is_lt) (le_rfl : i ≤ i)
  refine ⟨y, ?_⟩
  intro j
  by_cases hji : j.castSucc < i
  · -- Below the missing face, `succAbove` is just `castSucc`.
    simpa [Fin.succAbove_of_castSucc_lt _ _ hji] using hyLowerFinal j hji
  · have hij : i ≤ j.castSucc := le_of_not_gt hji
    -- Above the missing face, `succAbove` is just `succ`.
    simpa [Fin.succAbove_of_le_castSucc _ _ hij] using
      hyUpperFinal j (Fin.le_iff_val_le_val.mp hij)

/-- Helper for Lemma 14.31.7: the underlying simplicial set of a simplicial group is a Kan
complex. This local bridge replaces the broken import dependency while preserving the proof route
through horn filling in the simplicial kernel. -/
theorem simplicialGroup_kanComplex_local (K : SimplicialObject GrpCat.{u}) :
    SSet.KanComplex (K ⋙ forget GrpCat) := by
  -- Route correction: instead of reducing to a missing import, fill each horn directly by
  -- extracting its boundary family, sweeping through the lower faces, then sweeping back through
  -- the upper faces.
  change HomotopicalAlgebra.IsFibrant (K ⋙ forget GrpCat)
  rw [HomotopicalAlgebra.isFibrant_iff, SSet.fibration_iff_has_horn_lifting_property]
  intro n i
  refine ⟨fun {σ₀} {τ} sq ↦ ?_⟩
  cases n with
  | zero =>
      -- TODO: fill the `1`-horn by the degenerate edge on its visible vertex and transport the
      -- face equality through `SSet.yonedaEquiv` in the exact normal form expected by
      -- `SSet.horn.hom_ext`.
      sorry
  | succ n =>
      let x : Fin (n + 2) → K.obj (op ⦋n + 1⦌) := fun j ↦
        SSet.yonedaEquiv (SSet.horn.ι i (i.succAbove j) (Fin.succAbove_ne i j) ≫ σ₀)
      have hlower :
          ∀ {j k : Fin (n + 2)} (hkj : k < j), j.castSucc < i →
            (K.δ k) (x j) = (K.δ (j.pred (Fin.ne_zero_of_lt hkj)).castSucc) (x k) := by
        -- TODO: compose `hornLowerFaceCompositeEq` with `σ₀` and export it through
        -- `SSet.yonedaEquiv` as the lower-branch boundary compatibility needed by
        -- `existsHornFillerOfCompatibleFaces`.
        sorry
      have hcross :
          ∀ {j k : Fin (n + 2)}, k.castSucc < i → i ≤ j.castSucc →
            (K.δ k) (x j) = (K.δ j) (x k) := by
        -- TODO: compose `hornCrossFaceCompositeEq` with `σ₀` and transport it through
        -- `SSet.yonedaEquiv` to obtain the mixed lower/upper compatibility relation.
        sorry
      have hupper :
          ∀ {j k : Fin (n + 2)} (hjk : j < k), i ≤ j.castSucc →
            (K.δ k) (x j) = (K.δ (upperFaceBoundaryIndex hjk)) (x k) := by
        -- TODO: compose `hornUpperFaceCompositeEq` with `σ₀` and transport it through
        -- `SSet.yonedaEquiv` to obtain the upper-branch compatibility relation.
        sorry
      obtain ⟨y, hy⟩ := existsHornFillerOfCompatibleFaces (K := K) i x hlower hcross hupper
      let σ : Δ[n + 2] ⟶ K ⋙ forget GrpCat := SSet.yonedaEquiv.symm y
      refine CommSq.HasLift.mk' ?_
      refine
        { l := σ
          fac_left := ?_
          fac_right := ?_ }
      · -- Compare the two horn maps on each visible face and then apply horn extensionality.
        -- TODO: for each visible face `j ≠ i`, choose `l` with `i.succAbove l = j`, rewrite the
        -- corresponding face of `σ` using `hy l`, and conclude by `SSet.horn.hom_ext`.
        sorry
      · exact Subsingleton.elim _ _

instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := by
  -- Rewrite fibrations as horn lifting problems and follow the textbook kernel-reduction proof.
  rw [SSet.fibration_iff_has_horn_lifting_property]
  intro n i
  refine ⟨fun {α} {τ} sq ↦ ?_⟩
  have hf : ∀ m : SimplexCategoryᵒᵖ, Epi (f.app m) := by
    rw [← NatTrans.epi_iff_epi_app']
    infer_instance
  have hsurj :
      Function.Surjective (f.app (op ⦋n + 1⦌)) :=
    (GrpCat.epi_iff_surjective _).1 (hf (op ⦋n + 1⦌))
  obtain ⟨xLift, hxLift⟩ := hsurj (SSet.yonedaEquiv τ)
  let σx : (Δ[n + 1] : SSet.{u}) ⟶ X ⋙ forget GrpCat := SSet.yonedaEquiv.symm xLift
  have hσx : σx ≫ Functor.whiskerRight f (forget GrpCat) = τ := by
    -- Equality of maps out of `Δ[n+1]` is determined by the represented top simplex.
    dsimp [σx]
    calc
      SSet.yonedaEquiv.symm xLift ≫ Functor.whiskerRight f (forget GrpCat)
          = SSet.yonedaEquiv.symm
              ((Functor.whiskerRight f (forget GrpCat)).app (op ⦋n + 1⦌) xLift) := by
                simpa using
                  (SSet.yonedaEquiv_symm_comp
                    (x := xLift) (f := Functor.whiskerRight f (forget GrpCat)))
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv τ) := by
            change
              SSet.yonedaEquiv.symm ((ConcreteCategory.hom (f.app (op ⦋n + 1⦌))) xLift) =
                SSet.yonedaEquiv.symm (SSet.yonedaEquiv τ)
            rw [hxLift]
      _ = τ := by
            exact SSet.yonedaEquiv.symm_apply_apply τ
  let σcorr : (Λ[n + 1, i] : SSet.{u}) ⟶ X ⋙ forget GrpCat :=
    div_hom α (Λ[n + 1, i].ι ≫ σx)
  have hσcorr :
      σcorr ≫ Functor.whiskerRight f (forget GrpCat) = one_hom Y := by
    -- Replacing the horn by its quotient with the chosen lift reduces the square to the kernel.
    simpa [σcorr] using
      div_hom_comp_whiskerRight_eq_one_hom
        (f := f) (α := α) (τ := τ) (σx := σx) hσx sq.w
  have hσcorr_app :
      ∀ m : SimplexCategoryᵒᵖ, ∀ x : (Λ[n + 1, i] : SSet.{u}).obj m,
        f.app m (σcorr.app m x) = 1 := by
    intro m x
    exact congrFun (congrArg (fun η ↦ η.app m) hσcorr) x
  obtain ⟨σK, hσK⟩ := kernel_underlying_lift_of_one (f := f) σcorr hσcorr_app
  -- Route correction: this is exactly the source reduction to the kernel simplicial group, so
  -- the remaining lifting step is delegated to Lemma 14.31.6 once that prerequisite compiles.
  let _ : SSet.KanComplex ((CategoryTheory.Limits.kernel f) ⋙ forget GrpCat) :=
    simplicialGroup_kanComplex_local (CategoryTheory.Limits.kernel f)
  obtain ⟨τK, hτK⟩ :=
    SSet.KanComplex.hornFilling
      (S := (CategoryTheory.Limits.kernel f) ⋙ forget GrpCat)
      (n := n) (i := i) (σ₀ := σK)
  obtain ⟨hleft, hright⟩ :=
    horn_lift_of_kernel_correction
      (f := f) (α := α) (τ := τ) (σx := σx) hσx (σK := σK) hσK (τK := τK) hτK
  refine CommSq.HasLift.mk' ?_
  refine
    { l := mul_hom
        (τK ≫ Functor.whiskerRight (CategoryTheory.Limits.kernel.ι f) (forget GrpCat))
        σx
      fac_left := hleft
      fac_right := hright }

/-- Helper for Lemma 14.31.7: degreewise surjectivity upgrades a morphism of simplicial groups to
an epimorphism. -/
lemma epi_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) : Epi f := by
  -- The source-facing hypothesis is converted degreewise using the canonical `GrpCat` owner
  -- criterion, then assembled back into an epi natural transformation.
  rw [NatTrans.epi_iff_epi_app']
  intro n
  exact (GrpCat.epi_iff_surjective (f.app n)).2 (hsurj n)

/-- Lemma 14.31.7: a termwise surjective morphism of simplicial groups induces a Kan fibration on
the underlying simplicial sets. -/
@[stacks 08P0]
theorem simplicialGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := by
  -- The proof follows the source reduction: first turn termwise surjectivity into an epi, then
  -- invoke the canonical owner instance for epimorphisms of simplicial groups.
  letI : Epi f := epi_of_termwise_surjective (f := f) hsurj
  infer_instance

end

section

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/-- Specialization of Lemma 14.31.7 to simplicial abelian groups. -/
theorem simplicialAbelianGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  let g :=
    Functor.whiskerRight
      (Functor.whiskerRight f AddCommGrpCat.toCommGrp)
      (forget₂ CommGrpCat GrpCat)
  have hsurj' :
      ∀ n : SimplexCategoryᵒᵖ,
        Function.Surjective (g.app n) := by
    simpa [g] using hsurj
  simpa [g] using simplicialGroup_fibration_of_termwise_surjective g hsurj'

instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  have hf : ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n) := by
    rw [← NatTrans.epi_iff_epi_app']
    infer_instance
  apply simplicialAbelianGroup_fibration_of_termwise_surjective f
  intro n
  exact (AddCommGrpCat.epi_iff_surjective (f.app n)).1 (hf n)

end

end
