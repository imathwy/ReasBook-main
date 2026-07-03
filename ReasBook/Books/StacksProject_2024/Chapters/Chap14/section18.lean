import Mathlib
import Mathlib.AlgebraicTopology.SimplicialObject.Op
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_18_1 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory SimplexCategory.Truncated
open SimplexCategory.Truncated.Hom
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SimplicialObject.Truncated

open SimplicialObject.Splitting (IndexSet)

/-
Domain-style sampling for Definition 14.18.1:
- primary domain: split simplicial objects and their truncated degreewise coproduct decompositions
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.summand`,
  `SimplicialObject.Splitting.cofan'`,
  `SimplicialObject.Splitting.cofan`
- best owner abstraction: the source-facing owner
  `SimplicialObject.Truncated.Splitting X`, mirroring the established mathlib owner
  `SimplicialObject.Splitting X`
- primitive data: the chosen degreewise summands `N`, their inclusions `ι`, and the colimit
  witness `isColimit'`
- derived API: the canonical cofan `s.cofan Δ` and its colimit witness `s.isColimit Δ`
- source/core/bridge triage: this file is `source-facing`; the ordinary simplicial-object owner is
  the `core/canonical` model for statement shape, while the repeated arithmetic turning a surjection
  index into a truncated degree is only implementation bookkeeping and should stay internal
-/

namespace Splitting

private abbrev summandBound {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : A.1.unop.len ≤ n :=
  (len_le_of_epi A.e).trans Δ.unop.property

private def summandDegree {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : Fin (n + 1) :=
  ⟨A.1.unop.len, Nat.lt_succ_of_le (summandBound A)⟩

private abbrev summandMap {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet (op Δ.unop.obj)) : Δ.unop ⟶ ⦋A.1.unop.len, summandBound A⦌ₙ :=
  tr A.e Δ.unop.property (summandBound A)

/-- For a truncated simplicial object, the summand indexed by a surjection onto `Δ` is the object
in the truncated degree of the codomain simplex. -/
@[simp, nolint unusedArguments]
def summand {n : ℕ} (N : Fin (n + 1) → C) (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (A : IndexSet (op Δ.unop.obj)) : C :=
  N (summandDegree A)

/-- The canonical cofan attached to splitting data on a truncated simplicial object. -/
def cofan' {n : ℕ} (N : Fin (n + 1) → C) (X : SimplicialObject.Truncated C n)
    (ι : ∀ m, N m ⟶ X _⦋m⦌ₙ)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦
    ι (summandDegree A) ≫ X.map (summandMap A).op

end Splitting

/-- Definition 14.18.1: a splitting of an `n`-truncated simplicial object consists of chosen
nondegenerate summands in degrees `0` through `n` whose canonical coproduct cofan indexed by
surjections onto each degree is colimiting; for ordinary simplicial objects the corresponding
notion is `SimplicialObject.Splitting`. -/
structure Splitting {n : ℕ} (X : SimplicialObject.Truncated C n) where
  /-- The nondegenerate summand in each truncated degree. -/
  N : Fin (n + 1) → C
  /-- The inclusion of the nondegenerate summand into the corresponding degree. -/
  ι : ∀ m, N m ⟶ X _⦋m⦌ₙ
  /-- Each truncated degree is the coproduct of the chosen nondegenerate summands indexed by
  surjections onto that degree. -/
  isColimit' : ∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ, IsColimit (Splitting.cofan' N X ι Δ)

/-- The canonical cofan associated to a truncated splitting. -/
def Splitting.cofan {n : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (Splitting.summand s.N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦
    s.ι (summandDegree A) ≫ X.map (summandMap A).op

/-- The canonical cofan of a truncated splitting is colimiting. -/
def Splitting.isColimit {n : ℕ} {X : SimplicialObject.Truncated C n}
    (s : Splitting X) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) : IsColimit (s.cofan Δ) :=
  s.isColimit' Δ

end SimplicialObject.Truncated

end CategoryTheory

/-! ### Lemma_14_18_2 (from Chap14) -/
open CategoryTheory Opposite
open SimplicialObject
open SimplicialObject.Splitting
open scoped Simplicial

universe u

noncomputable section

namespace SSet

/- Domain-style sampling for 14.18.2:
- primary domain: simplicial-set splittings by nondegenerate simplices
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.cofan`,
  `SimplicialObject.Split.mk'`,
  `SSet.nonDegenerate`,
  `SSet.exists_nonDegenerate`
- best owner abstraction: `SimplicialObject.Splitting U`
- primitive data: the degreewise family `U.nonDegenerate`, the inclusions `Subtype.val`, and the
  colimit witness `s.isColimit'`
- derived API: the source-facing existence theorem `split_by_nondegenerate_simplices`
- source/core/bridge triage: the source lemma is `source-facing`, but its operational owner is the
  canonical `core/canonical` object `SimplicialObject.Splitting U`; this file therefore keeps the
  canonical owner construction and derives the source-facing existence statement directly from it.
-/

private def nonDegenerateSplittingIsColimit (U : SSet.{u}) (Δ : SimplexCategoryᵒᵖ) :
    Limits.IsColimit
      (Splitting.cofan' (fun n ↦ ↥(U.nonDegenerate n)) U
        (fun n ↦ (Subtype.val : U.nonDegenerate n → U _⦋n⦌)) Δ) := by
  let N : ℕ → Type u := fun n ↦ ↥(U.nonDegenerate n)
  let ι : ∀ n, N n → U _⦋n⦌ := fun n ↦ (Subtype.val : U.nonDegenerate n → U _⦋n⦌)
  obtain ⟨Δ⟩ := Δ
  induction Δ using SimplexCategory.rec with
  | _ n =>
      let c : Limits.Cofan (summand N (op ⦋n⦌)) :=
        Splitting.cofan' N U ι (op ⦋n⦌)
      have hc : c.cofanTypes.IsColimit := by
        refine Limits.CofanTypes.isColimit_mk c.cofanTypes ?_ ?_ ?_
        · intro x
          obtain ⟨m, f, _, y, hy⟩ := U.exists_nonDegenerate x
          refine ⟨IndexSet.mk f, y, ?_⟩
          simpa [c, Splitting.cofan', Splitting.IndexSet.mk] using hy.symm
        · intro A y₁ y₂ h
          change U.nonDegenerate A.1.unop.len at y₁ y₂
          let x : U _⦋n⦌ := U.map A.e.op y₁.1
          have hy₁ : x = U.map A.e.op y₁ := rfl
          have hy₂ : x = U.map A.e.op y₂ := by
            simpa [x, c, Splitting.cofan'] using h
          exact U.unique_nonDegenerate_simplex x A.e y₁ hy₁ A.e y₂ hy₂
        · rintro ⟨Δ₁, ⟨f₁, _⟩⟩ ⟨Δ₂, ⟨f₂, _⟩⟩ y z h
          change U.nonDegenerate Δ₁.unop.len at y
          change U.nonDegenerate Δ₂.unop.len at z
          let x : U _⦋n⦌ := U.map f₁.op y.1
          have hy : x = U.map f₁.op y := rfl
          have hz : x = U.map f₂.op z := by
            simpa [x, c, Splitting.cofan'] using h
          have hlen : Δ₁.unop.len = Δ₂.unop.len :=
            U.unique_nonDegenerate_dim x f₁ y hy f₂ z hz
          have hΔ : Δ₁ = Δ₂ := by
            exact Opposite.unop_injective (by ext; exact hlen)
          subst hΔ
          have hf : f₁ = f₂ :=
            U.unique_nonDegenerate_map x f₁ y hy f₂ z hz
          simp [hf]
      exact ((Limits.Cofan.isColimit_cofanTypes_iff c).1 hc).some

variable (U : SSet.{u})

-- Proof sketch: in degree `n`, take the distinguished summand to be the type of nondegenerate
-- `n`-simplices, included by the subtype map. The colimit proof is the canonical decomposition of
-- simplices by their unique nondegenerate presentation.
/-- The canonical splitting of a simplicial set whose degree-`n` distinguished summand is the type
of nondegenerate `n`-simplices. -/
abbrev nonDegenerateSplitting : Splitting U where
  N := fun n ↦ ↥(U.nonDegenerate n)
  ι n := (Subtype.val : U.nonDegenerate n → U _⦋n⦌)
  isColimit' := nonDegenerateSplittingIsColimit U

end SSet

namespace SSet

variable (U : SSet.{u})

-- Proof sketch: use the canonical owner `U.nonDegenerateSplitting`; in degree `n`, its
-- distinguished inclusion is `Subtype.val : U.nonDegenerate n → U _⦋n⦌`, whose range is exactly
-- `U.nonDegenerate n`.
/-- Lemma 14.18.2: every simplicial set admits a splitting whose degree-`n` distinguished summand
is exactly the set of nondegenerate `n`-simplices. -/
theorem split_by_nondegenerate_simplices :
    ∃ s : Splitting U, ∀ n : ℕ, Set.range (s.ι n) = U.nonDegenerate n := by
  refine ⟨U.nonDegenerateSplitting, ?_⟩
  intro n
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end SSet

/-! ### Lemma_14_18_3 (from Chap14) -/
open CategoryTheory Opposite
open SimplicialObject
open SimplicialObject.Splitting
open scoped Simplicial

universe u

noncomputable section

namespace SSet

variable {U V : SSet.{u}} (f : U ⟶ V)

/- Domain-style sampling for 14.18.3:
- primary domain: simplicial-set morphisms acting on nondegenerate simplices
- sampled owner API:
  `SimplicialObject.Splitting`,
  `SimplicialObject.Splitting.φ`,
  `SimplicialObject.Split.mk'`,
  `SimplicialObject.Split.Hom`,
  `SSet.nonDegenerateSplitting`
- best owner abstraction: the split simplicial sets `Split.mk' U.nonDegenerateSplitting` and
  `Split.mk' V.nonDegenerateSplitting`, together with the canonical bridge
  `toNonDegenerateSplitHom f hPreserves`
- primitive data: the canonical splittings, the underlying simplicial-set morphism `f`, and the
  proof that `f` sends nondegenerate simplices to nondegenerate simplices
- derived API: the induced degreewise maps on nondegenerate simplices
  `(toNonDegenerateSplitHom f hPreserves).f n`
- source/core/bridge triage: the degreewise injective, surjective, and bijective consequences are
  the `source-facing` statements; the induced maps on nondegenerate summands are only a
  `bridge/view`, so the public statements should use the canonical split-owner bridge rather than
  a parallel local wrapper
-/

section

variable
  (hPreserves :
    ∀ ⦃n : ℕ⦄ (x : U.nonDegenerate n),
      (U.nonDegenerateSplitting.φ f n) x ∈ V.nonDegenerate n)

/-- The canonical morphism between the split simplicial sets attached to the nondegenerate
splittings of `U` and `V`, induced by a simplicial-set morphism that preserves nondegenerate
simplices. -/
abbrev toNonDegenerateSplitHom :
    Split.mk' U.nonDegenerateSplitting ⟶ Split.mk' V.nonDegenerateSplitting where
  F := f
  f := fun n x ↦ ⟨U.nonDegenerateSplitting.φ f n x, hPreserves x⟩
  comm := fun _ ↦ rfl

-- Proof sketch: apply the canonical splittings `U.nonDegenerateSplitting` and
-- `V.nonDegenerateSplitting` by nondegenerate simplices. Hypothesis `hPreserves` makes the
-- canonical split morphism `toNonDegenerateSplitHom f hPreserves` land in the distinguished
-- nondegenerate summands of `V`, and injectivity on those summands implies injectivity on each
-- coproduct component, hence on every degree map `f.app (op ⦋n⦌)`.
/-- Lemma 14.18.3: if a morphism of simplicial sets sends nondegenerate simplices to
nondegenerate simplices and the induced map on nondegenerate simplices is injective, then each
degree map `f_n` is injective. -/
theorem degreewise_injective_of_nondegenerate_injective
    (hInjective :
      ∀ n : ℕ, Function.Injective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Injective (f.app (op ⦋n⦌)) := sorry

-- Proof sketch: use the same splitting argument as in the injective case. Surjectivity of the map
-- on nondegenerate summands implies surjectivity on each coproduct decomposition coming from
-- `U.nonDegenerateSplitting` and `V.nonDegenerateSplitting`, so every degree map of `f` is
-- surjective.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is surjective on the
nondegenerate simplices, then it is surjective in every degree. -/
theorem degreewise_surjective_of_nondegenerate_surjective
    (hSurjective :
      ∀ n : ℕ, Function.Surjective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)) := sorry

-- Proof sketch: combine the injective and surjective arguments for the induced map on the
-- nondegenerate summands. The canonical splitting decompositions then yield bijectivity of each
-- degree map.
/-- If a simplicial-set morphism preserves nondegenerate simplices and is bijective on the
nondegenerate simplices, then it is bijective in every degree. -/
theorem degreewise_bijective_of_nondegenerate_bijective
    (hBijective :
      ∀ n : ℕ, Function.Bijective ((toNonDegenerateSplitHom f hPreserves).f n)) :
    ∀ n : ℕ, Function.Bijective (f.app (op ⦋n⦌)) := sorry

end

end SSet

/-! ### Lemma_14_18_4 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

universe u

/- Domain-style sampling for Lemma 14.18.4:
- primary domain: simplicial-set skeletons, degenerate simplices, and the canonical
  dimension-`< n` owner predicate
- sampled owner API:
  `SSet.skeleton`,
  `SSet.mem_skeleton`,
  `SSet.skeleton_obj_eq_top`,
  `SSet.HasDimensionLT`,
  `SSet.mem_degenerate_iff`,
  `SSet.Subcomplex.mem_degenerate_iff`
- source/core/bridge triage:
  `source-facing`: the textbook degreewise description of the simplicial subset generated by
    simplices in degrees at most `n`;
  `core/canonical`: the owner subcomplex `U.skeleton n` together with the owner property
    `((U.skeleton n : SSet)).HasDimensionLT n`;
  `bridge/view`: the explicit range-based degreewise description of that skeleton and the
    higher-degree pointwise degeneracy corollary;
- owner abstraction: `SSet.skeleton`
- primitive data: only the canonical owner data `U.skeleton n`
- derived API: the range description, the induced `HasDimensionLT` instance, and the higher-degree
  pointwise degeneracy consequence
- layer target: the first and third theorems are `bridge/view`, while the dimension statement is
  `core/canonical`.
-/

-- Proof sketch: `U.skeleton (n + 1)` is the canonical subcomplex generated by nondegenerate
-- simplices in dimensions at most `n`. Unwinding `Subcomplex.ofSimplex` and the existence of a
-- nondegenerate presentation for every simplex identifies its degree-`m` part with the union of
-- the images of the restriction maps from degrees `i ≤ n`.
/-- Lemma 14.18.4: in degree `m`, the `(n + 1)`-skeleton of a simplicial set `U` consists exactly
of those simplices coming from some degree `i ≤ n` simplex along a map `[m] ⟶ [i]`. This is the
sub simplicial set defined by the textbook rule `U'_m = ⋃_{φ : [m] ⟶ [i], i ≤ n} Im(U(φ))`. -/
theorem skeleton_succ_obj_eq_generated_by_simplices_le
    (U : SSet.{u}) (n m : ℕ) :
    (U.skeleton (n + 1)).obj (op ⦋m⦌) =
      { x : U _⦋m⦌ | ∃ i ≤ n, ∃ φ : ⦋m⦌ ⟶ ⦋i⦌, x ∈ Set.range (U.map φ.op) } := by
  ext x
  constructor
  · intro hx
    simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    rcases hx with ⟨⟨i, hi⟩, y, hy⟩
    rcases (SSet.Subcomplex.mem_ofSimplex_obj_iff y.1 x).1 hy with ⟨φ, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ hi, φ, ⟨y.1, rfl⟩⟩
  · rintro ⟨i, hi, φ, ⟨y, rfl⟩⟩
    exact (U.skeleton (n + 1)).map φ.op (U.mem_skeleton y (Nat.lt_succ_of_le hi))

-- Proof sketch: `U.skeleton n` is the supremum of the simplex subcomplexes
-- `Subcomplex.ofSimplex x.1` over nondegenerate simplices `x` in dimensions `i < n`. The generic
-- owner lemma `SSet.hasDimensionLT_iSup_iff` reduces the claim to those generators. Each
-- `Subcomplex.ofSimplex x.1` is the range of the canonical map `Δ[i] ⟶ U`, and `Δ[i]` has
-- dimension `≤ i`, hence dimension `< n` because `i < n`.
instance skeleton_hasDimensionLT (U : SSet.{u}) (n : ℕ) :
    ((U.skeleton n : SSet)).HasDimensionLT n := by
  simp only [SSet.skeleton, OrderHom.coe_mk, SSet.hasDimensionLT_iSup_iff]
  intro i x
  obtain ⟨f, hf⟩ := SSet.yonedaEquiv.surjective x.1
  rw [← hf]
  rw [← SSet.Subcomplex.range_eq_ofSimplex f]
  let _ : (Δ[i] : SSet).HasDimensionLT n :=
    (Δ[i] : SSet).hasDimensionLT_of_le (i + 1) n (Nat.succ_le_of_lt i.2)
  infer_instance

/-- Every simplex of the `(n + 1)`-skeleton simplicial set in degree strictly larger than `n` is
degenerate. -/
theorem skeleton_succ_mem_degenerate_of_lt
    (U : SSet.{u}) {n m : ℕ} (h : n < m)
    (x : (U.skeleton (n + 1) : SSet) _⦋m⦌) :
    x ∈ ((U.skeleton (n + 1) : SSet).degenerate m) := by
  rw [((U.skeleton (n + 1) : SSet).degenerate_eq_top_of_hasDimensionLT (n + 1) m
    (Nat.succ_le_of_lt h))]
  exact Set.mem_univ x

/-! ### Lemma_14_18_5 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

noncomputable section

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.18.5:
- primary domain: split simplicial objects in simplicial abelian groups
- sampled owner API:
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`,
  `Abelian.DoldKan.equivalence.unitIso`,
  `SimplicialObject.Splitting`,
  `SimplicialObject.Split`,
  `NormalizedMooreComplex.objX`,
  `NormalizedMooreComplex.objX_zero`,
  `NormalizedMooreComplex.objX_add_one`
- best owner abstraction: the normalized Moore subobject
  `NormalizedMooreComplex.objX U n` together with the canonical functor
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- primitive data: `NormalizedMooreComplex.objX U n` and the canonical split owner
  `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- derived API: the successor-degree kernel-intersection formula, the forgetful comparison
  with the Dold-Kan unit isomorphism, and the degreewise identification coming from the
  definition of `Γ₀'`
- source/core/bridge triage: this file is `bridge/view`; Lemma 14.18.5 is the
  `AddCommGrpCat` specialization of the generic owner declarations in Lemma 14.18.6, so the
  correct refinement is direct specialized reuse of those declarations rather than a parallel
  specialized API.
-/

/- Companion check: simplicial abelian groups inherit the canonical normalized-Moore split
functor from the generic abelian-category owner in Lemma 14.18.6. -/
#check (N ⋙ DoldKan.Γ₀' :
  SimplicialObject AddCommGrpCat ⥤ SimplicialObject.Split AddCommGrpCat)

/- Companion recall: forgetting the canonical normalized-Moore split functor gives back the
underlying simplicial abelian group. -/
#check
  (((Functor.associator N DoldKan.Γ₀' (SimplicialObject.Split.forget AddCommGrpCat)).symm ≪≫
      (equivalence).unitIso.symm) :
    (N ⋙ DoldKan.Γ₀' : SimplicialObject AddCommGrpCat ⥤ SimplicialObject.Split AddCommGrpCat) ⋙
        SimplicialObject.Split.forget AddCommGrpCat ≅
      𝟭 (SimplicialObject AddCommGrpCat))

/- Companion recall: the degree-`n` nondegenerate term of the canonical split object is the
normalized Moore subobject. -/
#check
  (fun (U : SimplicialObject AddCommGrpCat) (n : ℕ) ↦
    (rfl :
      ((N ⋙ DoldKan.Γ₀').obj U).s.N n = (NormalizedMooreComplex.objX U n : AddCommGrpCat)))

/- Companion recall: for a simplicial abelian group, the normalized Moore subobject is the generic
abelian-category owner specialized to `AddCommGrpCat`. -/
recall NormalizedMooreComplex.objX

#check
  (NormalizedMooreComplex.objX :
    ∀ U : SimplicialObject AddCommGrpCat, ∀ n : ℕ, Subobject (U.obj (op ⦋n⦌)))

/- Companion recall: in degree `0`, the normalized Moore subobject is all of `U₀`. -/
recall NormalizedMooreComplex.objX_zero

#check
  (NormalizedMooreComplex.objX_zero :
    ∀ U : SimplicialObject AddCommGrpCat, NormalizedMooreComplex.objX U 0 = ⊤)

/- Companion recall: in positive degree, the normalized Moore subobject is the intersection of the
kernels of the face maps `d₁, \dotsc, d_{n+1}`. -/
recall NormalizedMooreComplex.objX_add_one

#check
  (NormalizedMooreComplex.objX_add_one :
    ∀ U : SimplicialObject AddCommGrpCat, ∀ n : ℕ,
      NormalizedMooreComplex.objX U (n + 1) =
        Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ k.succ)))

/- Lemma 14.18.5: simplicial abelian groups admit the functorial normalized-Moore splitting.
In the generic abelian-category owner file, this content is already exposed directly by the
canonical split functor `N ⋙ DoldKan.Γ₀'`, the Dold-Kan unit isomorphism rewritten through
`Γ₀' ⋙ SimplicialObject.Split.forget`, and the definitional identification of the nondegenerate
degree-`n` term with `NormalizedMooreComplex.objX U n`. -/

end CategoryTheory

/-! ### Lemma_14_18_6 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

universe v u

noncomputable section

namespace CategoryTheory

open _root_.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.18.6:
- primary domain: split simplicial objects and the Dold-Kan equivalence in abelian categories
- sampled owner API:
  `DoldKan.Γ₀'`,
  `SimplicialObject.Split.forget`,
  `Abelian.DoldKan.equivalence`,
  `NormalizedMooreComplex.objX`,
  `SimplicialObject.opFunctor`
- best owner abstraction: the canonical split functor `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`
- primitive data: that split functor together with the canonical normalized-Moore owner
  `NormalizedMooreComplex.objX`
- derived API: the forgetful comparison with `𝟭 (SimplicialObject A)` and the identification of
  its nondegenerate terms with `NormalizedMooreComplex.objX`; the lower-face convention
  `d₀, …, d_{n-1}` is a bridge/view obtained by applying `NormalizedMooreComplex.objX` to
  `SimplicialObject.opFunctor.obj U`
- source/core/bridge triage: the textbook lemma is `source-facing`, but its canonical owner is the
  split functor `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`; the forgetful isomorphism, the degreewise
  identification, and the lower-face kernel-intersection description are the relevant
  `bridge/view` consequences, so no extra existential wrapper should remain public.
-/

/- Lemma 14.18.6: the canonical functorial splitting of simplicial objects in an abelian category
is the Dold-Kan composite `Abelian.DoldKan.N ⋙ DoldKan.Γ₀'`. -/
#check (N ⋙ DoldKan.Γ₀' : SimplicialObject A ⥤ SimplicialObject.Split A)

namespace SimplicialObject

/-- The intersection of the kernels of the lower face maps in degree `n`. This is the normalized
Moore subobject of the simplicial object obtained from `U` by reversing the simplex indexing. -/
abbrev lowerFaceKernelSubobject (U : SimplicialObject A) (n : ℕ) :
    Subobject (U.obj (op ⦋n⦌)) :=
  NormalizedMooreComplex.objX (opFunctor.obj U) n

@[simp] theorem lowerFaceKernelSubobject_zero (U : SimplicialObject A) :
    U.lowerFaceKernelSubobject 0 = ⊤ :=
  rfl

@[simp] theorem lowerFaceKernelSubobject_add_one (U : SimplicialObject A) (n : ℕ) :
    U.lowerFaceKernelSubobject (n + 1) =
      Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ (Fin.castSucc k))) := by
  change NormalizedMooreComplex.objX (opFunctor.obj U) (n + 1) = _
  rw [NormalizedMooreComplex.objX_add_one]
  let g : Fin (n + 1) → Subobject (U.obj (op ⦋n + 1⦌)) :=
    fun k ↦ kernelSubobject (U.δ (Fin.castSucc k))
  let e : Fin (n + 1) ≃ Fin (n + 1) :=
    { toFun := Fin.rev
      invFun := Fin.rev
      left_inv := Fin.rev_rev
      right_inv := Fin.rev_rev }
  calc
    Finset.univ.inf
      (fun k : Fin (n + 1) ↦
        kernelSubobject ((opFunctor.obj U).δ k.succ))
      = Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ k.rev.castSucc)) := by
          refine congrArg
            (fun f : Fin (n + 1) → Subobject (U.obj (op ⦋n + 1⦌)) ↦ Finset.univ.inf f) ?_
          funext k
          rw [opFunctor_obj_δ, Fin.rev_succ]
          congr 1
          change
            𝟙 (U.obj (op ⦋n + 1⦌)) ≫ U.δ k.rev.castSucc ≫ 𝟙 (U.obj (op ⦋n⦌)) =
              U.δ k.rev.castSucc
          simp
    _ = (Finset.image (fun k : Fin (n + 1) ↦ k.rev) Finset.univ).inf g := by
          symm
          exact Finset.inf_image Finset.univ (fun k : Fin (n + 1) ↦ k.rev) g
    _ = Finset.univ.inf g := by
          simpa [g, e] using
            congrArg (fun s : Finset (Fin (n + 1)) ↦ s.inf g) (Finset.image_univ_equiv e)
    _ = Finset.univ.inf (fun k : Fin (n + 1) ↦ kernelSubobject (U.δ (Fin.castSucc k))) := by
          rfl

end SimplicialObject

/- Forgetting the canonical normalized-Moore splitting recovers the original simplicial object.
This is the Dold-Kan unit isomorphism rewritten through the split owner `Γ₀'`. -/
#check
  ((Functor.associator N DoldKan.Γ₀' (SimplicialObject.Split.forget A)).symm ≪≫
    (equivalence).unitIso.symm :
      (N ⋙ DoldKan.Γ₀') ⋙ SimplicialObject.Split.forget A ≅ 𝟭 (SimplicialObject A))

/- The nondegenerate degree-`n` term of the canonical normalized-Moore splitting is, by
definition, the normalized Moore subobject `NormalizedMooreComplex.objX U n`. -/
#check
  (fun (U : SimplicialObject A) (n : ℕ) ↦
    (rfl :
      ((N ⋙ DoldKan.Γ₀').obj U).s.N n = (NormalizedMooreComplex.objX U n : A)))

end CategoryTheory

/-! ### Lemma_14_18_7 (from Chap14) -/
open CategoryTheory Opposite AlgebraicTopology
open Abelian.DoldKan
open scoped Simplicial

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} (f : U ⟶ V)

/- Domain-style sampling for Lemma 14.18.7:
- primary domain: simplicial objects in an abelian category and the Dold-Kan normalized Moore
  complex functor
- sampled owner API:
  `N`,
  `equivalence`,
  `HomologicalComplex.mono_of_mono_f`,
  `HomologicalComplex.epi_of_epi_f`,
  `HomologicalComplex.Hom.isIso_of_components`
- best owner abstraction: the canonical functor `N : SimplicialObject A ⥤
  ChainComplex A ℕ`
- primitive data: the simplicial morphism `f` and the degree maps of `(N.map f)`
- derived API: global mono/epi/isIso detection for chain maps and objectwise detection for
  simplicial morphisms
- source/core/bridge triage: these lemmas are `source-facing` transfer statements; the owner
  `Abelian.DoldKan.N` is `core/canonical`; the Dold-Kan equivalence and the componentwise
  detection lemmas in `ChainComplex` and functor categories form the `bridge/view` layer used in
  the proofs.
-/

-- Proof sketch: componentwise monomorphisms make `N.map f` a monomorphism of chain complexes via
-- `HomologicalComplex.mono_of_mono_f`. The faithful Dold-Kan functor `N` reflects monos, so `f`
-- is mono; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are monomorphisms, then the
underlying simplicial morphism `f` is a monomorphism. -/
theorem mono_of_normalizedMooreComplex_degreewise_mono
    (h :
      ∀ i : ℕ, Mono ((N.map f).f i)) :
    Mono f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : Functor.Faithful F := by
    simpa [F, equivalence_functor] using
      (inferInstance : Functor.Faithful ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor))
  exact F.mono_of_mono_map <| by
    simpa [F] using (HomologicalComplex.mono_of_mono_f (N.map f) h)

/-- Lemma 14.18.7 (1): if the degree maps of the normalized Moore complex morphism `N(f)` are
monomorphisms, then every simplicial degree map `f_i` is a monomorphism. -/
theorem degreewise_mono_of_normalizedMooreComplex_degreewise_mono
    (h :
      ∀ i : ℕ, Mono ((N.map f).f i)) :
    ∀ i : ℕ, Mono (f.app (op ⦋i⦌)) := by
  let _ : Mono f := mono_of_normalizedMooreComplex_degreewise_mono f h
  exact fun _ ↦ inferInstance

-- Proof sketch: componentwise epimorphisms make `N.map f` an epimorphism of chain complexes via
-- `HomologicalComplex.epi_of_epi_f`. The faithful Dold-Kan functor `N` reflects epis, so `f` is
-- epi; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are epimorphisms, then the
underlying simplicial morphism `f` is an epimorphism. -/
theorem epi_of_normalizedMooreComplex_degreewise_epi
    (h :
      ∀ i : ℕ, Epi ((N.map f).f i)) :
    Epi f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : Functor.Faithful F := by
    simpa [F, equivalence_functor] using
      (inferInstance : Functor.Faithful ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor))
  exact F.epi_of_epi_map <| by
    simpa [F] using (HomologicalComplex.epi_of_epi_f (N.map f) h)

/-- If the degree maps of the normalized Moore complex morphism `N(f)` are epimorphisms, then
every simplicial degree map `f_i` is an epimorphism. -/
theorem degreewise_epi_of_normalizedMooreComplex_degreewise_epi
    (h :
      ∀ i : ℕ, Epi ((N.map f).f i)) :
    ∀ i : ℕ, Epi (f.app (op ⦋i⦌)) := by
  let _ : Epi f := epi_of_normalizedMooreComplex_degreewise_epi f h
  exact fun _ ↦ inferInstance

-- Proof sketch: componentwise isomorphisms make `N.map f` an isomorphism of chain complexes via
-- `HomologicalComplex.Hom.isIso_of_components`. The Dold-Kan functor `N` reflects isomorphisms,
-- so `f` is an isomorphism; evaluate objectwise in the simplicial functor category.
/-- If the degree maps of the normalized Moore complex morphism `N(f)` are isomorphisms, then the
underlying simplicial morphism `f` is an isomorphism. -/
theorem isIso_of_normalizedMooreComplex_degreewise_isIso
    (h :
      ∀ i : ℕ, IsIso ((N.map f).f i)) :
    IsIso f := by
  let F : SimplicialObject A ⥤ ChainComplex A ℕ := N
  haveI : F.ReflectsIsomorphisms := by
    simpa [F, equivalence_functor] using
      (inferInstance :
        ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsIsomorphisms)
  let _ : ∀ i : ℕ, IsIso ((N.map f).f i) := h
  have hF : IsIso (F.map f) := by
    simpa [F] using (HomologicalComplex.Hom.isIso_of_components (N.map f))
  exact isIso_of_reflects_iso f F

/-- If the degree maps of the normalized Moore complex morphism `N(f)` are isomorphisms, then
every simplicial degree map `f_i` is an isomorphism. -/
theorem degreewise_isIso_of_normalizedMooreComplex_degreewise_isIso
    (h :
      ∀ i : ℕ, IsIso ((N.map f).f i)) :
    ∀ i : ℕ, IsIso (f.app (op ⦋i⦌)) := by
  let _ : IsIso f := isIso_of_normalizedMooreComplex_degreewise_isIso f h
  exact fun _ ↦ inferInstance

end CategoryTheory

/-! ### Lemma_14_18_8 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe v u

noncomputable section

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.18.8:
- primary domain: simplicial objects in an abelian category, subobjects cut out by face-map
  kernels, and the simplicial identities relating adjacent face maps;
- sampled owner API:
  `NormalizedMooreComplex.objX`,
  `SimplicialObject.lowerFaceKernelSubobject`,
  `SimplicialObject.lowerFaceKernelSubobject_add_one`,
  `SimplicialObject.opFunctor`,
  `SimplicialObject.δ_comp_δ`,
  `Limits.pullback_factors_iff`;
- best owner abstraction: the core/canonical kernel-intersection owner in this domain is
  `NormalizedMooreComplex.objX`; the source-facing lower-face convention is already exposed
  upstream as the bridge/view owner `SimplicialObject.lowerFaceKernelSubobject`, defined from
  `NormalizedMooreComplex.objX` via `SimplicialObject.opFunctor`;
- source/core/bridge triage:
  `source-facing`: the stability of the lower-face kernel intersection under the last face map;
  `core/canonical`: `NormalizedMooreComplex.objX`;
  `bridge/view`: the owner `SimplicialObject.lowerFaceKernelSubobject` from
  [Lemma_14_18_6](/volume/math/AI4M/users/zcwang/StacksProject_2024/StacksProject_2024/Items/Chap14/Lemma_14_18_6.lean),
  which packages the lower-face convention as the reversed-simplex view of the normalized Moore
  subobject. -/

-- Proof sketch: for `m = 0` the target lower-face kernel intersection is `⊤`. For `m + 1`, the
-- degree-`m + 1` lower-face kernel intersection is the finite infimum of the kernel subobjects of
-- `U.δ (Fin.castSucc k)`. To show the last face factors through that infimum, it suffices to show
-- it factors through each kernel. For a fixed `k`, the simplicial identity rewrites
-- `U.δ (Fin.last (m + 2)) ≫ U.δ (Fin.castSucc k)` as
-- `U.δ (Fin.castSucc (Fin.castSucc k)) ≫ U.δ (Fin.last (m + 1))`, and the source arrow already
-- factors through the kernel of `U.δ (Fin.castSucc (Fin.castSucc k))`.
namespace SimplicialObject

/-- Lemma 14.18.8: the last face map sends the intersection of the kernels of the lower faces in
degree `m + 1` into the corresponding intersection in degree `m`. -/
theorem lowerFaceKernelSubobject_succ_le_pullback_last_face
    (U : SimplicialObject A) (m : ℕ) :
    U.lowerFaceKernelSubobject (m + 1) ≤
      (Subobject.pullback (U.δ (Fin.last (m + 1)))).obj
        (U.lowerFaceKernelSubobject m) := by
  cases m with
  | zero =>
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      simpa using
        (Subobject.top_factors ((U.lowerFaceKernelSubobject 1).arrow ≫ U.δ (Fin.last 1)))
  | succ m =>
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      rw [lowerFaceKernelSubobject_add_one U m]
      refine (Subobject.finset_inf_factors _).2 ?_
      intro k hk
      apply kernelSubobject_factors
      have hklt : Fin.castSucc (Fin.castSucc k) < Fin.last (m + 2) := by
        simp
      have hfac :
          (kernelSubobject (U.δ (Fin.castSucc (Fin.castSucc k)))).Factors
            (U.lowerFaceKernelSubobject (m + 2)).arrow := by
        rw [lowerFaceKernelSubobject_add_one U (m + 1)]
        exact
          Subobject.finset_inf_arrow_factors Finset.univ
            (fun l : Fin (m + 2) ↦ kernelSubobject (U.δ (Fin.castSucc l)))
            (Fin.castSucc k) (by simp)
      rw [Category.assoc, U.δ_comp_δ' hklt]
      simp only [Fin.pred_last]
      rw [← Subobject.factorThru_arrow _ _ hfac, Category.assoc,
        kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]

end SimplicialObject

end CategoryTheory

/-! ### Lemma_14_18_9 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject Opposite
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

/- 
Domain-style sampling for Lemma 14.18.9:
- primary domain: simplicial objects viewed through degreewise subobjects, images, pullbacks, and
  finite suprema, with the normalized Moore subobject appearing only in the final abelian step;
- sampled owner API:
  `imageSubobject`,
  `Subobject.pullback`,
  `Subobject.ofLE`,
  `Subobject.mk`,
  `Subobject.underlyingIso_hom_comp_eq_mk`,
  `NormalizedMooreComplex.objX`;
- best owner abstraction: the source-facing simplicial subobject generated by simplices in degrees
  at most `n`, with degree-`m` part the finite sum/supremum of the images of the maps
  `U_i ⟶ U_m` induced by morphisms `[m] ⟶ [i]` for `i ≤ n`, owned canonically as a
  `Subobject U`;
- primitive data: the degreewise finite sup of those image subobjects and the induced simplicial
  structure maps between them;
- derived API: the `Subobject U` owner, its inclusion `.arrow`, the degreewise least-upper-bound
  characterization, the low-degree `⊤` specialization, and the higher-degree vanishing of the
  normalized Moore subobject of its underlying simplicial object.

Source/core/bridge triage:
- `source-facing`: `SimplicialObject.generatedByDegreeLE U n`, the explicit sub simplicial object
  `U' ⊂ U` defined degreewise by the textbook formula;
- `core/canonical`: `NormalizedMooreComplex.objX`, together with the later skeleton adjunction
  owners `sk` and `skAdj`;
- `bridge/view`: later comparison results identifying the canonical skeleton counit with this
  explicit source-facing subobject.
-/

namespace SimplicialObject

section

variable {A : Type u} [Category.{v} A] [HasImages A] [HasFiniteCoproducts A]

/-- The degree-`m` subobject generated by simplices of `U` in degrees at most `n`. -/
def generatedByDegreeLEObj
    (U : SimplicialObject A) (n : ℕ) (Δ : SimplexCategory) :
    Subobject (U.obj (op Δ)) :=
  let α := Σ i : Fin (n + 1), Δ ⟶ ⦋i.1⦌
  let _ : Inhabited α := ⟨⟨0, SimplexCategory.const Δ ⦋0⦌ 0⟩⟩
  let _ : Fintype α := Fintype.ofFinite α
  let _ : DecidableEq α := Classical.decEq α
  Finset.univ.sup' Finset.univ_nonempty fun p : α ↦ imageSubobject (U.map p.2.op)

end

section

variable {A : Type u} [Category.{v} A] [HasPullbacks A] [HasImages A] [HasFiniteCoproducts A]

/-- The degreewise generated subobjects are stable under simplicial structure maps. -/
private theorem generatedByDegreeLEObj_le_pullback
    (U : SimplicialObject A) (n : ℕ) {Δ Δ' : SimplexCategory} (θ : Δ' ⟶ Δ) :
    U.generatedByDegreeLEObj n Δ ≤
      (Subobject.pullback (U.map θ.op)).obj (U.generatedByDegreeLEObj n Δ') := by
  classical
  let α := Σ i : Fin (n + 1), Δ ⟶ ⦋i.1⦌
  let _ : Inhabited α := ⟨⟨0, SimplexCategory.const Δ ⦋0⦌ 0⟩⟩
  let _ : Fintype α := Fintype.ofFinite α
  let _ : DecidableEq α := Classical.decEq α
  rw [SimplicialObject.generatedByDegreeLEObj, Finset.sup'_le_iff]
  intro p _
  have hfac :
      (U.generatedByDegreeLEObj n Δ').Factors (U.map p.2.op ≫ U.map θ.op) := by
    let β := Σ i : Fin (n + 1), Δ' ⟶ ⦋i.1⦌
    let _ : Inhabited β := ⟨⟨0, SimplexCategory.const Δ' ⦋0⦌ 0⟩⟩
    let _ : Fintype β := Fintype.ofFinite β
    let _ : DecidableEq β := Classical.decEq β
    have himage :
        imageSubobject (U.map ((θ ≫ p.2).op)) ≤ U.generatedByDegreeLEObj n Δ' := by
      simpa [SimplicialObject.generatedByDegreeLEObj, β] using
        (Finset.le_sup'
          (fun q : β ↦ imageSubobject (U.map q.2.op))
          (Finset.mem_univ ⟨p.1, θ ≫ p.2⟩))
    have hfac' : (U.generatedByDegreeLEObj n Δ').Factors (U.map ((θ ≫ p.2).op)) := by
      apply Subobject.factors_of_le (U.map ((θ ≫ p.2).op)) himage
      simpa using
        (imageSubobject_factors_comp_self (U.map ((θ ≫ p.2).op))
          (𝟙 (U.obj (op ⦋p.1.1⦌))))
    simpa using hfac'
  have hpull :
      ((Subobject.pullback (U.map θ.op)).obj (U.generatedByDegreeLEObj n Δ')).Factors
        (U.map p.2.op) := by
    rw [Limits.pullback_factors_iff]
    simpa using hfac
  exact imageSubobject_le (U.map p.2.op)
    (((Subobject.pullback (U.map θ.op)).obj (U.generatedByDegreeLEObj n Δ')).factorThru
      (U.map p.2.op) hpull)
    (((Subobject.pullback (U.map θ.op)).obj (U.generatedByDegreeLEObj n Δ')).factorThru_arrow
      (U.map p.2.op) hpull)

/-- The map on the source-facing sub simplicial object generated by simplices in degrees at most
`n`. -/
private def generatedByDegreeLEMap
    (U : SimplicialObject A) (n : ℕ) {Δ Δ' : SimplexCategory} (θ : Δ' ⟶ Δ) :
    (U.generatedByDegreeLEObj n Δ : A) ⟶ (U.generatedByDegreeLEObj n Δ' : A) :=
  Subobject.ofLE _ _ (U.generatedByDegreeLEObj_le_pullback n θ) ≫
    Subobject.pullbackπ (U.map θ.op) (U.generatedByDegreeLEObj n Δ')

@[reassoc]
private theorem generatedByDegreeLEMap_arrow
    (U : SimplicialObject A) (n : ℕ) {Δ Δ' : SimplexCategory} (θ : Δ' ⟶ Δ) :
    U.generatedByDegreeLEMap n θ ≫ (U.generatedByDegreeLEObj n Δ').arrow =
      (U.generatedByDegreeLEObj n Δ).arrow ≫ U.map θ.op := by
  rw [generatedByDegreeLEMap, Category.assoc,
    (Subobject.isPullback (U.map θ.op) (U.generatedByDegreeLEObj n Δ')).w,
    ← Category.assoc, Subobject.ofLE_arrow]

/-- The explicit simplicial object underlying the subobject of `U` generated by simplices in
degrees at most `n`. -/
private def generatedByDegreeLEUnderlying
    (U : SimplicialObject A) (n : ℕ) :
    SimplicialObject A where
  obj Δ := U.generatedByDegreeLEObj n Δ.unop
  map f := U.generatedByDegreeLEMap n f.unop
  map_id Δ := by
    apply Subobject.eq_of_comp_arrow_eq
    simp [generatedByDegreeLEMap_arrow]
  map_comp f g := by
    let hfg := (f ≫ g).unop
    let hg := g.unop
    let hf := f.unop
    apply Subobject.eq_of_comp_arrow_eq
    rw [U.generatedByDegreeLEMap_arrow n hfg, Category.assoc,
      U.generatedByDegreeLEMap_arrow n hg, ← Category.assoc,
      U.generatedByDegreeLEMap_arrow n hf]
    simp [hfg, hg, hf]

/-- The inclusion of the explicit simplicial object generated by simplices in degrees at most `n`
into `U`. -/
private def generatedByDegreeLEArrow
    (U : SimplicialObject A) (n : ℕ) :
    U.generatedByDegreeLEUnderlying n ⟶ U where
  app Δ := (U.generatedByDegreeLEObj n Δ.unop).arrow
  naturality := by
    intro X Y f
    simpa using
      (U.generatedByDegreeLEMap_arrow n
        (show Y.unop ⟶ X.unop from Quiver.Hom.unop f))

private theorem generatedByDegreeLEArrow_mono
    (U : SimplicialObject A) (n : ℕ) :
    Mono (U.generatedByDegreeLEArrow n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk m =>
          simpa [generatedByDegreeLEArrow] using
            (inferInstance : Mono ((U.generatedByDegreeLEObj n ⦋m⦌).arrow))

/-- The canonical subobject of `U` generated by simplices in degrees at most `n`. -/
def generatedByDegreeLE
    (U : SimplicialObject A) (n : ℕ) :
    Subobject U :=
  letI : Mono (U.generatedByDegreeLEArrow n) := U.generatedByDegreeLEArrow_mono n
  Subobject.mk (U.generatedByDegreeLEArrow n)

instance generatedByDegreeLE_arrow_app_mono
    (U : SimplicialObject A) (n m : ℕ) :
    Mono (((U.generatedByDegreeLE n).arrow).app (op ⦋m⦌)) := by
  haveI : Mono (U.generatedByDegreeLE n).arrow := Subobject.arrow_mono (U.generatedByDegreeLE n)
  infer_instance

/-- In degree `m`, the canonical generated subobject of `U` is represented by the explicit
degreewise image-supremum formula. -/
theorem generatedByDegreeLE_app_subobject
    (U : SimplicialObject A) (n : ℕ) (m : ℕ) :
    Subobject.mk (((U.generatedByDegreeLE n).arrow).app (op ⦋m⦌)) = U.generatedByDegreeLEObj n ⦋m⦌ := by
  let η : U.generatedByDegreeLEUnderlying n ⟶ U := U.generatedByDegreeLEArrow n
  letI : Mono η := U.generatedByDegreeLEArrow_mono n
  letI : Mono (((U.generatedByDegreeLE n).arrow).app (op ⦋m⦌)) :=
    generatedByDegreeLE_arrow_app_mono U n m
  exact Subobject.mk_eq_of_comm (((U.generatedByDegreeLE n).arrow).app (op ⦋m⦌))
    ((Subobject.underlyingIso η).app (op ⦋m⦌)) <|
    by
      simpa only [NatTrans.comp_app, generatedByDegreeLE, η] using
        congr_app (Subobject.underlyingIso_hom_comp_eq_mk η) (op ⦋m⦌)

end

end SimplicialObject

open SimplicialObject

section

variable {A : Type u} [Category.{v} A] [HasImages A] [HasFiniteCoproducts A]

-- Proof sketch: `generatedByDegreeLEObj` is the finite supremum over the nonempty family of all
-- pairs `(i ≤ n, θ : [m] ⟶ [i])`, so each generator is bounded by `Finset.le_sup'`.
/-- Each generating image is contained in the degreewise subobject generated by simplices of
degree at most `n`. -/
theorem imageSubobject_map_le_generatedByDegreeLEObj
    (U : SimplicialObject A) (n : ℕ) {Δ : SimplexCategory} {i : ℕ} (hi : i ≤ n)
    (θ : Δ ⟶ ⦋i⦌) :
    imageSubobject (U.map θ.op) ≤ U.generatedByDegreeLEObj n Δ := by
  classical
  let α := Σ j : Fin (n + 1), Δ ⟶ ⦋j.1⦌
  let _ : Inhabited α := ⟨⟨0, SimplexCategory.const Δ ⦋0⦌ 0⟩⟩
  let _ : Fintype α := Fintype.ofFinite α
  let _ : DecidableEq α := Classical.decEq α
  let p : α := ⟨⟨i, Nat.lt_succ_of_le hi⟩, θ⟩
  simpa [SimplicialObject.generatedByDegreeLEObj, α, p] using
    (Finset.le_sup' (fun q : α ↦ imageSubobject (U.map q.2.op)) (Finset.mem_univ p))

/-- Lemma 14.18.9 (1): if `U'` is the sub simplicial object of `U` defined degreewise by
`U'_m = ∑_{φ : [m] ⟶ [i],\, i ≤ n} Im(U(φ))`, then `U'_m` is the least upper bound of those image
subobjects. -/
theorem generatedByDegreeLEObj_isLUB_map_images
    (U : SimplicialObject A) (n m : ℕ) :
    IsLUB
      (setOf fun P : Subobject (U.obj (op ⦋m⦌)) ↦
        ∃ i, i ≤ n ∧ ∃ θ : ⦋m⦌ ⟶ ⦋i⦌, P = imageSubobject (U.map θ.op))
      (U.generatedByDegreeLEObj n ⦋m⦌) := by
  classical
  let α := Σ i : Fin (n + 1), ⦋m⦌ ⟶ ⦋i.1⦌
  let _ : Inhabited α := ⟨⟨0, SimplexCategory.const ⦋m⦌ ⦋0⦌ 0⟩⟩
  let _ : Fintype α := Fintype.ofFinite α
  let _ : DecidableEq α := Classical.decEq α
  refine ⟨?_, ?_⟩
  · intro P hP
    rcases hP with ⟨i, hi, θ, rfl⟩
    exact imageSubobject_map_le_generatedByDegreeLEObj U n hi θ
  · intro P hP
    rw [SimplicialObject.generatedByDegreeLEObj, Finset.sup'_le_iff]
    intro q _
    exact hP ⟨q.1.1, Nat.le_of_lt_succ q.1.2, q.2, rfl⟩

-- Proof sketch: for `i ≤ n`, the identity map `[i] ⟶ [i]` is one of the generators in degree `i`,
-- and its image is all of `U_i`.
/-- Lemma 14.18.9 (2): in every degree `i ≤ n`, the source-facing generated sub simplicial object
agrees with `U` itself. -/
theorem generatedByDegreeLEObj_eq_top_of_le
    (U : SimplicialObject A) {n i : ℕ} (h : i ≤ n) :
    U.generatedByDegreeLEObj n ⦋i⦌ = ⊤ := by
  have hp : imageSubobject (U.map (𝟙 ⦋i⦌).op) = ⊤ := by
    simpa [imageSubobject_mono] using
      (Subobject.mk_eq_top_of_isIso (U.map (𝟙 ⦋i⦌).op))
  refine le_antisymm le_top ?_
  rw [← hp]
  exact imageSubobject_map_le_generatedByDegreeLEObj U n h (𝟙 ⦋i⦌)

end

section

variable {A : Type u} [Category.{v} A] [HasPullbacks A] [HasImages A] [HasFiniteCoproducts A]

/-- In degree `i ≤ n`, the inclusion of the canonical generated subobject into `U` is an
isomorphism. -/
theorem generatedByDegreeLE_arrow_app_isIso_of_le
    (U : SimplicialObject A) (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    IsIso (((U.generatedByDegreeLE n).arrow).app (op ⦋i⦌)) := by
  rw [Subobject.isIso_iff_mk_eq_top, SimplicialObject.generatedByDegreeLE_app_subobject,
    generatedByDegreeLEObj_eq_top_of_le U hi]

end

-- Proof sketch: every generator in degree `m > n` comes from a strictly lower degree, hence is
-- degenerate; therefore the normalized Moore subobject of the generated simplicial object
-- vanishes in degree `m`.
section

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Lemma 14.18.9 (3): the normalized Moore subobject of the source-facing generated sub
simplicial object vanishes in every degree strictly larger than `n`. -/
theorem generatedByDegreeLE_normalizedMoore_eq_bot_of_lt
    (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    NormalizedMooreComplex.objX (U.generatedByDegreeLE n : SimplicialObject A) m = ⊥ := by
  let V : SimplicialObject A := U.generatedByDegreeLE n
  let η : V ⟶ U := (U.generatedByDegreeLE n).arrow
  let pU : U.obj (op ⦋m⦌) ⟶ U.obj (op ⦋m⦌) :=
    (PInfty : AlternatingFaceMapComplex.obj U ⟶ _).f m
  let pV : V.obj (op ⦋m⦌) ⟶ V.obj (op ⦋m⦌) :=
    (PInfty : AlternatingFaceMapComplex.obj V ⟶ _).f m
  haveI : Mono η := Subobject.arrow_mono (U.generatedByDegreeLE n)
  have hη :
      η.app (op ⦋m⦌) ≫ pU = 0 := by
    have hle :
        U.generatedByDegreeLEObj n ⦋m⦌ ≤ kernelSubobject pU := by
      refine (generatedByDegreeLEObj_isLUB_map_images U n m).2 ?_
      rintro P ⟨i, hi, φ, rfl⟩
      have hnotmono : ¬Mono φ := by
        intro hmono
        exact (Nat.not_le_of_gt (lt_of_le_of_lt hi h)) (SimplexCategory.len_le_of_mono φ)
      refine le_kernelSubobject (f := pU) _ ?_
      simpa [pU] using imageSubobject_arrow_comp_eq_zero (degeneracy_comp_PInfty U m φ hnotmono)
    have hmk :
        Subobject.mk (η.app (op ⦋m⦌)) ≤ Subobject.mk (kernelSubobject pU).arrow := by
      rw [generatedByDegreeLE_app_subobject, Subobject.mk_arrow]
      exact hle
    rw [← Subobject.ofMkLEMk_comp hmk, Category.assoc,
      kernelSubobject_arrow_comp (f := pU), comp_zero]
  have hP : pV = 0 := by
    apply (cancel_mono (η.app (op ⦋m⦌))).1
    rw [show pV ≫ η.app (op ⦋m⦌) = η.app (op ⦋m⦌) ≫ pU by
      simpa [pU, pV] using (PInfty_f_naturality (n := m) η).symm, hη, zero_comp]
  have harrow :
      (NormalizedMooreComplex.objX V m).arrow ≫ pV =
        (NormalizedMooreComplex.objX V m).arrow := by
    simpa [pV] using congrArg (fun φ ↦ φ.f m) (inclusionOfMooreComplexMap_comp_PInfty V)
  rw [hP, comp_zero] at harrow
  have hbot : NormalizedMooreComplex.objX V m = ⊥ := by
    rw [← Subobject.mk_arrow (NormalizedMooreComplex.objX V m)]
    exact (Subobject.mk_eq_bot_iff_zero).2 harrow.symm
  simpa [V] using hbot

end

end CategoryTheory
