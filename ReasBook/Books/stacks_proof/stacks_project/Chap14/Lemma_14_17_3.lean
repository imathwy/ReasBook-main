import stacks_proof.stacks_project.Chap14.Definition_14_17_1
import stacks_proof.stacks_project.Chap14.Lemma_14_13_2
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.Limits.Types.Yoneda
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable [HasBinaryCoproducts C] [HasFiniteLimits C]

section Restriction

variable (U : SSet.{w}) (V : SimplicialObject C)
variable [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]

/-- Helper for Lemma 14.17.3: the diagram indexed by the simplex-elements category of `U` whose
value at a simplex of `U` is the corresponding component of `V`. -/
private noncomputable def simplexElementsDiagram : U.Elements ⥤ C :=
  CategoryOfElements.π U ⋙ V

/-- Helper for Lemma 14.17.3: for a constant simplicial source `(const C).obj X`, compatible
families of maps into `V` are exactly cones from `X` to the simplex-elements diagram of `U`. -/
private noncomputable def compatibleFamily_const_equiv_cones (X : C) :
    SimplicialCopowerHomFamily.Compatible U ((const C).obj X) V ≃
      (simplexElementsDiagram U V).cones.obj (op X) where
  toFun F :=
    { app := fun A ↦ F.1 A.1 A.2
      naturality := by
        intro A B f
        -- Naturality is precisely the compatibility condition, specialized to the simplex
        -- represented by the morphism in the category of elements.
        simpa [simplexElementsDiagram, CategoryOfElements.map_snd f] using (F.2 f.val A.2) }
  invFun s :=
    ⟨fun Δ u ↦ s.app (Functor.elementsMk U Δ u), by
      intro Δ Δ' f u
      -- Evaluate the cone naturality on the canonical arrow in `U.Elements`.
      simpa [simplexElementsDiagram] using
        s.naturality
          (CategoryOfElements.homMk
            (Functor.elementsMk U Δ u)
            (Functor.elementsMk U Δ' (U.map f u))
            f rfl)⟩
  left_inv F := by
    apply Subtype.ext
    funext Δ u
    rfl
  right_inv s := by
    cases s
    rfl

/-- Helper for Lemma 14.17.3: the bounded full subcategory used in the finite-limit reduction is
cut out by the degree bound `2 * d` on simplices of `U`. -/
private def boundedSimplexProperty (d : ℕ) : ObjectProperty U.Elements :=
  fun A ↦ A.1.unop.len ≤ 2 * d

/-- Helper for Lemma 14.17.3: every simplex of `U` receives a map from a simplex lying in the
bounded full subcategory. The source proof uses a `2d` bound; the Lean reduction factors through
the unique nondegenerate source simplex, which is automatically of degree `≤ d ≤ 2d`. -/
private theorem exists_bounded_simplex_to (d : ℕ) [U.HasDimensionLE d] (A : U.Elements) :
    ∃ B : (boundedSimplexProperty U d).FullSubcategory, Nonempty (B.obj ⟶ A) := by
  obtain ⟨m, f, _, y, hy⟩ := U.exists_nonDegenerate A.2
  have hm : m ≤ d := U.dim_le_of_nonDegenerate y d
  have hB : boundedSimplexProperty U d (Functor.elementsMk U (op ⦋m⦌) y) := by
    exact le_trans hm (by simpa [two_mul] using Nat.le_add_right d d)
  let B₀ : U.Elements := Functor.elementsMk U (op ⦋m⦌) y
  have hA : op ⦋A.1.unop.len⦌ = A.1 := by
    simpa using congrArg Opposite.op (SimplexCategory.mk_len A.1.unop)
  refine ⟨⟨B₀, hB⟩, ⟨?_⟩⟩
  refine CategoryOfElements.homMk B₀ A (f.op ≫ eqToHom hA) ?_
  -- The chosen nondegenerate presentation of `A.2` gives the required arrow in `U.Elements`.
  simpa [FunctorToTypes.map_comp_apply, hA] using hy.symm

/-- Helper for Lemma 14.17.3: there are only finitely many simplex objects of degree `≤ 2 * d`. -/
private instance boundedSimplexIndex_finite (d : ℕ) :
    Finite {Δ : SimplexCategoryᵒᵖ // Δ.unop.len ≤ 2 * d} := by
  refine Finite.of_injective
    (fun Δ : {Δ : SimplexCategoryᵒᵖ // Δ.unop.len ≤ 2 * d} ↦
      (⟨Δ.1.unop.len, Nat.lt_succ_of_le Δ.2⟩ : Fin (2 * d + 1)))
    ?_
  intro A B h
  apply Subtype.ext
  apply Opposite.unop_injective
  ext
  exact congrArg Fin.val h

/-- Helper for Lemma 14.17.3: an object of the bounded simplex-elements full subcategory is the
same data as a simplex of degree `≤ 2 * d` together with a chosen element of `U` on that simplex. -/
private def boundedSimplexObjectsEquiv (d : ℕ) :
    (boundedSimplexProperty U d).FullSubcategory ≃
      Σ Δ : {Δ : SimplexCategoryᵒᵖ // Δ.unop.len ≤ 2 * d}, U.obj Δ.1 where
  toFun A := ⟨⟨A.obj.1, A.property⟩, A.obj.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, p.1.2⟩
  left_inv A := by
    cases A
    rfl
  right_inv p := by
    cases p
    rfl

/-- Helper for Lemma 14.17.3: the bounded simplex-elements full subcategory has finitely many
objects, because both the degree bound and each degree of `U` are finite. -/
private instance boundedSimplexObjects_finite (d : ℕ) :
    Finite ((boundedSimplexProperty U d).FullSubcategory) := by
  refine Finite.of_injective (boundedSimplexObjectsEquiv (U := U) d) ?_
  exact (boundedSimplexObjectsEquiv (U := U) d).injective

/-- Helper for Lemma 14.17.3: hom-sets in the bounded simplex-elements full subcategory are
finite, because a morphism is determined by its underlying simplex operator. -/
private instance boundedSimplexHom_finite (d : ℕ)
    (A B : (boundedSimplexProperty U d).FullSubcategory) :
    Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f : A ⟶ B ↦ Quiver.Hom.unop f.hom.val) ?_
  intro f g hfg
  apply ObjectProperty.hom_ext
  exact CategoryOfElements.ext U f.hom g.hom (congrArg Quiver.Hom.op hfg)

/-- Helper for Lemma 14.17.3: any presentation of a simplex factors through its chosen
nondegenerate presentation by a map between the source simplices. -/
private theorem nondegenerate_presentation_factors
    {n m₁ m₂ : ℕ} (x : U _⦋n⦌)
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁] (y₁ : U.nonDegenerate m₁) (hy₁ : x = U.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) (y₂ : U _⦋m₂⦌) (hy₂ : x = U.map f₂.op y₂) :
    ∃ g : ⦋m₁⦌ ⟶ ⦋m₂⦌, U.map g.op y₂ = y₁ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  refine ⟨hf₁.section_ ≫ f₂, ?_⟩
  -- Proof comment: precompose the second presentation by a section of the first map.
  rw [op_comp, FunctorToTypes.map_comp_apply, ← hy₂, hy₁, ← FunctorToTypes.map_comp_apply, ← op_comp,
    SplitEpi.id, op_id, FunctorToTypes.map_id_apply]

/-- Helper for Lemma 14.17.3: a normalized arrow into `A` determines the explicit simplex
operator from the target degree of `A` to the source degree of the normalized simplex. -/
private theorem boundedSimplex_explicit_arrow_operator
    {A : U.Elements} (hA : op ⦋A.1.unop.len⦌ = A.1)
    {m : ℕ} (y : U.nonDegenerate m)
    (g : Functor.elementsMk U (op ⦋m⦌) y ⟶ A) :
    A.2 = U.map (Quiver.Hom.unop (g.val ≫ eqToHom hA.symm)).op y := by
  -- Proof comment: the defining equation for a morphism in the category of elements becomes the
  -- desired simplex-operator formula after rewriting the target object of `A` by `hA`.
  simpa [FunctorToTypes.map_comp_apply, hA] using (CategoryOfElements.map_snd g).symm

/-- Helper for Lemma 14.17.3: if the source degree exceeds `m₁ + m₂`, then the pair of simplex
operators `(f₁, f₂)` cannot be injective on vertices. -/
private theorem boundedSimplex_pair_map_not_injective_of_gt
    {n m₁ m₂ : ℕ} (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌)
    (hgt : m₁ + m₂ < n) :
    ¬ Function.Injective (fun i : Fin (n + 1) ↦ (f₁.toOrderHom i, f₂.toOrderHom i)) := by
  intro hpair
  let s : Fin (n + 1) → Fin (m₁ + m₂ + 1) := fun i ↦
    ⟨(f₁.toOrderHom i : ℕ) + (f₂.toOrderHom i : ℕ), by
      have h1 : (f₁.toOrderHom i : ℕ) < m₁ + 1 := (f₁.toOrderHom i).is_lt
      have h2 : (f₂.toOrderHom i : ℕ) ≤ m₂ := Nat.le_of_lt_succ (f₂.toOrderHom i).is_lt
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_of_lt_of_le h1 h2⟩
  have hstrict : StrictMono fun i : Fin (n + 1) ↦ (s i : ℕ) := by
    intro i j hij
    have h1le : (f₁.toOrderHom i : ℕ) ≤ f₁.toOrderHom j :=
      Fin.le_iff_val_le_val.mp (f₁.toOrderHom.monotone (le_of_lt hij))
    have h2le : (f₂.toOrderHom i : ℕ) ≤ f₂.toOrderHom j :=
      Fin.le_iff_val_le_val.mp (f₂.toOrderHom.monotone (le_of_lt hij))
    have hpairNe : (f₁.toOrderHom i, f₂.toOrderHom i) ≠ (f₁.toOrderHom j, f₂.toOrderHom j) := by
      intro hEq
      exact hij.ne (hpair hEq)
    by_cases h1eq : f₁.toOrderHom i = f₁.toOrderHom j
    · have h2neq : f₂.toOrderHom i ≠ f₂.toOrderHom j := by
        intro h2eq
        apply hpairNe
        exact Prod.ext h1eq h2eq
      have h2lt : (f₂.toOrderHom i : ℕ) < f₂.toOrderHom j :=
        lt_of_le_of_ne h2le (by
          intro hval
          apply h2neq
          exact Fin.ext hval)
      simpa [s, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_of_le_of_lt h1le h2lt
    · have h1lt : (f₁.toOrderHom i : ℕ) < f₁.toOrderHom j :=
        lt_of_le_of_ne h1le (by
          intro hval
          apply h1eq
          exact Fin.ext hval)
      simpa [s] using Nat.add_lt_add_of_lt_of_le h1lt h2le
  have hs : Function.Injective s := by
    intro i j hij
    apply hstrict.injective
    exact congrArg Fin.val hij
  have hcard : n + 1 ≤ m₁ + m₂ + 1 := by
    simpa using Fintype.card_le_of_injective s hs
  exact Nat.not_lt_of_ge (Nat.le_of_succ_le_succ hcard) hgt

/-- Helper for Lemma 14.17.3: if the source degree exceeds `m₁ + m₂`, then two simplex operators
share a repeated adjacent vertex and hence factor through the same degeneracy map. -/
private theorem boundedSimplex_pair_repeats_of_gt
    {n m₁ m₂ : ℕ} (f₁ : ⦋n + 1⦌ ⟶ ⦋m₁⦌) (f₂ : ⦋n + 1⦌ ⟶ ⦋m₂⦌)
    (hgt : m₁ + m₂ < n + 1) :
    ∃ i : Fin (n + 1),
      f₁.toOrderHom i.castSucc = f₁.toOrderHom i.succ ∧
      f₂.toOrderHom i.castSucc = f₂.toOrderHom i.succ := by
  have hnot :
      ¬ Function.Injective (fun x : Fin (n + 2) ↦ (f₁.toOrderHom x, f₂.toOrderHom x)) :=
    boundedSimplex_pair_map_not_injective_of_gt (f₁ := f₁) (f₂ := f₂) hgt
  classical
  simp_rw [Function.Injective] at hnot
  push_neg at hnot
  rcases hnot with ⟨x, y, hEq, hxyNe⟩
  have hstep :
      ∀ {a b : Fin (n + 2)},
        a < b →
          (f₁.toOrderHom a, f₂.toOrderHom a) = (f₁.toOrderHom b, f₂.toOrderHom b) →
          ∃ i : Fin (n + 1),
            f₁.toOrderHom i.castSucc = f₁.toOrderHom i.succ ∧
            f₂.toOrderHom i.castSucc = f₂.toOrderHom i.succ := by
    intro a b hab habEq
    let i : Fin (n + 1) := a.castPred ((Fin.le_last _).trans_lt' hab).ne
    have ha : i.castSucc = a := by
      simpa [i] using Fin.castSucc_castPred ((Fin.le_last _).trans_lt' hab).ne
    have hsucc : i.succ ≤ b := by
      simpa [i] using
        (Fin.succ_castPred_le_iff ((Fin.le_last _).trans_lt' hab).ne).mpr hab
    have hEq₁ : f₁.toOrderHom a = f₁.toOrderHom b := congrArg (fun p ↦ p.1) habEq
    have hEq₂ : f₂.toOrderHom a = f₂.toOrderHom b := congrArg (fun p ↦ p.2) habEq
    refine ⟨i, ?_, ?_⟩
    · apply le_antisymm
      · exact f₁.toOrderHom.monotone (le_of_lt Fin.castSucc_lt_succ)
      · rw [ha, hEq₁]
        exact f₁.toOrderHom.monotone hsucc
    · apply le_antisymm
      · exact f₂.toOrderHom.monotone (le_of_lt Fin.castSucc_lt_succ)
      · rw [ha, hEq₂]
        exact f₂.toOrderHom.monotone hsucc
  rcases lt_or_gt_of_ne hxyNe with hxy | hyx
  · exact hstep hxy hEq
  · exact hstep hyx hEq.symm

/-- Helper for Lemma 14.17.3: two simplex operators with common source admit a common epi
quotient of degree at most the sum of the target degrees. -/
private theorem boundedSimplex_pair_operator_common_refinement
    {n m₁ m₂ : ℕ} (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) :
    ∃ (k : ℕ) (_ : k ≤ m₁ + m₂) (h : ⦋n⦌ ⟶ ⦋k⦌) (_ : Epi h)
      (g₁ : ⦋k⦌ ⟶ ⦋m₁⦌) (g₂ : ⦋k⦌ ⟶ ⦋m₂⦌),
      f₁ = h ≫ g₁ ∧ f₂ = h ≫ g₂ := by
  induction n generalizing m₁ m₂ with
  | zero =>
      refine ⟨0, Nat.zero_le _, 𝟙 _, inferInstance, f₁, f₂, ?_, ?_⟩
      · simp
      · simp
  | succ n ih =>
      by_cases hle : n + 1 ≤ m₁ + m₂
      · refine ⟨n + 1, hle, 𝟙 _, inferInstance, f₁, f₂, ?_, ?_⟩
        · simp
        · simp
      · have hgt : m₁ + m₂ < n + 1 := Nat.lt_of_not_ge hle
        obtain ⟨i, hi₁, hi₂⟩ :=
          boundedSimplex_pair_repeats_of_gt (f₁ := f₁) (f₂ := f₂) hgt
        obtain ⟨f₁', hf₁'⟩ := SimplexCategory.eq_σ_comp_of_not_injective' f₁ i hi₁
        obtain ⟨f₂', hf₂'⟩ := SimplexCategory.eq_σ_comp_of_not_injective' f₂ i hi₂
        obtain ⟨k, hk, h, hEpi, g₁, g₂, hh₁, hh₂⟩ := ih f₁' f₂'
        refine ⟨k, hk, SimplexCategory.σ i ≫ h, inferInstance, g₁, g₂, ?_, ?_⟩
        · -- Proof comment: both operators first factor through the same degeneracy `σ i`, and the
          -- inductive hypothesis then compresses the shortened pair through `h`.
          rw [hf₁', hh₁]
          simp [Category.assoc]
        · -- Proof comment: the second operator follows the same shared compression pattern.
          rw [hf₂', hh₂]
          simp [Category.assoc]

/-- Helper for Lemma 14.17.3: the arrow part of an object in the bounded costructured arrow over
`A` is an explicit equality of simplices in `U.Elements`. -/
private theorem boundedSimplex_arrowPresentation
    (d : ℕ) [U.HasDimensionLE d] {A : U.Elements}
    (Y : CostructuredArrow (boundedSimplexProperty U d).ι A) :
    U.map Y.hom.val Y.left.obj.2 = A.2 :=
  CategoryOfElements.map_snd Y.hom

/-- Helper for Lemma 14.17.3: after replacing the source simplex of `Y` by its nondegenerate
presentation, the resulting source still maps to `A` by the composite simplex operator. -/
private theorem boundedSimplex_normalizedPresentation
    (d : ℕ) [U.HasDimensionLE d] {A : U.Elements}
    (Y : CostructuredArrow (boundedSimplexProperty U d).ι A)
    {mY : ℕ} (fY : ⦋Y.left.obj.1.unop.len⦌ ⟶ ⦋mY⦌) [Epi fY]
    (yY : U.nonDegenerate mY) (hyY : Y.left.obj.2 = U.map fY.op yY) :
    A.2 = U.map (fY.op ≫ eqToHom (by
      simpa using congrArg Opposite.op (SimplexCategory.mk_len Y.left.obj.1.unop)) ≫ Y.hom.val) yY := by
  have hY :
      op ⦋Y.left.obj.1.unop.len⦌ = Y.left.obj.1 := by
    simpa using congrArg Opposite.op (SimplexCategory.mk_len Y.left.obj.1.unop)
  -- Proof comment: rewrite the source simplex of `Y` by its nondegenerate presentation and then
  -- use the defining equality of the arrow `Y ⟶ A`.
  calc
    A.2 = U.map Y.hom.val Y.left.obj.2 := (boundedSimplex_arrowPresentation (U := U) d Y).symm
    _ = U.map Y.hom.val (U.map fY.op yY) := by rw [hyY]
    _ = U.map (fY.op ≫ eqToHom hY ≫ Y.hom.val) yY := by
      simp [FunctorToTypes.map_comp_apply]

/-- Helper for Lemma 14.17.3: every object over `A` in the bounded costructured arrow category is
reached by a morphism from an object whose source simplex is already nondegenerate of degree
`≤ d`. -/
private theorem boundedSimplex_has_nondegenerate_source
    (d : ℕ) [U.HasDimensionLE d] (A : U.Elements) :
    ∀ Y : CostructuredArrow (boundedSimplexProperty U d).ι A,
      ∃ Z : CostructuredArrow (boundedSimplexProperty U d).ι A, Nonempty (Z ⟶ Y) := by
  intro Y
  obtain ⟨mY, fY, _, yY, hyY⟩ := U.exists_nonDegenerate Y.left.obj.2
  have hmY : mY ≤ d := U.dim_le_of_nonDegenerate yY d
  have hZ :
      boundedSimplexProperty U d (Functor.elementsMk U (op ⦋mY⦌) yY) := by
    exact le_trans hmY (by simpa [two_mul] using Nat.le_add_right d d)
  let Zobj : U.Elements := Functor.elementsMk U (op ⦋mY⦌) yY
  let Zleft : (boundedSimplexProperty U d).FullSubcategory := ⟨Zobj, hZ⟩
  have hY :
      op ⦋Y.left.obj.1.unop.len⦌ = Y.left.obj.1 := by
    simpa using congrArg Opposite.op (SimplexCategory.mk_len Y.left.obj.1.unop)
  let ZhomElem : Zleft.obj ⟶ A :=
    CategoryOfElements.homMk Zobj A
      (fY.op ≫ eqToHom hY ≫ Y.hom.val)
      (boundedSimplex_normalizedPresentation (U := U) d Y fY yY hyY).symm
  let Z : CostructuredArrow (boundedSimplexProperty U d).ι A := ⟨Zleft, ⟨⟨⟩⟩, ZhomElem⟩
  let toYElem : Zleft.obj ⟶ Y.left.obj :=
    CategoryOfElements.homMk Zobj Y.left.obj
      (fY.op ≫ eqToHom hY)
      (by
        -- Proof comment: the chosen nondegenerate source maps to the original source of `Y`
        -- by the simplex operator obtained from `exists_nonDegenerate`.
        simpa [FunctorToTypes.map_comp_apply, hY] using hyY.symm)
  let toYLeft : Z.left ⟶ Y.left := ObjectProperty.homMk toYElem
  refine ⟨Z, ⟨CostructuredArrow.homMk toYLeft ?_⟩⟩
  -- Proof comment: the defining arrow of `Z` was chosen precisely so that the triangle over `A`
  -- commutes after composing with `Y.hom`.
  apply CategoryOfElements.ext U
  rfl

/-- Helper for Lemma 14.17.3: normalize an object over `A` to an explicit bounded source simplex
that is already nondegenerate. -/
private theorem boundedSimplex_normalize_to_nondegenerate
    (d : ℕ) [U.HasDimensionLE d] {A : U.Elements}
    (Y : CostructuredArrow (boundedSimplexProperty U d).ι A) :
    ∃ (mY : ℕ) (yY : U.nonDegenerate mY)
      (hYBound : boundedSimplexProperty U d (Functor.elementsMk U (op ⦋mY⦌) yY))
      (gY : Functor.elementsMk U (op ⦋mY⦌) yY ⟶ A),
      Nonempty
        (((⟨⟨Functor.elementsMk U (op ⦋mY⦌) yY, hYBound⟩, ⟨⟨⟩⟩, gY⟩ :
            CostructuredArrow (boundedSimplexProperty U d).ι A)) ⟶ Y) := by
  obtain ⟨mY, fY, _, yY, hyY⟩ := U.exists_nonDegenerate Y.left.obj.2
  have hmY : mY ≤ d := U.dim_le_of_nonDegenerate yY d
  have hZ :
      boundedSimplexProperty U d (Functor.elementsMk U (op ⦋mY⦌) yY) := by
    exact le_trans hmY (by simpa [two_mul] using Nat.le_add_right d d)
  let Zobj : U.Elements := Functor.elementsMk U (op ⦋mY⦌) yY
  let Zleft : (boundedSimplexProperty U d).FullSubcategory := ⟨Zobj, hZ⟩
  have hY :
      op ⦋Y.left.obj.1.unop.len⦌ = Y.left.obj.1 := by
    simpa using congrArg Opposite.op (SimplexCategory.mk_len Y.left.obj.1.unop)
  let ZhomElem : Zleft.obj ⟶ A :=
    CategoryOfElements.homMk Zobj A
      (fY.op ≫ eqToHom hY ≫ Y.hom.val)
      (boundedSimplex_normalizedPresentation (U := U) d Y fY yY hyY).symm
  let Z : CostructuredArrow (boundedSimplexProperty U d).ι A := ⟨Zleft, ⟨⟨⟩⟩, ZhomElem⟩
  have htoY :
      U.map (fY.op ≫ eqToHom hY) yY = Y.left.obj.2 := by
    -- Proof comment: the new source simplex was chosen as a nondegenerate presentation of the
    -- original source of `Y`, so the obvious map lands back on `Y.left.obj.2`.
    simpa [FunctorToTypes.map_comp_apply, hY] using hyY.symm
  let toYElem : Zleft.obj ⟶ Y.left.obj :=
    CategoryOfElements.homMk Zobj Y.left.obj
      (fY.op ≫ eqToHom hY)
      htoY
  let toYLeft : Z.left ⟶ Y.left := ObjectProperty.homMk toYElem
  have hcomm : toYLeft.hom ≫ Y.hom = Z.hom := by
    -- Proof comment: the defining arrow of `Z` is the composite of the normalization map with
    -- the original arrow `Y ⟶ A`.
    apply CategoryOfElements.ext U
    rfl
  refine ⟨mY, yY, hZ, ZhomElem, ?_⟩
  exact ⟨CostructuredArrow.homMk toYLeft hcomm⟩

/-- Helper for Lemma 14.17.3: the bounded costructured arrow over `A` is connected.
The remaining source-faithful step is to connect two normalized nondegenerate sources by the
common-refinement argument inside degrees `≤ 2 * d`. -/
private theorem boundedSimplex_costructured_isConnected
    (d : ℕ) [U.HasDimensionLE d] (A : U.Elements) :
    IsConnected (CostructuredArrow (boundedSimplexProperty U d).ι A) := by
  -- Route correction: the previous universal-object route is stronger than the Stacks proof
  -- needs. The proof now normalizes both objects over `A`, compresses their source operators
  -- through a bounded common quotient, and packages that quotient simplex as the common target.
  have hnonempty : Nonempty (CostructuredArrow (boundedSimplexProperty U d).ι A) := by
    obtain ⟨B, ⟨f⟩⟩ := exists_bounded_simplex_to (U := U) d A
    exact ⟨⟨B, ⟨⟨⟩⟩, f⟩⟩
  letI : Nonempty (CostructuredArrow (boundedSimplexProperty U d).ι A) := hnonempty
  refine zigzag_isConnected ?_
  intro Y₁ Y₂
  have hA : op ⦋A.1.unop.len⦌ = A.1 := by
    -- Proof comment: replace the target simplex of `A` by the standard simplex on its degree once.
    simpa using congrArg Opposite.op (SimplexCategory.mk_len A.1.unop)
  obtain ⟨m₁, y₁, h₁Bound, g₁, ⟨hZ₁⟩⟩ :=
    boundedSimplex_normalize_to_nondegenerate (U := U) d Y₁
  let Z₁ : CostructuredArrow (boundedSimplexProperty U d).ι A :=
    ⟨⟨Functor.elementsMk U (op ⦋m₁⦌) y₁, h₁Bound⟩, ⟨⟨⟩⟩, g₁⟩
  let f₁ : ⦋A.1.unop.len⦌ ⟶ ⦋m₁⦌ := Quiver.Hom.unop (g₁.val ≫ eqToHom hA.symm)
  have hg₁ :
      A.2 = U.map f₁.op y₁ := by
    -- Proof comment: the normalized object over `A` exposes an explicit simplex operator out of
    -- the degree of `A`.
    exact boundedSimplex_explicit_arrow_operator (U := U) hA y₁ g₁
  obtain ⟨m₂, y₂, h₂Bound, g₂, ⟨hZ₂⟩⟩ :=
    boundedSimplex_normalize_to_nondegenerate (U := U) d Y₂
  let Z₂ : CostructuredArrow (boundedSimplexProperty U d).ι A :=
    ⟨⟨Functor.elementsMk U (op ⦋m₂⦌) y₂, h₂Bound⟩, ⟨⟨⟩⟩, g₂⟩
  let f₂ : ⦋A.1.unop.len⦌ ⟶ ⦋m₂⦌ := Quiver.Hom.unop (g₂.val ≫ eqToHom hA.symm)
  have hg₂ :
      A.2 = U.map f₂.op y₂ := by
    -- Proof comment: the second normalized source is treated by the same explicit-operator
    -- description.
    exact boundedSimplex_explicit_arrow_operator (U := U) hA y₂ g₂
  have hm₁ : m₁ ≤ d := U.dim_le_of_nonDegenerate y₁ d
  have hm₂ : m₂ ≤ d := U.dim_le_of_nonDegenerate y₂ d
  obtain ⟨k, hk, h, _, r₁, r₂, hh₁, hh₂⟩ :=
    boundedSimplex_pair_operator_common_refinement (f₁ := f₁) (f₂ := f₂)
  let z : U _⦋k⦌ := U.map r₁.op y₁
  have hAz : A.2 = U.map h.op z := by
    -- Proof comment: the common quotient `h` carries the refined simplex `z` back to `A.2`.
    calc
      A.2 = U.map f₁.op y₁ := hg₁
      _ = U.map (h ≫ r₁).op y₁ := by rw [hh₁]
      _ = U.map h.op (U.map r₁.op y₁) := by
        simp [FunctorToTypes.map_comp_apply]
      _ = U.map h.op z := rfl
  have hz₂_map :
      U.map h.op (U.map r₂.op y₂) = U.map h.op z := by
    -- Proof comment: both normalized sources become the same simplex after postcomposing by `h`.
    calc
      U.map h.op (U.map r₂.op y₂) = U.map (h ≫ r₂).op y₂ := by
        simp [FunctorToTypes.map_comp_apply]
      _ = U.map f₂.op y₂ := by rw [hh₂]
      _ = A.2 := hg₂.symm
      _ = U.map h.op z := hAz
  have hz₂ : U.map r₂.op y₂ = z := by
    have hInjective : Function.Injective (U.map h.op) := by
      -- Proof comment: an epi in `SimplexCategory` splits, so `U.map h.op` has an explicit left
      -- inverse and is therefore injective.
      obtain ⟨⟨hh⟩⟩ := isSplitEpi_of_epi h
      intro a b hab
      have hCompA : U.map hh.section_.op (U.map h.op a) = U.map ((hh.section_ ≫ h).op) a := by
        rw [op_comp, FunctorToTypes.map_comp_apply]
      have hLeftInvA : U.map hh.section_.op (U.map h.op a) = a := by
        calc
          U.map hh.section_.op (U.map h.op a) = U.map ((hh.section_ ≫ h).op) a := hCompA
          _ = U.map (𝟙 _).op a := by
            rw [hh.id]
          _ = a := by
            rw [op_id, FunctorToTypes.map_id_apply]
      have hCompB : U.map hh.section_.op (U.map h.op b) = U.map ((hh.section_ ≫ h).op) b := by
        rw [op_comp, FunctorToTypes.map_comp_apply]
      have hLeftInvB : U.map hh.section_.op (U.map h.op b) = b := by
        calc
          U.map hh.section_.op (U.map h.op b) = U.map ((hh.section_ ≫ h).op) b := hCompB
          _ = U.map (𝟙 _).op b := by
            rw [hh.id]
          _ = b := by
            rw [op_id, FunctorToTypes.map_id_apply]
      have hSection := congrArg (U.map hh.section_.op) hab
      calc
        a = U.map hh.section_.op (U.map h.op a) := hLeftInvA.symm
        _ = U.map hh.section_.op (U.map h.op b) := hSection
        _ = b := hLeftInvB
    exact hInjective hz₂_map
  have hkBound : boundedSimplexProperty U d (Functor.elementsMk U (op ⦋k⦌) z) := by
    -- Proof comment: the common quotient degree stays below `m₁ + m₂ ≤ 2d`.
    calc
      k ≤ m₁ + m₂ := hk
      _ ≤ d + d := Nat.add_le_add hm₁ hm₂
      _ = 2 * d := by simp [two_mul]
  let Wobj : U.Elements := Functor.elementsMk U (op ⦋k⦌) z
  let Wleft : (boundedSimplexProperty U d).FullSubcategory := ⟨Wobj, hkBound⟩
  have hWMap : U.map (h.op ≫ eqToHom hA) z = A.2 := by
    -- Proof comment: package the refined simplex `z` as an actual object over `A`.
    simpa [FunctorToTypes.map_comp_apply, hA] using hAz.symm
  let Whom : Wleft.obj ⟶ A := CategoryOfElements.homMk Wobj A (h.op ≫ eqToHom hA) hWMap
  let W : CostructuredArrow (boundedSimplexProperty U d).ι A := ⟨Wleft, ⟨⟨⟩⟩, Whom⟩
  have hr₁_map : U.map r₁.op y₁ = z := rfl
  let hW₁Elem : Z₁.left.obj ⟶ W.left.obj := CategoryOfElements.homMk Z₁.left.obj W.left.obj r₁.op hr₁_map
  let hW₁Left : Z₁.left ⟶ W.left := ObjectProperty.homMk hW₁Elem
  have hW₁Comm : hW₁Left.hom ≫ W.hom = Z₁.hom := by
    -- Proof comment: the first comparison map composes to the original normalized arrow by the
    -- operator factorization `f₁ = h ≫ r₁`.
    apply CategoryOfElements.ext U
    dsimp [hW₁Left, hW₁Elem, W, Whom, Z₁, z, f₁]
    calc
      r₁.op ≫ (h.op ≫ eqToHom hA) = (h ≫ r₁).op ≫ eqToHom hA := by
        simp [Category.assoc]
      _ = f₁.op ≫ eqToHom hA := by rw [hh₁]
      _ = g₁.val := by
        dsimp [f₁]
        simp
  have hW₁ : Z₁ ⟶ W := CostructuredArrow.homMk hW₁Left hW₁Comm
  have hr₂_map : U.map r₂.op y₂ = z := hz₂
  let hW₂Elem : Z₂.left.obj ⟶ W.left.obj := CategoryOfElements.homMk Z₂.left.obj W.left.obj r₂.op hr₂_map
  let hW₂Left : Z₂.left ⟶ W.left := ObjectProperty.homMk hW₂Elem
  have hW₂Comm : hW₂Left.hom ≫ W.hom = Z₂.hom := by
    -- Proof comment: the second normalized arrow factors through the same common quotient object.
    apply CategoryOfElements.ext U
    dsimp [hW₂Left, hW₂Elem, W, Whom, Z₂, f₂]
    calc
      r₂.op ≫ (h.op ≫ eqToHom hA) = (h ≫ r₂).op ≫ eqToHom hA := by
        simp [Category.assoc]
      _ = f₂.op ≫ eqToHom hA := by rw [hh₂]
      _ = g₂.val := by
        dsimp [f₂]
        simp
  have hW₂ : Z₂ ⟶ W := CostructuredArrow.homMk hW₂Left hW₂Comm
  have hLeft : Zigzag Y₁ W := by
    -- Proof comment: move from `Y₁` to its normalized source and then into the common hub `W`.
    exact (Zigzag.of_hom hZ₁).symm.trans (Zigzag.of_hom hW₁)
  have hRight : Zigzag W Y₂ := by
    -- Proof comment: reverse the same two-step pattern on the second object.
    exact (Zigzag.of_hom hW₂).symm.trans (Zigzag.of_hom hZ₂)
  exact hLeft.trans hRight

/-- Helper for Lemma 14.17.3: the bounded full subcategory of simplex elements is initial in the
full simplex-elements category. -/
private theorem boundedSimplexInclusion_initial
    (d : ℕ) [U.HasDimensionLE d] :
    (boundedSimplexProperty U d).ι.Initial := by
  -- Proof comment: the source proof only needs the costructured arrow categories to be connected,
  -- and the preceding normalization lemma reduces the remaining work to a common-refinement zigzag.
  refine ObjectProperty.initial_ι (boundedSimplexProperty U d) ?_
  intro A _
  exact boundedSimplex_costructured_isConnected (U := U) d A

/-- Helper for Lemma 14.17.3: the bounded restriction of the simplex-elements diagram has a limit,
because after smallifying the indexing category it becomes a finite small category. -/
private theorem boundedSimplex_restrictedDiagram_hasLimit
    (d : ℕ) [U.HasDimensionLE d] :
    HasLimit (((boundedSimplexProperty U d).ι) ⋙ simplexElementsDiagram U V) := by
  let J := (boundedSimplexProperty U d).FullSubcategory
  let J' := AsSmall.{0} J
  haveI : Finite J' := by
    change Finite (ULift J)
    infer_instance
  haveI (X Y : J') : Finite (X ⟶ Y) := by
    change Finite (ULift (AsSmall.down.obj X ⟶ AsSmall.down.obj Y))
    infer_instance
  letI : FinCategory J' := by
    constructor
    · exact Fintype.ofFinite J'
    · intro X Y
      exact Fintype.ofFinite (X ⟶ Y)
  have hsmall :
      HasLimit (AsSmall.down ⋙ (((boundedSimplexProperty U d).ι) ⋙ simplexElementsDiagram U V)) := by
    infer_instance
  exact hasLimit_of_equivalence_comp (AsSmall.equiv.symm : J' ≌ J)

/-- Helper for Lemma 14.17.3: on the constant-object restriction, a morphism `f : X ⟶ Y` acts by
precomposition with the induced map on simplicial copowers. -/
private theorem const_hom_presheaf_map_app
    {X Y : C} (f : X ⟶ Y)
    (γ : (((const C).op ⋙ simplicialHomPresheaf U V).obj (op Y))) :
    (((const C).op ⋙ simplicialHomPresheaf U V).map f.op γ) =
      simplicialCopowerHom U ((const C).map f) ≫ γ :=
  rfl

/-- Helper for Lemma 14.17.3: precomposing a compatible family with `f : X ⟶ Y` acts degreewise
by left composition with `f`. -/
private theorem precompose_compatibleFamily_const_isCompatible
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((const C).obj Y) V) :
    SimplicialCopowerHomFamily.IsCompatible
      (U := U) (V := ((const C).obj X)) (W := V)
      (fun Δ u ↦ f ≫ F.1 Δ u) := by
  -- Proof comment: compatibility of `F` already gives the target equation; precompose it by `f`
  -- and reassociate.
  intro Δ Δ' g u
  simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) (F.2 g u)

/-- Helper for Lemma 14.17.3: the source-side action on compatible families induced by
`f : X ⟶ Y`. -/
private def precompose_compatibleFamily_const
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((const C).obj Y) V) :
    SimplicialCopowerHomFamily.Compatible U ((const C).obj X) V :=
  ⟨fun Δ u ↦ f ≫ F.1 Δ u,
    precompose_compatibleFamily_const_isCompatible (U := U) (V := V) f F⟩

/-- Helper for Lemma 14.17.3: under the compatible-family equivalence, the restricted presheaf map
is the source-side precomposition map. -/
private theorem homToCompatibleFamily_const_naturality
    {X Y : C} (f : X ⟶ Y)
    (γ : (((const C).op ⋙ simplicialHomPresheaf U V).obj (op Y))) :
    (simplicialCopowerCompatibleFamilyCorepresentableBy U
        ((const C).obj X)).homEquiv
        ((((const C).op ⋙ simplicialHomPresheaf U V).map f.op) γ) =
      precompose_compatibleFamily_const (U := U) (V := V) f
        ((simplicialCopowerCompatibleFamilyCorepresentableBy U
          ((const C).obj Y)).homEquiv γ) := by
  -- Proof comment: both sides are the degreewise family obtained by restricting
  -- `simplicialCopowerHom U ((const C).map f) ≫ γ` along the coproduct injections.
  apply Subtype.ext
  funext Δ u
  rw [const_hom_presheaf_map_app]
  simp [precompose_compatibleFamily_const, simplicialCopowerHom_app]

/-- Helper for Lemma 14.17.3: the compatible-family/cone equivalence intertwines source-side
precomposition with the cone-functor action. -/
private theorem compatibleFamily_const_equiv_cones_naturality
    {X Y : C} (f : X ⟶ Y)
    (F : SimplicialCopowerHomFamily.Compatible U ((const C).obj Y) V) :
    compatibleFamily_const_equiv_cones (U := U) (V := V) X
        (precompose_compatibleFamily_const (U := U) (V := V) f F) =
      (simplexElementsDiagram U V).cones.map f.op
        (compatibleFamily_const_equiv_cones (U := U) (V := V) Y F) := by
  -- Proof comment: both cones have component `(Δ,u) ↦ f ≫ F(Δ,u)`, so cone extensionality
  -- reduces to a definitional equality after unpacking the compatible family.
  cases F
  rfl

/-- Helper for Lemma 14.17.3: objectwise, the `ulift`ed constant-source restriction is the same
as the cone functor on the simplex-elements diagram. -/
private noncomputable def const_restriction_ulift_objEquiv_cones (X : C) :
    ULift ((((const C).op ⋙ simplicialHomPresheaf U V).obj (op X))) ≃
      (simplexElementsDiagram U V).cones.obj (op X) :=
  Equiv.ulift.trans
    (((simplicialCopowerCompatibleFamilyCorepresentableBy U
      ((const C).obj X)).homEquiv).trans
      (compatibleFamily_const_equiv_cones (U := U) (V := V) X))

/-- Helper for Lemma 14.17.3: the objectwise `ulift`-to-cones equivalence is natural in the
constant object. -/
private theorem const_restriction_ulift_objEquiv_cones_naturality
    {X Y : C} (f : X ⟶ Y)
    (g : ULift ((((const C).op ⋙ simplicialHomPresheaf U V).obj (op Y)))) :
    const_restriction_ulift_objEquiv_cones (U := U) (V := V) X
        (((((const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}).map f.op) g) =
      ((simplexElementsDiagram U V).cones.map f.op)
        (const_restriction_ulift_objEquiv_cones (U := U) (V := V) Y g) := by
  -- Proof comment: remove the `ULift`, use the compatible-family naturality bridge, and then
  -- invoke the pointwise cone-family naturality already proved above.
  cases g with
  | up γ =>
      change
        compatibleFamily_const_equiv_cones (U := U) (V := V) X
            ((simplicialCopowerCompatibleFamilyCorepresentableBy U
              ((const C).obj X)).homEquiv
              ((((const C).op ⋙ simplicialHomPresheaf U V).map f.op γ))) =
          (simplexElementsDiagram U V).cones.map f.op
            (compatibleFamily_const_equiv_cones (U := U) (V := V) Y
              ((simplicialCopowerCompatibleFamilyCorepresentableBy U
                ((const C).obj Y)).homEquiv γ))
      rw [homToCompatibleFamily_const_naturality]
      exact compatibleFamily_const_equiv_cones_naturality
        (U := U) (V := V) f
        ((simplicialCopowerCompatibleFamilyCorepresentableBy U
          ((const C).obj Y)).homEquiv γ)

/-- Helper for Lemma 14.17.3: after applying `uliftFunctor` to align universes, mapping out of a
constant simplicial source into `V` is naturally identified with the cone functor on the
simplex-elements diagram of `U`. -/
private noncomputable def const_restriction_ulift_iso_cones :
    (((const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}) ≅
      (simplexElementsDiagram U V).cones :=
  NatIso.ofComponents
    (fun X ↦
      Equiv.toIso (const_restriction_ulift_objEquiv_cones (U := U) (V := V) X.unop))
    (by
      intro X Y f
      ext g
      -- Proof comment: for a morphism in `Cᵒᵖ`, reuse the objectwise naturality statement with
      -- the corresponding morphism in `C`.
      exact const_restriction_ulift_objEquiv_cones_naturality
        (U := U) (V := V) (X := Y.unop) (Y := X.unop) f.unop g)

/-- Helper for Lemma 14.17.3: once the simplex-elements diagram has a limit, that limit
represents the `ulift` of the constant-source restriction of the mapping presheaf. -/
private noncomputable def const_restriction_ulift_representableBy_limit
    [HasLimit (simplexElementsDiagram U V)] :
    ((((const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w}).RepresentableBy
      (limit (simplexElementsDiagram U V))) :=
  (Limits.IsLimit.representableBy (limit.isLimit (simplexElementsDiagram U V))).ofIso
    (const_restriction_ulift_iso_cones (U := U) (V := V)).symm

/- Domain-style sampling for Lemma 14.17.3:
- primary domain: representability of the `C`-indexed restriction of the simplicial mapping-object
  presheaf under a finite-dimensionality hypothesis on the source simplicial set;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `simplicialHomPresheaf`,
  `(const C).op ⋙ simplicialHomPresheaf U V`,
  `SSet.HasDimensionLE`;
- best owner abstraction: the ambient owner remains `simplicialHomPresheaf U V`, while this lemma
  is the `source-facing` `bridge/view` statement for its restriction along constant simplicial
  objects, so it should not be collapsed to the later owner-level statement of Lemma `14.17.4`;
- primitive data: the simplicial set `U`, the simplicial object `V`, the direct degreewise-finite
  family on `U`, a `0`-simplex of `U`, and the chapter owner predicate
  `∃ d : ℕ, U.HasDimensionLE d`;
- derived API: representability of the restricted presheaf
  `(const C).op ⋙ simplicialHomPresheaf U V`, expressed with the canonical owner
  `((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable`.
-/

-- Proof sketch: choose `d` with `U.HasDimensionLE d`, replace the indexing category from the proof
-- of `Lemma 14.17.2` by its finite full subcategory on simplices in degrees at most `2d`, and use
-- the initial-functor criterion from `Definition 4.17.3` and `Lemma 4.17.4` to identify the
-- resulting finite limit with the original compatible-family limit.
/-- Lemma 14.17.3: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate (formalized as
`∃ d : ℕ, U.HasDimensionLE d`), then the presheaf
`X ↦ Mor_{Simp(C)}(X × U, V)` is representable.
Here this presheaf is the constant-object restriction
`(const C).op ⋙ simplicialHomPresheaf U V` from Lemma 14.17.2. -/
@[stacks 017K]
theorem simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable := by
  obtain ⟨d, hd⟩ := hU
  let _ : U.HasDimensionLE d := hd
  have hInitial : (boundedSimplexProperty U d).ι.Initial :=
    boundedSimplexInclusion_initial (U := U) d
  have hBoundedLimit :
      HasLimit (((boundedSimplexProperty U d).ι) ⋙ simplexElementsDiagram U V) :=
    boundedSimplex_restrictedDiagram_hasLimit (U := U) (V := V) d
  have hLimit : HasLimit (simplexElementsDiagram U V) :=
    Functor.Initial.hasLimit_of_comp ((boundedSimplexProperty U d).ι)
  -- The simplex-elements diagram now has a limit, so the cone functor is representable, and the
  -- natural cone description of the `ulift`ed restricted mapping presheaf finishes the argument.
  have hRepUlift :
      ((((const C).op ⋙ simplicialHomPresheaf U V) ⋙ uliftFunctor.{w})).IsRepresentable :=
    (const_restriction_ulift_representableBy_limit (U := U) (V := V)).isRepresentable
  exact (Functor.isRepresentable_comp_uliftFunctor_iff
    (F := ((const C).op ⋙ simplicialHomPresheaf U V))).mp hRepUlift

instance simplicialHomPresheaf_const_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    ((const C).op ⋙ simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate U V Fact.out

end Restriction

end

end CategoryTheory
